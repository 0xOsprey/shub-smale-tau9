/*
 * Unconditional Z-wide certifier for the Shub-Smale tau-conjecture.
 *
 * Proves unconditionally over ALL of Z (no magnitude bound on roots) that every
 * canonical tau-gate constant-free SLP over {1, x} and {+, -, *} either:
 *   1. Is certified to have <= K distinct integer roots in Z via:
 *      (a) Product bound: f = A * B with z_ub(A) + z_ub(B) <= K, or
 *      (b) Simple-Root Modular Certificate modulo a prime p in {31, 19, 23, 29, 37, 41, 43}:
 *          f mod p is nonzero (zeros < p), has no double root in F_p
 *          (no a in F_p with f(a) = f'(a) = 0 mod p), and has <= K roots in F_p.
 *   2. Is zero or duplicates an earlier gate (so computable in <= tau - 1 gates).
 *   3. Is logged (deduplicated by 3-prime hash) to a survivor file for 100% exact
 *      Z[x] root certification in verify_z9_all_Z.py.
 *
 * Uses the exact same lossless canonicalization as tau_parallel.c:
 *   - Sign canonicalization (+: i<=j, -: i<j, *: i<=j)
 *   - Dead-gate pruning (unused_cnt <= tau - k + 1)
 *   - Duplicate/zero pruning via 2-point hash (mod P1=2^31-1, P2=10^9+9)
 *   - Lex-minimal topological ordering for independent gates
 *   - Lock-free / mutex dynamic work queue across N threads
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <pthread.h>

#define MAX_TAU 12
#ifdef ALT_PRIMES
/* Independent second prime triple for deterministic hash cross-check */
#define MP 2147483629U   /* prime < 2^31 - 1 */
#define P2 1000000021ULL /* prime */
#define P3 1000000033ULL /* prime */
#define HASH_X1 987654321U
#define HASH_X2 123456789ULL
#define HASH_X3 555555555ULL
#else
#define MP 2147483647U   /* 2^31 - 1 */
#define P2 1000000009ULL
#define P3 1000000007ULL
#define HASH_X1 314159265U
#define HASH_X2 271828182ULL
#define HASH_X3 141421356ULL
#endif

#define P1_PRIME 31
#define NUM_FALLBACK_PRIMES 3
static const int FALLBACK_PRIMES[NUM_FALLBACK_PRIMES] = {19, 23, 29};

#ifdef ALT_PRIMES
static inline uint32_t madd(uint32_t a, uint32_t b) {
    uint32_t s = a + b;
    return s >= MP ? s - MP : s;
}

static inline uint32_t msub(uint32_t a, uint32_t b) {
    return a >= b ? a - b : a + (MP - b);
}

static inline uint32_t mmul(uint32_t a, uint32_t b) {
    return (uint32_t)(((uint64_t)a * (uint64_t)b) % (uint64_t)MP);
}
#else
static inline uint32_t madd(uint32_t a, uint32_t b) {
    uint32_t s = a + b;
    s = (s & MP) + (s >> 31);
    return s >= MP ? s - MP : s;
}

static inline uint32_t msub(uint32_t a, uint32_t b) {
    uint32_t s = a + (MP - b);
    s = (s & MP) + (s >> 31);
    return s >= MP ? s - MP : s;
}

static inline uint32_t mmul(uint32_t a, uint32_t b) {
    uint64_t t = (uint64_t)a * (uint64_t)b;
    uint64_t s = (t & MP) + (t >> 31);
    s = (s & MP) + (s >> 31);
    return (uint32_t)(s >= MP ? s - MP : s);
}
#endif

static inline uint8_t mod31_reduce(uint16_t t) {
    t = (t & 31U) + (t >> 5);
    t = (t & 31U) + (t >> 5);
    return (uint8_t)(t >= 31U ? t - 31U : t);
}

typedef struct {
    int op;
    int i;
    int j;
} Gate;

typedef struct {
    Gate prefix[3];
    int key[3];
    uint32_t unused_mask;
    int unused_cnt;
    int prefix_len;
} WorkItem;

typedef struct {
    int target_tau;
    int cert_bound; /* K: certify <= K roots */
    uint64_t nodes_visited;
    uint64_t leaves_checked;
    uint64_t cert_deg;
    uint64_t cert_prod;
    uint64_t cert_p1;
    uint64_t cert_taylor;
    uint64_t cert_dup_zero;
    uint64_t cert_fallback[NUM_FALLBACK_PRIMES];
    uint64_t survivors_raw;

    uint8_t v31[MAX_TAU + 2][32];
    uint8_t d31[MAX_TAU + 2][32];
    uint8_t z_ub[MAX_TAU + 2];
    uint16_t deg_ub[MAX_TAU + 2];
    uint16_t prod_mask[MAX_TAU + 2];

    uint32_t h1[MAX_TAU + 2];
    uint64_t h2[MAX_TAU + 2];
    uint32_t nh1[MAX_TAU + 2];
    uint64_t nh2[MAX_TAU + 2];
    Gate path[MAX_TAU];
    int key[MAX_TAU];
} SearchCtx;

/* Deduplicated survivor hash table (open addressing) */
typedef struct {
    uint32_t h1;
    uint32_t h2;
    uint32_t h3;
    uint8_t used;
} SurvKey;

static pthread_mutex_t g_surv_lock = PTHREAD_MUTEX_INITIALIZER;
static SurvKey *g_surv_tab = NULL;
static size_t g_surv_cap = 0;
static size_t g_surv_cnt = 0;
static FILE *g_surv_fp = NULL;

static void surv_table_reset(void) {
    if (g_surv_tab) free(g_surv_tab);
    g_surv_cap = 1 << 16;
    g_surv_tab = (SurvKey *)calloc(g_surv_cap, sizeof(SurvKey));
    g_surv_cnt = 0;
}

static void surv_table_grow(void) {
    size_t new_cap = g_surv_cap * 2;
    SurvKey *nt = (SurvKey *)calloc(new_cap, sizeof(SurvKey));
    size_t mask = new_cap - 1;
    for (size_t i = 0; i < g_surv_cap; i++) {
        if (!g_surv_tab[i].used) continue;
        uint64_t mix = ((uint64_t)g_surv_tab[i].h1 * 0x9e3779b97f4a7c15ULL) ^
                       ((uint64_t)g_surv_tab[i].h2 * 0xbf58476d1ce4e5b9ULL) ^
                       ((uint64_t)g_surv_tab[i].h3 * 0x94d049bb133111ebULL);
        size_t pos = (size_t)(mix & mask);
        while (nt[pos].used) pos = (pos + 1) & mask;
        nt[pos] = g_surv_tab[i];
    }
    free(g_surv_tab);
    g_surv_tab = nt;
    g_surv_cap = new_cap;
}

static void write_slp_line(FILE *fp, const Gate *gates, int tau, uint32_t h1, uint32_t h2, uint32_t h3) {
    const char *ops = "+-*";
    fprintf(fp, "%u %u %u | ", h1, h2, h3);
    for (int k = 0; k < tau; k++) {
        if (k > 0) fprintf(fp, "; ");
        int i = gates[k].i - 1;
        int j = gates[k].j - 1;
        char si[16], sj[16];
        if (i == -1) strcpy(si, "1");
        else if (i == 0) strcpy(si, "x");
        else sprintf(si, "g%d", i);
        if (j == -1) strcpy(sj, "1");
        else if (j == 0) strcpy(sj, "x");
        else sprintf(sj, "g%d", j);
        fprintf(fp, "g%d = %s %c %s", k + 1, si, ops[gates[k].op], sj);
    }
    fprintf(fp, "\n");
}

static uint32_t compute_h3(const Gate *gates, int tau) {
    uint64_t h[MAX_TAU + 2];
    h[0] = 1;
    h[1] = HASH_X3;
    for (int d = 0; d < tau; d++) {
        uint64_t a = h[gates[d].i], b = h[gates[d].j];
        int op = gates[d].op;
        if (op == 0) {
            uint64_t s = a + b;
            h[d + 2] = s >= P3 ? s - P3 : s;
        } else if (op == 1) {
            h[d + 2] = a >= b ? a - b : a + P3 - b;
        } else {
            h[d + 2] = (a * b) % P3;
        }
    }
    return (uint32_t)h[tau + 1];
}

static void record_survivor(const Gate *gates, int tau, uint32_t r1, uint64_t r2) {
    uint32_t r3 = compute_h3(gates, tau);
    /* Canonicalize sign so f and -f share the same key */
    uint32_t nr1 = r1 == 0 ? 0 : MP - r1;
    uint32_t nr2 = r2 == 0 ? 0 : (uint32_t)(P2 - r2);
    uint32_t nr3 = r3 == 0 ? 0 : (uint32_t)(P3 - r3);
    uint32_t k1 = r1, k2 = (uint32_t)r2, k3 = r3;
    if (nr1 < k1 || (nr1 == k1 && (nr2 < k2 || (nr2 == k2 && nr3 < k3)))) {
        k1 = nr1; k2 = nr2; k3 = nr3;
    }

    pthread_mutex_lock(&g_surv_lock);
    if (g_surv_cnt * 2 >= g_surv_cap) surv_table_grow();
    size_t mask = g_surv_cap - 1;
    uint64_t mix = ((uint64_t)k1 * 0x9e3779b97f4a7c15ULL) ^
                   ((uint64_t)k2 * 0xbf58476d1ce4e5b9ULL) ^
                   ((uint64_t)k3 * 0x94d049bb133111ebULL);
    size_t pos = (size_t)(mix & mask);
    int found = 0;
    while (g_surv_tab[pos].used) {
        if (g_surv_tab[pos].h1 == k1 && g_surv_tab[pos].h2 == k2 && g_surv_tab[pos].h3 == k3) {
            found = 1;
            break;
        }
        pos = (pos + 1) & mask;
    }
    if (!found) {
        g_surv_tab[pos] = (SurvKey){k1, k2, k3, 1};
        g_surv_cnt++;
        if (g_surv_fp) {
            write_slp_line(g_surv_fp, gates, tau, k1, k2, k3);
        }
    }
    pthread_mutex_unlock(&g_surv_lock);
}

static void init_base(SearchCtx *ctx) {
    for (int a = 0; a < P1_PRIME; a++) {
        ctx->v31[0][a] = 1;
        ctx->d31[0][a] = 0;
        ctx->v31[1][a] = (uint8_t)a;
        ctx->d31[1][a] = 1;
    }
    ctx->z_ub[0] = 0; /* constant 1 has 0 roots */
    ctx->z_ub[1] = 1; /* x has 1 root */
    ctx->deg_ub[0] = 0;
    ctx->deg_ub[1] = 1;
    ctx->prod_mask[0] = 0;
    ctx->prod_mask[1] = (1U << 1);

    ctx->h1[0] = 1;
    ctx->h2[0] = 1;
    ctx->nh1[0] = MP - 1;
    ctx->nh2[0] = P2 - 1;

    ctx->h1[1] = HASH_X1;
    ctx->h2[1] = HASH_X2;
    ctx->nh1[1] = MP - HASH_X1;
    ctx->nh2[1] = P2 - HASH_X2;
}

static inline int compute_hash_and_check_dup(
    SearchCtx *ctx, int idx, int op, int i, int j,
    uint32_t *out_h1, uint64_t *out_h2
) {
    uint32_t a1 = ctx->h1[i], b1 = ctx->h1[j];
    uint64_t a2 = ctx->h2[i], b2 = ctx->h2[j];
    uint32_t r1;
    uint64_t r2;
    if (op == 0) {
        r1 = madd(a1, b1);
        r2 = a2 + b2; if (r2 >= P2) r2 -= P2;
    } else if (op == 1) {
        r1 = msub(a1, b1);
        r2 = a2 >= b2 ? a2 - b2 : a2 + P2 - b2;
    } else {
        r1 = mmul(a1, b1);
        r2 = (a2 * b2) % P2;
    }
    if (r1 == 0 && r2 == 0) return 0;
    for (int m = 0; m < idx; m++) {
        if ((r1 == ctx->h1[m] && r2 == ctx->h2[m]) ||
            (r1 == ctx->nh1[m] && r2 == ctx->nh2[m])) {
            return 0;
        }
    }
    *out_h1 = r1;
    *out_h2 = r2;
    return 1;
}

static inline int sum_mask_ub(uint16_t mask, const uint8_t *z_ub) {
    int s = 0;
    while (mask) {
        int a = __builtin_ctz(mask);
        s += z_ub[a];
        mask &= (uint16_t)(mask - 1);
    }
    return s;
}

static inline void eval_gate_p1(SearchCtx *ctx, int idx, int op, int i, int j) {
    const uint8_t * __restrict va = ctx->v31[i];
    const uint8_t * __restrict da = ctx->d31[i];
    const uint8_t * __restrict vb = ctx->v31[j];
    const uint8_t * __restrict db = ctx->d31[j];
    uint8_t * __restrict vc = ctx->v31[idx];
    uint8_t * __restrict dc = ctx->d31[idx];

    int zeros = 0, doubles = 0;
    if (op == 0) {
        for (int a = 0; a < P1_PRIME; a++) {
            uint8_t v = va[a] + vb[a]; if (v >= 31) v -= 31;
            uint8_t d = da[a] + db[a]; if (d >= 31) d -= 31;
            vc[a] = v;
            dc[a] = d;
            int iz = (v == 0);
            zeros += iz;
            doubles += (iz & (d == 0));
        }
    } else if (op == 1) {
        for (int a = 0; a < P1_PRIME; a++) {
            uint8_t v = va[a] >= vb[a] ? va[a] - vb[a] : va[a] + 31 - vb[a];
            uint8_t d = da[a] >= db[a] ? da[a] - db[a] : da[a] + 31 - db[a];
            vc[a] = v;
            dc[a] = d;
            int iz = (v == 0);
            zeros += iz;
            doubles += (iz & (d == 0));
        }
    } else {
        for (int a = 0; a < P1_PRIME; a++) {
            uint8_t v = mod31_reduce((uint16_t)va[a] * (uint16_t)vb[a]);
            uint8_t d = mod31_reduce((uint16_t)da[a] * (uint16_t)vb[a] + (uint16_t)va[a] * (uint16_t)db[a]);
            vc[a] = v;
            dc[a] = d;
            int iz = (v == 0);
            zeros += iz;
            doubles += (iz & (d == 0));
        }
    }

    uint16_t dub = (op == 2)
        ? (uint16_t)(ctx->deg_ub[i] + ctx->deg_ub[j])
        : (ctx->deg_ub[i] > ctx->deg_ub[j] ? ctx->deg_ub[i] : ctx->deg_ub[j]);
    ctx->deg_ub[idx] = dub;

    uint16_t pmask;
    if (dub == 0) {
        pmask = 0;
    } else if (op == 2) {
        pmask = ctx->prod_mask[i] | ctx->prod_mask[j];
    } else if (op == 0 && i == j) {
        pmask = ctx->prod_mask[i];
    } else {
        pmask = (uint16_t)(1U << idx);
    }
    ctx->prod_mask[idx] = pmask;

    uint8_t ub = (dub < 255) ? (uint8_t)dub : 255;
    if (zeros < P1_PRIME && doubles == 0 && zeros < ub) ub = (uint8_t)zeros;
    if (op == 2) {
        int pub = sum_mask_ub(pmask, ctx->z_ub);
        if (pub < ub) ub = (uint8_t)pub;
    } else if (op == 0 && i == j) {
        if (ctx->z_ub[i] < ub) ub = ctx->z_ub[i];
    }
    ctx->z_ub[idx] = ub;
}

/* Exact __int128 truncated Taylor expansion of SLP at x = r0 (mod t^8).
 * Returns 1 if exact (no overflow) and finds lowest nonzero term c_m (0 <= m < 8),
 * writing m to *out_mult and c_m to *out_cm. Returns 0 on overflow or m >= 8. */
#define TAYLOR_DEG 12
static int exact_taylor_at(const Gate *gates, int tau, int r0, int *out_mult, __int128 *out_cm) {
    static const __int128 LIM = (__int128)100000000000000000LL; /* 10^17: 8 * LIM^2 < 2^127 */
    __int128 c[MAX_TAU + 2][TAYLOR_DEG];
    memset(c[0], 0, sizeof(c[0]));
    memset(c[1], 0, sizeof(c[1]));
    c[0][0] = 1;
    c[1][0] = r0;
    c[1][1] = 1;

    for (int step = 0; step < tau; step++) {
        int idx = step + 2;
        int op = gates[step].op, i = gates[step].i, j = gates[step].j;
        if (op == 0) {
            for (int k = 0; k < TAYLOR_DEG; k++) {
                __int128 v = c[i][k] + c[j][k];
                if (v > LIM || v < -LIM) return 0;
                c[idx][k] = v;
            }
        } else if (op == 1) {
            for (int k = 0; k < TAYLOR_DEG; k++) {
                __int128 v = c[i][k] - c[j][k];
                if (v > LIM || v < -LIM) return 0;
                c[idx][k] = v;
            }
        } else {
            for (int k = 0; k < TAYLOR_DEG; k++) {
                __int128 acc = 0;
                for (int a = 0; a <= k; a++) {
                    acc += c[i][a] * c[j][k - a];
                }
                if (acc > LIM || acc < -LIM) return 0;
                c[idx][k] = acc;
            }
        }
    }
    for (int k = 0; k < TAYLOR_DEG; k++) {
        if (c[tau + 1][k] != 0) {
            *out_mult = k;
            *out_cm = c[tau + 1][k];
            return 1;
        }
    }
    return 0;
}

/* Try to certify f using exact multiplicities at double-root residues among {0, 1, -1, 2, -2, 3, -3}
 * modulo prime p (p >= 19 odd; max pairwise diff is 6 < 19 so gcd(p, r - r') = 1).
 * `dbl_mask` has bits 0..6 for {0, 1, -1, 2, -2, 3, -3}.
 * Caller guarantees NO double roots exist outside dbl_mask in F_p, and total distinct zeros in F_p <= K. */
#define NUM_KNOWN_ROOTS 7
static const int KNOWN_ROOTS[NUM_KNOWN_ROOTS] = {0, 1, -1, 2, -2, 3, -3};

static int certify_taylor_roots(const Gate *gates, int tau, int p, int dbl_mask, int dub, int K) {
    for (int b = 0; b < NUM_KNOWN_ROOTS; b++) {
        if (!((dbl_mask >> b) & 1)) continue;
        int m = 0;
        __int128 cm = 0;
        if (!exact_taylor_at(gates, tau, KNOWN_ROOTS[b], &m, &cm)) return 0;
        if (m < 1) return 0;
        if ((cm % p) == 0) return 0;
    }
    (void)dub;
    (void)K;
    return 1;
}

/* Evaluate full SLP mod prime p (dual numbers + product z_ub propagation).
 * Returns 1 if certified <= K roots over all Z, 0 otherwise. */
static int certify_slp_mod_p(const Gate *gates, int tau, int p, int K) {
    uint8_t v[MAX_TAU + 2][48];
    uint8_t d[MAX_TAU + 2][48];
    uint8_t ub[MAX_TAU + 2];
    uint16_t dub[MAX_TAU + 2];
    uint16_t pmask[MAX_TAU + 2];

    for (int a = 0; a < p; a++) {
        v[0][a] = 1; d[0][a] = 0;
        v[1][a] = (uint8_t)a; d[1][a] = 1;
    }
    ub[0] = 0; dub[0] = 0; pmask[0] = 0;
    ub[1] = 1; dub[1] = 1; pmask[1] = (1U << 1);

    int last_zeros = 0, last_other_doubles = 0, last_dbl_mask = 0;
    for (int step = 0; step < tau; step++) {
        int idx = step + 2;
        int op = gates[step].op, i = gates[step].i, j = gates[step].j;
        uint16_t cur_dub = (op == 2) ? (uint16_t)(dub[i] + dub[j])
                                     : (dub[i] > dub[j] ? dub[i] : dub[j]);
        dub[idx] = cur_dub;
        uint16_t cur_pm;
        if (cur_dub == 0) cur_pm = 0;
        else if (op == 2) cur_pm = pmask[i] | pmask[j];
        else if (op == 0 && i == j) cur_pm = pmask[i];
        else cur_pm = (uint16_t)(1U << idx);
        pmask[idx] = cur_pm;

        if (op == 2 && step == tau - 1) {
            if (sum_mask_ub(cur_pm, ub) <= K) return 1;
        }
        int zeros = 0, doubles = 0, dbl_mask = 0, other_doubles = 0;
        if (op == 0) {
            for (int a = 0; a < p; a++) {
                uint8_t vv = v[i][a] + v[j][a]; if (vv >= p) vv -= p;
                uint8_t dd = d[i][a] + d[j][a]; if (dd >= p) dd -= p;
                v[idx][a] = vv; d[idx][a] = dd;
                if (vv == 0) {
                    zeros++;
                    if (dd == 0) {
                        doubles++;
                        if (a == 0) dbl_mask |= 1;
                        else if (a == 1) dbl_mask |= 2;
                        else if (a == p - 1) dbl_mask |= 4;
                        else if (a == 2) dbl_mask |= 8;
                        else if (a == p - 2) dbl_mask |= 16;
                        else if (a == 3) dbl_mask |= 32;
                        else if (a == p - 3) dbl_mask |= 64;
                        else other_doubles++;
                    }
                }
            }
        } else if (op == 1) {
            for (int a = 0; a < p; a++) {
                uint8_t vv = v[i][a] >= v[j][a] ? v[i][a] - v[j][a] : v[i][a] + p - v[j][a];
                uint8_t dd = d[i][a] >= d[j][a] ? d[i][a] - d[j][a] : d[i][a] + p - d[j][a];
                v[idx][a] = vv; d[idx][a] = dd;
                if (vv == 0) {
                    zeros++;
                    if (dd == 0) {
                        doubles++;
                        if (a == 0) dbl_mask |= 1;
                        else if (a == 1) dbl_mask |= 2;
                        else if (a == p - 1) dbl_mask |= 4;
                        else if (a == 2) dbl_mask |= 8;
                        else if (a == p - 2) dbl_mask |= 16;
                        else if (a == 3) dbl_mask |= 32;
                        else if (a == p - 3) dbl_mask |= 64;
                        else other_doubles++;
                    }
                }
            }
        } else {
            for (int a = 0; a < p; a++) {
                uint8_t vv = (uint8_t)(((int)v[i][a] * (int)v[j][a]) % p);
                uint8_t dd = (uint8_t)(((int)d[i][a] * (int)v[j][a] + (int)v[i][a] * (int)d[j][a]) % p);
                v[idx][a] = vv; d[idx][a] = dd;
                if (vv == 0) {
                    zeros++;
                    if (dd == 0) {
                        doubles++;
                        if (a == 0) dbl_mask |= 1;
                        else if (a == 1) dbl_mask |= 2;
                        else if (a == p - 1) dbl_mask |= 4;
                        else if (a == 2) dbl_mask |= 8;
                        else if (a == p - 2) dbl_mask |= 16;
                        else if (a == 3) dbl_mask |= 32;
                        else if (a == p - 3) dbl_mask |= 64;
                        else other_doubles++;
                    }
                }
            }
        }
        uint8_t cur_ub = (cur_dub < 255) ? (uint8_t)cur_dub : 255;
        if (zeros < p && doubles == 0 && zeros < cur_ub) cur_ub = (uint8_t)zeros;
        if (op == 2) {
            int pub = sum_mask_ub(cur_pm, ub);
            if (pub < cur_ub) cur_ub = (uint8_t)pub;
        } else if (op == 0 && i == j) {
            if (ub[i] < cur_ub) cur_ub = ub[i];
        }
        ub[idx] = cur_ub;
        if (step == tau - 1) {
            last_zeros = zeros;
            last_other_doubles = other_doubles;
            last_dbl_mask = dbl_mask;
        }
    }
    if (ub[tau + 1] <= K) return 1;
    if (last_zeros <= K && last_other_doubles == 0 && last_dbl_mask != 0) {
        if (certify_taylor_roots(gates, tau, p, last_dbl_mask, dub[tau + 1], K)) return 1;
    }
    return 0;
}

static inline void check_leaf(SearchCtx *ctx, int depth, int idx, int op, int i, int j) {
    ctx->leaves_checked++;
    int K = ctx->cert_bound;

    /* Fast path 0a: exact degree upper bound deg(f) <= K */
    int dub = (op == 2)
        ? ((int)ctx->deg_ub[i] + (int)ctx->deg_ub[j])
        : (ctx->deg_ub[i] > ctx->deg_ub[j] ? (int)ctx->deg_ub[i] : (int)ctx->deg_ub[j]);
    if (dub <= K) {
        ctx->cert_deg++;
        return;
    }

    /* Fast path 0b: atomic product-factor union bound z(A * B) <= sum_{a in prod_mask} z_ub(a),
     * and z(A + A) = z(2A) = z(A) */
    if (op == 2) {
        uint16_t pmask = ctx->prod_mask[i] | ctx->prod_mask[j];
        if (sum_mask_ub(pmask, ctx->z_ub) <= K) {
            ctx->cert_prod++;
            return;
        }
    } else if (op == 0 && i == j) {
        if (ctx->z_ub[i] <= K) {
            ctx->cert_prod++;
            return;
        }
    }

    /* Fast path 1: Simple-Root Modular Certificate mod p1 = 31 (ZERO multiplications!) */
    const uint8_t * __restrict va = ctx->v31[i];
    const uint8_t * __restrict da = ctx->d31[i];
    const uint8_t * __restrict vb = ctx->v31[j];
    const uint8_t * __restrict db = ctx->d31[j];
    int zeros = 0, doubles = 0;

    if (op == 0) {
        for (int a = 0; a < P1_PRIME; a++) {
            uint8_t sv = va[a] + vb[a];
            uint8_t sd = da[a] + db[a];
            int iz = (sv == 0) | (sv == 31);
            int idz = (sd == 0) | (sd == 31);
            zeros += iz;
            doubles += (iz & idz);
        }
    } else if (op == 1) {
        for (int a = 0; a < P1_PRIME; a++) {
            int iz = (va[a] == vb[a]);
            int idz = (da[a] == db[a]);
            zeros += iz;
            doubles += (iz & idz);
        }
    } else {
        for (int a = 0; a < P1_PRIME; a++) {
            int za = (va[a] == 0);
            int zb = (vb[a] == 0);
            int iz = za | zb;
            int id = (za & zb) | (za & (da[a] == 0)) | (zb & (db[a] == 0));
            zeros += iz;
            doubles += id;
        }
    }

    if (zeros <= K && doubles == 0) {
        ctx->cert_p1++;
        return;
    }

    /* Filter out zero / duplicate polynomials (computable in <= tau - 1 gates) */
    uint32_t r1;
    uint64_t r2;
    if (!compute_hash_and_check_dup(ctx, idx, op, i, j, &r1, &r2)) {
        ctx->cert_dup_zero++;
        return;
    }

    /* Fast path 1b: if mod 31 has <= K roots and ONLY double roots at {0, ±1, ±2, ±3}, certify via exact Taylor! */
    ctx->path[depth] = (Gate){op, i, j};
    if (zeros <= K && doubles > 0) {
        int dbl_mask = 0;
        int known_doubles = 0;
        static const int PTS[NUM_KNOWN_ROOTS] = {0, 1, 30, 2, 29, 3, 28};
        for (int b = 0; b < NUM_KNOWN_ROOTS; b++) {
            int a = PTS[b];
            int iz, id;
            if (op == 0) {
                uint8_t sv = va[a] + vb[a];
                uint8_t sd = da[a] + db[a];
                iz = (sv == 0) | (sv == 31);
                id = iz & ((sd == 0) | (sd == 31));
            } else if (op == 1) {
                iz = (va[a] == vb[a]);
                id = iz & (da[a] == db[a]);
            } else {
                int za = (va[a] == 0), zb = (vb[a] == 0);
                id = (za & zb) | (za & (da[a] == 0)) | (zb & (db[a] == 0));
            }
            if (id) {
                dbl_mask |= (1 << b);
                known_doubles++;
            }
        }
        if (known_doubles == doubles && dbl_mask != 0) {
            if (certify_taylor_roots(ctx->path, ctx->target_tau, P1_PRIME, dbl_mask, dub, K)) {
                ctx->cert_taylor++;
                return;
            }
        }
    }

    /* Fallback primes */
    for (int f = 0; f < NUM_FALLBACK_PRIMES; f++) {
        if (certify_slp_mod_p(ctx->path, ctx->target_tau, FALLBACK_PRIMES[f], K)) {
            ctx->cert_fallback[f]++;
            return;
        }
    }

    /* Survivor! Record deduplicated SLP for exact Z[x] verification */
    ctx->survivors_raw++;
    record_survivor(ctx->path, ctx->target_tau, r1, r2);
}

static void dfs(SearchCtx *ctx, int depth, uint32_t unused_mask, int unused_cnt) {
    int tau = ctx->target_tau;
    int idx = depth + 2;
    int rem_after = tau - 1 - depth;
    int max_unused_after = rem_after + 1;
    int prev_idx = idx - 1;

    if (depth == tau - 1) {
        if (unused_cnt == 2) {
            int i = __builtin_ctz(unused_mask);
            int j = __builtin_ctz(unused_mask ^ (1U << i));
            check_leaf(ctx, depth, idx, 0, i, j);
            check_leaf(ctx, depth, idx, 1, i, j);
            check_leaf(ctx, depth, idx, 2, i, j);
            return;
        }
        if (unused_cnt == 0) {
            for (int i = 0; i < idx; i++) {
                for (int j = i; j < idx; j++) {
                    check_leaf(ctx, depth, idx, 0, i, j);
                    if (i != j) check_leaf(ctx, depth, idx, 1, i, j);
                    check_leaf(ctx, depth, idx, 2, i, j);
                }
            }
            return;
        }
        int u0 = __builtin_ctz(unused_mask);
        for (int other = 0; other < idx; other++) {
            int i = other < u0 ? other : u0;
            int j = other < u0 ? u0 : other;
            check_leaf(ctx, depth, idx, 0, i, j);
            if (i != j) check_leaf(ctx, depth, idx, 1, i, j);
            check_leaf(ctx, depth, idx, 2, i, j);
        }
        return;
    }

    int min_removed = unused_cnt + 1 - max_unused_after;

    for (int i = 0; i < idx; i++) {
        int ui = (unused_mask >> i) & 1U;
        if (min_removed == 2 && !ui) continue;
        for (int j = i; j < idx; j++) {
            int uj = (unused_mask >> j) & 1U;
            int removed = (i == j) ? ui : (ui + uj);
            if (removed < min_removed) continue;

            int uses_prev = (depth > 0) && (i == prev_idx || j == prev_idx);

            for (int op = 0; op < 3; op++) {
                if (op == 1 && i == j) continue;
                int k = (op << 10) | (i << 5) | j;
                if (depth > 0 && !uses_prev && k < ctx->key[depth - 1]) continue;

                uint32_t r1;
                uint64_t r2;
                if (!compute_hash_and_check_dup(ctx, idx, op, i, j, &r1, &r2)) continue;

                ctx->nodes_visited++;
                ctx->h1[idx] = r1;
                ctx->h2[idx] = r2;
                ctx->nh1[idx] = r1 == 0 ? 0 : MP - r1;
                ctx->nh2[idx] = r2 == 0 ? 0 : P2 - r2;
                ctx->path[depth] = (Gate){op, i, j};
                ctx->key[depth] = k;

                eval_gate_p1(ctx, idx, op, i, j);

                uint32_t next_mask = (unused_mask & ~(1U << i) & ~(1U << j)) | (1U << idx);
                int next_cnt = unused_cnt - removed + 1;
                dfs(ctx, depth + 1, next_mask, next_cnt);
            }
        }
    }
}

static WorkItem *g_work = NULL;
static int g_work_cnt = 0;
static int g_work_cap = 0;
static int g_work_next = 0;
static pthread_mutex_t g_work_lock = PTHREAD_MUTEX_INITIALIZER;

static void collect_work(SearchCtx *ctx, int depth, int split_depth, uint32_t unused_mask, int unused_cnt) {
    if (depth == split_depth) {
        if (g_work_cnt == g_work_cap) {
            g_work_cap = g_work_cap ? g_work_cap * 2 : 1024;
            g_work = (WorkItem *)realloc(g_work, sizeof(WorkItem) * g_work_cap);
        }
        WorkItem *w = &g_work[g_work_cnt++];
        memcpy(w->prefix, ctx->path, sizeof(Gate) * split_depth);
        memcpy(w->key, ctx->key, sizeof(int) * split_depth);
        w->unused_mask = unused_mask;
        w->unused_cnt = unused_cnt;
        w->prefix_len = split_depth;
        return;
    }

    int tau = ctx->target_tau;
    int idx = depth + 2;
    int rem_after = tau - 1 - depth;
    int max_unused_after = rem_after + 1;
    int prev_idx = idx - 1;
    int min_removed = unused_cnt + 1 - max_unused_after;

    for (int i = 0; i < idx; i++) {
        int ui = (unused_mask >> i) & 1U;
        if (min_removed == 2 && !ui) continue;
        for (int j = i; j < idx; j++) {
            int uj = (unused_mask >> j) & 1U;
            int removed = (i == j) ? ui : (ui + uj);
            if (removed < min_removed) continue;

            int uses_prev = (depth > 0) && (i == prev_idx || j == prev_idx);

            for (int op = 0; op < 3; op++) {
                if (op == 1 && i == j) continue;
                int k = (op << 10) | (i << 5) | j;
                if (depth > 0 && !uses_prev && k < ctx->key[depth - 1]) continue;

                uint32_t r1;
                uint64_t r2;
                if (!compute_hash_and_check_dup(ctx, idx, op, i, j, &r1, &r2)) continue;

                ctx->h1[idx] = r1;
                ctx->h2[idx] = r2;
                ctx->nh1[idx] = r1 == 0 ? 0 : MP - r1;
                ctx->nh2[idx] = r2 == 0 ? 0 : P2 - r2;
                ctx->path[depth] = (Gate){op, i, j};
                ctx->key[depth] = k;

                eval_gate_p1(ctx, idx, op, i, j);

                uint32_t next_mask = (unused_mask & ~(1U << i) & ~(1U << j)) | (1U << idx);
                int next_cnt = unused_cnt - removed + 1;
                collect_work(ctx, depth + 1, split_depth, next_mask, next_cnt);
            }
        }
    }
}

typedef struct {
    int tid;
    int target_tau;
    int cert_bound;
    uint64_t nodes_visited;
    uint64_t leaves_checked;
    uint64_t cert_deg;
    uint64_t cert_prod;
    uint64_t cert_p1;
    uint64_t cert_taylor;
    uint64_t cert_dup_zero;
    uint64_t cert_fallback[NUM_FALLBACK_PRIMES];
    uint64_t survivors_raw;
} WorkerArg;

static void *worker_fn(void *arg) {
    WorkerArg *wa = (WorkerArg *)arg;
    SearchCtx ctx;
    memset(&ctx, 0, sizeof(ctx));
    ctx.target_tau = wa->target_tau;
    ctx.cert_bound = wa->cert_bound;
    init_base(&ctx);

    while (1) {
        int wi;
        pthread_mutex_lock(&g_work_lock);
        wi = g_work_next++;
        pthread_mutex_unlock(&g_work_lock);
        if (wi >= g_work_cnt) break;

        WorkItem *w = &g_work[wi];
        for (int d = 0; d < w->prefix_len; d++) {
            int idx = d + 2;
            Gate g = w->prefix[d];
            uint32_t r1;
            uint64_t r2;
            compute_hash_and_check_dup(&ctx, idx, g.op, g.i, g.j, &r1, &r2);
            ctx.h1[idx] = r1;
            ctx.h2[idx] = r2;
            ctx.nh1[idx] = r1 == 0 ? 0 : MP - r1;
            ctx.nh2[idx] = r2 == 0 ? 0 : P2 - r2;
            ctx.path[d] = g;
            ctx.key[d] = w->key[d];
            eval_gate_p1(&ctx, idx, g.op, g.i, g.j);
        }
        dfs(&ctx, w->prefix_len, w->unused_mask, w->unused_cnt);
    }

    wa->nodes_visited = ctx.nodes_visited;
    wa->leaves_checked = ctx.leaves_checked;
    wa->cert_deg = ctx.cert_deg;
    wa->cert_prod = ctx.cert_prod;
    wa->cert_p1 = ctx.cert_p1;
    wa->cert_taylor = ctx.cert_taylor;
    wa->cert_dup_zero = ctx.cert_dup_zero;
    memcpy(wa->cert_fallback, ctx.cert_fallback, sizeof(ctx.cert_fallback));
    wa->survivors_raw = ctx.survivors_raw;
    return NULL;
}

int main(int argc, char **argv) {
    /* Usage: ./tau_z9_unconditional <tau> <cert_bound_K> [nthreads=12] [survivor_file=/tmp/z_survivors.txt] */
    if (argc < 3) {
        fprintf(stderr, "Usage: %s <tau> <cert_bound_K> [nthreads=12] [survivor_file]\n", argv[0]);
        return 1;
    }
    int tau = atoi(argv[1]);
    int K = atoi(argv[2]);
    int nthreads = (argc >= 4) ? atoi(argv[3]) : 12;
    const char *surv_path = (argc >= 5) ? argv[4] : "/tmp/z_survivors.txt";

    if (K < 0 || K >= 19) {
        fprintf(stderr, "Error: cert_bound_K must be in [0, 18]\n");
        return 1;
    }

    surv_table_reset();
    g_surv_fp = fopen(surv_path, "w");
    if (!g_surv_fp) {
        perror("fopen survivor_file");
        return 1;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    uint64_t tot_nodes = 0, tot_leaves = 0, tot_deg = 0, tot_prod = 0, tot_p1 = 0, tot_taylor = 0, tot_dup = 0, tot_surv_raw = 0;
    uint64_t tot_fb[NUM_FALLBACK_PRIMES] = {0};

    if (tau <= 4) {
        SearchCtx ctx;
        memset(&ctx, 0, sizeof(ctx));
        ctx.target_tau = tau;
        ctx.cert_bound = K;
        init_base(&ctx);
        dfs(&ctx, 0, 0U, 0);
        tot_nodes = ctx.nodes_visited;
        tot_leaves = ctx.leaves_checked;
        tot_deg = ctx.cert_deg;
        tot_prod = ctx.cert_prod;
        tot_p1 = ctx.cert_p1;
        tot_taylor = ctx.cert_taylor;
        tot_dup = ctx.cert_dup_zero;
        for (int f = 0; f < NUM_FALLBACK_PRIMES; f++) tot_fb[f] = ctx.cert_fallback[f];
        tot_surv_raw = ctx.survivors_raw;
    } else {
        int split_depth = (tau >= 8) ? 3 : 2;
        g_work_cnt = 0;
        g_work_next = 0;
        SearchCtx root_ctx;
        memset(&root_ctx, 0, sizeof(root_ctx));
        root_ctx.target_tau = tau;
        root_ctx.cert_bound = K;
        init_base(&root_ctx);
        collect_work(&root_ctx, 0, split_depth, 0U, 0);

        pthread_t threads[64];
        WorkerArg args[64];
        if (nthreads > 64) nthreads = 64;
        for (int t = 0; t < nthreads; t++) {
            memset(&args[t], 0, sizeof(WorkerArg));
            args[t].tid = t;
            args[t].target_tau = tau;
            args[t].cert_bound = K;
            pthread_create(&threads[t], NULL, worker_fn, &args[t]);
        }
        for (int t = 0; t < nthreads; t++) {
            pthread_join(threads[t], NULL);
            tot_nodes += args[t].nodes_visited;
            tot_leaves += args[t].leaves_checked;
            tot_deg += args[t].cert_deg;
            tot_prod += args[t].cert_prod;
            tot_p1 += args[t].cert_p1;
            tot_taylor += args[t].cert_taylor;
            tot_dup += args[t].cert_dup_zero;
            for (int f = 0; f < NUM_FALLBACK_PRIMES; f++) tot_fb[f] += args[t].cert_fallback[f];
            tot_surv_raw += args[t].survivors_raw;
        }
    }

    fclose(g_surv_fp);
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double dt = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;

#ifdef ALT_PRIMES
    printf("CERTIFY [ALT_PRIMES P1=%u P2=%llu P3=%llu] tau=%d K=%d time=%.3fs (%.1fM leaves/s)\n",
           MP, (unsigned long long)P2, (unsigned long long)P3,
           tau, K, dt, (double)tot_leaves / (dt * 1e6 + 1e-9));
#else
    printf("CERTIFY tau=%d K=%d time=%.3fs (%.1fM leaves/s)\n",
           tau, K, dt, (double)tot_leaves / (dt * 1e6 + 1e-9));
#endif
    printf("  nodes_visited  = %llu\n", (unsigned long long)tot_nodes);
    printf("  leaves_checked = %llu\n", (unsigned long long)tot_leaves);
    printf("  cert_deg       = %llu (%.2f%%)\n", (unsigned long long)tot_deg, 100.0 * tot_deg / (tot_leaves + 1e-9));
    printf("  cert_prod      = %llu (%.2f%%)\n", (unsigned long long)tot_prod, 100.0 * tot_prod / (tot_leaves + 1e-9));
    printf("  cert_p31       = %llu (%.2f%%)\n", (unsigned long long)tot_p1, 100.0 * tot_p1 / (tot_leaves + 1e-9));
    printf("  cert_taylor31  = %llu (%.2f%%)\n", (unsigned long long)tot_taylor, 100.0 * tot_taylor / (tot_leaves + 1e-9));
    printf("  cert_dup_zero  = %llu (%.2f%%)\n", (unsigned long long)tot_dup, 100.0 * tot_dup / (tot_leaves + 1e-9));
    for (int f = 0; f < NUM_FALLBACK_PRIMES; f++) {
        printf("  cert_p%d       = %llu (%.4f%%)\n",
               FALLBACK_PRIMES[f], (unsigned long long)tot_fb[f], 100.0 * tot_fb[f] / (tot_leaves + 1e-9));
    }
    printf("  survivors_raw  = %llu\n", (unsigned long long)tot_surv_raw);
    printf("  survivors_uniq = %zu (written to %s)\n", g_surv_cnt, surv_path);
    fflush(stdout);
    return 0;
}
