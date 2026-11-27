/*
 * Exact-confirmed unconditional Z-wide certifier for the Shub-Smale tau-conjecture.
 *
 * Hardened evolution of tau_z9_unconditional.c:
 *   1. Every hash-based decision (internal dup/zero pruning, leaf dup/zero,
 *      survivor deduplication) is confirmed by an EXACT multi-prime CRT
 *      polynomial identity test over Z[x] using rigorous degree and L1-norm
 *      bounds. Hashes act strictly as a prefilter; a hash collision can NEVER
 *      prune a genuine subtree or merge distinct survivors.
 *   2. Certifies each leaf has <= K distinct integer roots in Z via:
 *      (a) Degree upper bound: deg_ub(f) <= K
 *      (b) Atomic product-factor union bound: f = A * B with sum z_ub <= K
 *          (or f = A + A with z_ub(A) <= K)
 *      (c) Simple-Root Modular Certificate mod p1 = 31
 *      (d) Exact __int128 truncated Taylor certificate (mod t^12) at known
 *          double-root residues {0, +-1, +-2, +-3} mod p
 *      (e) Fallback primes {19, 23, 29} (plus {37, 41, 43, 47, 53} with -DEXTRA_PRIMES)
 *   3. Long-run support: --split, --items A:B, --sample FRAC SEED,
 *      --checkpoint DIR (fsync'd done.tsv + atomic per-item compact survivor
 *      shards), --prefix, --threads, --compact, --membership FILE, and 60s
 *      stderr progress/ETA reporting.
 *   4. Audit & testing modes: -DDUMP_LEAVES, -DALT_PRIMES, -DEXTRA_PRIMES,
 *      and mutation/bug-injection flags (MUT_NO_DEADGATE, MUT_NO_KEYORDER,
 *      MUT_NO_SIGNCANON, MUT_NO_DUP, BUG_DEADGATE_OFF_BY_ONE, BUG_NO_SQUARE,
 *      BUG_SKIP_SUB_INPUTS, BUG_TAYLOR_M0, BUG_IGNORE_DOUBLES).
 *
 * Canonicalization rules (identical search order to tau_z9_unconditional.c):
 *   - Sign canonicalization (+: i<=j, -: i<j, *: i<=j)
 *   - Dead-gate pruning (unused_cnt <= tau - k + 1)
 *   - Exact-confirmed duplicate/zero pruning (prefiltered by 2-point hash)
 *   - Lex-minimal topological ordering for independent gates
 */

#define _POSIX_C_SOURCE 200809L

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <string.h>
#include <ctype.h>
#include <time.h>
#include <errno.h>
#include <pthread.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/types.h>

#define MAX_TAU 12
#define MAX_SPLIT MAX_TAU
#define Q0_CACHE_MAX_D 64

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

#ifdef EXTRA_PRIMES
#define NUM_FALLBACK_PRIMES 8
static const int FALLBACK_PRIMES[NUM_FALLBACK_PRIMES] = {19, 23, 29, 37, 41, 43, 47, 53};
#else
#define NUM_FALLBACK_PRIMES 3
static const int FALLBACK_PRIMES[NUM_FALLBACK_PRIMES] = {19, 23, 29};
#endif

/*
 * 40 primes < 2^61 (all > 2^60, verified via deterministic 64-bit Miller-Rabin
 * with bases {2,3,5,7,11,13,17,19,23,29,31,37}).
 * EXACT_PRIMES[0] = 2^61 - 1 (Mersenne prime M_61) for division-free fast path.
 * 40 primes give > 2400 bits of CRT modulus, covering MAX_TAU = 12 (max nb <= 2048).
 */
#define NUM_EXACT_PRIMES 40
#define M61 2305843009213693951ULL /* (1ULL << 61) - 1 */
static const uint64_t EXACT_PRIMES[NUM_EXACT_PRIMES] = {
    2305843009213693951ULL,
    2305843009213693921ULL,
    2305843009213693907ULL,
    2305843009213693723ULL,
    2305843009213693693ULL,
    2305843009213693669ULL,
    2305843009213693613ULL,
    2305843009213693561ULL,
    2305843009213693549ULL,
    2305843009213693487ULL,
    2305843009213693421ULL,
    2305843009213693373ULL,
    2305843009213693277ULL,
    2305843009213693193ULL,
    2305843009213693153ULL,
    2305843009213693133ULL,
    2305843009213693123ULL,
    2305843009213693109ULL,
    2305843009213693093ULL,
    2305843009213693013ULL,
    2305843009213692967ULL,
    2305843009213692937ULL,
    2305843009213692799ULL,
    2305843009213692757ULL,
    2305843009213692737ULL,
    2305843009213692671ULL,
    2305843009213692653ULL,
    2305843009213692601ULL,
    2305843009213692581ULL,
    2305843009213692527ULL,
    2305843009213692463ULL,
    2305843009213692427ULL,
    2305843009213692419ULL,
    2305843009213692409ULL,
    2305843009213692343ULL,
    2305843009213692331ULL,
    2305843009213692283ULL,
    2305843009213692211ULL,
    2305843009213692199ULL,
    2305843009213692139ULL
};

static void die_oom(const char *what) {
    fprintf(stderr, "FATAL: out of memory allocating %s\n", what);
    exit(3);
}

static void die_io(const char *what) {
    fprintf(stderr, "FATAL: I/O error on %s: %s\n", what, strerror(errno));
    exit(3);
}

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

/* Fast Mersenne mod M61 = 2^61 - 1 arithmetic */
static inline uint64_t m61_add(uint64_t a, uint64_t b) {
    uint64_t s = a + b;
    return s >= M61 ? s - M61 : s;
}

static inline uint64_t m61_sub(uint64_t a, uint64_t b) {
    return a >= b ? a - b : a + (M61 - b);
}

static inline uint64_t m61_mul(uint64_t a, uint64_t b) {
    unsigned __int128 t = (unsigned __int128)a * (unsigned __int128)b;
    uint64_t s = (uint64_t)(t & M61) + (uint64_t)(t >> 61);
    s = (s & M61) + (s >> 61);
    return s >= M61 ? s - M61 : s;
}

/* General mod q (< 2^61) arithmetic */
static inline uint64_t mq_add(uint64_t a, uint64_t b, uint64_t q) {
    uint64_t s = a + b;
    return s >= q ? s - q : s;
}

static inline uint64_t mq_sub(uint64_t a, uint64_t b, uint64_t q) {
    return a >= b ? a - b : a + (q - b);
}

static inline uint64_t mq_mul(uint64_t a, uint64_t b, uint64_t q) {
    return (uint64_t)(((unsigned __int128)a * (unsigned __int128)b) % q);
}

typedef struct {
    int op;
    int i;
    int j;
} Gate;

typedef struct {
    Gate prefix[MAX_SPLIT];
    int key[MAX_SPLIT];
    uint32_t unused_mask;
    int unused_cnt;
    int prefix_len;
} WorkItem;

typedef struct {
    uint64_t nodes_visited;
    uint64_t leaves_checked;
    uint64_t cert_deg;
    uint64_t cert_prod;
    uint64_t cert_p1;
    uint64_t cert_taylor;
    uint64_t cert_dup_zero;
    uint64_t cert_fallback[NUM_FALLBACK_PRIMES];
    uint64_t survivors_raw;
    uint64_t survivors_uniq;
    uint64_t dup_hash_hits;
    uint64_t dup_exact_confirmed;
    uint64_t dup_false_positive;
    uint64_t zero_hash_hits;
    uint64_t zero_exact_confirmed;
    uint64_t zero_false_positive;
    uint64_t surv_hash_hits;
    uint64_t surv_exact_confirmed;
    uint64_t surv_false_positive;
} Stats;

static void stats_add(Stats *dst, const Stats *src) {
    dst->nodes_visited += src->nodes_visited;
    dst->leaves_checked += src->leaves_checked;
    dst->cert_deg += src->cert_deg;
    dst->cert_prod += src->cert_prod;
    dst->cert_p1 += src->cert_p1;
    dst->cert_taylor += src->cert_taylor;
    dst->cert_dup_zero += src->cert_dup_zero;
    for (int f = 0; f < NUM_FALLBACK_PRIMES; f++) {
        dst->cert_fallback[f] += src->cert_fallback[f];
    }
    dst->survivors_raw += src->survivors_raw;
    dst->survivors_uniq += src->survivors_uniq;
    dst->dup_hash_hits += src->dup_hash_hits;
    dst->dup_exact_confirmed += src->dup_exact_confirmed;
    dst->dup_false_positive += src->dup_false_positive;
    dst->zero_hash_hits += src->zero_hash_hits;
    dst->zero_exact_confirmed += src->zero_exact_confirmed;
    dst->zero_false_positive += src->zero_false_positive;
    dst->surv_hash_hits += src->surv_hash_hits;
    dst->surv_exact_confirmed += src->surv_exact_confirmed;
    dst->surv_false_positive += src->surv_false_positive;
}

/* Exact-deduplicated survivor hash table (open addressing) */
typedef struct {
    uint32_t h1;
    uint32_t h2;
    uint32_t h3;
    uint8_t used;
    Gate gates[MAX_TAU];
} SurvEntry;

typedef struct {
    SurvEntry *tab;
    size_t cap;
    size_t cnt;
    uint64_t hash_hits;
    uint64_t exact_confirmed;
    uint64_t false_positive;
} SurvTable;

typedef struct {
    int target_tau;
    int cert_bound; /* K: certify <= K roots */
    Stats st;

    uint8_t v31[MAX_TAU + 2][32];
    uint8_t d31[MAX_TAU + 2][32];
    uint8_t z_ub[MAX_TAU + 2];
    uint16_t deg_ub[MAX_TAU + 2];
    uint32_t nb[MAX_TAU + 2]; /* log2 L1-norm bound: ||w||_1 <= 2^{nb[w]} */
    uint16_t prod_mask[MAX_TAU + 2];

    uint32_t h1[MAX_TAU + 2];
    uint64_t h2[MAX_TAU + 2];
    uint32_t nh1[MAX_TAU + 2];
    uint64_t nh2[MAX_TAU + 2];
    Gate path[MAX_TAU];
    int key[MAX_TAU];

    /* Lazy evaluation cache mod M61 for t = 0..Q0_CACHE_MAX_D */
    uint64_t eval_q0[MAX_TAU + 2][Q0_CACHE_MAX_D + 1];
    uint16_t eval_q0_pts[MAX_TAU + 2];

    /* Optional per-item survivor table & buffer (non-NULL in --checkpoint mode) */
    SurvTable *local_surv;
    Gate *local_surv_list;
    size_t local_surv_cap;
    size_t local_surv_len;
} SearchCtx;

/* Global state */
static pthread_mutex_t g_surv_lock = PTHREAD_MUTEX_INITIALIZER;
static SurvTable g_surv;
static FILE *g_surv_fp = NULL;
static int g_compact_out = 0;

static WorkItem *g_work = NULL;
static int g_work_cnt = 0;
static int g_work_cap = 0;
static int *g_sel_items = NULL;
static int g_sel_cnt = 0;
static int g_sel_next = 0;
static pthread_mutex_t g_work_lock = PTHREAD_MUTEX_INITIALIZER;

/* Checkpoint & progress state */
static const char *g_ckpt_dir = NULL;
static FILE *g_done_fp = NULL;
static pthread_mutex_t g_ckpt_lock = PTHREAD_MUTEX_INITIALIZER;
static Stats g_ckpt_tot;

static pthread_mutex_t g_prog_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t g_prog_cond = PTHREAD_COND_INITIALIZER;
static int g_prog_stop = 0;
static int g_items_done = 0;
static int g_items_total = 0;
static uint64_t g_prog_leaves = 0;
static uint64_t g_prog_surv_raw = 0;
static struct timespec g_start_ts;

/* Exact degree and L1-norm bound for an arbitrary SLP */
static void compute_slp_bounds(const Gate *gates, int tau, uint16_t *out_deg, uint32_t *out_nb) {
    uint16_t deg[MAX_TAU + 2];
    uint32_t nb[MAX_TAU + 2];
    deg[0] = 0; nb[0] = 0;
    deg[1] = 1; nb[1] = 0;
    for (int d = 0; d < tau; d++) {
        int idx = d + 2;
        int op = gates[d].op, i = gates[d].i, j = gates[d].j;
        if (op == 2) {
            deg[idx] = (uint16_t)(deg[i] + deg[j]);
            nb[idx] = nb[i] + nb[j];
        } else {
            deg[idx] = deg[i] > deg[j] ? deg[i] : deg[j];
            nb[idx] = (nb[i] > nb[j] ? nb[i] : nb[j]) + 1U;
        }
    }
    *out_deg = deg[tau + 1];
    *out_nb = nb[tau + 1];
}

/* Exact polynomial equality up to sign (+1 or -1) between two tau-gate SLPs */
static int exact_slps_equal_upto_sign(const Gate *gA, const Gate *gB, int tau) {
    uint16_t degA = 0, degB = 0;
    uint32_t nbA = 0, nbB = 0;
    compute_slp_bounds(gA, tau, &degA, &nbA);
    compute_slp_bounds(gB, tau, &degB, &nbB);
    int D = (degA > degB) ? (int)degA : (int)degB;
    uint32_t max_nb = (nbA > nbB) ? nbA : nbB;
    int r = (int)((max_nb + 2U) / 60U) + 1;
    if (r > NUM_EXACT_PRIMES) {
        fprintf(stderr, "FATAL: exact_slps_equal_upto_sign needs %d primes (> %d) for nb=%u\n",
                r, NUM_EXACT_PRIMES, max_nb);
        exit(3);
    }

    int eq_pos = 1, eq_neg = 1;
    uint64_t vA[MAX_TAU + 2], vB[MAX_TAU + 2];

    for (int p_idx = 0; p_idx < r; p_idx++) {
        uint64_t q = EXACT_PRIMES[p_idx];
        for (int t = 0; t <= D; t++) {
            vA[0] = 1; vA[1] = (uint64_t)t;
            vB[0] = 1; vB[1] = (uint64_t)t;
            if (p_idx == 0) {
                for (int d = 0; d < tau; d++) {
                    int idx = d + 2;
                    int opA = gA[d].op, iA = gA[d].i, jA = gA[d].j;
                    if (opA == 0) vA[idx] = m61_add(vA[iA], vA[jA]);
                    else if (opA == 1) vA[idx] = m61_sub(vA[iA], vA[jA]);
                    else vA[idx] = m61_mul(vA[iA], vA[jA]);

                    int opB = gB[d].op, iB = gB[d].i, jB = gB[d].j;
                    if (opB == 0) vB[idx] = m61_add(vB[iB], vB[jB]);
                    else if (opB == 1) vB[idx] = m61_sub(vB[iB], vB[jB]);
                    else vB[idx] = m61_mul(vB[iB], vB[jB]);
                }
            } else {
                for (int d = 0; d < tau; d++) {
                    int idx = d + 2;
                    int opA = gA[d].op, iA = gA[d].i, jA = gA[d].j;
                    if (opA == 0) vA[idx] = mq_add(vA[iA], vA[jA], q);
                    else if (opA == 1) vA[idx] = mq_sub(vA[iA], vA[jA], q);
                    else vA[idx] = mq_mul(vA[iA], vA[jA], q);

                    int opB = gB[d].op, iB = gB[d].i, jB = gB[d].j;
                    if (opB == 0) vB[idx] = mq_add(vB[iB], vB[jB], q);
                    else if (opB == 1) vB[idx] = mq_sub(vB[iB], vB[jB], q);
                    else vB[idx] = mq_mul(vB[iB], vB[jB], q);
                }
            }
            uint64_t a = vA[tau + 1];
            uint64_t b = vB[tau + 1];
            if (eq_pos && a != b) eq_pos = 0;
            uint64_t nb_val = (b == 0) ? 0 : (q - b);
            if (eq_neg && a != nb_val) eq_neg = 0;
            if (!eq_pos && !eq_neg) return 0;
        }
    }
    return eq_pos || eq_neg;
}

static void surv_table_init(SurvTable *st, size_t init_cap) {
    memset(st, 0, sizeof(*st));
    st->cap = init_cap;
    st->tab = (SurvEntry *)calloc(st->cap, sizeof(SurvEntry));
    if (!st->tab) die_oom("SurvTable");
}

static void surv_table_free(SurvTable *st) {
    free(st->tab);
    memset(st, 0, sizeof(*st));
}

static void surv_table_grow(SurvTable *st) {
    size_t new_cap = st->cap * 2;
    SurvEntry *nt = (SurvEntry *)calloc(new_cap, sizeof(SurvEntry));
    if (!nt) die_oom("SurvTable grow");
    size_t mask = new_cap - 1;
    for (size_t i = 0; i < st->cap; i++) {
        if (!st->tab[i].used) continue;
        uint64_t mix = ((uint64_t)st->tab[i].h1 * 0x9e3779b97f4a7c15ULL) ^
                       ((uint64_t)st->tab[i].h2 * 0xbf58476d1ce4e5b9ULL) ^
                       ((uint64_t)st->tab[i].h3 * 0x94d049bb133111ebULL);
        size_t pos = (size_t)(mix & mask);
        while (nt[pos].used) pos = (pos + 1) & mask;
        nt[pos] = st->tab[i];
    }
    free(st->tab);
    st->tab = nt;
    st->cap = new_cap;
}

/* Returns 1 if newly inserted (unique), 0 if exact duplicate */
static int surv_table_insert(SurvTable *st, const Gate *gates, int tau,
                             uint32_t k1, uint32_t k2, uint32_t k3) {
    if (st->cnt * 2 >= st->cap) surv_table_grow(st);
    size_t mask = st->cap - 1;
    uint64_t mix = ((uint64_t)k1 * 0x9e3779b97f4a7c15ULL) ^
                   ((uint64_t)k2 * 0xbf58476d1ce4e5b9ULL) ^
                   ((uint64_t)k3 * 0x94d049bb133111ebULL);
    size_t pos = (size_t)(mix & mask);
    while (st->tab[pos].used) {
        if (st->tab[pos].h1 == k1 && st->tab[pos].h2 == k2 && st->tab[pos].h3 == k3) {
            st->hash_hits++;
            if (exact_slps_equal_upto_sign(gates, st->tab[pos].gates, tau)) {
                st->exact_confirmed++;
                return 0;
            }
            st->false_positive++;
        }
        pos = (pos + 1) & mask;
    }
    st->tab[pos].h1 = k1;
    st->tab[pos].h2 = k2;
    st->tab[pos].h3 = k3;
    st->tab[pos].used = 1;
    memcpy(st->tab[pos].gates, gates, sizeof(Gate) * (size_t)tau);
    st->cnt++;
    return 1;
}

static void write_slp_legacy(FILE *fp, const Gate *gates, int tau,
                             uint32_t h1, uint32_t h2, uint32_t h3) {
    const char *ops = "+-*";
    if (fprintf(fp, "%u %u %u | ", h1, h2, h3) < 0) die_io("survivor write");
    for (int k = 0; k < tau; k++) {
        if (k > 0 && fprintf(fp, "; ") < 0) die_io("survivor write");
        int i = gates[k].i - 1;
        int j = gates[k].j - 1;
        char si[16], sj[16];
        if (i == -1) strcpy(si, "1");
        else if (i == 0) strcpy(si, "x");
        else snprintf(si, sizeof(si), "g%d", i);
        if (j == -1) strcpy(sj, "1");
        else if (j == 0) strcpy(sj, "x");
        else snprintf(sj, sizeof(sj), "g%d", j);
        if (fprintf(fp, "g%d = %s %c %s", k + 1, si, ops[gates[k].op], sj) < 0)
            die_io("survivor write");
    }
    if (fprintf(fp, "\n") < 0) die_io("survivor write");
}

static void write_slp_compact(FILE *fp, const Gate *gates, int tau) {
    static const char op_ch[3] = {'a', 's', 'm'};
    if (fprintf(fp, "%d", tau) < 0) die_io("survivor write");
    for (int k = 0; k < tau; k++) {
        if (fprintf(fp, " %c%d.%d", op_ch[gates[k].op], gates[k].i, gates[k].j) < 0)
            die_io("survivor write");
    }
    if (fprintf(fp, "\n") < 0) die_io("survivor write");
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

static void record_survivor(SearchCtx *ctx, const Gate *gates, int tau,
                            uint32_t r1, uint64_t r2) {
    uint32_t r3 = compute_h3(gates, tau);
    uint32_t nr1 = r1 == 0 ? 0 : MP - r1;
    uint32_t nr2 = r2 == 0 ? 0 : (uint32_t)(P2 - r2);
    uint32_t nr3 = r3 == 0 ? 0 : (uint32_t)(P3 - r3);
    uint32_t k1 = r1, k2 = (uint32_t)r2, k3 = r3;
    if (nr1 < k1 || (nr1 == k1 && (nr2 < k2 || (nr2 == k2 && nr3 < k3)))) {
        k1 = nr1; k2 = nr2; k3 = nr3;
    }

    if (ctx->local_surv) {
        if (surv_table_insert(ctx->local_surv, gates, tau, k1, k2, k3)) {
            if (ctx->local_surv_len == ctx->local_surv_cap) {
                size_t nc = ctx->local_surv_cap ? ctx->local_surv_cap * 2 : 64;
                Gate *nl = (Gate *)realloc(ctx->local_surv_list, nc * (size_t)tau * sizeof(Gate));
                if (!nl) die_oom("local_surv_list");
                ctx->local_surv_list = nl;
                ctx->local_surv_cap = nc;
            }
            memcpy(ctx->local_surv_list + ctx->local_surv_len * (size_t)tau,
                   gates, sizeof(Gate) * (size_t)tau);
            ctx->local_surv_len++;
        }
        return;
    }

    pthread_mutex_lock(&g_surv_lock);
    if (surv_table_insert(&g_surv, gates, tau, k1, k2, k3)) {
        if (g_surv_fp) {
            if (g_compact_out) {
                write_slp_compact(g_surv_fp, gates, tau);
            } else {
                write_slp_legacy(g_surv_fp, gates, tau, k1, k2, k3);
            }
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
    ctx->nb[0] = 0;   /* ||1||_1 = 1 = 2^0 */
    ctx->nb[1] = 0;   /* ||x||_1 = 1 = 2^0 */
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

    for (int t = 0; t <= Q0_CACHE_MAX_D; t++) {
        ctx->eval_q0[0][t] = 1;
        ctx->eval_q0[1][t] = (uint64_t)t;
    }
    ctx->eval_q0_pts[0] = Q0_CACHE_MAX_D + 1;
    ctx->eval_q0_pts[1] = Q0_CACHE_MAX_D + 1;
}

static inline void ensure_q0_cache(SearchCtx *ctx, int idx, int D) {
    for (int w = 2; w < idx; w++) {
        int cur = (int)ctx->eval_q0_pts[w];
        if (cur <= D) {
            Gate g = ctx->path[w - 2];
            const uint64_t * __restrict va = ctx->eval_q0[g.i];
            const uint64_t * __restrict vb = ctx->eval_q0[g.j];
            uint64_t * __restrict vc = ctx->eval_q0[w];
            if (g.op == 0) {
                for (int t = cur; t <= D; t++) vc[t] = m61_add(va[t], vb[t]);
            } else if (g.op == 1) {
                for (int t = cur; t <= D; t++) vc[t] = m61_sub(va[t], vb[t]);
            } else {
                for (int t = cur; t <= D; t++) vc[t] = m61_mul(va[t], vb[t]);
            }
            ctx->eval_q0_pts[w] = (uint16_t)(D + 1);
        }
    }
}

/*
 * Exact multi-prime CRT test for:
 *   sign ==  0: cand(op, i, j) == 0
 *   sign == +1: cand(op, i, j) == +wire[target_m]
 *   sign == -1: cand(op, i, j) == -wire[target_m]
 */
static int exact_check_rel(SearchCtx *ctx, int idx, int op, int i, int j,
                           int target_m, int sign) {
    uint16_t cand_deg = (op == 2)
        ? (uint16_t)(ctx->deg_ub[i] + ctx->deg_ub[j])
        : (ctx->deg_ub[i] > ctx->deg_ub[j] ? ctx->deg_ub[i] : ctx->deg_ub[j]);
    uint32_t cand_nb = (op == 2)
        ? (ctx->nb[i] + ctx->nb[j])
        : ((ctx->nb[i] > ctx->nb[j] ? ctx->nb[i] : ctx->nb[j]) + 1U);

    int D;
    uint32_t max_nb;
    if (sign == 0) {
        D = (int)cand_deg;
        max_nb = cand_nb;
    } else {
        uint16_t md = ctx->deg_ub[target_m];
        uint32_t mn = ctx->nb[target_m];
        D = (cand_deg > md) ? (int)cand_deg : (int)md;
        max_nb = (cand_nb > mn) ? cand_nb : mn;
    }

    int r = (int)((max_nb + 2U) / 60U) + 1;
    if (r > NUM_EXACT_PRIMES) {
        fprintf(stderr, "FATAL: exact_check_rel needs %d primes (> %d) for nb=%u\n",
                r, NUM_EXACT_PRIMES, max_nb);
        exit(3);
    }

    int start_p = 0;
    if (D <= Q0_CACHE_MAX_D) {
        ensure_q0_cache(ctx, idx, D);
        const uint64_t * __restrict va = ctx->eval_q0[i];
        const uint64_t * __restrict vb = ctx->eval_q0[j];
        if (sign == 0) {
            if (op == 0) {
                for (int t = 0; t <= D; t++) {
                    if (m61_add(va[t], vb[t]) != 0) return 0;
                }
            } else if (op == 1) {
                for (int t = 0; t <= D; t++) {
                    if (va[t] != vb[t]) return 0;
                }
            } else {
                for (int t = 0; t <= D; t++) {
                    if (va[t] != 0 && vb[t] != 0) return 0;
                }
            }
        } else if (sign == 1) {
            const uint64_t * __restrict vm = ctx->eval_q0[target_m];
            if (op == 0) {
                for (int t = 0; t <= D; t++) {
                    if (m61_add(va[t], vb[t]) != vm[t]) return 0;
                }
            } else if (op == 1) {
                for (int t = 0; t <= D; t++) {
                    if (m61_sub(va[t], vb[t]) != vm[t]) return 0;
                }
            } else {
                for (int t = 0; t <= D; t++) {
                    if (m61_mul(va[t], vb[t]) != vm[t]) return 0;
                }
            }
        } else {
            const uint64_t * __restrict vm = ctx->eval_q0[target_m];
            if (op == 0) {
                for (int t = 0; t <= D; t++) {
                    uint64_t v = m61_add(va[t], vb[t]);
                    uint64_t nv = vm[t] == 0 ? 0 : M61 - vm[t];
                    if (v != nv) return 0;
                }
            } else if (op == 1) {
                for (int t = 0; t <= D; t++) {
                    uint64_t v = m61_sub(va[t], vb[t]);
                    uint64_t nv = vm[t] == 0 ? 0 : M61 - vm[t];
                    if (v != nv) return 0;
                }
            } else {
                for (int t = 0; t <= D; t++) {
                    uint64_t v = m61_mul(va[t], vb[t]);
                    uint64_t nv = vm[t] == 0 ? 0 : M61 - vm[t];
                    if (v != nv) return 0;
                }
            }
        }
        start_p = 1;
    }

    uint64_t val[MAX_TAU + 2];
    for (int p_idx = start_p; p_idx < r; p_idx++) {
        uint64_t q = EXACT_PRIMES[p_idx];
        for (int t = 0; t <= D; t++) {
            val[0] = 1;
            val[1] = (uint64_t)t;
            if (p_idx == 0) {
                for (int w = 2; w < idx; w++) {
                    Gate g = ctx->path[w - 2];
                    if (g.op == 0) val[w] = m61_add(val[g.i], val[g.j]);
                    else if (g.op == 1) val[w] = m61_sub(val[g.i], val[g.j]);
                    else val[w] = m61_mul(val[g.i], val[g.j]);
                }
                uint64_t v;
                if (op == 0) v = m61_add(val[i], val[j]);
                else if (op == 1) v = m61_sub(val[i], val[j]);
                else v = m61_mul(val[i], val[j]);

                if (sign == 0) {
                    if (v != 0) return 0;
                } else if (sign == 1) {
                    if (v != val[target_m]) return 0;
                } else {
                    uint64_t nv = val[target_m] == 0 ? 0 : M61 - val[target_m];
                    if (v != nv) return 0;
                }
            } else {
                for (int w = 2; w < idx; w++) {
                    Gate g = ctx->path[w - 2];
                    if (g.op == 0) val[w] = mq_add(val[g.i], val[g.j], q);
                    else if (g.op == 1) val[w] = mq_sub(val[g.i], val[g.j], q);
                    else val[w] = mq_mul(val[g.i], val[g.j], q);
                }
                uint64_t v;
                if (op == 0) v = mq_add(val[i], val[j], q);
                else if (op == 1) v = mq_sub(val[i], val[j], q);
                else v = mq_mul(val[i], val[j], q);

                if (sign == 0) {
                    if (v != 0) return 0;
                } else if (sign == 1) {
                    if (v != val[target_m]) return 0;
                } else {
                    uint64_t nv = val[target_m] == 0 ? 0 : q - val[target_m];
                    if (v != nv) return 0;
                }
            }
        }
    }
    return 1;
}

/* Pure hash computation with NO pruning decisions (used for prefix replay & MUT_NO_DUP) */
static inline void compute_hash_only(
    const SearchCtx *ctx, int op, int i, int j,
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
    *out_h1 = r1;
    *out_h2 = r2;
}

/*
 * Returns:
 *   1 if NOT zero and NOT duplicate of any earlier wire
 *   0 if EXACTLY zero (out_reason = 1 if non-NULL)
 *   0 if EXACTLY duplicate (out_reason = 2 if non-NULL)
 */
static inline int compute_hash_and_check_dup_ex(
    SearchCtx *ctx, int idx, int op, int i, int j,
    uint32_t *out_h1, uint64_t *out_h2, int *out_reason
) {
    uint32_t r1;
    uint64_t r2;
    compute_hash_only(ctx, op, i, j, &r1, &r2);

    if (r1 == 0 && r2 == 0) {
        ctx->st.zero_hash_hits++;
        if (exact_check_rel(ctx, idx, op, i, j, 0, 0)) {
            ctx->st.zero_exact_confirmed++;
            if (out_reason) *out_reason = 1;
            return 0;
        }
        ctx->st.zero_false_positive++;
    }
    for (int m = 0; m < idx; m++) {
        int mp = (r1 == ctx->h1[m] && r2 == ctx->h2[m]);
        int mn = (r1 == ctx->nh1[m] && r2 == ctx->nh2[m]);
        if (mp || mn) {
            ctx->st.dup_hash_hits++;
            int eq = 0;
            if (mp && exact_check_rel(ctx, idx, op, i, j, m, 1)) eq = 1;
            else if (mn && exact_check_rel(ctx, idx, op, i, j, m, -1)) eq = 1;
            if (eq) {
                ctx->st.dup_exact_confirmed++;
                if (out_reason) *out_reason = 2;
                return 0;
            }
            ctx->st.dup_false_positive++;
        }
    }
    *out_h1 = r1;
    *out_h2 = r2;
    if (out_reason) *out_reason = 0;
    return 1;
}

static inline int compute_hash_and_check_dup(
    SearchCtx *ctx, int idx, int op, int i, int j,
    uint32_t *out_h1, uint64_t *out_h2
) {
    return compute_hash_and_check_dup_ex(ctx, idx, op, i, j, out_h1, out_h2, NULL);
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

    uint32_t norm_b = (op == 2)
        ? (ctx->nb[i] + ctx->nb[j])
        : ((ctx->nb[i] > ctx->nb[j] ? ctx->nb[i] : ctx->nb[j]) + 1U);
    ctx->nb[idx] = norm_b;
    ctx->eval_q0_pts[idx] = 0;

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
#ifdef BUG_IGNORE_DOUBLES
    (void)doubles;
    if (zeros < P1_PRIME && zeros < ub) ub = (uint8_t)zeros;
#else
    if (zeros < P1_PRIME && doubles == 0 && zeros < ub) ub = (uint8_t)zeros;
#endif
    if (op == 2) {
        int pub = sum_mask_ub(pmask, ctx->z_ub);
        if (pub < ub) ub = (uint8_t)pub;
    } else if (op == 0 && i == j) {
        if (ctx->z_ub[i] < ub) ub = ctx->z_ub[i];
    }
    ctx->z_ub[idx] = ub;
}

#ifndef DUMP_LEAVES
/*
 * Exact __int128 truncated Taylor expansion of SLP at x = r0 (mod t^TAYLOR_DEG,
 * where TAYLOR_DEG = 12).
 * Returns 1 if exact (no overflow) and finds lowest nonzero term c_m
 * (0 <= m < TAYLOR_DEG), writing m to *out_mult and c_m to *out_cm.
 * Returns 0 on overflow or if all terms 0..TAYLOR_DEG-1 vanish.
 * Overflow safety: LIM = 10^17 => TAYLOR_DEG * LIM^2 = 1.2e35 < 2^127 (~1.70e38).
 */
#define TAYLOR_DEG 12
static int exact_taylor_at(const Gate *gates, int tau, int r0, int *out_mult, __int128 *out_cm) {
    static const __int128 LIM = (__int128)100000000000000000LL; /* 10^17: 12 * LIM^2 < 2^127 */
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

/*
 * Try to certify f using exact multiplicities at double-root residues among
 * {0, 1, -1, 2, -2, 3, -3} modulo prime p (p >= 19 odd; max pairwise diff is
 * 6 < 19 so gcd(p, r - r') = 1).
 * `dbl_mask` has bits 0..6 for {0, 1, -1, 2, -2, 3, -3}.
 * Caller guarantees NO double roots exist outside dbl_mask in F_p, and total
 * distinct zeros in F_p <= K < p.
 */
#define NUM_KNOWN_ROOTS 7
static const int KNOWN_ROOTS[NUM_KNOWN_ROOTS] = {0, 1, -1, 2, -2, 3, -3};

static int certify_taylor_roots(const Gate *gates, int tau, int p, int dbl_mask, int dub, int K) {
    for (int b = 0; b < NUM_KNOWN_ROOTS; b++) {
        if (!((dbl_mask >> b) & 1)) continue;
        int m = 0;
        __int128 cm = 0;
        if (!exact_taylor_at(gates, tau, KNOWN_ROOTS[b], &m, &cm)) return 0;
#ifndef BUG_TAYLOR_M0
        if (m < 1) return 0;
#endif
        if ((cm % p) == 0) return 0;
    }
    (void)dub;
    (void)K;
    return 1;
}

/* Evaluate full SLP mod prime p (dual numbers + product z_ub propagation).
 * Returns 1 if certified <= K roots over all Z, 0 otherwise. */
static int certify_slp_mod_p(const Gate *gates, int tau, int p, int K) {
    uint8_t v[MAX_TAU + 2][64];
    uint8_t d[MAX_TAU + 2][64];
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
                uint8_t vv = v[i][a] + v[j][a]; if (vv >= p) vv -= (uint8_t)p;
                uint8_t dd = d[i][a] + d[j][a]; if (dd >= p) dd -= (uint8_t)p;
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
                uint8_t vv = v[i][a] >= v[j][a] ? (uint8_t)(v[i][a] - v[j][a]) : (uint8_t)(v[i][a] + p - v[j][a]);
                uint8_t dd = d[i][a] >= d[j][a] ? (uint8_t)(d[i][a] - d[j][a]) : (uint8_t)(d[i][a] + p - d[j][a]);
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
#ifdef BUG_IGNORE_DOUBLES
        (void)doubles;
        if (zeros < p && zeros < cur_ub) cur_ub = (uint8_t)zeros;
#else
        if (zeros < p && doubles == 0 && zeros < cur_ub) cur_ub = (uint8_t)zeros;
#endif
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
#endif /* !DUMP_LEAVES */

static inline void check_leaf(SearchCtx *ctx, int depth, int idx, int op, int i, int j) {
#ifdef BUG_NO_SQUARE
    if (op == 2 && i == j) return;
#endif
#ifdef BUG_SKIP_SUB_INPUTS
    if (op == 1 && i < 2 && j < 2) return;
#endif

    ctx->st.leaves_checked++;

#ifdef DUMP_LEAVES
    uint32_t r1;
    uint64_t r2;
    if (!compute_hash_and_check_dup(ctx, idx, op, i, j, &r1, &r2)) {
        ctx->st.cert_dup_zero++;
        return;
    }
    ctx->path[depth] = (Gate){op, i, j};
    ctx->st.survivors_raw++;
    record_survivor(ctx, ctx->path, ctx->target_tau, r1, r2);
    return;
#else
    int K = ctx->cert_bound;

    /* Fast path 0a: exact degree upper bound deg(f) <= K */
    int dub = (op == 2)
        ? ((int)ctx->deg_ub[i] + (int)ctx->deg_ub[j])
        : (ctx->deg_ub[i] > ctx->deg_ub[j] ? (int)ctx->deg_ub[i] : (int)ctx->deg_ub[j]);
    if (dub <= K) {
        ctx->st.cert_deg++;
        return;
    }

    /* Fast path 0b: atomic product-factor union bound z(A * B) <= sum_{a in prod_mask} z_ub(a),
     * and z(A + A) = z(2A) = z(A) */
    if (op == 2) {
        uint16_t pmask = ctx->prod_mask[i] | ctx->prod_mask[j];
        if (sum_mask_ub(pmask, ctx->z_ub) <= K) {
            ctx->st.cert_prod++;
            return;
        }
    } else if (op == 0 && i == j) {
        if (ctx->z_ub[i] <= K) {
            ctx->st.cert_prod++;
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

#ifdef BUG_IGNORE_DOUBLES
    if (zeros <= K) {
        ctx->st.cert_p1++;
        return;
    }
#else
    if (zeros <= K && doubles == 0) {
        ctx->st.cert_p1++;
        return;
    }
#endif

    /* Filter out zero / duplicate polynomials (computable in <= tau - 1 gates), exact-confirmed */
    uint32_t r1;
    uint64_t r2;
    if (!compute_hash_and_check_dup(ctx, idx, op, i, j, &r1, &r2)) {
        ctx->st.cert_dup_zero++;
        return;
    }

    /* Fast path 1b: if mod 31 has <= K roots and ONLY double roots at {0, +-1, +-2, +-3}, certify via exact Taylor! */
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
                ctx->st.cert_taylor++;
                return;
            }
        }
    }

    /* Fallback primes */
    for (int f = 0; f < NUM_FALLBACK_PRIMES; f++) {
        if (certify_slp_mod_p(ctx->path, ctx->target_tau, FALLBACK_PRIMES[f], K)) {
            ctx->st.cert_fallback[f]++;
            return;
        }
    }

    /* Survivor! Record exact-deduplicated SLP for exact Z[x] verification */
    ctx->st.survivors_raw++;
    record_survivor(ctx, ctx->path, ctx->target_tau, r1, r2);
#endif /* !DUMP_LEAVES */
}

static inline void check_leaf_pair(SearchCtx *ctx, int depth, int idx, int i, int j) {
    check_leaf(ctx, depth, idx, 0, i, j);
    if (i != j) check_leaf(ctx, depth, idx, 1, i, j);
    check_leaf(ctx, depth, idx, 2, i, j);
}

static void dfs(SearchCtx *ctx, int depth, uint32_t unused_mask, int unused_cnt) {
    int tau = ctx->target_tau;
    int idx = depth + 2;
    int rem_after = tau - 1 - depth;
#ifdef BUG_DEADGATE_OFF_BY_ONE
    int max_unused_after = rem_after;
#else
    int max_unused_after = rem_after + 1;
#endif
    int prev_idx = idx - 1;

    if (depth == tau - 1) {
#ifdef MUT_NO_DEADGATE
        for (int i = 0; i < idx; i++) {
#ifdef MUT_NO_SIGNCANON
            for (int j = 0; j < idx; j++) {
#else
            for (int j = i; j < idx; j++) {
#endif
                check_leaf_pair(ctx, depth, idx, i, j);
            }
        }
        return;
#else
        if (unused_cnt > 2) return;
        if (unused_cnt == 2) {
            int i = __builtin_ctz(unused_mask);
            int j = __builtin_ctz(unused_mask ^ (1U << i));
            check_leaf_pair(ctx, depth, idx, i, j);
#ifdef MUT_NO_SIGNCANON
            check_leaf_pair(ctx, depth, idx, j, i);
#endif
            return;
        }
        if (unused_cnt == 0) {
            for (int i = 0; i < idx; i++) {
#ifdef MUT_NO_SIGNCANON
                for (int j = 0; j < idx; j++) {
#else
                for (int j = i; j < idx; j++) {
#endif
                    check_leaf_pair(ctx, depth, idx, i, j);
                }
            }
            return;
        }
        int u0 = __builtin_ctz(unused_mask);
        for (int other = 0; other < idx; other++) {
#ifdef MUT_NO_SIGNCANON
            check_leaf_pair(ctx, depth, idx, u0, other);
            if (other != u0) check_leaf_pair(ctx, depth, idx, other, u0);
#else
            int i = other < u0 ? other : u0;
            int j = other < u0 ? u0 : other;
            check_leaf_pair(ctx, depth, idx, i, j);
#endif
        }
        return;
#endif /* MUT_NO_DEADGATE */
    }

#ifdef MUT_NO_DEADGATE
    (void)max_unused_after;
#else
    int min_removed = unused_cnt + 1 - max_unused_after;
#endif

    for (int i = 0; i < idx; i++) {
        int ui = (int)((unused_mask >> i) & 1U);
#ifndef MUT_NO_DEADGATE
        if (min_removed == 2 && !ui) continue;
#endif
#ifdef MUT_NO_SIGNCANON
        for (int j = 0; j < idx; j++) {
#else
        for (int j = i; j < idx; j++) {
#endif
            int uj = (int)((unused_mask >> j) & 1U);
            int removed = (i == j) ? ui : (ui + uj);
#ifndef MUT_NO_DEADGATE
            if (removed < min_removed) continue;
#endif

            int uses_prev = (depth > 0) && (i == prev_idx || j == prev_idx);

            for (int op = 0; op < 3; op++) {
                if (op == 1 && i == j) continue;
#ifdef BUG_NO_SQUARE
                if (op == 2 && i == j) continue;
#endif
#ifdef BUG_SKIP_SUB_INPUTS
                if (op == 1 && i < 2 && j < 2) continue;
#endif
                int k = (op << 10) | (i << 5) | j;
#ifndef MUT_NO_KEYORDER
                if (depth > 0 && !uses_prev && k < ctx->key[depth - 1]) continue;
#else
                (void)uses_prev;
#endif

                uint32_t r1;
                uint64_t r2;
#ifdef MUT_NO_DUP
                compute_hash_only(ctx, op, i, j, &r1, &r2);
#else
                if (!compute_hash_and_check_dup(ctx, idx, op, i, j, &r1, &r2)) continue;
#endif

                ctx->st.nodes_visited++;
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

static void collect_work(SearchCtx *ctx, int depth, int split_depth,
                         uint32_t unused_mask, int unused_cnt) {
    if (depth == split_depth) {
        if (g_work_cnt == g_work_cap) {
            int nc = g_work_cap ? g_work_cap * 2 : 1024;
            WorkItem *nw = (WorkItem *)realloc(g_work, sizeof(WorkItem) * (size_t)nc);
            if (!nw) die_oom("g_work");
            g_work = nw;
            g_work_cap = nc;
        }
        WorkItem *w = &g_work[g_work_cnt++];
        if (split_depth > 0) {
            memcpy(w->prefix, ctx->path, sizeof(Gate) * (size_t)split_depth);
            memcpy(w->key, ctx->key, sizeof(int) * (size_t)split_depth);
        }
        w->unused_mask = unused_mask;
        w->unused_cnt = unused_cnt;
        w->prefix_len = split_depth;
        return;
    }

    int tau = ctx->target_tau;
    int idx = depth + 2;
    int rem_after = tau - 1 - depth;
#ifdef BUG_DEADGATE_OFF_BY_ONE
    int max_unused_after = rem_after;
#else
    int max_unused_after = rem_after + 1;
#endif
    int prev_idx = idx - 1;
#ifdef MUT_NO_DEADGATE
    (void)max_unused_after;
#else
    int min_removed = unused_cnt + 1 - max_unused_after;
#endif

    for (int i = 0; i < idx; i++) {
        int ui = (int)((unused_mask >> i) & 1U);
#ifndef MUT_NO_DEADGATE
        if (min_removed == 2 && !ui) continue;
#endif
#ifdef MUT_NO_SIGNCANON
        for (int j = 0; j < idx; j++) {
#else
        for (int j = i; j < idx; j++) {
#endif
            int uj = (int)((unused_mask >> j) & 1U);
            int removed = (i == j) ? ui : (ui + uj);
#ifndef MUT_NO_DEADGATE
            if (removed < min_removed) continue;
#endif

            int uses_prev = (depth > 0) && (i == prev_idx || j == prev_idx);

            for (int op = 0; op < 3; op++) {
                if (op == 1 && i == j) continue;
#ifdef BUG_NO_SQUARE
                if (op == 2 && i == j) continue;
#endif
#ifdef BUG_SKIP_SUB_INPUTS
                if (op == 1 && i < 2 && j < 2) continue;
#endif
                int k = (op << 10) | (i << 5) | j;
#ifndef MUT_NO_KEYORDER
                if (depth > 0 && !uses_prev && k < ctx->key[depth - 1]) continue;
#else
                (void)uses_prev;
#endif

                uint32_t r1;
                uint64_t r2;
#ifdef MUT_NO_DUP
                compute_hash_only(ctx, op, i, j, &r1, &r2);
#else
                if (!compute_hash_and_check_dup(ctx, idx, op, i, j, &r1, &r2)) continue;
#endif

                ctx->st.nodes_visited++;
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

/* Checkpoint I/O */
static void write_done_row(FILE *fp, int item_id, const Stats *s) {
    if (fprintf(fp, "%d\t%" PRIu64 "\t%" PRIu64 "\t%" PRIu64 "\t%" PRIu64
                    "\t%" PRIu64 "\t%" PRIu64 "\t%" PRIu64,
                item_id, s->nodes_visited, s->leaves_checked,
                s->cert_deg, s->cert_prod, s->cert_p1,
                s->cert_taylor, s->cert_dup_zero) < 0) {
        die_io("done.tsv");
    }
    for (int f = 0; f < NUM_FALLBACK_PRIMES; f++) {
        if (fprintf(fp, "\t%" PRIu64, s->cert_fallback[f]) < 0) die_io("done.tsv");
    }
    if (fprintf(fp, "\t%" PRIu64 "\t%" PRIu64
                    "\t%" PRIu64 "\t%" PRIu64 "\t%" PRIu64
                    "\t%" PRIu64 "\t%" PRIu64 "\t%" PRIu64
                    "\t%" PRIu64 "\t%" PRIu64 "\t%" PRIu64 "\n",
                s->survivors_raw, s->survivors_uniq,
                s->dup_hash_hits, s->dup_exact_confirmed, s->dup_false_positive,
                s->zero_hash_hits, s->zero_exact_confirmed, s->zero_false_positive,
                s->surv_hash_hits, s->surv_exact_confirmed, s->surv_false_positive) < 0) {
        die_io("done.tsv");
    }
    if (fflush(fp) != 0) die_io("done.tsv fflush");
    if (fsync(fileno(fp)) != 0) die_io("done.tsv fsync");
}

static int parse_done_row(const char *line, int *out_item_id, Stats *s) {
    memset(s, 0, sizeof(*s));
    size_t len = strlen(line);
    if (len == 0 || line[len - 1] != '\n') return 0;

    const char *p = line;
    char *end = NULL;
    long id = strtol(p, &end, 10);
    if (end == p) return 0;
    *out_item_id = (int)id;
    p = end;

    uint64_t *fields[18 + NUM_FALLBACK_PRIMES];
    int nf = 0;
    fields[nf++] = &s->nodes_visited;
    fields[nf++] = &s->leaves_checked;
    fields[nf++] = &s->cert_deg;
    fields[nf++] = &s->cert_prod;
    fields[nf++] = &s->cert_p1;
    fields[nf++] = &s->cert_taylor;
    fields[nf++] = &s->cert_dup_zero;
    for (int f = 0; f < NUM_FALLBACK_PRIMES; f++) fields[nf++] = &s->cert_fallback[f];
    fields[nf++] = &s->survivors_raw;
    fields[nf++] = &s->survivors_uniq;
    fields[nf++] = &s->dup_hash_hits;
    fields[nf++] = &s->dup_exact_confirmed;
    fields[nf++] = &s->dup_false_positive;
    fields[nf++] = &s->zero_hash_hits;
    fields[nf++] = &s->zero_exact_confirmed;
    fields[nf++] = &s->zero_false_positive;
    fields[nf++] = &s->surv_hash_hits;
    fields[nf++] = &s->surv_exact_confirmed;
    fields[nf++] = &s->surv_false_positive;

    for (int k = 0; k < nf; k++) {
        unsigned long long v = strtoull(p, &end, 10);
        if (end == p) return 0;
        *fields[k] = (uint64_t)v;
        p = end;
    }
    while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n') p++;
    if (*p != '\0') return 0;
    return 1;
}

static void write_item_survivors_atomic(int item_id, const Gate *list, size_t len, int tau) {
    char tmp_path[1024], final_path[1024];
    snprintf(tmp_path, sizeof(tmp_path), "%s/surv/%d.txt.tmp", g_ckpt_dir, item_id);
    snprintf(final_path, sizeof(final_path), "%s/surv/%d.txt", g_ckpt_dir, item_id);
    if (len == 0) {
        unlink(final_path);
        return;
    }
    FILE *fp = fopen(tmp_path, "w");
    if (!fp) die_io(tmp_path);
    for (size_t k = 0; k < len; k++) {
        write_slp_compact(fp, list + k * (size_t)tau, tau);
    }
    if (fflush(fp) != 0) die_io(tmp_path);
    if (fsync(fileno(fp)) != 0) die_io(tmp_path);
    if (fclose(fp) != 0) die_io(tmp_path);
    if (rename(tmp_path, final_path) != 0) die_io(final_path);
}

typedef struct {
    int tid;
    int target_tau;
    int cert_bound;
    Stats st;
} WorkerArg;

static void *worker_fn(void *arg) {
    WorkerArg *wa = (WorkerArg *)arg;
    SearchCtx ctx;
    memset(&ctx, 0, sizeof(ctx));
    ctx.target_tau = wa->target_tau;
    ctx.cert_bound = wa->cert_bound;
    init_base(&ctx);

    SurvTable local_surv;
    int use_ckpt = (g_ckpt_dir != NULL);

    while (1) {
        int sel_idx;
        pthread_mutex_lock(&g_work_lock);
        sel_idx = g_sel_next++;
        pthread_mutex_unlock(&g_work_lock);
        if (sel_idx >= g_sel_cnt) break;

        int wi = g_sel_items[sel_idx];
        WorkItem *w = &g_work[wi];

        if (use_ckpt) {
            memset(&ctx.st, 0, sizeof(ctx.st));
            surv_table_init(&local_surv, 256);
            ctx.local_surv = &local_surv;
            ctx.local_surv_list = NULL;
            ctx.local_surv_cap = 0;
            ctx.local_surv_len = 0;
        }

        /* Prefix replay: recompute hashes, deg_ub, nb, v31/d31 ONLY -- NO pruning decisions */
        for (int d = 0; d < w->prefix_len; d++) {
            int idx = d + 2;
            Gate g = w->prefix[d];
            uint32_t r1;
            uint64_t r2;
            compute_hash_only(&ctx, g.op, g.i, g.j, &r1, &r2);
            ctx.h1[idx] = r1;
            ctx.h2[idx] = r2;
            ctx.nh1[idx] = r1 == 0 ? 0 : MP - r1;
            ctx.nh2[idx] = r2 == 0 ? 0 : P2 - r2;
            ctx.path[d] = g;
            ctx.key[d] = w->key[d];
            eval_gate_p1(&ctx, idx, g.op, g.i, g.j);
        }

        uint64_t leaves_before = ctx.st.leaves_checked;
        uint64_t surv_before = ctx.st.survivors_raw;

        dfs(&ctx, w->prefix_len, w->unused_mask, w->unused_cnt);

        uint64_t d_leaves = ctx.st.leaves_checked - leaves_before;
        uint64_t d_surv = ctx.st.survivors_raw - surv_before;

        if (use_ckpt) {
            ctx.st.survivors_uniq = local_surv.cnt;
            ctx.st.surv_hash_hits = local_surv.hash_hits;
            ctx.st.surv_exact_confirmed = local_surv.exact_confirmed;
            ctx.st.surv_false_positive = local_surv.false_positive;

            write_item_survivors_atomic(wi, ctx.local_surv_list, ctx.local_surv_len, wa->target_tau);
            free(ctx.local_surv_list);
            ctx.local_surv_list = NULL;
            surv_table_free(&local_surv);
            ctx.local_surv = NULL;

            pthread_mutex_lock(&g_ckpt_lock);
            write_done_row(g_done_fp, wi, &ctx.st);
            stats_add(&g_ckpt_tot, &ctx.st);
            pthread_mutex_unlock(&g_ckpt_lock);
        }

        pthread_mutex_lock(&g_prog_lock);
        g_items_done++;
        g_prog_leaves += d_leaves;
        g_prog_surv_raw += d_surv;
        pthread_mutex_unlock(&g_prog_lock);
    }

    if (!use_ckpt) {
        wa->st = ctx.st;
    }
    return NULL;
}

static void *progress_fn(void *arg) {
    (void)arg;
    pthread_mutex_lock(&g_prog_lock);
    while (!g_prog_stop) {
        struct timespec ts;
        clock_gettime(CLOCK_REALTIME, &ts);
        ts.tv_sec += 60;
        int rc = pthread_cond_timedwait(&g_prog_cond, &g_prog_lock, &ts);
        if (g_prog_stop) break;
        if (rc == ETIMEDOUT) {
            struct timespec now;
            clock_gettime(CLOCK_MONOTONIC, &now);
            double elapsed = (now.tv_sec - g_start_ts.tv_sec) +
                             (now.tv_nsec - g_start_ts.tv_nsec) * 1e-9;
            double pct = g_items_total > 0 ? (100.0 * g_items_done / g_items_total) : 0.0;
            double eta = (g_items_done > 0 && g_items_done < g_items_total)
                ? elapsed * ((double)(g_items_total - g_items_done) / g_items_done)
                : 0.0;
            fprintf(stderr,
                    "[PROGRESS] items=%d/%d (%.1f%%) elapsed=%.1fs eta=%.1fs leaves=%" PRIu64 " surv_raw=%" PRIu64 "\n",
                    g_items_done, g_items_total, pct, elapsed, eta,
                    g_prog_leaves, g_prog_surv_raw);
            fflush(stderr);
        }
    }
    pthread_mutex_unlock(&g_prog_lock);
    return NULL;
}

/* SplitMix64 for deterministic --sample FRAC SEED */
static uint64_t splitmix64(uint64_t x) {
    x += 0x9e3779b97f4a7c15ULL;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}

/* Parse compact gate token: <op><i>.<j>, op in {a, s, m} */
static int parse_compact_token(const char *tok, Gate *out) {
    int op;
    if (tok[0] == 'a') op = 0;
    else if (tok[0] == 's') op = 1;
    else if (tok[0] == 'm') op = 2;
    else return 0;
    char *dot = NULL;
    long i = strtol(tok + 1, &dot, 10);
    if (!dot || *dot != '.' || dot == tok + 1) return 0;
    char *end = NULL;
    long j = strtol(dot + 1, &end, 10);
    if (!end || *end != '\0' || end == dot + 1) return 0;
    out->op = op;
    out->i = (int)i;
    out->j = (int)j;
    return 1;
}

static int parse_prefix_str(const char *s, Gate *out, int max_gates) {
    int n = 0;
    const char *p = s;
    while (*p) {
        while (*p && isspace((unsigned char)*p)) p++;
        if (!*p) break;
        char tok[64];
        int k = 0;
        while (*p && !isspace((unsigned char)*p) && k < 63) tok[k++] = *p++;
        tok[k] = '\0';
        if (n >= max_gates) return -1;
        if (!parse_compact_token(tok, &out[n])) return -1;
        n++;
    }
    return n;
}

/*
 * Validate a gate sequence of length len (<= tau) step-by-step against every
 * pruning rule in the exact same order as dfs().
 * If all gates pass, leaves ctx ready at depth = len and sets *out_mask, *out_cnt.
 * If pruned at depth d, sets *out_depth = d, *out_rule = rule name, and returns 0.
 */
static int trace_gates(SearchCtx *ctx, const Gate *gates, int len,
                       uint32_t *out_mask, int *out_cnt,
                       int *out_depth, const char **out_rule) {
    int tau = ctx->target_tau;
    uint32_t unused_mask = 0U;
    int unused_cnt = 0;

    for (int depth = 0; depth < len; depth++) {
        int idx = depth + 2;
        int op = gates[depth].op;
        int i = gates[depth].i;
        int j = gates[depth].j;
        int prev_idx = idx - 1;

        if (op < 0 || op > 2 || i < 0 || i >= idx || j < 0 || j >= idx) {
            *out_depth = depth;
            *out_rule = "invalid_wire";
            return 0;
        }

        /* 1. Canonical op-ordering / sign canonicalization */
        if (op == 1 && i == j) {
            *out_depth = depth;
            *out_rule = "sub_self";
            return 0;
        }
#ifndef MUT_NO_SIGNCANON
        if (i > j) {
            *out_depth = depth;
            *out_rule = "sign_canon";
            return 0;
        }
#endif

        /* 2. Dead-gate pruning */
        int ui = (int)((unused_mask >> i) & 1U);
        int uj = (int)((unused_mask >> j) & 1U);
        int removed = (i == j) ? ui : (ui + uj);
#ifndef MUT_NO_DEADGATE
        if (depth == tau - 1) {
            if (removed < unused_cnt) {
                *out_depth = depth;
                *out_rule = "dead_gate";
                return 0;
            }
        } else {
            int rem_after = tau - 1 - depth;
#ifdef BUG_DEADGATE_OFF_BY_ONE
            int max_unused_after = rem_after;
#else
            int max_unused_after = rem_after + 1;
#endif
            int min_removed = unused_cnt + 1 - max_unused_after;
            if (removed < min_removed) {
                *out_depth = depth;
                *out_rule = "dead_gate";
                return 0;
            }
        }
#endif

        /* 3. Planted bug rules (if enabled) */
#ifdef BUG_NO_SQUARE
        if (op == 2 && i == j) {
            *out_depth = depth;
            *out_rule = "bug_no_square";
            return 0;
        }
#endif
#ifdef BUG_SKIP_SUB_INPUTS
        if (op == 1 && i < 2 && j < 2) {
            *out_depth = depth;
            *out_rule = "bug_skip_sub_inputs";
            return 0;
        }
#endif

        if (depth == tau - 1) {
            ctx->path[depth] = gates[depth];
            unused_mask = (unused_mask & ~(1U << i) & ~(1U << j)) | (1U << idx);
            unused_cnt = unused_cnt - removed + 1;
            continue;
        }

        /* 4. Lex-key ordering */
        int k = (op << 10) | (i << 5) | j;
        int uses_prev = (depth > 0) && (i == prev_idx || j == prev_idx);
#ifndef MUT_NO_KEYORDER
        if (depth > 0 && !uses_prev && k < ctx->key[depth - 1]) {
            *out_depth = depth;
            *out_rule = "lex_key";
            return 0;
        }
#else
        (void)uses_prev;
#endif

        /* 5. Exact-confirmed dup/zero pruning */
        uint32_t r1;
        uint64_t r2;
#ifdef MUT_NO_DUP
        compute_hash_only(ctx, op, i, j, &r1, &r2);
#else
        int reason = 0;
        if (!compute_hash_and_check_dup_ex(ctx, idx, op, i, j, &r1, &r2, &reason)) {
            *out_depth = depth;
            *out_rule = (reason == 1) ? "zero" : "dup";
            return 0;
        }
#endif

        ctx->h1[idx] = r1;
        ctx->h2[idx] = r2;
        ctx->nh1[idx] = r1 == 0 ? 0 : MP - r1;
        ctx->nh2[idx] = r2 == 0 ? 0 : P2 - r2;
        ctx->path[depth] = gates[depth];
        ctx->key[depth] = k;
        eval_gate_p1(ctx, idx, op, i, j);

        unused_mask = (unused_mask & ~(1U << i) & ~(1U << j)) | (1U << idx);
        unused_cnt = unused_cnt - removed + 1;
    }

    *out_mask = unused_mask;
    *out_cnt = unused_cnt;
    return 1;
}

static int run_membership(const char *path, int tau, int K) {
    FILE *fp = fopen(path, "r");
    if (!fp) {
        perror("fopen --membership");
        return 1;
    }
    char line[4096];
    uint64_t total = 0, found = 0, pruned = 0;
    while (fgets(line, sizeof(line), fp)) {
        char *p = line;
        while (*p && isspace((unsigned char)*p)) p++;
        if (!*p || *p == '#') continue;

        char *end = NULL;
        long n = strtol(p, &end, 10);
        if (end == p || n != tau) {
            fprintf(stderr, "Error: membership line has n=%ld, expected tau=%d: %s", n, tau, line);
            fclose(fp);
            return 1;
        }
        Gate gates[MAX_TAU];
        int parsed = parse_prefix_str(end, gates, MAX_TAU);
        if (parsed != tau) {
            fprintf(stderr, "Error: membership line parsed %d gates, expected %d: %s", parsed, tau, line);
            fclose(fp);
            return 1;
        }

        SearchCtx ctx;
        memset(&ctx, 0, sizeof(ctx));
        ctx.target_tau = tau;
        ctx.cert_bound = K;
        init_base(&ctx);

        uint32_t umask = 0;
        int ucnt = 0, pdepth = -1;
        const char *prule = NULL;
        total++;
        if (trace_gates(&ctx, gates, tau, &umask, &ucnt, &pdepth, &prule)) {
            found++;
            printf("FOUND\t%s", p);
        } else {
            pruned++;
            printf("PRUNED-AT depth %d by rule %s\t%s", pdepth, prule, p);
        }
        if (p[strlen(p) - 1] != '\n') printf("\n");
    }
    fclose(fp);
    printf("MEMBERSHIP SUMMARY tau=%d total=%" PRIu64 " found=%" PRIu64 " pruned=%" PRIu64 "\n",
           tau, total, found, pruned);
    return 0;
}

static int ensure_dir(const char *path) {
    if (mkdir(path, 0755) != 0 && errno != EEXIST) {
        perror(path);
        return 0;
    }
    return 1;
}

static void print_usage(const char *prog) {
    fprintf(stderr,
        "Usage: %s <tau> <cert_bound_K> [nthreads] [survivor_file] [options]\n"
        "Options:\n"
        "  --threads N          Number of worker threads (default 12, >= 1)\n"
        "  --split D            Work-item split depth (0 <= D < tau)\n"
        "  --items A:B          Process only work items in [A, B)\n"
        "  --sample FRAC SEED   Deterministic subset of work items\n"
        "  --checkpoint DIR     Resumable checkpoint directory (done.tsv + surv/*.txt)\n"
        "  --prefix \"a0.1 ...\"  Explore only paths starting with compact prefix\n"
        "  --compact            Write single survivor file in compact format\n"
        "  --membership FILE    Test compact SLPs in FILE against pruning rules\n",
        prog);
}

int main(int argc, char **argv) {
    int pos_cnt = 0;
    const char *pos_args[4] = {NULL, NULL, NULL, NULL};
    int opt_threads = -1;
    int opt_split = -1;
    int has_items = 0, item_a = 0, item_b = 0;
    int has_sample = 0;
    double sample_frac = 1.0;
    uint64_t sample_seed = 0;
    const char *opt_ckpt = NULL;
    const char *opt_prefix = NULL;
    const char *opt_membership = NULL;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--threads") == 0) {
            if (i + 1 >= argc) { print_usage(argv[0]); return 1; }
            opt_threads = atoi(argv[++i]);
        } else if (strcmp(argv[i], "--split") == 0) {
            if (i + 1 >= argc) { print_usage(argv[0]); return 1; }
            opt_split = atoi(argv[++i]);
        } else if (strcmp(argv[i], "--items") == 0) {
            if (i + 1 >= argc) { print_usage(argv[0]); return 1; }
            if (sscanf(argv[++i], "%d:%d", &item_a, &item_b) != 2 || item_a < 0 || item_b < item_a) {
                fprintf(stderr, "Error: invalid --items A:B\n");
                return 1;
            }
            has_items = 1;
        } else if (strcmp(argv[i], "--sample") == 0) {
            if (i + 2 >= argc) { print_usage(argv[0]); return 1; }
            sample_frac = atof(argv[++i]);
            sample_seed = strtoull(argv[++i], NULL, 10);
            if (sample_frac < 0.0 || sample_frac > 1.0) {
                fprintf(stderr, "Error: --sample FRAC must be in [0, 1]\n");
                return 1;
            }
            has_sample = 1;
        } else if (strcmp(argv[i], "--checkpoint") == 0) {
            if (i + 1 >= argc) { print_usage(argv[0]); return 1; }
            opt_ckpt = argv[++i];
        } else if (strcmp(argv[i], "--prefix") == 0) {
            if (i + 1 >= argc) { print_usage(argv[0]); return 1; }
            opt_prefix = argv[++i];
        } else if (strcmp(argv[i], "--compact") == 0) {
            g_compact_out = 1;
        } else if (strcmp(argv[i], "--membership") == 0) {
            if (i + 1 >= argc) { print_usage(argv[0]); return 1; }
            opt_membership = argv[++i];
        } else if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
            print_usage(argv[0]);
            return 0;
        } else if (argv[i][0] == '-') {
            fprintf(stderr, "Error: unknown option %s\n", argv[i]);
            return 1;
        } else {
            if (pos_cnt >= 4) {
                fprintf(stderr, "Error: too many positional arguments\n");
                return 1;
            }
            pos_args[pos_cnt++] = argv[i];
        }
    }

    if (pos_cnt < 2) {
        print_usage(argv[0]);
        return 1;
    }

    int tau = atoi(pos_args[0]);
    int K = atoi(pos_args[1]);
    int nthreads = 12;
    const char *surv_path = "/tmp/z_survivors.txt";

    if (pos_cnt >= 3) {
        /* If arg 3 is purely numeric, treat as nthreads; otherwise survivor_file */
        char *end = NULL;
        long v = strtol(pos_args[2], &end, 10);
        if (end != pos_args[2] && *end == '\0') {
            nthreads = (int)v;
            if (pos_cnt >= 4) surv_path = pos_args[3];
        } else {
            surv_path = pos_args[2];
        }
    }
    if (opt_threads != -1) nthreads = opt_threads;

    if (tau < 1 || tau > MAX_TAU) {
        fprintf(stderr, "Error: tau must be in [1, %d]\n", MAX_TAU);
        return 1;
    }
    if (K < 1 || K >= 19) {
        fprintf(stderr, "Error: cert_bound_K must be in [1, 18]\n");
        return 1;
    }
    if (nthreads < 1) {
        fprintf(stderr, "Error: nthreads must be >= 1\n");
        return 1;
    }
    if (nthreads > 64) nthreads = 64;

#ifdef DUMP_LEAVES
    g_compact_out = 1;
#endif

    if (opt_membership) {
        return run_membership(opt_membership, tau, K);
    }

    Gate prefix_gates[MAX_TAU];
    int prefix_len = 0;
    if (opt_prefix) {
        prefix_len = parse_prefix_str(opt_prefix, prefix_gates, MAX_TAU);
        if (prefix_len < 0 || prefix_len > tau) {
            fprintf(stderr, "Error: invalid --prefix \"%s\" (must have 0..%d compact gates)\n",
                    opt_prefix, tau);
            return 1;
        }
    }

    if (opt_split != -1 && (opt_split < 0 || opt_split >= tau)) {
        fprintf(stderr, "Error: --split D must be in [0, %d]\n", tau - 1);
        return 1;
    }

    clock_gettime(CLOCK_MONOTONIC, &g_start_ts);

    /* Validate --prefix if provided */
    SearchCtx root_ctx;
    memset(&root_ctx, 0, sizeof(root_ctx));
    root_ctx.target_tau = tau;
    root_ctx.cert_bound = K;
    init_base(&root_ctx);

    uint32_t start_mask = 0U;
    int start_cnt = 0;
    if (prefix_len > 0) {
        int pdepth = -1;
        const char *prule = NULL;
        if (!trace_gates(&root_ctx, prefix_gates, prefix_len,
                         &start_mask, &start_cnt, &pdepth, &prule)) {
            printf("PREFIX PRUNED at depth %d by rule %s (0 leaves checked)\n", pdepth, prule);
            return 0;
        }
        /* If prefix_len == tau, evaluate the single leaf directly */
        if (prefix_len == tau) {
            SurvTable local_surv;
            if (opt_ckpt) {
                g_ckpt_dir = opt_ckpt;
                char surv_dir[1024];
                snprintf(surv_dir, sizeof(surv_dir), "%s/surv", g_ckpt_dir);
                if (!ensure_dir(g_ckpt_dir) || !ensure_dir(surv_dir)) return 1;
                surv_table_init(&local_surv, 16);
                root_ctx.local_surv = &local_surv;
            } else {
                surv_table_init(&g_surv, 1 << 16);
                g_surv_fp = fopen(surv_path, "w");
                if (!g_surv_fp) { perror("fopen survivor_file"); return 1; }
            }
            Gate last = prefix_gates[tau - 1];
            check_leaf(&root_ctx, tau - 1, tau + 1, last.op, last.i, last.j);
            if (opt_ckpt) {
                write_item_survivors_atomic(0, root_ctx.local_surv_list, root_ctx.local_surv_len, tau);
                free(root_ctx.local_surv_list);
                root_ctx.local_surv_list = NULL;
                surv_table_free(&local_surv);
                root_ctx.local_surv = NULL;
            } else {
                if (g_surv_fp && fclose(g_surv_fp) != 0) die_io("survivor_file fclose");
                g_surv_fp = NULL;
                surv_table_free(&g_surv);
            }
            printf("PREFIX LEAF tau=%d K=%d leaves_checked=%" PRIu64 " survivors_raw=%" PRIu64 "\n",
                   tau, K, root_ctx.st.leaves_checked, root_ctx.st.survivors_raw);
            return 0;
        }
    }

    /* Decide single-threaded direct DFS vs work-item parallel execution */
    int use_work_items = (tau > 4) || (opt_split != -1) || has_items || has_sample || (opt_ckpt != NULL);
    int split_depth = 0;
    if (use_work_items) {
        if (opt_split != -1) {
            split_depth = opt_split;
        } else if (tau >= 8) {
            split_depth = 3;
        } else if (tau > 4) {
            split_depth = 2;
        } else {
            split_depth = (tau >= 2) ? 1 : 0;
        }
        if (split_depth < prefix_len) split_depth = prefix_len;
    }

    Stats tot;
    memset(&tot, 0, sizeof(tot));
    uint64_t prefix_nodes = 0;
    int work_items_total = 0;
    int work_items_selected = 0;
    int work_items_skipped_ckpt = 0;

    if (!use_work_items) {
        surv_table_init(&g_surv, 1 << 16);
        g_surv_fp = fopen(surv_path, "w");
        if (!g_surv_fp) { perror("fopen survivor_file"); return 1; }

        dfs(&root_ctx, prefix_len, start_mask, start_cnt);
        tot = root_ctx.st;
        tot.survivors_uniq = g_surv.cnt;
        tot.surv_hash_hits = g_surv.hash_hits;
        tot.surv_exact_confirmed = g_surv.exact_confirmed;
        tot.surv_false_positive = g_surv.false_positive;

        if (fclose(g_surv_fp) != 0) die_io("survivor_file fclose");
        g_surv_fp = NULL;
    } else {
        g_work_cnt = 0;
        collect_work(&root_ctx, prefix_len, split_depth, start_mask, start_cnt);
        work_items_total = g_work_cnt;
        prefix_nodes = root_ctx.st.nodes_visited;

        /* Select work items according to --items and --sample */
        int lo = has_items ? item_a : 0;
        int hi = has_items ? item_b : g_work_cnt;
        if (lo > g_work_cnt) lo = g_work_cnt;
        if (hi > g_work_cnt) hi = g_work_cnt;

        uint8_t *selected = (uint8_t *)calloc((size_t)(g_work_cnt > 0 ? g_work_cnt : 1), 1);
        if (!selected) die_oom("selected");
        uint64_t thresh = (sample_frac >= 1.0)
            ? UINT64_MAX
            : (uint64_t)(sample_frac * (double)UINT64_MAX);
        for (int wi = lo; wi < hi; wi++) {
            if (has_sample) {
                if (sample_frac <= 0.0) continue;
                if (sample_frac < 1.0) {
                    uint64_t h = splitmix64(sample_seed ^ ((uint64_t)wi * 0x9e3779b97f4a7c15ULL));
                    if (h >= thresh) continue;
                }
            }
            selected[wi] = 1;
            work_items_selected++;
        }

        uint8_t *done_flags = (uint8_t *)calloc((size_t)(g_work_cnt > 0 ? g_work_cnt : 1), 1);
        if (!done_flags) die_oom("done_flags");

        if (opt_ckpt) {
            g_ckpt_dir = opt_ckpt;
            char surv_dir[1024], done_path[1024];
            snprintf(surv_dir, sizeof(surv_dir), "%s/surv", g_ckpt_dir);
            snprintf(done_path, sizeof(done_path), "%s/done.tsv", g_ckpt_dir);
            if (!ensure_dir(g_ckpt_dir) || !ensure_dir(surv_dir)) return 1;

            /* Build canonical # meta header for resume validation */
            char norm_prefix[512];
            if (prefix_len == 0) {
                strcpy(norm_prefix, "none");
            } else {
                static const char op_ch[3] = {'a', 's', 'm'};
                size_t pos = 0;
                norm_prefix[0] = '\0';
                for (int d = 0; d < prefix_len; d++) {
                    int n = snprintf(norm_prefix + pos, sizeof(norm_prefix) - pos,
                                     "%s%c%d.%d", d > 0 ? "," : "",
                                     op_ch[prefix_gates[d].op], prefix_gates[d].i, prefix_gates[d].j);
                    if (n > 0 && pos + (size_t)n < sizeof(norm_prefix)) pos += (size_t)n;
                }
            }
#ifdef EXTRA_PRIMES
            const int build_extra = 1;
#else
            const int build_extra = 0;
#endif
#ifdef ALT_PRIMES
            const int build_alt = 1;
#else
            const int build_alt = 0;
#endif
#ifdef DUMP_LEAVES
            const int build_dump = 1;
#else
            const int build_dump = 0;
#endif
            char expected_meta[1024];
            snprintf(expected_meta, sizeof(expected_meta),
                     "# meta tau=%d K=%d split=%d prefix=%s extra=%d alt=%d dump=%d\n",
                     tau, K, split_depth, norm_prefix, build_extra, build_alt, build_dump);

            memset(&g_ckpt_tot, 0, sizeof(g_ckpt_tot));
            int need_header = 0;
            struct stat st_buf;
            if (stat(done_path, &st_buf) != 0 || st_buf.st_size == 0) {
                need_header = 1;
            } else {
                FILE *rfp = fopen(done_path, "r");
                if (!rfp) die_io(done_path);
                char line[4096];
                int saw_meta = 0;
                long clean_end = 0;
                int needs_truncate = 0;
                while (fgets(line, sizeof(line), rfp)) {
                    size_t llen = strlen(line);
                    if (llen == 0 || line[llen - 1] != '\n') {
                        /* Incomplete trailing line (e.g. crash mid-write): truncate cleanly */
                        needs_truncate = 1;
                        break;
                    }
                    long after_pos = ftell(rfp);
                    if (strncmp(line, "# meta ", 7) == 0) {
                        saw_meta = 1;
                        if (strcmp(line, expected_meta) != 0) {
                            fprintf(stderr,
                                    "Error: checkpoint metadata mismatch in %s\n"
                                    "  expected: %s"
                                    "  found:    %s",
                                    done_path, expected_meta, line);
                            fclose(rfp);
                            return 1;
                        }
                        clean_end = after_pos;
                        continue;
                    }
                    if (line[0] == '#' || line[0] == '\n' || line[0] == '\r') {
                        clean_end = after_pos;
                        continue;
                    }
                    int id = -1;
                    Stats row;
                    if (!parse_done_row(line, &id, &row)) {
                        fprintf(stderr, "Error: malformed or mismatched row in %s: %s", done_path, line);
                        fclose(rfp);
                        return 1;
                    }
                    if (id >= 0 && id < g_work_cnt && !done_flags[id]) {
                        done_flags[id] = 1;
                        if (selected[id]) {
                            stats_add(&g_ckpt_tot, &row);
                            work_items_skipped_ckpt++;
                        }
                    }
                    clean_end = after_pos;
                }
                fclose(rfp);
                if (!saw_meta) {
                    fprintf(stderr, "Error: checkpoint %s is missing '# meta' header (refusing unsafe resume)\n",
                            done_path);
                    return 1;
                }
                if (needs_truncate) {
                    if (truncate(done_path, (off_t)clean_end) != 0) die_io("done.tsv truncate");
                    fprintf(stderr, "Note: truncated incomplete trailing line in %s to %ld bytes\n",
                            done_path, clean_end);
                }
            }

            g_done_fp = fopen(done_path, "a");
            if (!g_done_fp) die_io(done_path);
            if (need_header) {
                if (fputs(expected_meta, g_done_fp) == EOF) die_io(done_path);
                if (fprintf(g_done_fp, "# item_id nodes leaves deg prod p31 taylor dup_zero") < 0)
                    die_io(done_path);
                for (int f = 0; f < NUM_FALLBACK_PRIMES; f++) {
                    if (fprintf(g_done_fp, " p%d", FALLBACK_PRIMES[f]) < 0) die_io(done_path);
                }
                if (fprintf(g_done_fp, " surv_raw surv_uniq dup_hits dup_ok dup_fp zero_hits zero_ok zero_fp surv_hits surv_ok surv_fp\n") < 0)
                    die_io(done_path);
                if (fflush(g_done_fp) != 0) die_io(done_path);
                if (fsync(fileno(g_done_fp)) != 0) die_io(done_path);
            }
        } else {
            surv_table_init(&g_surv, 1 << 16);
            g_surv_fp = fopen(surv_path, "w");
            if (!g_surv_fp) { perror("fopen survivor_file"); return 1; }
        }

        g_sel_items = (int *)malloc(sizeof(int) * (size_t)(work_items_selected > 0 ? work_items_selected : 1));
        if (!g_sel_items) die_oom("g_sel_items");
        g_sel_cnt = 0;
        for (int wi = 0; wi < g_work_cnt; wi++) {
            if (selected[wi] && !done_flags[wi]) {
                g_sel_items[g_sel_cnt++] = wi;
            }
        }
        g_sel_next = 0;
        g_items_done = work_items_skipped_ckpt;
        g_items_total = work_items_selected;
        g_prog_leaves = opt_ckpt ? g_ckpt_tot.leaves_checked : 0;
        g_prog_surv_raw = opt_ckpt ? g_ckpt_tot.survivors_raw : 0;
        g_prog_stop = 0;

        pthread_t prog_th;
        if (pthread_create(&prog_th, NULL, progress_fn, NULL) != 0) {
            fprintf(stderr, "FATAL: pthread_create progress failed\n");
            return 3;
        }

        pthread_t threads[64];
        WorkerArg args[64];
        for (int t = 0; t < nthreads; t++) {
            memset(&args[t], 0, sizeof(WorkerArg));
            args[t].tid = t;
            args[t].target_tau = tau;
            args[t].cert_bound = K;
            if (pthread_create(&threads[t], NULL, worker_fn, &args[t]) != 0) {
                fprintf(stderr, "FATAL: pthread_create worker %d failed\n", t);
                return 3;
            }
        }
        for (int t = 0; t < nthreads; t++) {
            pthread_join(threads[t], NULL);
        }

        pthread_mutex_lock(&g_prog_lock);
        g_prog_stop = 1;
        pthread_cond_signal(&g_prog_cond);
        pthread_mutex_unlock(&g_prog_lock);
        pthread_join(prog_th, NULL);

        if (opt_ckpt) {
            if (fclose(g_done_fp) != 0) die_io("done.tsv fclose");
            g_done_fp = NULL;
            tot = g_ckpt_tot;
        } else {
            for (int t = 0; t < nthreads; t++) {
                stats_add(&tot, &args[t].st);
            }
            tot.survivors_uniq = g_surv.cnt;
            tot.surv_hash_hits = g_surv.hash_hits;
            tot.surv_exact_confirmed = g_surv.exact_confirmed;
            tot.surv_false_positive = g_surv.false_positive;
            if (fclose(g_surv_fp) != 0) die_io("survivor_file fclose");
            g_surv_fp = NULL;
        }

        /* Add prefix-level dup/zero hash confirmation counts (do not alter nodes_visited semantics) */
        tot.dup_hash_hits += root_ctx.st.dup_hash_hits;
        tot.dup_exact_confirmed += root_ctx.st.dup_exact_confirmed;
        tot.dup_false_positive += root_ctx.st.dup_false_positive;
        tot.zero_hash_hits += root_ctx.st.zero_hash_hits;
        tot.zero_exact_confirmed += root_ctx.st.zero_exact_confirmed;
        tot.zero_false_positive += root_ctx.st.zero_false_positive;

        free(selected);
        free(done_flags);
        free(g_sel_items);
        g_sel_items = NULL;
    }

    struct timespec t1;
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double dt = (t1.tv_sec - g_start_ts.tv_sec) + (t1.tv_nsec - g_start_ts.tv_nsec) * 1e-9;

    /* Conservation check */
    uint64_t cat_sum = tot.cert_deg + tot.cert_prod + tot.cert_p1 + tot.cert_taylor +
                       tot.cert_dup_zero + tot.survivors_raw;
    for (int f = 0; f < NUM_FALLBACK_PRIMES; f++) cat_sum += tot.cert_fallback[f];
    int conservation_ok = (tot.leaves_checked == cat_sum);

#ifdef ALT_PRIMES
    printf("CERTIFY_EXACT [ALT_PRIMES P1=%u P2=%llu P3=%llu] tau=%d K=%d time=%.3fs (%.1fM leaves/s)\n",
           MP, (unsigned long long)P2, (unsigned long long)P3,
           tau, K, dt, (double)tot.leaves_checked / (dt * 1e6 + 1e-9));
#else
    printf("CERTIFY_EXACT tau=%d K=%d time=%.3fs (%.1fM leaves/s)\n",
           tau, K, dt, (double)tot.leaves_checked / (dt * 1e6 + 1e-9));
#endif
    if (use_work_items) {
        printf("  work_items     = %d selected / %d total (split=%d, resumed=%d)\n",
               work_items_selected, work_items_total, split_depth, work_items_skipped_ckpt);
        printf("  prefix_nodes   = %" PRIu64 " (nodes_total = %" PRIu64 ")\n",
               prefix_nodes, tot.nodes_visited + prefix_nodes);
    }
    printf("  nodes_visited  = %" PRIu64 "\n", tot.nodes_visited);
    printf("  leaves_checked = %" PRIu64 "\n", tot.leaves_checked);
    printf("  cert_deg       = %" PRIu64 " (%.2f%%)\n", tot.cert_deg, 100.0 * (double)tot.cert_deg / ((double)tot.leaves_checked + 1e-9));
    printf("  cert_prod      = %" PRIu64 " (%.2f%%)\n", tot.cert_prod, 100.0 * (double)tot.cert_prod / ((double)tot.leaves_checked + 1e-9));
    printf("  cert_p31       = %" PRIu64 " (%.2f%%)\n", tot.cert_p1, 100.0 * (double)tot.cert_p1 / ((double)tot.leaves_checked + 1e-9));
    printf("  cert_taylor31  = %" PRIu64 " (%.2f%%)\n", tot.cert_taylor, 100.0 * (double)tot.cert_taylor / ((double)tot.leaves_checked + 1e-9));
    printf("  cert_dup_zero  = %" PRIu64 " (%.2f%%)\n", tot.cert_dup_zero, 100.0 * (double)tot.cert_dup_zero / ((double)tot.leaves_checked + 1e-9));
    for (int f = 0; f < NUM_FALLBACK_PRIMES; f++) {
        printf("  cert_p%d       = %" PRIu64 " (%.4f%%)\n",
               FALLBACK_PRIMES[f], tot.cert_fallback[f], 100.0 * (double)tot.cert_fallback[f] / ((double)tot.leaves_checked + 1e-9));
    }
    printf("  survivors_raw  = %" PRIu64 "\n", tot.survivors_raw);
    if (opt_ckpt) {
        printf("  survivors_uniq = %" PRIu64 " (per-item deduped in %s/surv/)\n", tot.survivors_uniq, opt_ckpt);
    } else {
        printf("  survivors_uniq = %" PRIu64 " (written to %s)\n", tot.survivors_uniq, surv_path);
    }
    printf("  dup_hash_hits        = %" PRIu64 "\n", tot.dup_hash_hits);
    printf("  dup_exact_confirmed  = %" PRIu64 "\n", tot.dup_exact_confirmed);
    printf("  dup_false_positive   = %" PRIu64 "\n", tot.dup_false_positive);
    printf("  zero_hash_hits       = %" PRIu64 "\n", tot.zero_hash_hits);
    printf("  zero_exact_confirmed = %" PRIu64 "\n", tot.zero_exact_confirmed);
    printf("  zero_false_positive  = %" PRIu64 "\n", tot.zero_false_positive);
    printf("  surv_hash_hits       = %" PRIu64 "\n", tot.surv_hash_hits);
    printf("  surv_exact_confirmed = %" PRIu64 "\n", tot.surv_exact_confirmed);
    printf("  surv_false_positive  = %" PRIu64 "\n", tot.surv_false_positive);
    printf("  conservation_check   = %s (leaves=%" PRIu64 ", sum=%" PRIu64 ")\n",
           conservation_ok ? "PASS" : "FAIL", tot.leaves_checked, cat_sum);
    fflush(stdout);

    free(g_work);
    surv_table_free(&g_surv);

    return conservation_ok ? 0 : 2;
}
