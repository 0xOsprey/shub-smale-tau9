/*
 * Track B Record Witness Hunter Accelerator (tau = 10, 11, 12, 13, 14)
 * Multi-threaded (pthreads) engine with three modes:
 *   1. compose: Exhaustive weighted outer-SLP search P(Q(x)) up to tau_P = 8
 *               for a rich bank of high-collision inner polynomials Q(x) (cost 1..6).
 *   2. beam:    Multi-objective diverse beam search for tau = 1..14 on [-64, 63].
 *   3. extend:  Seeded exhaustive extension from elite DAGs up to tau = 14.
 *
 * Uses division-free Mersenne arithmetic mod P1 = 2^31 - 1 with P2 = 10^9 + 9
 * cross-check to eliminate modular false positives.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>
#include <time.h>

#define MAX_TAU 14
#define NPTS 128
#define X_MIN (-64)
#define MP 2147483647U
#define P2 1000000009ULL
#define HASH_X1 314159265U
#define HASH_X2 271828182ULL

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
static inline uint32_t int_to_mp(int64_t x) {
    int64_t r = x % (int64_t)MP;
    if (r < 0) r += (int64_t)MP;
    return (uint32_t)r;
}
static inline uint64_t int_to_p2(int64_t x) {
    int64_t r = x % (int64_t)P2;
    if (r < 0) r += (int64_t)P2;
    return (uint64_t)r;
}

typedef struct {
    uint8_t op; /* 0='+', 1='-', 2='*' */
    uint8_t i;  /* 0=1, 1=x(or y), k+1=g_k */
    uint8_t j;
} Gate;

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static void format_slp_buf(char *out, const Gate *gates, int tau, const char *var_name) {
    const char *ops = "+-*";
    char *p = out;
    for (int k = 0; k < tau; k++) {
        if (k > 0) { *p++ = ';'; *p++ = ' '; }
        int i = (int)gates[k].i - 1;
        int j = (int)gates[k].j - 1;
        char si[16], sj[16];
        if (i == -1) strcpy(si, "1");
        else if (i == 0) strcpy(si, var_name);
        else sprintf(si, "g%d", i);
        if (j == -1) strcpy(sj, "1");
        else if (j == 0) strcpy(sj, var_name);
        else sprintf(sj, "g%d", j);
        p += sprintf(p, "g%d = %s %c %s", k + 1, si, ops[gates[k].op], sj);
    }
    *p = '\0';
}

/* ============================================================================
 * MODE 1: EXHAUSTIVE WEIGHTED COMPOSITION SEARCH P(Q(x))
 * ============================================================================ */

#define MAX_WPTS 64

typedef struct {
    const char *name;
    int q_cost;
    const char *q_slp;
    int npts;
    int64_t y_vals[MAX_WPTS];
    int weights[MAX_WPTS];
    uint32_t y_mp[MAX_WPTS];
    uint64_t y_p2[MAX_WPTS];
} QTarget;

typedef struct {
    int target_tau_p;
    const QTarget *qt;
    uint32_t vals[12][MAX_WPTS];
    uint32_t h1[12];
    uint64_t h2[12];
    uint32_t nh1[12];
    uint64_t nh2[12];
    uint32_t keys[12];
    Gate path[12];
    uint64_t leaves;
    int local_best;
} CompCtx;

static pthread_mutex_t g_print_lock = PTHREAD_MUTEX_INITIALIZER;
static int g_comp_best = 0;

static int comp_verify_p2(const QTarget *qt, const Gate *gates, int tau_p) {
    uint64_t v[12][MAX_WPTS];
    int n = qt->npts;
    for (int p = 0; p < n; p++) {
        v[0][p] = 1;
        v[1][p] = qt->y_p2[p];
    }
    for (int d = 0; d < tau_p; d++) {
        int idx = d + 2;
        int op = gates[d].op, i = gates[d].i, j = gates[d].j;
        if (op == 0) {
            for (int p = 0; p < n; p++) {
                uint64_t s = v[i][p] + v[j][p];
                v[idx][p] = s >= P2 ? s - P2 : s;
            }
        } else if (op == 1) {
            for (int p = 0; p < n; p++) {
                v[idx][p] = v[i][p] >= v[j][p] ? v[i][p] - v[j][p] : v[i][p] + P2 - v[j][p];
            }
        } else {
            for (int p = 0; p < n; p++) {
                v[idx][p] = (v[i][p] * v[j][p]) % P2;
            }
        }
    }
    int wsum = 0;
    for (int p = 0; p < n; p++) {
        if (v[tau_p + 1][p] == 0) wsum += qt->weights[p];
    }
    return wsum;
}

static inline int comp_check_dup(CompCtx *ctx, int idx, int op, int i, int j,
                                 uint32_t *out1, uint64_t *out2) {
    uint32_t a1 = ctx->h1[i], b1 = ctx->h1[j];
    uint64_t a2 = ctx->h2[i], b2 = ctx->h2[j];
    uint32_t r1; uint64_t r2;
    if (op == 0) { r1 = madd(a1, b1); r2 = a2 + b2; if (r2 >= P2) r2 -= P2; }
    else if (op == 1) { r1 = msub(a1, b1); r2 = a2 >= b2 ? a2 - b2 : a2 + P2 - b2; }
    else { r1 = mmul(a1, b1); r2 = (a2 * b2) % P2; }
    if (r1 == 0 && r2 == 0) return 0;
    for (int m = 0; m < idx; m++) {
        if ((r1 == ctx->h1[m] && r2 == ctx->h2[m]) ||
            (r1 == ctx->nh1[m] && r2 == ctx->nh2[m])) return 0;
    }
    *out1 = r1; *out2 = r2;
    return 1;
}

static inline int comp_leaf_score(const QTarget *qt, const uint32_t *va, const uint32_t *vb, int op) {
    int n = qt->npts;
    const int *w = qt->weights;
    int s = 0;
    if (op == 0) {
        for (int p = 0; p < n; p++) {
            uint32_t sum = va[p] + vb[p];
            if (sum == 0 || sum == MP) s += w[p];
        }
    } else if (op == 1) {
        for (int p = 0; p < n; p++) {
            if (va[p] == vb[p]) s += w[p];
        }
    } else {
        for (int p = 0; p < n; p++) {
            if (va[p] == 0 || vb[p] == 0) s += w[p];
        }
    }
    return s;
}

static inline void comp_report(CompCtx *ctx, int op, int i, int j, int wscore) {
    int tau_p = ctx->target_tau_p;
    ctx->path[tau_p - 1] = (Gate){(uint8_t)op, (uint8_t)i, (uint8_t)j};
    int vscore = comp_verify_p2(ctx->qt, ctx->path, tau_p);
    if (vscore > ctx->local_best) {
        pthread_mutex_lock(&g_print_lock);
        if (vscore >= g_comp_best) {
            if (vscore > g_comp_best) g_comp_best = vscore;
            char buf[512];
            format_slp_buf(buf, ctx->path, tau_p, "y");
            printf("COMP_FOUND Q=[%s](cost=%d) tau_P=%d total_tau=%d roots=%d | Q: %s | P(y): %s\n",
                   ctx->qt->name, ctx->qt->q_cost, tau_p, ctx->qt->q_cost + tau_p,
                   vscore, ctx->qt->q_slp, buf);
            fflush(stdout);
        }
        ctx->local_best = g_comp_best;
        pthread_mutex_unlock(&g_print_lock);
    }
}

static void comp_dfs(CompCtx *ctx, int depth, uint32_t unused_mask, int unused_cnt) {
    int tau = ctx->target_tau_p;
    int idx = depth + 2;
    int max_unused_after = (tau - 1 - depth) + 1;
    const QTarget *qt = ctx->qt;
    int n = qt->npts;

    if (depth == tau - 1) {
        if (unused_cnt == 2) {
            int i = __builtin_ctz(unused_mask);
            int j = __builtin_ctz(unused_mask ^ (1U << i));
            uint32_t r1; uint64_t r2;
            const uint32_t *va = ctx->vals[i], *vb = ctx->vals[j];
            for (int op = 0; op < 3; op++) {
                ctx->leaves++;
                int sc = comp_leaf_score(qt, va, vb, op);
                if (sc >= ctx->local_best && comp_check_dup(ctx, idx, op, i, j, &r1, &r2)) {
                    comp_report(ctx, op, i, j, sc);
                }
            }
            return;
        }
        if (unused_cnt == 1) {
            int u = __builtin_ctz(unused_mask);
            uint32_t r1; uint64_t r2;
            const uint32_t *vu = ctx->vals[u];
            for (int k = 0; k < idx; k++) {
                int i = k < u ? k : u;
                int j = k < u ? u : k;
                const uint32_t *va = ctx->vals[i], *vb = ctx->vals[j];
                /* op = 0 (+) */
                ctx->leaves++;
                int sc0 = comp_leaf_score(qt, va, vb, 0);
                if (sc0 >= ctx->local_best && comp_check_dup(ctx, idx, 0, i, j, &r1, &r2))
                    comp_report(ctx, 0, i, j, sc0);
                /* op = 1 (-) only if i < j */
                if (i < j) {
                    ctx->leaves++;
                    int sc1 = comp_leaf_score(qt, va, vb, 1);
                    if (sc1 >= ctx->local_best && comp_check_dup(ctx, idx, 1, i, j, &r1, &r2))
                        comp_report(ctx, 1, i, j, sc1);
                }
                /* op = 2 (*) */
                ctx->leaves++;
                int sc2 = comp_leaf_score(qt, va, vb, 2);
                if (sc2 >= ctx->local_best && comp_check_dup(ctx, idx, 2, i, j, &r1, &r2))
                    comp_report(ctx, 2, i, j, sc2);
            }
            return;
        }
        /* unused_cnt == 0 */
        uint32_t r1; uint64_t r2;
        for (int i = 0; i < idx; i++) {
            const uint32_t *va = ctx->vals[i];
            for (int j = i; j < idx; j++) {
                const uint32_t *vb = ctx->vals[j];
                ctx->leaves++;
                int sc0 = comp_leaf_score(qt, va, vb, 0);
                if (sc0 >= ctx->local_best && comp_check_dup(ctx, idx, 0, i, j, &r1, &r2))
                    comp_report(ctx, 0, i, j, sc0);
                if (i < j) {
                    ctx->leaves++;
                    int sc1 = comp_leaf_score(qt, va, vb, 1);
                    if (sc1 >= ctx->local_best && comp_check_dup(ctx, idx, 1, i, j, &r1, &r2))
                        comp_report(ctx, 1, i, j, sc1);
                }
                ctx->leaves++;
                int sc2 = comp_leaf_score(qt, va, vb, 2);
                if (sc2 >= ctx->local_best && comp_check_dup(ctx, idx, 2, i, j, &r1, &r2))
                    comp_report(ctx, 2, i, j, sc2);
            }
        }
        return;
    }

    uint32_t prev_key = (depth > 0) ? ctx->keys[depth - 1] : 0;
    uint32_t prev_gate_idx = (depth > 0) ? (uint32_t)(idx - 1) : 99;
    uint32_t r1; uint64_t r2;
    uint32_t *vc = ctx->vals[idx];

    for (int i = 0; i < idx; i++) {
        int i_used = (unused_mask >> i) & 1U;
        for (int j = i; j < idx; j++) {
            int j_used = (unused_mask >> j) & 1U;
            int dec = i_used + ((j != i) ? j_used : 0);
            int new_unused_cnt = unused_cnt - dec + 1;
            if (new_unused_cnt > max_unused_after) continue;
            uint32_t new_mask = (unused_mask & ~(1U << i) & ~(1U << j)) | (1U << idx);
            int uses_prev = (i == (int)prev_gate_idx || j == (int)prev_gate_idx);

            for (int op = 0; op < 3; op++) {
                if (op == 1 && i == j) continue;
                uint32_t key = ((uint32_t)op << 10) | ((uint32_t)i << 5) | (uint32_t)j;
                if (depth > 0 && !uses_prev && key < prev_key) continue;
                if (!comp_check_dup(ctx, idx, op, i, j, &r1, &r2)) continue;

                ctx->h1[idx] = r1; ctx->h2[idx] = r2;
                ctx->nh1[idx] = (r1 == 0) ? 0 : (MP - r1);
                ctx->nh2[idx] = (r2 == 0) ? 0 : (P2 - r2);
                ctx->keys[depth] = key;
                ctx->path[depth] = (Gate){(uint8_t)op, (uint8_t)i, (uint8_t)j};

                const uint32_t *va = ctx->vals[i], *vb = ctx->vals[j];
                if (op == 0) for (int p = 0; p < n; p++) vc[p] = madd(va[p], vb[p]);
                else if (op == 1) for (int p = 0; p < n; p++) vc[p] = msub(va[p], vb[p]);
                else for (int p = 0; p < n; p++) vc[p] = mmul(va[p], vb[p]);

                comp_dfs(ctx, depth + 1, new_mask, new_unused_cnt);
            }
        }
    }
}

typedef struct {
    Gate g0, g1;
    uint32_t k0, k1;
} CompJob;

static CompJob *g_cjobs = NULL;
static int g_ncjobs = 0;
static int g_cjob_next = 0;
static pthread_mutex_t g_cjob_lock = PTHREAD_MUTEX_INITIALIZER;
static const QTarget *g_cur_qt = NULL;
static int g_cur_tau_p = 0;

static void *comp_worker(void *arg) {
    (void)arg;
    CompCtx ctx;
    ctx.target_tau_p = g_cur_tau_p;
    ctx.qt = g_cur_qt;
    ctx.leaves = 0;
    ctx.local_best = g_comp_best;

    int n = ctx.qt->npts;
    for (int p = 0; p < n; p++) {
        ctx.vals[0][p] = 1;
        ctx.vals[1][p] = ctx.qt->y_mp[p];
    }
    ctx.h1[0] = 1; ctx.h2[0] = 1; ctx.nh1[0] = MP - 1; ctx.nh2[0] = P2 - 1;
    ctx.h1[1] = HASH_X1; ctx.h2[1] = HASH_X2; ctx.nh1[1] = MP - HASH_X1; ctx.nh2[1] = P2 - HASH_X2;

    while (1) {
        pthread_mutex_lock(&g_cjob_lock);
        int id = g_cjob_next++;
        pthread_mutex_unlock(&g_cjob_lock);
        if (id >= g_ncjobs) break;

        CompJob jb = g_cjobs[id];
        uint32_t r1; uint64_t r2;
        /* Apply g0 at depth 0 (idx 2) */
        comp_check_dup(&ctx, 2, jb.g0.op, jb.g0.i, jb.g0.j, &r1, &r2);
        ctx.h1[2] = r1; ctx.h2[2] = r2; ctx.nh1[2] = r1 ? MP - r1 : 0; ctx.nh2[2] = r2 ? P2 - r2 : 0;
        ctx.keys[0] = jb.k0; ctx.path[0] = jb.g0;
        for (int p = 0; p < n; p++) {
            uint32_t a = ctx.vals[jb.g0.i][p], b = ctx.vals[jb.g0.j][p];
            ctx.vals[2][p] = jb.g0.op == 0 ? madd(a, b) : (jb.g0.op == 1 ? msub(a, b) : mmul(a, b));
        }
        /* Apply g1 at depth 1 (idx 3) */
        comp_check_dup(&ctx, 3, jb.g1.op, jb.g1.i, jb.g1.j, &r1, &r2);
        ctx.h1[3] = r1; ctx.h2[3] = r2; ctx.nh1[3] = r1 ? MP - r1 : 0; ctx.nh2[3] = r2 ? P2 - r2 : 0;
        ctx.keys[1] = jb.k1; ctx.path[1] = jb.g1;
        for (int p = 0; p < n; p++) {
            uint32_t a = ctx.vals[jb.g1.i][p], b = ctx.vals[jb.g1.j][p];
            ctx.vals[3][p] = jb.g1.op == 0 ? madd(a, b) : (jb.g1.op == 1 ? msub(a, b) : mmul(a, b));
        }

        uint32_t mask = 1U << 2;
        int cnt = 1;
        if (jb.g1.i == 2 || jb.g1.j == 2) { mask &= ~(1U << 2); cnt--; }
        mask |= (1U << 3); cnt++;
        ctx.local_best = g_comp_best;
        comp_dfs(&ctx, 2, mask, cnt);
    }
    return NULL;
}

static void build_qtarget_from_eval(QTarget *qt, const char *name, int q_cost, const char *q_slp,
                                    int64_t (*fn)(int64_t), int xlo, int xhi) {
    qt->name = name;
    qt->q_cost = q_cost;
    qt->q_slp = q_slp;
    /* Collect (val, count) over [xlo, xhi] */
    typedef struct { int64_t v; int c; } VC;
    VC arr[512];
    int na = 0;
    for (int x = xlo; x <= xhi; x++) {
        int64_t v = fn(x);
        int found = 0;
        for (int k = 0; k < na; k++) {
            if (arr[k].v == v) { arr[k].c++; found = 1; break; }
        }
        if (!found && na < 512) { arr[na].v = v; arr[na].c = 1; na++; }
    }
    /* Sort by count descending, then |v| ascending */
    for (int i = 0; i < na; i++) {
        for (int j = i + 1; j < na; j++) {
            int64_t ai = arr[i].v < 0 ? -arr[i].v : arr[i].v;
            int64_t aj = arr[j].v < 0 ? -arr[j].v : arr[j].v;
            if (arr[j].c > arr[i].c || (arr[j].c == arr[i].c && aj < ai)) {
                VC tmp = arr[i]; arr[i] = arr[j]; arr[j] = tmp;
            }
        }
    }
    int take = na < MAX_WPTS ? na : MAX_WPTS;
    qt->npts = take;
    for (int k = 0; k < take; k++) {
        qt->y_vals[k] = arr[k].v;
        qt->weights[k] = arr[k].c;
        qt->y_mp[k] = int_to_mp(arr[k].v);
        qt->y_p2[k] = int_to_p2(arr[k].v);
    }
}

/* Inner Q(x) evaluation functions */
static int64_t q_x2(int64_t x) { return x * x; }
static int64_t q_pronic(int64_t x) { return x * (x + 1); }
static int64_t q_x2_m2(int64_t x) { return x * x - 2; }
static int64_t q_x2_m5(int64_t x) { return x * x - 5; }
static int64_t q_x2_m10(int64_t x) { return x * x - 10; }
static int64_t q_q_m2(int64_t x) { return x * (x + 1) - 2; }
static int64_t q_q_m4(int64_t x) { return x * (x + 1) - 4; }
static int64_t q_q_m6(int64_t x) { return x * (x + 1) - 6; }
static int64_t q_q_m16(int64_t x) { return x * (x + 1) - 16; }
static int64_t q_x2_m2_sq(int64_t x) { int64_t u = x * x - 2; return u * u; }
static int64_t q_x2_m5_sq(int64_t x) { int64_t u = x * x - 5; return u * u; }
static int64_t q_q_m4_sq(int64_t x) { int64_t u = x * (x + 1) - 4; return u * u; }
static int64_t q_q_m16_sq(int64_t x) { int64_t u = x * (x + 1) - 16; return u * u; }
static int64_t q_diffsq2(int64_t x) { int64_t u = 2 - x * x; return x * x - u * u; }
static int64_t q_cubic1(int64_t x) { return x * (x * x - 1); }
static int64_t q_cubic4(int64_t x) { return x * (x * x - 4); }
static int64_t q_q_q2(int64_t x) { int64_t q = x * (x + 1); return q * (q - 2); }
static int64_t q_x2_m10_sq(int64_t x) { int64_t u = x * x - 10; return u * u; }
static int64_t q_x2_m13_sq(int64_t x) { int64_t u = x * x - 13; return u * u; }
static int64_t q_x2_m17_sq(int64_t x) { int64_t u = x * x - 17; return u * u; }
static int64_t q_x2_m20_sq(int64_t x) { int64_t u = x * x - 20; return u * u; }
static int64_t q_x2_m25_sq(int64_t x) { int64_t u = x * x - 25; return u * u; }

static void run_compose_for_qt(const QTarget *qt, int tau_p, int min_report, int nthreads) {
    /* Build 2-gate jobs */
    CompCtx tmp;
    tmp.h1[0] = 1; tmp.h2[0] = 1; tmp.nh1[0] = MP - 1; tmp.nh2[0] = P2 - 1;
    tmp.h1[1] = HASH_X1; tmp.h2[1] = HASH_X2; tmp.nh1[1] = MP - HASH_X1; tmp.nh2[1] = P2 - HASH_X2;

    CompJob jobs[1024];
    int nj = 0;
    uint32_t r1, r1b; uint64_t r2, r2b;
    for (int i0 = 0; i0 < 2; i0++) {
        for (int j0 = i0; j0 < 2; j0++) {
            for (int op0 = 0; op0 < 3; op0++) {
                if (op0 == 1 && i0 == j0) continue;
                if (!comp_check_dup(&tmp, 2, op0, i0, j0, &r1, &r2)) continue;
                tmp.h1[2] = r1; tmp.h2[2] = r2; tmp.nh1[2] = r1 ? MP - r1 : 0; tmp.nh2[2] = r2 ? P2 - r2 : 0;
                uint32_t k0 = ((uint32_t)op0 << 10) | ((uint32_t)i0 << 5) | (uint32_t)j0;
                for (int i1 = 0; i1 < 3; i1++) {
                    for (int j1 = i1; j1 < 3; j1++) {
                        int uses_prev = (i1 == 2 || j1 == 2);
                        for (int op1 = 0; op1 < 3; op1++) {
                            if (op1 == 1 && i1 == j1) continue;
                            uint32_t k1 = ((uint32_t)op1 << 10) | ((uint32_t)i1 << 5) | (uint32_t)j1;
                            if (!uses_prev && k1 < k0) continue;
                            if (!comp_check_dup(&tmp, 3, op1, i1, j1, &r1b, &r2b)) continue;
                            jobs[nj++] = (CompJob){
                                {(uint8_t)op0, (uint8_t)i0, (uint8_t)j0},
                                {(uint8_t)op1, (uint8_t)i1, (uint8_t)j1},
                                k0, k1
                            };
                        }
                    }
                }
            }
        }
    }

    g_cjobs = jobs;
    g_ncjobs = nj;
    g_cjob_next = 0;
    g_cur_qt = qt;
    g_cur_tau_p = tau_p;
    g_comp_best = min_report;

    double t0 = now_sec();
    pthread_t th[32];
    for (int t = 0; t < nthreads; t++) pthread_create(&th[t], NULL, comp_worker, NULL);
    for (int t = 0; t < nthreads; t++) pthread_join(th[t], NULL);
    double dt = now_sec() - t0;
    printf("[compose] Q=%-14s (cost=%d) tau_P=%d (total=%2d) best=%2d  (%.2fs)\n",
           qt->name, qt->q_cost, tau_p, qt->q_cost + tau_p, g_comp_best, dt);
    fflush(stdout);
}

static void run_compose_suite(int max_tau_p, int nthreads) {
    struct {
        const char *name;
        int cost;
        const char *slp;
        int64_t (*fn)(int64_t);
        int min_rep;
    } bank[] = {
        {"x^2",        1, "q1 = x * x", q_x2, 8},
        {"x(x+1)",     2, "q1 = 1 + x; q2 = x * q1", q_pronic, 8},
        {"x^2-2",      3, "q1 = 1 + 1; q2 = x * x; q3 = q2 - q1", q_x2_m2, 8},
        {"q-2",        4, "q1 = 1 + 1; q2 = 1 + x; q3 = x * q2; q4 = q3 - q1", q_q_m2, 8},
        {"(x^2-2)^2",  4, "q1 = 1 + 1; q2 = x * x; q3 = q2 - q1; q4 = q3 * q3", q_x2_m2_sq, 8},
        {"x(x^2-1)",   3, "q1 = x * x; q2 = q1 - 1; q3 = x * q2", q_cubic1, 8},
        {"x^2-(2-x^2)^2", 5, "q1 = 1 + 1; q2 = x * x; q3 = q1 - q2; q4 = q3 * q3; q5 = q2 - q4", q_diffsq2, 8},
        {"q(q-2)",     5, "q1 = 1 + 1; q2 = 1 + x; q3 = x * q2; q4 = q3 - q1; q5 = q3 * q4", q_q_q2, 8},
        {"(q-4)^2",    6, "q1 = 1 + 1; q2 = q1 + q1; q3 = 1 + x; q4 = x * q3; q5 = q4 - q2; q6 = q5 * q5", q_q_m4_sq, 8},
        {"(x^2-5)^2",  6, "q1 = 1 + 1; q2 = q1 + q1; q3 = q2 + 1; q4 = x * x; q5 = q4 - q3; q6 = q5 * q5", q_x2_m5_sq, 8},
        {"(x^2-10)^2", 7, "q1 = 1 + 1; q2 = q1 + 1; q3 = q2 * q2; q4 = q3 + 1; q5 = x * x; q6 = q5 - q4; q7 = q6 * q6", q_x2_m10_sq, 8},
        {"(q-16)^2",   7, "q1 = 1 + x; q2 = x * q1; q3 = 1 + 1; q4 = q3 + q3; q5 = q4 * q4; q6 = q2 - q5; q7 = q6 * q6", q_q_m16_sq, 9},
        {"(x^2-17)^2", 7, "q1 = 1 + 1; q2 = q1 + q1; q3 = q2 * q2; q4 = q3 + 1; q5 = x * x; q6 = q5 - q4; q7 = q6 * q6", q_x2_m17_sq, 8},
        {"(x^2-25)^2", 7, "q1 = 1 + 1; q2 = q1 + q1; q3 = q2 + 1; q4 = q3 * q3; q5 = x * x; q6 = q5 - q4; q7 = q6 * q6", q_x2_m25_sq, 8},
    };
    int nb = (int)(sizeof(bank) / sizeof(bank[0]));
    for (int i = 0; i < nb; i++) {
        QTarget qt;
        build_qtarget_from_eval(&qt, bank[i].name, bank[i].cost, bank[i].slp, bank[i].fn, -40, 40);
        int tp = max_tau_p;
        if (bank[i].cost + tp > 14) tp = 14 - bank[i].cost;
        if (tp < 5) continue;
        int min_rep = (bank[i].cost + tp <= 10) ? 7 : ((bank[i].cost + tp <= 12) ? 8 : 9);
        run_compose_for_qt(&qt, tp, min_rep, nthreads);
    }
}

/* ============================================================================
 * MODE 2: MULTI-OBJECTIVE DIVERSE BEAM SEARCH (tau = 1..14)
 * ============================================================================ */

static uint32_t g_base0[NPTS], g_base1[NPTS];

static void init_bases(void) {
    for (int p = 0; p < NPTS; p++) {
        int x = X_MIN + p;
        g_base0[p] = 1;
        g_base1[p] = (x >= 0) ? (uint32_t)x : (MP - (uint32_t)(-x));
    }
}

typedef struct {
    int len;
    Gate gates[MAX_TAU];
    int max_roots;
    int pair_roots;
    int coll_score;
    int total_score;
    uint64_t sig;
} BeamCand;

static int cmp_beam_desc(const void *a, const void *b) {
    const BeamCand *ca = (const BeamCand *)a;
    const BeamCand *cb = (const BeamCand *)b;
    if (cb->total_score != ca->total_score) return cb->total_score - ca->total_score;
    if (cb->max_roots != ca->max_roots) return cb->max_roots - ca->max_roots;
    return (cb->sig > ca->sig) ? 1 : (cb->sig < ca->sig ? -1 : 0);
}

static int cmp_coll_desc(const void *a, const void *b) {
    const BeamCand *ca = (const BeamCand *)a;
    const BeamCand *cb = (const BeamCand *)b;
    if (cb->coll_score != ca->coll_score) return cb->coll_score - ca->coll_score;
    if (cb->total_score != ca->total_score) return cb->total_score - ca->total_score;
    return (cb->sig > ca->sig) ? 1 : (cb->sig < ca->sig ? -1 : 0);
}

static int cmp_pair_desc(const void *a, const void *b) {
    const BeamCand *ca = (const BeamCand *)a;
    const BeamCand *cb = (const BeamCand *)b;
    if (cb->pair_roots != ca->pair_roots) return cb->pair_roots - ca->pair_roots;
    if (cb->total_score != ca->total_score) return cb->total_score - ca->total_score;
    return (cb->sig > ca->sig) ? 1 : (cb->sig < ca->sig ? -1 : 0);
}

static int verify_p2_full(const Gate *gates, int tau) {
    uint64_t v[MAX_TAU + 2][NPTS];
    for (int p = 0; p < NPTS; p++) {
        int x = X_MIN + p;
        v[0][p] = 1;
        v[1][p] = int_to_p2(x);
    }
    for (int d = 0; d < tau; d++) {
        int idx = d + 2;
        int op = gates[d].op, i = gates[d].i, j = gates[d].j;
        if (op == 0) for (int p = 0; p < NPTS; p++) { uint64_t s = v[i][p] + v[j][p]; v[idx][p] = s >= P2 ? s - P2 : s; }
        else if (op == 1) for (int p = 0; p < NPTS; p++) v[idx][p] = v[i][p] >= v[j][p] ? v[i][p] - v[j][p] : v[i][p] + P2 - v[j][p];
        else for (int p = 0; p < NPTS; p++) v[idx][p] = (v[i][p] * v[j][p]) % P2;
    }
    int z = 0;
    for (int p = 0; p < NPTS; p++) z += (v[tau + 1][p] == 0);
    return z;
}

/* Fast small collision counter on 64 middle points (x in [-32, 31]) */
static int fast_collision_score(const uint32_t *v) {
    /* Copy middle 64 values and insertion/shell sort to find top-2 multiplicities */
    uint32_t a[64];
    memcpy(a, v + 32, 64 * sizeof(uint32_t));
    /* Shell sort with gaps 23, 7, 1 */
    static const int gaps[3] = {23, 7, 1};
    for (int g = 0; g < 3; g++) {
        int gap = gaps[g];
        for (int i = gap; i < 64; i++) {
            uint32_t t = a[i];
            int j = i;
            while (j >= gap && a[j - gap] > t) {
                a[j] = a[j - gap];
                j -= gap;
            }
            a[j] = t;
        }
    }
    int top1 = 0, top2 = 0;
    int i = 0;
    while (i < 64) {
        int j = i + 1;
        while (j < 64 && a[j] == a[i]) j++;
        int c = j - i;
        if (c > top1) { top2 = top1; top1 = c; }
        else if (c > top2) { top2 = c; }
        i = j;
    }
    if (top1 >= 60) return 0; /* ignore constant polynomials! */
    return top1 * 25 + top2 * 18;
}

typedef struct {
    const BeamCand *parents;
    int n_parents;
    int depth; /* new length = depth + 1 */
    int tid;
    int nthreads;
    BeamCand *out;
    int out_cap;
    int out_cnt;
    int *global_best_per_tau;
} BeamWorkerArg;

static void *beam_worker(void *arg) {
    BeamWorkerArg *wa = (BeamWorkerArg *)arg;
    int depth = wa->depth;
    int new_len = depth + 1;
    int idx = depth + 2;

    uint32_t vals[MAX_TAU + 2][NPTS];
    uint32_t h1[MAX_TAU + 2], nh1[MAX_TAU + 2];
    uint64_t h2[MAX_TAU + 2], nh2[MAX_TAU + 2];
    uint32_t zmask_lo[MAX_TAU + 2], zmask_hi[MAX_TAU + 2]; /* bitmasks on middle 64 pts */
    uint32_t vc[NPTS];

    for (int pi = wa->tid; pi < wa->n_parents; pi += wa->nthreads) {
        const BeamCand *par = &wa->parents[pi];
        memcpy(vals[0], g_base0, sizeof(g_base0));
        memcpy(vals[1], g_base1, sizeof(g_base1));
        h1[0] = 1; h2[0] = 1; nh1[0] = MP - 1; nh2[0] = P2 - 1;
        h1[1] = HASH_X1; h2[1] = HASH_X2; nh1[1] = MP - HASH_X1; nh2[1] = P2 - HASH_X2;

        for (int d = 0; d < depth; d++) {
            int k = d + 2;
            int op = par->gates[d].op, gi = par->gates[d].i, gj = par->gates[d].j;
            uint32_t a1 = h1[gi], b1 = h1[gj];
            uint64_t a2 = h2[gi], b2 = h2[gj];
            uint32_t r1; uint64_t r2;
            if (op == 0) { r1 = madd(a1, b1); r2 = a2 + b2; if (r2 >= P2) r2 -= P2; }
            else if (op == 1) { r1 = msub(a1, b1); r2 = a2 >= b2 ? a2 - b2 : a2 + P2 - b2; }
            else { r1 = mmul(a1, b1); r2 = (a2 * b2) % P2; }
            h1[k] = r1; h2[k] = r2; nh1[k] = r1 ? MP - r1 : 0; nh2[k] = r2 ? P2 - r2 : 0;
            const uint32_t *va = vals[gi], *vb = vals[gj];
            uint32_t *vd = vals[k];
            if (op == 0) for (int p = 0; p < NPTS; p++) vd[p] = madd(va[p], vb[p]);
            else if (op == 1) for (int p = 0; p < NPTS; p++) vd[p] = msub(va[p], vb[p]);
            else for (int p = 0; p < NPTS; p++) vd[p] = mmul(va[p], vb[p]);
        }

        for (int k = 0; k < idx; k++) {
            uint32_t ml = 0, mh = 0;
            for (int p = 0; p < 32; p++) if (vals[k][32 + p] == 0) ml |= (1U << p);
            for (int p = 0; p < 32; p++) if (vals[k][64 + p] == 0) mh |= (1U << p);
            zmask_lo[k] = ml; zmask_hi[k] = mh;
        }

        for (int i = 0; i < idx; i++) {
            for (int j = i; j < idx; j++) {
                for (int op = 0; op < 3; op++) {
                    if (op == 1 && i == j) continue;
                    uint32_t a1 = h1[i], b1 = h1[j];
                    uint64_t a2 = h2[i], b2 = h2[j];
                    uint32_t r1; uint64_t r2;
                    if (op == 0) { r1 = madd(a1, b1); r2 = a2 + b2; if (r2 >= P2) r2 -= P2; }
                    else if (op == 1) { r1 = msub(a1, b1); r2 = a2 >= b2 ? a2 - b2 : a2 + P2 - b2; }
                    else { r1 = mmul(a1, b1); r2 = (a2 * b2) % P2; }
                    if (r1 == 0 && r2 == 0) continue;
                    int dup = 0;
                    for (int m = 0; m < idx; m++) {
                        if ((r1 == h1[m] && r2 == h2[m]) || (r1 == nh1[m] && r2 == nh2[m])) { dup = 1; break; }
                    }
                    if (dup) continue;

                    const uint32_t *va = vals[i], *vb = vals[j];
                    int z = 0;
                    if (op == 0) {
                        for (int p = 0; p < NPTS; p++) { uint32_t v = madd(va[p], vb[p]); vc[p] = v; z += (v == 0); }
                    } else if (op == 1) {
                        for (int p = 0; p < NPTS; p++) { uint32_t v = msub(va[p], vb[p]); vc[p] = v; z += (v == 0); }
                    } else {
                        for (int p = 0; p < NPTS; p++) { uint32_t v = mmul(va[p], vb[p]); vc[p] = v; z += (v == 0); }
                    }

                    /* Check if new record for new_len */
                    int cur_best = wa->global_best_per_tau[new_len];
                    if (z > cur_best || (new_len >= 10 && z >= cur_best && z >= 7)) {
                        Gate tmpg[MAX_TAU];
                        memcpy(tmpg, par->gates, depth * sizeof(Gate));
                        tmpg[depth] = (Gate){(uint8_t)op, (uint8_t)i, (uint8_t)j};
                        int vz = verify_p2_full(tmpg, new_len);
                        if (vz > wa->global_best_per_tau[new_len]) {
                            pthread_mutex_lock(&g_print_lock);
                            if (vz > wa->global_best_per_tau[new_len]) {
                                wa->global_best_per_tau[new_len] = vz;
                                char buf[512];
                                format_slp_buf(buf, tmpg, new_len, "x");
                                printf("BEAM_RECORD tau=%d roots=%d: %s\n", new_len, vz, buf);
                                fflush(stdout);
                            }
                            pthread_mutex_unlock(&g_print_lock);
                        }
                    }

                    /* Compute multi-objective score */
                    int max_r = z > par->max_roots ? z : par->max_roots;
                    uint32_t ml = 0, mh = 0;
                    for (int p = 0; p < 32; p++) if (vc[32 + p] == 0) ml |= (1U << p);
                    for (int p = 0; p < 32; p++) if (vc[64 + p] == 0) mh |= (1U << p);
                    int best_pair = par->pair_roots;
                    for (int k = 1; k < idx; k++) {
                        int u = __builtin_popcount(ml | zmask_lo[k]) + __builtin_popcount(mh | zmask_hi[k]);
                        if (u > best_pair) best_pair = u;
                    }
                    int coll = fast_collision_score(vc);
                    if (par->coll_score > coll) coll = par->coll_score;
                    int score = max_r * 100 + z * 25 + best_pair * 40 + coll;

                    /* Append to local buffer (keep top if full) */
                    if (wa->out_cnt < wa->out_cap) {
                        BeamCand *c = &wa->out[wa->out_cnt++];
                        c->len = new_len;
                        memcpy(c->gates, par->gates, depth * sizeof(Gate));
                        c->gates[depth] = (Gate){(uint8_t)op, (uint8_t)i, (uint8_t)j};
                        c->max_roots = max_r;
                        c->pair_roots = best_pair;
                        c->coll_score = coll;
                        c->total_score = score;
                        c->sig = ((uint64_t)r1 << 32) ^ (r2 * 0x9E3779B97F4A7C15ULL);
                    }
                }
            }
        }
    }
    return NULL;
}

static void run_beam(int max_tau, int beam_width, int nthreads) {
    init_bases();
    int best_per_tau[MAX_TAU + 1];
    memset(best_per_tau, 0, sizeof(best_per_tau));
    /* Set known baselines so we see records immediately */
    best_per_tau[10] = 7;
    best_per_tau[11] = 8;
    best_per_tau[12] = 9;
    best_per_tau[13] = 10;
    best_per_tau[14] = 10;

    BeamCand *beam = (BeamCand *)calloc((size_t)beam_width + 16, sizeof(BeamCand));
    int n_beam = 1;
    beam[0].len = 0;

    int per_thread_cap = 1500000;
    BeamCand **tbufs = (BeamCand **)malloc(nthreads * sizeof(BeamCand *));
    for (int t = 0; t < nthreads; t++) {
        tbufs[t] = (BeamCand *)malloc((size_t)per_thread_cap * sizeof(BeamCand));
    }

    for (int d = 0; d < max_tau; d++) {
        double t0 = now_sec();
        pthread_t th[32];
        BeamWorkerArg args[32];
        for (int t = 0; t < nthreads; t++) {
            args[t] = (BeamWorkerArg){
                beam, n_beam, d, t, nthreads, tbufs[t], per_thread_cap, 0, best_per_tau
            };
            pthread_create(&th[t], NULL, beam_worker, &args[t]);
        }
        int total_cands = 0;
        for (int t = 0; t < nthreads; t++) {
            pthread_join(th[t], NULL);
            total_cands += args[t].out_cnt;
        }
        BeamCand *all = (BeamCand *)malloc((size_t)(total_cands + 1) * sizeof(BeamCand));
        int pos = 0;
        for (int t = 0; t < nthreads; t++) {
            memcpy(all + pos, tbufs[t], (size_t)args[t].out_cnt * sizeof(BeamCand));
            pos += args[t].out_cnt;
        }
        qsort(all, (size_t)total_cands, sizeof(BeamCand), cmp_beam_desc);

        /* Deduplicate by sig and keep diverse buckets:
         * 50% top total_score, 25% top coll_score, 25% top pair_roots */
        int keep = 0;
        int hsz = 1;
        while (hsz < beam_width * 4) hsz <<= 1;
        uint64_t *ht = (uint64_t *)calloc((size_t)hsz, sizeof(uint64_t));

        int b1 = (beam_width * 85) / 100;
        int b2 = beam_width;

        for (int i = 0; i < total_cands && keep < b1; i++) {
            uint64_t s = all[i].sig | 1ULL;
            int slot = (int)(s & (uint64_t)(hsz - 1));
            int seen = 0;
            while (ht[slot]) { if (ht[slot] == s) { seen = 1; break; } slot = (slot + 1) & (hsz - 1); }
            if (seen) continue;
            ht[slot] = s;
            beam[keep++] = all[i];
        }
        qsort(all, (size_t)total_cands, sizeof(BeamCand), cmp_coll_desc);
        for (int i = 0; i < total_cands && keep < b2; i++) {
            uint64_t s = all[i].sig | 1ULL;
            int slot = (int)(s & (uint64_t)(hsz - 1));
            int seen = 0;
            while (ht[slot]) { if (ht[slot] == s) { seen = 1; break; } slot = (slot + 1) & (hsz - 1); }
            if (seen) continue;
            ht[slot] = s;
            beam[keep++] = all[i];
        }
        qsort(all, (size_t)total_cands, sizeof(BeamCand), cmp_pair_desc);
        for (int i = 0; i < total_cands && keep < beam_width; i++) {
            uint64_t s = all[i].sig | 1ULL;
            int slot = (int)(s & (uint64_t)(hsz - 1));
            int seen = 0;
            while (ht[slot]) { if (ht[slot] == s) { seen = 1; break; } slot = (slot + 1) & (hsz - 1); }
            if (seen) continue;
            ht[slot] = s;
            beam[keep++] = all[i];
        }
        free(ht);
        free(all);
        n_beam = keep;
        printf("[beam] tau=%2d: expanded=%d, kept=%d, best_roots=%d (%.2fs)\n",
               d + 1, total_cands, n_beam, best_per_tau[d + 1], now_sec() - t0);
        fflush(stdout);
    }

    for (int t = 0; t < nthreads; t++) free(tbufs[t]);
    free(tbufs);
    free(beam);
}

/* ============================================================================
 * MODE 3: SEEDED EXHAUSTIVE EXTENSION (up to tau = 14)
 * ============================================================================ */

typedef struct {
    const char *name;
    int seed_len;
    Gate seed[MAX_TAU];
    int target_tau;
    int min_report;
} ExtSeed;

static int parse_slp_str_c(const char *s, Gate *out) {
    int n = 0;
    const char *p = s;
    while (*p) {
        while (*p == ' ' || *p == ';') p++;
        if (!*p) break;
        /* skip "gK =" */
        while (*p && *p != '=') p++;
        if (*p == '=') p++;
        while (*p == ' ') p++;
        char a[16], op_s[4], b[16];
        if (sscanf(p, "%15s %3s %15[^;]", a, op_s, b) != 3) break;
        int ia = (a[0] == '1') ? 0 : (a[0] == 'x' ? 1 : atoi(a + 1) + 1);
        int ib = (b[0] == '1') ? 0 : (b[0] == 'x' ? 1 : atoi(b + 1) + 1);
        int op = (op_s[0] == '+') ? 0 : (op_s[0] == '-' ? 1 : 2);
        out[n++] = (Gate){(uint8_t)op, (uint8_t)ia, (uint8_t)ib};
        while (*p && *p != ';') p++;
    }
    return n;
}

typedef struct {
    int target_tau;
    int seed_len;
    int best_roots;
    const char *name;
    uint32_t vals[MAX_TAU + 2][NPTS];
    uint32_t h1[MAX_TAU + 2], nh1[MAX_TAU + 2];
    uint64_t h2[MAX_TAU + 2], nh2[MAX_TAU + 2];
    Gate path[MAX_TAU];
    uint64_t leaves;
} ExtCtx;

static void ext_dfs(ExtCtx *ctx, int depth) {
    int tau = ctx->target_tau;
    int idx = depth + 2;
    if (depth == tau - 1) {
        for (int i = 0; i < idx; i++) {
            const uint32_t *va = ctx->vals[i];
            for (int j = i; j < idx; j++) {
                const uint32_t *vb = ctx->vals[j];
                for (int op = 0; op < 3; op++) {
                    if (op == 1 && i == j) continue;
                    ctx->leaves++;
                    int z = 0;
                    if (op == 0) { for (int p = 0; p < NPTS; p++) { uint32_t s = va[p] + vb[p]; z += (s == 0 || s == MP); } }
                    else if (op == 1) { for (int p = 0; p < NPTS; p++) z += (va[p] == vb[p]); }
                    else { for (int p = 0; p < NPTS; p++) z += (va[p] == 0 || vb[p] == 0); }
                    if (z > ctx->best_roots) {
                        uint32_t a1 = ctx->h1[i], b1 = ctx->h1[j];
                        uint64_t a2 = ctx->h2[i], b2 = ctx->h2[j];
                        uint32_t r1; uint64_t r2;
                        if (op == 0) { r1 = madd(a1, b1); r2 = a2 + b2; if (r2 >= P2) r2 -= P2; }
                        else if (op == 1) { r1 = msub(a1, b1); r2 = a2 >= b2 ? a2 - b2 : a2 + P2 - b2; }
                        else { r1 = mmul(a1, b1); r2 = (a2 * b2) % P2; }
                        if (r1 == 0 && r2 == 0) continue;
                        ctx->path[depth] = (Gate){(uint8_t)op, (uint8_t)i, (uint8_t)j};
                        int vz = verify_p2_full(ctx->path, tau);
                        if (vz > ctx->best_roots) {
                            ctx->best_roots = vz;
                            char buf[512];
                            format_slp_buf(buf, ctx->path, tau, "x");
                            printf("EXT_RECORD [%s] tau=%d roots=%d: %s\n", ctx->name, tau, vz, buf);
                            fflush(stdout);
                        }
                    }
                }
            }
        }
        return;
    }

    uint32_t *vc = ctx->vals[idx];
    for (int i = 0; i < idx; i++) {
        for (int j = i; j < idx; j++) {
            for (int op = 0; op < 3; op++) {
                if (op == 1 && i == j) continue;
                uint32_t a1 = ctx->h1[i], b1 = ctx->h1[j];
                uint64_t a2 = ctx->h2[i], b2 = ctx->h2[j];
                uint32_t r1; uint64_t r2;
                if (op == 0) { r1 = madd(a1, b1); r2 = a2 + b2; if (r2 >= P2) r2 -= P2; }
                else if (op == 1) { r1 = msub(a1, b1); r2 = a2 >= b2 ? a2 - b2 : a2 + P2 - b2; }
                else { r1 = mmul(a1, b1); r2 = (a2 * b2) % P2; }
                if (r1 == 0 && r2 == 0) continue;
                int dup = 0;
                for (int m = 0; m < idx; m++) {
                    if ((r1 == ctx->h1[m] && r2 == ctx->h2[m]) ||
                        (r1 == ctx->nh1[m] && r2 == ctx->nh2[m])) { dup = 1; break; }
                }
                if (dup) continue;
                ctx->h1[idx] = r1; ctx->h2[idx] = r2;
                ctx->nh1[idx] = r1 ? MP - r1 : 0; ctx->nh2[idx] = r2 ? P2 - r2 : 0;
                ctx->path[depth] = (Gate){(uint8_t)op, (uint8_t)i, (uint8_t)j};
                const uint32_t *va = ctx->vals[i], *vb = ctx->vals[j];
                if (op == 0) for (int p = 0; p < NPTS; p++) vc[p] = madd(va[p], vb[p]);
                else if (op == 1) for (int p = 0; p < NPTS; p++) vc[p] = msub(va[p], vb[p]);
                else for (int p = 0; p < NPTS; p++) vc[p] = mmul(va[p], vb[p]);
                ext_dfs(ctx, depth + 1);
            }
        }
    }
}

static void run_extend_suite(void) {
    init_bases();
    struct { const char *name; const char *slp; int target_tau; int min_rep; } seeds[] = {
        /* Can tau=10 reach 8 from our best 6,7,8-gate seeds? */
        {"tau6_5r->10", "g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4; g6 = x * g5", 10, 7},
        {"tau8_6r->10", "g1 = 1 + 1; g2 = 1 + x; g3 = g1 + g1; g4 = x * g2; g5 = g1 - g4; g6 = g3 + g5; g7 = g4 * g5; g8 = g6 * g7", 10, 7},
        {"tau8_6r->11", "g1 = 1 + 1; g2 = 1 + x; g3 = g1 + g1; g4 = x * g2; g5 = g1 - g4; g6 = g3 + g5; g7 = g4 * g5; g8 = g6 * g7", 11, 8},
        /* Can tau=12 reach 10 or tau=13 reach 11 or tau=14 reach 11/12 from our best 9,10,11,12-gate seeds? */
        {"tau10_7r_sym->13", "g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4; g6 = x * g5; g7 = 1 + g1; g8 = g7 * g7; g9 = g2 - g8; g10 = g6 * g9", 13, 9},
        {"tau11_8r_mid->14", "g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4; g6 = g1 * g1; g7 = g6 * g6; g8 = g2 - g7; g9 = g5 * g8; g10 = g3 - g8; g11 = g9 * g10", 14, 10},
        {"tau11_8r_q->14", "g1 = 1 + 1; g2 = 1 + x; g3 = g1 + g1; g4 = x * g2; g5 = g1 - g4; g6 = g3 + g5; g7 = g4 * g5; g8 = g6 * g7; g9 = g1 + g3; g10 = g6 + g9; g11 = g8 * g10", 14, 10},
        {"tau12_8r_psq->14", "g1 = 1 + x; g2 = x * g1; g3 = 1 + 1; g4 = g3 + g3; g5 = g4 * g4; g6 = g2 - g5; g7 = g6 * g6; g8 = g5 - g3; g9 = g8 * g8; g10 = g7 - g9; g11 = g7 - g5; g12 = g10 * g11", 14, 10},
        {"tau10_psq_pre->13", "g1 = 1 + x; g2 = x * g1; g3 = 1 + 1; g4 = g3 + g3; g5 = g4 * g4; g6 = g2 - g5; g7 = g6 * g6; g8 = g5 - g3; g9 = g8 * g8; g10 = g7 - g9", 13, 9},
        {"tau10_psq_pre->14", "g1 = 1 + x; g2 = x * g1; g3 = 1 + 1; g4 = g3 + g3; g5 = g4 * g4; g6 = g2 - g5; g7 = g6 * g6; g8 = g5 - g3; g9 = g8 * g8; g10 = g7 - g9", 14, 10},
        {"tau9_mid_pre->12", "g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4; g6 = g1 * g1; g7 = g6 * g6; g8 = g2 - g7; g9 = g5 * g8", 12, 8},
        {"tau9_mid_pre->13", "g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4; g6 = g1 * g1; g7 = g6 * g6; g8 = g2 - g7; g9 = g5 * g8", 13, 9},
    };
    int ns = (int)(sizeof(seeds) / sizeof(seeds[0]));
    for (int s = 0; s < ns; s++) {
        ExtCtx ctx;
        memset(&ctx, 0, sizeof(ctx));
        ctx.name = seeds[s].name;
        ctx.target_tau = seeds[s].target_tau;
        ctx.best_roots = seeds[s].min_rep;
        ctx.seed_len = parse_slp_str_c(seeds[s].slp, ctx.path);
        memcpy(ctx.vals[0], g_base0, sizeof(g_base0));
        memcpy(ctx.vals[1], g_base1, sizeof(g_base1));
        ctx.h1[0] = 1; ctx.h2[0] = 1; ctx.nh1[0] = MP - 1; ctx.nh2[0] = P2 - 1;
        ctx.h1[1] = HASH_X1; ctx.h2[1] = HASH_X2; ctx.nh1[1] = MP - HASH_X1; ctx.nh2[1] = P2 - HASH_X2;
        for (int d = 0; d < ctx.seed_len; d++) {
            int idx = d + 2;
            int op = ctx.path[d].op, i = ctx.path[d].i, j = ctx.path[d].j;
            uint32_t a1 = ctx.h1[i], b1 = ctx.h1[j];
            uint64_t a2 = ctx.h2[i], b2 = ctx.h2[j];
            uint32_t r1; uint64_t r2;
            if (op == 0) { r1 = madd(a1, b1); r2 = a2 + b2; if (r2 >= P2) r2 -= P2; }
            else if (op == 1) { r1 = msub(a1, b1); r2 = a2 >= b2 ? a2 - b2 : a2 + P2 - b2; }
            else { r1 = mmul(a1, b1); r2 = (a2 * b2) % P2; }
            ctx.h1[idx] = r1; ctx.h2[idx] = r2; ctx.nh1[idx] = r1 ? MP - r1 : 0; ctx.nh2[idx] = r2 ? P2 - r2 : 0;
            const uint32_t *va = ctx.vals[i], *vb = ctx.vals[j];
            uint32_t *vc = ctx.vals[idx];
            if (op == 0) for (int p = 0; p < NPTS; p++) vc[p] = madd(va[p], vb[p]);
            else if (op == 1) for (int p = 0; p < NPTS; p++) vc[p] = msub(va[p], vb[p]);
            else for (int p = 0; p < NPTS; p++) vc[p] = mmul(va[p], vb[p]);
        }
        double t0 = now_sec();
        ext_dfs(&ctx, ctx.seed_len);
        printf("[extend] %-18s (seed=%2d -> tau=%2d): best=%2d, leaves=%llu (%.2fs)\n",
               ctx.name, ctx.seed_len, ctx.target_tau, ctx.best_roots,
               (unsigned long long)ctx.leaves, now_sec() - t0);
        fflush(stdout);
    }
}

/* ============================================================================
 * MODE 4: LOCAL MUTATION + 2-GATE NEIGHBORHOOD SEARCH AROUND ELITE WITNESSES
 * ============================================================================ */

static int eval_slp_fast_mp(const Gate *gates, int tau, int *out_best_gate) {
    uint32_t vals[MAX_TAU + 2][NPTS];
    uint32_t h1[MAX_TAU + 2];
    uint64_t h2[MAX_TAU + 2];
    memcpy(vals[0], g_base0, sizeof(g_base0));
    memcpy(vals[1], g_base1, sizeof(g_base1));
    h1[0] = 1; h2[0] = 1;
    h1[1] = HASH_X1; h2[1] = HASH_X2;
    int best_z = 0, best_k = tau;
    for (int d = 0; d < tau; d++) {
        int idx = d + 2;
        int op = gates[d].op, i = gates[d].i, j = gates[d].j;
        uint32_t a1 = h1[i], b1 = h1[j];
        uint64_t a2 = h2[i], b2 = h2[j];
        uint32_t r1; uint64_t r2;
        if (op == 0) { r1 = madd(a1, b1); r2 = a2 + b2; if (r2 >= P2) r2 -= P2; }
        else if (op == 1) { r1 = msub(a1, b1); r2 = a2 >= b2 ? a2 - b2 : a2 + P2 - b2; }
        else { r1 = mmul(a1, b1); r2 = (a2 * b2) % P2; }
        h1[idx] = r1; h2[idx] = r2;
        const uint32_t *va = vals[i], *vb = vals[j];
        uint32_t *vc = vals[idx];
        int z = 0;
        if (op == 0) for (int p = 0; p < NPTS; p++) { uint32_t v = madd(va[p], vb[p]); vc[p] = v; z += (v == 0); }
        else if (op == 1) for (int p = 0; p < NPTS; p++) { uint32_t v = msub(va[p], vb[p]); vc[p] = v; z += (v == 0); }
        else for (int p = 0; p < NPTS; p++) { uint32_t v = mmul(va[p], vb[p]); vc[p] = v; z += (v == 0); }
        if ((r1 != 0 || r2 != 0) && z > best_z) { best_z = z; best_k = d + 1; }
    }
    if (out_best_gate) *out_best_gate = best_k;
    return best_z;
}

static void run_mutate_suite(void) {
    init_bases();
    struct { const char *name; const char *slp; int min_rep; } elites[] = {
        {"tau10_7r_sym", "g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4; g6 = x * g5; g7 = 1 + g1; g8 = g7 * g7; g9 = g2 - g8; g10 = g6 * g9", 7},
        {"tau11_8r_q",   "g1 = 1 + 1; g2 = 1 + x; g3 = g1 + g1; g4 = x * g2; g5 = g1 - g4; g6 = g3 + g5; g7 = g4 * g5; g8 = g6 * g7; g9 = g1 + g3; g10 = g6 + g9; g11 = g8 * g10", 8},
        {"tau11_8r_mid", "g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4; g6 = g1 * g1; g7 = g6 * g6; g8 = g2 - g7; g9 = g5 * g8; g10 = g3 - g8; g11 = g9 * g10", 8},
        {"tau12_9r_mid", "g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4; g6 = g1 * g1; g7 = g6 * g6; g8 = g2 - g7; g9 = g5 * g8; g10 = g3 - g8; g11 = g9 * g10; g12 = x * g11", 9},
        {"tau13_10r_psq","g1 = 1 + x; g2 = x * g1; g3 = 1 + 1; g4 = g3 + g3; g5 = g4 * g4; g6 = g2 - g5; g7 = g6 * g6; g8 = g5 - g3; g9 = g8 * g8; g10 = g7 - g9; g11 = g7 - g5; g12 = g10 * g11; g13 = g12 * g2", 10},
        {"tau14_10r_q5", "g1 = 1 + 1; g2 = 1 + x; g3 = g1 + g1; g4 = x * g2; g5 = g1 - g4; g6 = g3 + g5; g7 = g4 * g5; g8 = g6 * g7; g9 = g1 + g3; g10 = g6 + g9; g11 = g8 * g10; g12 = g3 + g3; g13 = g10 + g12; g14 = g11 * g13", 10},
        {"tau14_10r_psq_pad","g1 = 1 + x; g2 = x * g1; g3 = 1 + 1; g4 = g3 + g3; g5 = g4 * g4; g6 = g2 - g5; g7 = g6 * g6; g8 = g5 - g3; g9 = g8 * g8; g10 = g7 - g9; g11 = g7 - g5; g12 = g10 * g11; g13 = g12 * g2; g14 = g13 * x", 10},
    };
    int ne = (int)(sizeof(elites) / sizeof(elites[0]));
    for (int e = 0; e < ne; e++) {
        Gate base[MAX_TAU];
        int tau = parse_slp_str_c(elites[e].slp, base);
        int best = elites[e].min_rep;
        double t0 = now_sec();
        uint64_t tested = 0;

        /* 1-gate mutations */
        for (int pos = 0; pos < tau; pos++) {
            int idx = pos + 2;
            Gate g[MAX_TAU];
            memcpy(g, base, sizeof(base));
            for (int i = 0; i < idx; i++) {
                for (int j = i; j < idx; j++) {
                    for (int op = 0; op < 3; op++) {
                        if (op == 1 && i == j) continue;
                        g[pos] = (Gate){(uint8_t)op, (uint8_t)i, (uint8_t)j};
                        tested++;
                        int bk = tau;
                        int z = eval_slp_fast_mp(g, tau, &bk);
                        if (z > best) {
                            int vz = verify_p2_full(g, bk);
                            if (vz > best) {
                                best = vz;
                                char buf[512];
                                format_slp_buf(buf, g, bk, "x");
                                printf("MUT1_RECORD [%s] tau=%d roots=%d: %s\n", elites[e].name, bk, vz, buf);
                                fflush(stdout);
                            }
                        }
                    }
                }
            }
        }
        /* 2-gate mutations on the last 6 gates */
        int start = tau > 6 ? tau - 6 : 0;
        for (int p1 = start; p1 < tau; p1++) {
            int idx1 = p1 + 2;
            for (int p2 = p1 + 1; p2 < tau; p2++) {
                int idx2 = p2 + 2;
                Gate g[MAX_TAU];
                memcpy(g, base, sizeof(base));
                for (int i1 = 0; i1 < idx1; i1++) {
                    for (int j1 = i1; j1 < idx1; j1++) {
                        for (int op1 = 0; op1 < 3; op1++) {
                            if (op1 == 1 && i1 == j1) continue;
                            g[p1] = (Gate){(uint8_t)op1, (uint8_t)i1, (uint8_t)j1};
                            for (int i2 = 0; i2 < idx2; i2++) {
                                for (int j2 = i2; j2 < idx2; j2++) {
                                    for (int op2 = 0; op2 < 3; op2++) {
                                        if (op2 == 1 && i2 == j2) continue;
                                        g[p2] = (Gate){(uint8_t)op2, (uint8_t)i2, (uint8_t)j2};
                                        tested++;
                                        int bk = tau;
                                        int z = eval_slp_fast_mp(g, tau, &bk);
                                        if (z > best) {
                                            int vz = verify_p2_full(g, bk);
                                            if (vz > best) {
                                                best = vz;
                                                char buf[512];
                                                format_slp_buf(buf, g, bk, "x");
                                                printf("MUT2_RECORD [%s] tau=%d roots=%d: %s\n", elites[e].name, bk, vz, buf);
                                                fflush(stdout);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        printf("[mutate] %-18s (tau=%2d): best=%2d, tested=%llu (%.2fs)\n",
               elites[e].name, tau, best, (unsigned long long)tested, now_sec() - t0);
        fflush(stdout);
    }
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "Usage:\n"
                        "  %s compose <max_tau_p> <nthreads>\n"
                        "  %s beam <max_tau> <beam_width> <nthreads>\n"
                        "  %s extend\n"
                        "  %s mutate\n", argv[0], argv[0], argv[0], argv[0]);
        return 1;
    }
    if (strcmp(argv[1], "compose") == 0) {
        int max_tp = argc >= 3 ? atoi(argv[2]) : 8;
        int nthreads = argc >= 4 ? atoi(argv[3]) : 12;
        run_compose_suite(max_tp, nthreads);
    } else if (strcmp(argv[1], "beam") == 0) {
        int max_tau = argc >= 3 ? atoi(argv[2]) : 14;
        int bw = argc >= 4 ? atoi(argv[3]) : 4000;
        int nthreads = argc >= 5 ? atoi(argv[4]) : 12;
        run_beam(max_tau, bw, nthreads);
    } else if (strcmp(argv[1], "extend") == 0) {
        run_extend_suite();
    } else if (strcmp(argv[1], "mutate") == 0) {
        run_mutate_suite();
    } else {
        fprintf(stderr, "Unknown mode: %s\n", argv[1]);
        return 1;
    }
    return 0;
}
