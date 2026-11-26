/*
 * Weighted-Target Exhaustive Composition Search for the Shub-Smale tau-Conjecture!
 *
 * Given a base polynomial Q(x) computable in tau_Q gates, with distinct values
 * v_0, ..., v_{M-1} taken on Z (for x in [-64, 64]) with multiplicities w_0, ..., w_{M-1},
 * this exhaustively searches all constant-free SLPs P(y) of length tau_P <= 8
 * maximizing sum_{P(v_p) == 0} w_p.
 *
 * Every solution yields P(Q(x)) of total gate length tau_Q + tau_P with at least
 * that many distinct integer roots!
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <pthread.h>

#define MAX_TAU 10
#define MAX_PTS 128
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

typedef struct { int op, i, j; } Gate;

typedef struct {
    const char *name;
    int tau_Q;
    int npts;
    int64_t raw_v[MAX_PTS];
    uint32_t v_mp[MAX_PTS];
    uint64_t v_p2[MAX_PTS];
    int w[MAX_PTS];
} TargetSet;

static TargetSet g_target;

static void add_target_val(TargetSet *ts, int64_t v) {
    for (int k = 0; k < ts->npts; k++) {
        if (ts->raw_v[k] == v) { ts->w[k]++; return; }
    }
    if (ts->npts >= MAX_PTS) return;
    int idx = ts->npts++;
    ts->raw_v[idx] = v;
    int64_t m1 = v % (int64_t)MP; if (m1 < 0) m1 += MP;
    int64_t m2 = v % (int64_t)P2; if (m2 < 0) m2 += P2;
    ts->v_mp[idx] = (uint32_t)m1;
    ts->v_p2[idx] = (uint64_t)m2;
    ts->w[idx] = 1;
}

static void build_target(int which) {
    memset(&g_target, 0, sizeof(g_target));
    if (which == 1) {
        g_target.name = "Q1=x^2";
        g_target.tau_Q = 1;
        for (int x = -32; x <= 32; x++) add_target_val(&g_target, (int64_t)x * x);
    } else if (which == 2) {
        g_target.name = "Q2=x^2-x";
        g_target.tau_Q = 2;
        for (int x = -32; x <= 33; x++) add_target_val(&g_target, (int64_t)x * x - x);
    } else if (which == 3) {
        g_target.name = "Q3=x^3-x";
        g_target.tau_Q = 3;
        for (int x = -20; x <= 20; x++) add_target_val(&g_target, (int64_t)x * x * x - x);
    } else if (which == 4) {
        g_target.name = "Q4=(x^2-1)(x^2-4)";
        g_target.tau_Q = 5;
        for (int x = -16; x <= 16; x++) {
            int64_t x2 = (int64_t)x * x;
            add_target_val(&g_target, (x2 - 1) * (x2 - 4));
        }
    } else if (which == 5) {
        g_target.name = "Q5=q(q-2)";
        g_target.tau_Q = 5;
        for (int x = -16; x <= 17; x++) {
            int64_t q = (int64_t)x * x - x;
            add_target_val(&g_target, q * (q - 2));
        }
    } else if (which == 6) {
        g_target.name = "Q6=x(x^2-1)(x^2-4)";
        g_target.tau_Q = 6;
        for (int x = -12; x <= 12; x++) {
            int64_t x2 = (int64_t)x * x;
            add_target_val(&g_target, (int64_t)x * (x2 - 1) * (x2 - 4));
        }
    }
}

typedef struct {
    Gate prefix[3];
    int key[3];
    uint32_t unused_mask;
    int unused_cnt;
    int prefix_len;
} WorkItem;

typedef struct {
    int target_tau;
    int best_roots;
    Gate best_gates[MAX_TAU];
    uint32_t vals[MAX_TAU + 2][MAX_PTS];
    uint32_t h1[MAX_TAU + 2];
    uint64_t h2[MAX_TAU + 2];
    uint32_t nh1[MAX_TAU + 2];
    uint64_t nh2[MAX_TAU + 2];
    Gate path[MAX_TAU];
    int key[MAX_TAU];
} SearchCtx;

static pthread_mutex_t g_print_lock = PTHREAD_MUTEX_INITIALIZER;
static int g_global_best = 0;

static void init_base(SearchCtx *ctx) {
    for (int p = 0; p < g_target.npts; p++) {
        ctx->vals[0][p] = 1;
        ctx->vals[1][p] = g_target.v_mp[p];
    }
    ctx->h1[0] = 1; ctx->h2[0] = 1; ctx->nh1[0] = MP - 1; ctx->nh2[0] = P2 - 1;
    ctx->h1[1] = HASH_X1; ctx->h2[1] = HASH_X2; ctx->nh1[1] = MP - HASH_X1; ctx->nh2[1] = P2 - HASH_X2;
}

static int verify_weighted_p2(const Gate *gates, int tau) {
    uint64_t v[MAX_TAU + 2][MAX_PTS];
    int n = g_target.npts;
    for (int p = 0; p < n; p++) { v[0][p] = 1; v[1][p] = g_target.v_p2[p]; }
    for (int d = 0; d < tau; d++) {
        int idx = d + 2;
        int op = gates[d].op, i = gates[d].i, j = gates[d].j;
        if (op == 0) for (int p = 0; p < n; p++) { uint64_t s = v[i][p] + v[j][p]; v[idx][p] = s >= P2 ? s - P2 : s; }
        else if (op == 1) for (int p = 0; p < n; p++) v[idx][p] = v[i][p] >= v[j][p] ? v[i][p] - v[j][p] : v[i][p] + P2 - v[j][p];
        else for (int p = 0; p < n; p++) v[idx][p] = (v[i][p] * v[j][p]) % P2;
    }
    int z = 0;
    for (int p = 0; p < n; p++) if (v[tau + 1][p] == 0) z += g_target.w[p];
    return z;
}

static void print_slp_locked(const Gate *gates, int tau_P, int roots) {
    pthread_mutex_lock(&g_print_lock);
    if (roots > g_global_best) {
        g_global_best = roots;
        printf("COMP %s total_tau=%d (tau_Q=%d + tau_P=%d) roots=%d: ",
               g_target.name, g_target.tau_Q + tau_P, g_target.tau_Q, tau_P, roots);
        const char *ops = "+-*";
        for (int k = 0; k < tau_P; k++) {
            if (k > 0) printf("; ");
            int i = gates[k].i - 1, j = gates[k].j - 1;
            char si[16], sj[16];
            if (i == -1) strcpy(si, "1"); else if (i == 0) strcpy(si, "y"); else sprintf(si, "p%d", i);
            if (j == -1) strcpy(sj, "1"); else if (j == 0) strcpy(sj, "y"); else sprintf(sj, "p%d", j);
            printf("p%d = %s %c %s", k + 1, si, ops[gates[k].op], sj);
        }
        printf("\n");
        fflush(stdout);
    }
    pthread_mutex_unlock(&g_print_lock);
}

static inline int check_dup(SearchCtx *ctx, int idx, int op, int i, int j, uint32_t *out1, uint64_t *out2) {
    uint32_t a1 = ctx->h1[i], b1 = ctx->h1[j];
    uint64_t a2 = ctx->h2[i], b2 = ctx->h2[j];
    uint32_t r1; uint64_t r2;
    if (op == 0) { r1 = madd(a1, b1); r2 = a2 + b2; if (r2 >= P2) r2 -= P2; }
    else if (op == 1) { r1 = msub(a1, b1); r2 = a2 >= b2 ? a2 - b2 : a2 + P2 - b2; }
    else { r1 = mmul(a1, b1); r2 = (a2 * b2) % P2; }
    if (r1 == 0 && r2 == 0) return 0;
    for (int m = 0; m < idx; m++) {
        if ((r1 == ctx->h1[m] && r2 == ctx->h2[m]) || (r1 == ctx->nh1[m] && r2 == ctx->nh2[m])) return 0;
    }
    *out1 = r1; *out2 = r2;
    return 1;
}

static inline void eval_gate(SearchCtx *ctx, int idx, int op, int i, int j) {
    const uint32_t * __restrict va = ctx->vals[i], * __restrict vb = ctx->vals[j];
    uint32_t * __restrict vc = ctx->vals[idx];
    int n = g_target.npts;
    if (op == 0) for (int p = 0; p < n; p++) vc[p] = madd(va[p], vb[p]);
    else if (op == 1) for (int p = 0; p < n; p++) vc[p] = msub(va[p], vb[p]);
    else for (int p = 0; p < n; p++) vc[p] = mmul(va[p], vb[p]);
}

static inline int count_weighted(const uint32_t * __restrict va, const uint32_t * __restrict vb, int op) {
    int n = g_target.npts, z = 0;
    const int * __restrict w = g_target.w;
    if (op == 0) {
        for (int p = 0; p < n; p++) { uint32_t s = va[p] + vb[p]; if (s == 0 || s == MP) z += w[p]; }
    } else if (op == 1) {
        for (int p = 0; p < n; p++) { if (va[p] == vb[p]) z += w[p]; }
    } else {
        for (int p = 0; p < n; p++) { if (va[p] == 0 || vb[p] == 0) z += w[p]; }
    }
    return z;
}

static inline void check_leaf(SearchCtx *ctx, int depth, int idx, int op, int i, int j) {
    int z = count_weighted(ctx->vals[i], ctx->vals[j], op);
    if (z > ctx->best_roots) {
        uint32_t r1; uint64_t r2;
        if (!check_dup(ctx, idx, op, i, j, &r1, &r2)) return;
        ctx->path[depth] = (Gate){op, i, j};
        int z2 = verify_weighted_p2(ctx->path, ctx->target_tau);
        if (z2 < z) z = z2;
        if (z > ctx->best_roots) {
            ctx->best_roots = z;
            memcpy(ctx->best_gates, ctx->path, sizeof(Gate) * ctx->target_tau);
            if (z > g_global_best) print_slp_locked(ctx->path, ctx->target_tau, z);
        }
    }
}

static void dfs(SearchCtx *ctx, int depth, uint32_t unused_mask, int unused_cnt) {
    int tau = ctx->target_tau, idx = depth + 2;
    int max_unused_after = (tau - 1 - depth) + 1;
    int prev_idx = idx - 1;

    if (depth == tau - 1) {
        if (unused_cnt == 2) {
            int i = __builtin_ctz(unused_mask), j = __builtin_ctz(unused_mask ^ (1U << i));
            check_leaf(ctx, depth, idx, 0, i, j);
            check_leaf(ctx, depth, idx, 1, i, j);
            check_leaf(ctx, depth, idx, 2, i, j);
            return;
        }
        if (unused_cnt == 0) {
            for (int i = 0; i < idx; i++)
                for (int j = i; j < idx; j++) {
                    check_leaf(ctx, depth, idx, 0, i, j);
                    if (i != j) check_leaf(ctx, depth, idx, 1, i, j);
                    check_leaf(ctx, depth, idx, 2, i, j);
                }
            return;
        }
        int u0 = __builtin_ctz(unused_mask);
        for (int other = 0; other < idx; other++) {
            int i = other < u0 ? other : u0, j = other < u0 ? u0 : other;
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
                uint32_t r1; uint64_t r2;
                if (!check_dup(ctx, idx, op, i, j, &r1, &r2)) continue;
                ctx->h1[idx] = r1; ctx->h2[idx] = r2;
                ctx->nh1[idx] = r1 == 0 ? 0 : MP - r1;
                ctx->nh2[idx] = r2 == 0 ? 0 : P2 - r2;
                ctx->path[depth] = (Gate){op, i, j};
                ctx->key[depth] = k;
                eval_gate(ctx, idx, op, i, j);
                uint32_t next_mask = (unused_mask & ~(1U << i) & ~(1U << j)) | (1U << idx);
                dfs(ctx, depth + 1, next_mask, unused_cnt - removed + 1);
            }
        }
    }
}

static WorkItem *g_work = NULL;
static int g_work_cnt = 0, g_work_cap = 0, g_work_next = 0;
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
    int tau = ctx->target_tau, idx = depth + 2;
    int min_removed = unused_cnt + 1 - ((tau - 1 - depth) + 1);
    int prev_idx = idx - 1;
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
                uint32_t r1; uint64_t r2;
                if (!check_dup(ctx, idx, op, i, j, &r1, &r2)) continue;
                ctx->h1[idx] = r1; ctx->h2[idx] = r2;
                ctx->nh1[idx] = r1 == 0 ? 0 : MP - r1;
                ctx->nh2[idx] = r2 == 0 ? 0 : P2 - r2;
                ctx->path[depth] = (Gate){op, i, j};
                ctx->key[depth] = k;
                eval_gate(ctx, idx, op, i, j);
                uint32_t next_mask = (unused_mask & ~(1U << i) & ~(1U << j)) | (1U << idx);
                collect_work(ctx, depth + 1, split_depth, next_mask, unused_cnt - removed + 1);
            }
        }
    }
}

static int g_cur_tau_P = 0;
static void *worker_fn(void *arg) {
    (void)arg;
    SearchCtx ctx;
    memset(&ctx, 0, sizeof(ctx));
    ctx.target_tau = g_cur_tau_P;
    init_base(&ctx);
    while (1) {
        pthread_mutex_lock(&g_work_lock);
        int wi = g_work_next++;
        pthread_mutex_unlock(&g_work_lock);
        if (wi >= g_work_cnt) break;
        WorkItem *w = &g_work[wi];
        for (int d = 0; d < w->prefix_len; d++) {
            int idx = d + 2; Gate g = w->prefix[d];
            uint32_t r1; uint64_t r2;
            check_dup(&ctx, idx, g.op, g.i, g.j, &r1, &r2);
            ctx.h1[idx] = r1; ctx.h2[idx] = r2;
            ctx.nh1[idx] = r1 == 0 ? 0 : MP - r1;
            ctx.nh2[idx] = r2 == 0 ? 0 : P2 - r2;
            ctx.path[d] = g; ctx.key[d] = w->key[d];
            eval_gate(&ctx, idx, g.op, g.i, g.j);
        }
        dfs(&ctx, w->prefix_len, w->unused_mask, w->unused_cnt);
    }
    return NULL;
}

int main(int argc, char **argv) {
    int which = 2, max_tau_P = 8, nthreads = 12;
    if (argc >= 2) which = atoi(argv[1]);
    if (argc >= 3) max_tau_P = atoi(argv[2]);
    if (argc >= 4) nthreads = atoi(argv[3]);

    build_target(which);
    printf("=== Target %s (tau_Q=%d, distinct values=%d) ===\n",
           g_target.name, g_target.tau_Q, g_target.npts);
    fflush(stdout);

    for (int tau_P = 1; tau_P <= max_tau_P; tau_P++) {
        g_global_best = 0;
        g_cur_tau_P = tau_P;
        if (tau_P <= 4) {
            SearchCtx ctx;
            memset(&ctx, 0, sizeof(ctx));
            ctx.target_tau = tau_P;
            init_base(&ctx);
            dfs(&ctx, 0, 0U, 0);
            printf("DONE %s total_tau=%d best_roots=%d\n", g_target.name, g_target.tau_Q + tau_P, g_global_best);
            fflush(stdout);
            continue;
        }
        int split_depth = (tau_P >= 8) ? 3 : 2;
        g_work_cnt = 0; g_work_next = 0;
        SearchCtx rctx;
        memset(&rctx, 0, sizeof(rctx));
        rctx.target_tau = tau_P;
        init_base(&rctx);
        collect_work(&rctx, 0, split_depth, 0U, 0);

        pthread_t th[32];
        if (nthreads > 32) nthreads = 32;
        for (int t = 0; t < nthreads; t++) pthread_create(&th[t], NULL, worker_fn, NULL);
        for (int t = 0; t < nthreads; t++) pthread_join(th[t], NULL);
        printf("DONE %s total_tau=%d best_roots=%d\n", g_target.name, g_target.tau_Q + tau_P, g_global_best);
        fflush(stdout);
    }
    return 0;
}
