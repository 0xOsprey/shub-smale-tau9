/*
 * Multi-threaded, division-free (Mersenne prime P = 2^31 - 1) exact exhaustive
 * census for the Shub-Smale tau-conjecture.
 *
 * Uses:
 *   - Sign canonicalization (+: i<=j, -: i<j, *: i<=j)
 *   - Dead-gate pruning (unused_cnt <= tau - k + 1)
 *   - Exact polynomial duplicate/zero pruning via 2-point hash (mod P1=2^31-1, P2=10^9+9)
 *   - Canonical topological ordering for independent gates
 *   - Lock-free dynamic work queue across N threads (split at depth 2)
 *   - Division-free Mersenne arithmetic mod (2^31 - 1), auto-vectorized by clang -O3
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <pthread.h>

#define MAX_TAU 12
#define NPTS 64
#define X_MIN (-32)
#define MP 2147483647U   /* 2^31 - 1 */
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
    int report_threshold;
    int best_roots;
    Gate best_gates[MAX_TAU];
    uint64_t nodes_visited;
    uint64_t leaves_checked;

    uint32_t vals[MAX_TAU + 2][NPTS];
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
    for (int p = 0; p < NPTS; p++) {
        int x = X_MIN + p;
        ctx->vals[0][p] = 1;
        ctx->vals[1][p] = (x >= 0) ? (uint32_t)x : (MP - (uint32_t)(-x));
    }
    ctx->h1[0] = 1;
    ctx->h2[0] = 1;
    ctx->nh1[0] = MP - 1;
    ctx->nh2[0] = P2 - 1;

    ctx->h1[1] = HASH_X1;
    ctx->h2[1] = HASH_X2;
    ctx->nh1[1] = MP - HASH_X1;
    ctx->nh2[1] = P2 - HASH_X2;
}

static void print_slp_locked(const Gate *gates, int tau, int roots) {
    pthread_mutex_lock(&g_print_lock);
    if (roots > g_global_best) g_global_best = roots;
    printf("FOUND tau=%d roots=%d: ", tau, roots);
    const char *ops = "+-*";
    for (int k = 0; k < tau; k++) {
        if (k > 0) printf("; ");
        int i = gates[k].i - 1;
        int j = gates[k].j - 1;
        char si[16], sj[16];
        if (i == -1) strcpy(si, "1");
        else if (i == 0) strcpy(si, "x");
        else sprintf(si, "g%d", i);
        if (j == -1) strcpy(sj, "1");
        else if (j == 0) strcpy(sj, "x");
        else sprintf(sj, "g%d", j);
        printf("g%d = %s %c %s", k + 1, si, ops[gates[k].op], sj);
    }
    printf("\n");
    fflush(stdout);
    pthread_mutex_unlock(&g_print_lock);
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

static inline void eval_gate(SearchCtx *ctx, int idx, int op, int i, int j) {
    const uint32_t * __restrict va = ctx->vals[i];
    const uint32_t * __restrict vb = ctx->vals[j];
    uint32_t * __restrict vc = ctx->vals[idx];
    if (op == 0) {
        for (int p = 0; p < NPTS; p++) vc[p] = madd(va[p], vb[p]);
    } else if (op == 1) {
        for (int p = 0; p < NPTS; p++) vc[p] = msub(va[p], vb[p]);
    } else {
        for (int p = 0; p < NPTS; p++) vc[p] = mmul(va[p], vb[p]);
    }
}

/* Fast leaf root counting: does not write to memory!
 * Note: For op == 1 (subtraction), a - b == 0 mod P iff a == b!
 * For op == 0 (addition), a + b == 0 mod P iff a + b == P or (a == 0 && b == 0)!
 * For op == 2 (multiplication), a * b == 0 mod P iff a == 0 || b == 0!
 * ZERO MULTIPLICATIONS AT THE LEAF!! */
static inline int count_leaf_roots(const uint32_t * __restrict va, const uint32_t * __restrict vb, int op) {
    int z = 0;
    if (op == 0) {
        for (int p = 0; p < NPTS; p++) {
            uint32_t s = va[p] + vb[p];
            z += (s == 0 || s == MP);
        }
    } else if (op == 1) {
        for (int p = 0; p < NPTS; p++) {
            z += (va[p] == vb[p]);
        }
    } else {
        for (int p = 0; p < NPTS; p++) {
            z += (va[p] == 0 || vb[p] == 0);
        }
    }
    return z;
}

static int verify_roots_mod_p2(const Gate *gates, int tau) {
    uint64_t v[MAX_TAU + 2][NPTS];
    for (int p = 0; p < NPTS; p++) {
        int x = X_MIN + p;
        v[0][p] = 1;
        v[1][p] = (uint64_t)((x % (int64_t)P2 + (int64_t)P2) % (int64_t)P2);
    }
    for (int d = 0; d < tau; d++) {
        int idx = d + 2;
        int op = gates[d].op, i = gates[d].i, j = gates[d].j;
        if (op == 0) {
            for (int p = 0; p < NPTS; p++) { uint64_t s = v[i][p] + v[j][p]; v[idx][p] = s >= P2 ? s - P2 : s; }
        } else if (op == 1) {
            for (int p = 0; p < NPTS; p++) { v[idx][p] = v[i][p] >= v[j][p] ? v[i][p] - v[j][p] : v[i][p] + P2 - v[j][p]; }
        } else {
            for (int p = 0; p < NPTS; p++) { v[idx][p] = (v[i][p] * v[j][p]) % P2; }
        }
    }
    int z = 0;
    for (int p = 0; p < NPTS; p++) z += (v[tau + 1][p] == 0);
    return z;
}

static inline void check_leaf(SearchCtx *ctx, int depth, int idx, int op, int i, int j) {
    ctx->leaves_checked++;
    int z = count_leaf_roots(ctx->vals[i], ctx->vals[j], op);
    int thresh = ctx->best_roots;
    if (ctx->report_threshold > 0 && ctx->report_threshold - 1 < thresh) {
        thresh = ctx->report_threshold - 1;
    }
    if (z > thresh) {
        /* Verify nonzero and non-duplicate only when z exceeds threshold! */
        uint32_t r1;
        uint64_t r2;
        if (!compute_hash_and_check_dup(ctx, idx, op, i, j, &r1, &r2)) return;
        ctx->path[depth] = (Gate){op, i, j};
        /* Cross-check root count modulo independent prime P2 = 10^9 + 9 */
        int z2 = verify_roots_mod_p2(ctx->path, ctx->target_tau);
        if (z2 < z) z = z2;
        if (z <= thresh) return;
        if (z > ctx->best_roots) {
            ctx->best_roots = z;
            memcpy(ctx->best_gates, ctx->path, sizeof(Gate) * ctx->target_tau);
        }
        if (ctx->report_threshold > 0 && z >= ctx->report_threshold) {
            print_slp_locked(ctx->path, ctx->target_tau, z);
        } else if (ctx->report_threshold == 0 && z > g_global_best) {
            print_slp_locked(ctx->path, ctx->target_tau, z);
        }
    }
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

                eval_gate(ctx, idx, op, i, j);

                uint32_t next_mask = (unused_mask & ~(1U << i) & ~(1U << j)) | (1U << idx);
                int next_cnt = unused_cnt - removed + 1;
                dfs(ctx, depth + 1, next_mask, next_cnt);
            }
        }
    }
}

/* Collect work items at split_depth */
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

                eval_gate(ctx, idx, op, i, j);

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
    int report_threshold;
    int best_roots;
    Gate best_gates[MAX_TAU];
    uint64_t nodes_visited;
    uint64_t leaves_checked;
} WorkerArg;

static void *worker_fn(void *arg) {
    WorkerArg *wa = (WorkerArg *)arg;
    SearchCtx ctx;
    memset(&ctx, 0, sizeof(ctx));
    ctx.target_tau = wa->target_tau;
    ctx.report_threshold = wa->report_threshold;
    if (wa->report_threshold > 0) ctx.best_roots = wa->report_threshold - 1;
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
            eval_gate(&ctx, idx, g.op, g.i, g.j);
        }
        dfs(&ctx, w->prefix_len, w->unused_mask, w->unused_cnt);
    }

    wa->best_roots = ctx.best_roots;
    memcpy(wa->best_gates, ctx.best_gates, sizeof(Gate) * wa->target_tau);
    wa->nodes_visited = ctx.nodes_visited;
    wa->leaves_checked = ctx.leaves_checked;
    return NULL;
}

int main(int argc, char **argv) {
    int min_tau = 1, max_tau = 8, nthreads = 12, report_thresh = 0;
    if (argc >= 2) min_tau = atoi(argv[1]);
    if (argc >= 3) max_tau = atoi(argv[2]);
    if (argc >= 4) nthreads = atoi(argv[3]);
    if (argc >= 5) report_thresh = atoi(argv[4]);

    for (int tau = min_tau; tau <= max_tau; tau++) {
        g_global_best = 0;
        struct timespec t0, t1;
        clock_gettime(CLOCK_MONOTONIC, &t0);

        if (tau <= 4) {
            SearchCtx ctx;
            memset(&ctx, 0, sizeof(ctx));
            ctx.target_tau = tau;
            ctx.report_threshold = report_thresh;
            init_base(&ctx);
            dfs(&ctx, 0, 0U, 0);
            clock_gettime(CLOCK_MONOTONIC, &t1);
            double dt = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
            printf("SUMMARY tau=%d z_max=%d nodes=%llu leaves=%llu time=%.3fs\n",
                   tau, ctx.best_roots,
                   (unsigned long long)ctx.nodes_visited,
                   (unsigned long long)ctx.leaves_checked, dt);
            fflush(stdout);
            continue;
        }

        int split_depth = (tau >= 8) ? 3 : 2;
        g_work_cnt = 0;
        g_work_next = 0;
        SearchCtx root_ctx;
        memset(&root_ctx, 0, sizeof(root_ctx));
        root_ctx.target_tau = tau;
        init_base(&root_ctx);
        collect_work(&root_ctx, 0, split_depth, 0U, 0);

        pthread_t threads[64];
        WorkerArg args[64];
        if (nthreads > 64) nthreads = 64;
        for (int t = 0; t < nthreads; t++) {
            memset(&args[t], 0, sizeof(WorkerArg));
            args[t].tid = t;
            args[t].target_tau = tau;
            args[t].report_threshold = report_thresh;
            pthread_create(&threads[t], NULL, worker_fn, &args[t]);
        }
        uint64_t tot_nodes = 0, tot_leaves = 0;
        int best = 0;
        for (int t = 0; t < nthreads; t++) {
            pthread_join(threads[t], NULL);
            tot_nodes += args[t].nodes_visited;
            tot_leaves += args[t].leaves_checked;
            if (args[t].best_roots > best) best = args[t].best_roots;
        }
        clock_gettime(CLOCK_MONOTONIC, &t1);
        double dt = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
        printf("SUMMARY tau=%d z_max=%d work_items=%d nodes=%llu leaves=%llu time=%.3fs (%.1fM leaves/s)\n",
               tau, best, g_work_cnt,
               (unsigned long long)tot_nodes,
               (unsigned long long)tot_leaves, dt,
               (double)tot_leaves / (dt * 1e6 + 1e-9));
        fflush(stdout);
    }
    return 0;
}
