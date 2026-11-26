/*
 * Fast exact-DAG exhaustive census & search for the Shub-Smale tau-conjecture.
 *
 * Constant-free SLP of length tau:
 *   g[-1] = 1, g[0] = x
 *   For k = 1..tau: g[k] = g[i] op g[j], op in {+, -, *}, -1 <= i, j < k.
 *
 * Optimizations:
 *   1. Sign canonicalization: every gate represents +-g[k].
 *      Operations reduce to:
 *        op 0 (+): i <= j
 *        op 1 (-): i < j
 *        op 2 (*): i <= j
 *      Zero polynomial is never needed in an optimal SLP.
 *   2. Dead-gate pruning: at depth k, let u = number of unused gates in {1..k}.
 *      Each remaining gate reduces u by at most 1, and final u == 1, so u <= tau - k + 1.
 *   3. Exact-polynomial-equivalence pruning within the current path:
 *      Skip computing any polynomial equal to 0 or +-g[m] for any m < k.
 *   4. Canonical topological ordering for independent gates:
 *      If g[k] does not use g[k-1], require canon_key(k) >= canon_key(k-1).
 *   5. Evaluation over F_P (P = 1000000007) at M points x in [-R, R] (M = 64)
 *      plus a random point r_hash mod P2 = 1000000009 for collision-free identity check.
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
#define P1 1000000007ULL
#define P2 1000000009ULL
#define HASH_X 314159265ULL
#define HASH_X2 271828182ULL

static inline uint32_t add_mod(uint32_t a, uint32_t b) {
    uint32_t s = a + b;
    return s >= P1 ? s - (uint32_t)P1 : s;
}

static inline uint32_t sub_mod(uint32_t a, uint32_t b) {
    return a >= b ? a - b : a + (uint32_t)P1 - b;
}

static inline uint32_t mul_mod(uint32_t a, uint32_t b) {
    return (uint32_t)(((uint64_t)a * (uint64_t)b) % P1);
}

static inline uint32_t neg_mod(uint32_t a) {
    return a == 0 ? 0 : (uint32_t)P1 - a;
}

typedef struct {
    int op; /* 0='+', 1='-', 2='*' */
    int i;  /* 0 means g[-1]=1, 1 means g[0]=x, k+1 means g[k] */
    int j;
} Gate;

typedef struct {
    int target_tau;
    int best_roots;
    Gate best_gates[MAX_TAU];
    uint64_t nodes_visited;
    uint64_t leaves_checked;

    /* State stack indexed by idx = 0..tau+1 (0=1, 1=x, 2..tau+1=g1..gtau) */
    uint32_t vals[MAX_TAU + 2][NPTS];
    uint64_t h1[MAX_TAU + 2]; /* eval at HASH_X mod P1 */
    uint64_t h2[MAX_TAU + 2]; /* eval at HASH_X2 mod P2 */
    uint64_t nh1[MAX_TAU + 2];
    uint64_t nh2[MAX_TAU + 2];
    Gate path[MAX_TAU];
    int key[MAX_TAU];
} SearchCtx;

static void init_base(SearchCtx *ctx) {
    for (int p = 0; p < NPTS; p++) {
        int x = X_MIN + p;
        ctx->vals[0][p] = 1;
        ctx->vals[1][p] = (uint32_t)((x % (int64_t)P1 + (int64_t)P1) % (int64_t)P1);
    }
    ctx->h1[0] = 1;
    ctx->h2[0] = 1;
    ctx->nh1[0] = P1 - 1;
    ctx->nh2[0] = P2 - 1;

    ctx->h1[1] = HASH_X;
    ctx->h2[1] = HASH_X2;
    ctx->nh1[1] = P1 - HASH_X;
    ctx->nh2[1] = P2 - HASH_X2;
}

static void print_slp(const Gate *gates, int tau, int roots) {
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
}

static inline int compute_hash_and_check_dup(
    SearchCtx *ctx, int idx, int op, int i, int j,
    uint64_t *out_h1, uint64_t *out_h2
) {
    uint64_t a1 = ctx->h1[i], b1 = ctx->h1[j];
    uint64_t a2 = ctx->h2[i], b2 = ctx->h2[j];
    uint64_t r1, r2;
    if (op == 0) {
        r1 = a1 + b1; if (r1 >= P1) r1 -= P1;
        r2 = a2 + b2; if (r2 >= P2) r2 -= P2;
    } else if (op == 1) {
        r1 = a1 >= b1 ? a1 - b1 : a1 + P1 - b1;
        r2 = a2 >= b2 ? a2 - b2 : a2 + P2 - b2;
    } else {
        r1 = (a1 * b1) % P1;
        r2 = (a2 * b2) % P2;
    }
    /* Reject zero polynomial */
    if (r1 == 0 && r2 == 0) return 0;
    /* Reject duplicate (up to sign) of any existing gate */
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

static inline int eval_gate_and_count_roots(SearchCtx *ctx, int idx, int op, int i, int j) {
    const uint32_t *va = ctx->vals[i];
    const uint32_t *vb = ctx->vals[j];
    uint32_t *vc = ctx->vals[idx];
    int z = 0;
    if (op == 0) {
        for (int p = 0; p < NPTS; p++) {
            uint32_t v = add_mod(va[p], vb[p]);
            vc[p] = v;
            z += (v == 0);
        }
    } else if (op == 1) {
        for (int p = 0; p < NPTS; p++) {
            uint32_t v = sub_mod(va[p], vb[p]);
            vc[p] = v;
            z += (v == 0);
        }
    } else {
        for (int p = 0; p < NPTS; p++) {
            uint32_t v = mul_mod(va[p], vb[p]);
            vc[p] = v;
            z += (v == 0);
        }
    }
    return z;
}

static inline void eval_gate(SearchCtx *ctx, int idx, int op, int i, int j) {
    const uint32_t *va = ctx->vals[i];
    const uint32_t *vb = ctx->vals[j];
    uint32_t *vc = ctx->vals[idx];
    if (op == 0) {
        for (int p = 0; p < NPTS; p++) vc[p] = add_mod(va[p], vb[p]);
    } else if (op == 1) {
        for (int p = 0; p < NPTS; p++) vc[p] = sub_mod(va[p], vb[p]);
    } else {
        for (int p = 0; p < NPTS; p++) vc[p] = mul_mod(va[p], vb[p]);
    }
}

static void dfs(SearchCtx *ctx, int depth, uint32_t unused_mask, int unused_cnt) {
    int tau = ctx->target_tau;
    int idx = depth + 2; /* index of gate g_{depth+1} in vals[] */
    int rem_after = tau - 1 - depth; /* gates remaining after this one */
    int max_unused_after = rem_after + 1;
    int prev_idx = idx - 1; /* index of previous gate g_{depth} */

    /* At the last gate (depth == tau - 1), unused_cnt <= 2.
     * If unused_cnt == 2, we MUST pick the exact two unused gates! */
    if (depth == tau - 1) {
        if (unused_cnt == 2) {
            int i = __builtin_ctz(unused_mask);
            int j = __builtin_ctz(unused_mask ^ (1U << i));
            /* i < j guaranteed */
            for (int op = 0; op < 3; op++) {
                uint64_t r1, r2;
                if (!compute_hash_and_check_dup(ctx, idx, op, i, j, &r1, &r2)) continue;
                ctx->leaves_checked++;
                int z = eval_gate_and_count_roots(ctx, idx, op, i, j);
                if (z > ctx->best_roots) {
                    ctx->best_roots = z;
                    ctx->path[depth] = (Gate){op, i, j};
                    memcpy(ctx->best_gates, ctx->path, sizeof(Gate) * tau);
                    print_slp(ctx->best_gates, tau, z);
                }
            }
            return;
        }
        if (unused_cnt == 0) {
            /* Only happens when tau == 1 */
            for (int i = 0; i < idx; i++) {
                for (int j = i; j < idx; j++) {
                    for (int op = 0; op < 3; op++) {
                        if (op == 1 && i == j) continue;
                        uint64_t r1, r2;
                        if (!compute_hash_and_check_dup(ctx, idx, op, i, j, &r1, &r2)) continue;
                        ctx->leaves_checked++;
                        int z = eval_gate_and_count_roots(ctx, idx, op, i, j);
                        if (z > ctx->best_roots) {
                            ctx->best_roots = z;
                            ctx->path[depth] = (Gate){op, i, j};
                            memcpy(ctx->best_gates, ctx->path, sizeof(Gate) * tau);
                            print_slp(ctx->best_gates, tau, z);
                        }
                    }
                }
            }
            return;
        }
        /* unused_cnt == 1: at least one of i, j must be the single unused gate u0 */
        int u0 = __builtin_ctz(unused_mask);
        for (int other = 0; other < idx; other++) {
            int i = other < u0 ? other : u0;
            int j = other < u0 ? u0 : other;
            for (int op = 0; op < 3; op++) {
                if (op == 1 && i == j) continue;
                uint64_t r1, r2;
                if (!compute_hash_and_check_dup(ctx, idx, op, i, j, &r1, &r2)) continue;
                ctx->leaves_checked++;
                int z = eval_gate_and_count_roots(ctx, idx, op, i, j);
                if (z > ctx->best_roots) {
                    ctx->best_roots = z;
                    ctx->path[depth] = (Gate){op, i, j};
                    memcpy(ctx->best_gates, ctx->path, sizeof(Gate) * tau);
                    print_slp(ctx->best_gates, tau, z);
                }
            }
        }
        return;
    }

    /* Internal node: depth < tau - 1 */
    /* We will add 1 new unused gate (bit idx), and remove up to 2 from unused_mask.
     * Need: unused_cnt - removed + 1 <= max_unused_after
     *   => removed >= unused_cnt + 1 - max_unused_after. */
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

                uint64_t r1, r2;
                if (!compute_hash_and_check_dup(ctx, idx, op, i, j, &r1, &r2)) continue;

                ctx->nodes_visited++;
                ctx->h1[idx] = r1;
                ctx->h2[idx] = r2;
                ctx->nh1[idx] = r1 == 0 ? 0 : P1 - r1;
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

int main(int argc, char **argv) {
    int max_tau = 6;
    if (argc >= 2) max_tau = atoi(argv[1]);
    if (max_tau > MAX_TAU) max_tau = MAX_TAU;

    for (int tau = 1; tau <= max_tau; tau++) {
        SearchCtx ctx;
        memset(&ctx, 0, sizeof(ctx));
        ctx.target_tau = tau;
        init_base(&ctx);

        struct timespec t0, t1;
        clock_gettime(CLOCK_MONOTONIC, &t0);
        dfs(&ctx, 0, 0U, 0);
        clock_gettime(CLOCK_MONOTONIC, &t1);
        double dt = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;

        printf("SUMMARY tau=%d z_max=%d nodes=%llu leaves=%llu time=%.3fs\n",
               tau, ctx.best_roots,
               (unsigned long long)ctx.nodes_visited,
               (unsigned long long)ctx.leaves_checked, dt);
        fflush(stdout);
    }
    return 0;
}
