/*
 * Seeded Exhaustive Extension Search for tau = 9, 10, 11, 12.
 * Starts from high-value seed DAGs (retaining all intermediate gates!)
 * and exhaustively searches all extensions of length d = 1..max_ext.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define MAX_TAU 14
#define NPTS 128
#define X_MIN (-64)
#define MP 2147483647U
#define P2 1000000009ULL
#define HASH_X1 314159265U
#define HASH_X2 271828182ULL

static inline uint32_t madd(uint32_t a, uint32_t b) {
    uint32_t s = a + b; s = (s & MP) + (s >> 31); return s >= MP ? s - MP : s;
}
static inline uint32_t msub(uint32_t a, uint32_t b) {
    uint32_t s = a + (MP - b); s = (s & MP) + (s >> 31); return s >= MP ? s - MP : s;
}
static inline uint32_t mmul(uint32_t a, uint32_t b) {
    uint64_t t = (uint64_t)a * (uint64_t)b;
    uint64_t s = (t & MP) + (t >> 31); s = (s & MP) + (s >> 31);
    return (uint32_t)(s >= MP ? s - MP : s);
}

typedef struct { int op, i, j; } Gate;

typedef struct {
    int target_tau;
    int seed_len;
    int best_roots;
    uint32_t vals[MAX_TAU + 2][NPTS];
    uint32_t h1[MAX_TAU + 2];
    uint64_t h2[MAX_TAU + 2];
    uint32_t nh1[MAX_TAU + 2];
    uint64_t nh2[MAX_TAU + 2];
    Gate path[MAX_TAU];
} Ctx;

static int verify_p2(const Gate *gates, int tau) {
    uint64_t v[MAX_TAU + 2][NPTS];
    for (int p = 0; p < NPTS; p++) {
        int x = X_MIN + p;
        v[0][p] = 1;
        v[1][p] = (uint64_t)((x % (int64_t)P2 + (int64_t)P2) % (int64_t)P2);
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

static void print_slp(const char *tag, const Gate *gates, int tau, int roots) {
    printf("EXT [%s] tau=%d roots=%d: ", tag, tau, roots);
    const char *ops = "+-*";
    for (int k = 0; k < tau; k++) {
        if (k > 0) printf("; ");
        int i = gates[k].i - 1, j = gates[k].j - 1;
        char si[16], sj[16];
        if (i == -1) strcpy(si, "1"); else if (i == 0) strcpy(si, "x"); else sprintf(si, "g%d", i);
        if (j == -1) strcpy(sj, "1"); else if (j == 0) strcpy(sj, "x"); else sprintf(sj, "g%d", j);
        printf("g%d = %s %c %s", k + 1, si, ops[gates[k].op], sj);
    }
    printf("\n");
    fflush(stdout);
}

static inline int check_dup(Ctx *ctx, int idx, int op, int i, int j, uint32_t *out1, uint64_t *out2) {
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

static inline void eval_gate(Ctx *ctx, int idx, int op, int i, int j) {
    const uint32_t * __restrict va = ctx->vals[i], * __restrict vb = ctx->vals[j];
    uint32_t * __restrict vc = ctx->vals[idx];
    if (op == 0) for (int p = 0; p < NPTS; p++) vc[p] = madd(va[p], vb[p]);
    else if (op == 1) for (int p = 0; p < NPTS; p++) vc[p] = msub(va[p], vb[p]);
    else for (int p = 0; p < NPTS; p++) vc[p] = mmul(va[p], vb[p]);
}

static inline int count_leaf(const uint32_t * __restrict va, const uint32_t * __restrict vb, int op) {
    int z = 0;
    if (op == 0) { for (int p = 0; p < NPTS; p++) { uint32_t s = va[p] + vb[p]; z += (s == 0 || s == MP); } }
    else if (op == 1) { for (int p = 0; p < NPTS; p++) z += (va[p] == vb[p]); }
    else { for (int p = 0; p < NPTS; p++) z += (va[p] == 0 || vb[p] == 0); }
    return z;
}

static const char *g_tag = "";

static void dfs(Ctx *ctx, int depth, uint32_t unused_mask, int unused_cnt) {
    int tau = ctx->target_tau, idx = depth + 2;
    int max_unused_after = (tau - 1 - depth) + 1;

    if (depth == tau - 1) {
        if (unused_cnt == 2) {
            int i = __builtin_ctz(unused_mask), j = __builtin_ctz(unused_mask ^ (1U << i));
            for (int op = 0; op < 3; op++) {
                int z = count_leaf(ctx->vals[i], ctx->vals[j], op);
                if (z > ctx->best_roots) {
                    uint32_t r1; uint64_t r2;
                    if (!check_dup(ctx, idx, op, i, j, &r1, &r2)) continue;
                    ctx->path[depth] = (Gate){op, i, j};
                    int z2 = verify_p2(ctx->path, tau);
                    if (z2 < z) z = z2;
                    if (z > ctx->best_roots) { ctx->best_roots = z; print_slp(g_tag, ctx->path, tau, z); }
                }
            }
            return;
        }
        int u0 = __builtin_ctz(unused_mask);
        for (int other = 0; other < idx; other++) {
            int i = other < u0 ? other : u0, j = other < u0 ? u0 : other;
            for (int op = 0; op < 3; op++) {
                if (op == 1 && i == j) continue;
                int z = count_leaf(ctx->vals[i], ctx->vals[j], op);
                if (z > ctx->best_roots) {
                    uint32_t r1; uint64_t r2;
                    if (!check_dup(ctx, idx, op, i, j, &r1, &r2)) continue;
                    ctx->path[depth] = (Gate){op, i, j};
                    int z2 = verify_p2(ctx->path, tau);
                    if (z2 < z) z = z2;
                    if (z > ctx->best_roots) { ctx->best_roots = z; print_slp(g_tag, ctx->path, tau, z); }
                }
            }
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
            for (int op = 0; op < 3; op++) {
                if (op == 1 && i == j) continue;
                uint32_t r1; uint64_t r2;
                if (!check_dup(ctx, idx, op, i, j, &r1, &r2)) continue;
                ctx->h1[idx] = r1; ctx->h2[idx] = r2;
                ctx->nh1[idx] = r1 == 0 ? 0 : MP - r1;
                ctx->nh2[idx] = r2 == 0 ? 0 : P2 - r2;
                ctx->path[depth] = (Gate){op, i, j};
                eval_gate(ctx, idx, op, i, j);
                uint32_t next_mask = (unused_mask & ~(1U << i) & ~(1U << j)) | (1U << idx);
                dfs(ctx, depth + 1, next_mask, unused_cnt - removed + 1);
            }
        }
    }
}

static void run_seed(const char *name, const Gate *seed, int seed_len, int target_tau, int start_best) {
    Ctx ctx;
    memset(&ctx, 0, sizeof(ctx));
    ctx.target_tau = target_tau;
    ctx.seed_len = seed_len;
    ctx.best_roots = start_best;
    g_tag = name;

    for (int p = 0; p < NPTS; p++) {
        int x = X_MIN + p;
        ctx.vals[0][p] = 1;
        ctx.vals[1][p] = (x >= 0) ? (uint32_t)x : (MP - (uint32_t)(-x));
    }
    ctx.h1[0] = 1; ctx.h2[0] = 1; ctx.nh1[0] = MP - 1; ctx.nh2[0] = P2 - 1;
    ctx.h1[1] = HASH_X1; ctx.h2[1] = HASH_X2; ctx.nh1[1] = MP - HASH_X1; ctx.nh2[1] = P2 - HASH_X2;

    uint32_t mask = 0;
    int ucnt = 0;
    for (int d = 0; d < seed_len; d++) {
        int idx = d + 2;
        Gate g = seed[d];
        uint32_t r1; uint64_t r2;
        check_dup(&ctx, idx, g.op, g.i, g.j, &r1, &r2);
        ctx.h1[idx] = r1; ctx.h2[idx] = r2;
        ctx.nh1[idx] = r1 == 0 ? 0 : MP - r1;
        ctx.nh2[idx] = r2 == 0 ? 0 : P2 - r2;
        ctx.path[d] = g;
        eval_gate(&ctx, idx, g.op, g.i, g.j);
        int ui = (mask >> g.i) & 1U, uj = (mask >> g.j) & 1U;
        int rem = (g.i == g.j) ? ui : (ui + uj);
        mask = (mask & ~(1U << g.i) & ~(1U << g.j)) | (1U << idx);
        ucnt = ucnt - rem + 1;
    }
    dfs(&ctx, seed_len, mask, ucnt);
    printf("SEED_DONE [%s] tau=%d best=%d\n", name, target_tau, ctx.best_roots);
    fflush(stdout);
}

int main(void) {
    /* Indices: 0=1, 1=x, 2=g1, 3=g2, ... */
    /* Seed A: tau=6, 5 roots: -x(x^2-1)(x^2-4) */
    Gate seedA[6] = {
        {0, 0, 0}, /* g1 = 1 + 1 = 2 */
        {2, 1, 1}, /* g2 = x * x */
        {1, 2, 3}, /* g3 = 2 - x^2 */
        {2, 4, 4}, /* g4 = (2-x^2)^2 */
        {1, 3, 5}, /* g5 = x^2 - (2-x^2)^2 */
        {2, 1, 6}, /* g6 = x * g5 */
    };
    /* Seed B: tau=8, 6 roots: q(q-2)(q-6) */
    Gate seedB[8] = {
        {0, 0, 0}, /* g1 = 2 */
        {0, 0, 1}, /* g2 = 1 + x */
        {0, 2, 2}, /* g3 = 4 */
        {2, 1, 3}, /* g4 = x(1+x) = q */
        {1, 2, 5}, /* g5 = 2 - q */
        {0, 4, 6}, /* g6 = 6 - q */
        {2, 5, 6}, /* g7 = q(2-q) */
        {2, 7, 8}, /* g8 = q(2-q)(6-q) */
    };
    /* Seed C: tau=5, 4 roots: q(q-2) */
    Gate seedC[5] = {
        {0, 0, 0}, /* g1 = 2 */
        {0, 0, 1}, /* g2 = 1 + x */
        {2, 1, 3}, /* g3 = x(1+x) */
        {1, 2, 4}, /* g4 = 2 - g3 */
        {2, 4, 5}, /* g5 = g3 * g4 */
    };
    /* Seed D: tau=5, 4 roots: -(x^2-1)(x^2-4) */
    Gate seedD[5] = {
        {0, 0, 0}, /* g1 = 2 */
        {2, 1, 1}, /* g2 = x^2 */
        {1, 2, 3}, /* g3 = 2 - x^2 */
        {2, 4, 4}, /* g4 = (2-x^2)^2 */
        {1, 3, 5}, /* g5 = x^2 - (2-x^2)^2 */
    };

    run_seed("seedB_q6", seedB, 8, 10, 6);
    run_seed("seedB_q6", seedB, 8, 11, 7);
    run_seed("seedB_q6", seedB, 8, 12, 7);

    run_seed("seedA_x5", seedA, 6, 9, 5);
    run_seed("seedA_x5", seedA, 6, 10, 6);

    run_seed("seedC_q4", seedC, 5, 9, 5);
    run_seed("seedD_x4", seedD, 5, 9, 5);
    return 0;
}
