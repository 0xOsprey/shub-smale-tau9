/*
 * Targeted Multi-Seed Extension + Evolutionary DAG Search for tau = 10, 11, 12.
 *
 * Strategy 1: Exhaustive 2- and 3-gate extensions from ALL distinct high-root
 *             witnesses at tau = 8 (6 roots), tau = 9 (6 roots), tau = 10 (7 roots),
 *             tau = 11 (8 roots).
 * Strategy 2: Algebraic family generator:
 *             - Products of difference-of-squares factors:
 *               f_k(x) = x^2 - (x^2 - k)^2  for k in {2, 6, 12, 20, 30}
 *               g_m(x) = (m*x)^2 - (x^2 - k)^2
 *             - Products of q-factors: q = x^2 - x, (q - c_i)
 *             - Symmetric quartic differences: ((x^2 - A)^2 - B^2)
 * Strategy 3: Parallel random-restart hill-climbing / simulated annealing on DAGs
 *             of length 10, 11, 12 over wide root range [-128, 127].
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <pthread.h>

#define MAX_TAU 14
#define NPTS 256
#define X_MIN (-128)
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

static uint32_t g_b0[NPTS], g_b1[NPTS];
static uint64_t g_b0_p2[NPTS], g_b1_p2[NPTS];
static pthread_mutex_t g_lock = PTHREAD_MUTEX_INITIALIZER;
static int g_best[MAX_TAU + 1];

static void init_tables(void) {
    for (int p = 0; p < NPTS; p++) {
        int x = X_MIN + p;
        g_b0[p] = 1;
        g_b1[p] = (x >= 0) ? (uint32_t)x : (MP - (uint32_t)(-x));
        g_b0_p2[p] = 1;
        g_b1_p2[p] = (uint64_t)((x % (int64_t)P2 + (int64_t)P2) % (int64_t)P2);
    }
}

static int verify_p2(const Gate *gates, int tau) {
    uint64_t v[MAX_TAU + 2][NPTS];
    memcpy(v[0], g_b0_p2, sizeof(g_b0_p2));
    memcpy(v[1], g_b1_p2, sizeof(g_b1_p2));
    uint64_t h2[MAX_TAU + 2];
    h2[0] = 1; h2[1] = HASH_X2;
    for (int d = 0; d < tau; d++) {
        int idx = d + 2, op = gates[d].op, i = gates[d].i, j = gates[d].j;
        if (op == 0) {
            uint64_t s = h2[i] + h2[j]; h2[idx] = s >= P2 ? s - P2 : s;
            for (int p = 0; p < NPTS; p++) { uint64_t t = v[i][p] + v[j][p]; v[idx][p] = t >= P2 ? t - P2 : t; }
        } else if (op == 1) {
            h2[idx] = h2[i] >= h2[j] ? h2[i] - h2[j] : h2[i] + P2 - h2[j];
            for (int p = 0; p < NPTS; p++) v[idx][p] = v[i][p] >= v[j][p] ? v[i][p] - v[j][p] : v[i][p] + P2 - v[j][p];
        } else {
            h2[idx] = (h2[i] * h2[j]) % P2;
            for (int p = 0; p < NPTS; p++) v[idx][p] = (v[i][p] * v[j][p]) % P2;
        }
    }
    if (h2[tau + 1] == 0) return 0; /* zero poly */
    int z = 0;
    for (int p = 0; p < NPTS; p++) z += (v[tau + 1][p] == 0);
    return z;
}

static void report_if_best(const char *tag, const Gate *gates, int tau, int roots) {
    int z2 = verify_p2(gates, tau);
    if (z2 < roots) roots = z2;
    pthread_mutex_lock(&g_lock);
    if (roots > g_best[tau]) {
        g_best[tau] = roots;
        printf("RECORD [%s] tau=%d roots=%d: ", tag, tau, roots);
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
    pthread_mutex_unlock(&g_lock);
}

static inline uint64_t xorshift(uint64_t *s) {
    uint64_t x = *s;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    *s = x; return x;
}

/* Evaluate DAG and return (roots of final gate, max_roots of any gate, collision_score) */
static int eval_dag(const Gate *gates, int tau, int *out_final_roots) {
    uint32_t v[MAX_TAU + 2][NPTS];
    uint32_t h1[MAX_TAU + 2];
    memcpy(v[0], g_b0, sizeof(g_b0));
    memcpy(v[1], g_b1, sizeof(g_b1));
    h1[0] = 1; h1[1] = HASH_X1;

    int best_r = 0;
    for (int d = 0; d < tau; d++) {
        int idx = d + 2, op = gates[d].op, i = gates[d].i, j = gates[d].j;
        if (op == 0) {
            h1[idx] = madd(h1[i], h1[j]);
            for (int p = 0; p < NPTS; p++) v[idx][p] = madd(v[i][p], v[j][p]);
        } else if (op == 1) {
            h1[idx] = msub(h1[i], h1[j]);
            for (int p = 0; p < NPTS; p++) v[idx][p] = msub(v[i][p], v[j][p]);
        } else {
            h1[idx] = mmul(h1[i], h1[j]);
            for (int p = 0; p < NPTS; p++) v[idx][p] = mmul(v[i][p], v[j][p]);
        }
        if (h1[idx] != 0) {
            int r = 0;
            for (int p = 0; p < NPTS; p++) r += (v[idx][p] == 0);
            if (r > best_r) best_r = r;
            if (d == tau - 1) *out_final_roots = r;
        } else if (d == tau - 1) {
            *out_final_roots = 0;
        }
    }
    return best_r;
}

typedef struct {
    int tid;
    int tau;
    int iters;
} EvoArg;

static const Gate SEED_10_X7[10] = {
    {0, 0, 0}, {2, 1, 1}, {1, 2, 3}, {2, 4, 4}, {1, 3, 5},
    {2, 1, 6}, {0, 0, 2}, {2, 8, 8}, {1, 3, 9}, {2, 7, 10}
};
static const Gate SEED_11_Q8[11] = {
    {0, 0, 0}, {0, 0, 1}, {0, 2, 2}, {2, 1, 3}, {1, 2, 5},
    {0, 4, 6}, {2, 5, 6}, {2, 7, 8}, {0, 2, 4}, {0, 7, 10}, {2, 9, 11}
};

static void *evo_worker(void *arg) {
    EvoArg *ea = (EvoArg *)arg;
    int tau = ea->tau;
    uint64_t rng = ((uint64_t)time(NULL) << 16) ^ ((uint64_t)ea->tid * 0x9E3779B97F4A7C15ULL) ^ (uint64_t)tau;

    Gate cur[MAX_TAU], cand[MAX_TAU];
    for (int restart = 0; restart < ea->iters; restart++) {
        /* Initialize either from a known strong seed (30%) or random valid DAG (70%) */
        int mode = (int)(xorshift(&rng) % 10);
        if (mode < 2 && tau >= 10) {
            memcpy(cur, SEED_10_X7, sizeof(Gate) * 10);
            for (int d = 10; d < tau; d++) {
                int idx = d + 2;
                int op = (int)(xorshift(&rng) % 3);
                int i = (int)(xorshift(&rng) % idx);
                int j = (int)(xorshift(&rng) % idx);
                if (i > j) { int t = i; i = j; j = t; }
                if (op == 1 && i == j) op = 0;
                cur[d] = (Gate){op, i, j};
            }
        } else if (mode < 4 && tau >= 11) {
            memcpy(cur, SEED_11_Q8, sizeof(Gate) * 11);
            for (int d = 11; d < tau; d++) {
                int idx = d + 2;
                int op = (int)(xorshift(&rng) % 3);
                int i = (int)(xorshift(&rng) % idx);
                int j = (int)(xorshift(&rng) % idx);
                if (i > j) { int t = i; i = j; j = t; }
                if (op == 1 && i == j) op = 0;
                cur[d] = (Gate){op, i, j};
            }
        } else {
            for (int d = 0; d < tau; d++) {
                int idx = d + 2;
                int op = (int)(xorshift(&rng) % 3);
                int i = (int)(xorshift(&rng) % idx);
                int j = (int)(xorshift(&rng) % idx);
                if (i > j) { int t = i; i = j; j = t; }
                if (op == 1 && i == j) op = 0;
                cur[d] = (Gate){op, i, j};
            }
        }

        int cur_fr = 0;
        int cur_sc = eval_dag(cur, tau, &cur_fr) * 10 + cur_fr * 15;
        if (cur_fr > g_best[tau]) report_if_best("evo_init", cur, tau, cur_fr);

        for (int step = 0; step < 300; step++) {
            memcpy(cand, cur, sizeof(Gate) * tau);
            int nmut = (xorshift(&rng) % 4 == 0) ? 2 : 1;
            for (int m = 0; m < nmut; m++) {
                int d = (int)(xorshift(&rng) % tau);
                int idx = d + 2;
                int op = (int)(xorshift(&rng) % 3);
                int i = (int)(xorshift(&rng) % idx);
                int j = (int)(xorshift(&rng) % idx);
                if (i > j) { int t = i; i = j; j = t; }
                if (op == 1 && i == j) op = 0;
                cand[d] = (Gate){op, i, j};
            }
            int fr = 0;
            int sc = eval_dag(cand, tau, &fr) * 10 + fr * 15;
            if (fr > g_best[tau]) report_if_best("evo", cand, tau, fr);
            if (sc >= cur_sc || (xorshift(&rng) % 40 == 0)) {
                memcpy(cur, cand, sizeof(Gate) * tau);
                cur_sc = sc;
                cur_fr = fr;
            }
        }
    }
    return NULL;
}

int main(void) {
    init_tables();
    memset(g_best, 0, sizeof(g_best));

    int taus[3] = {10, 11, 12};
    for (int ti = 0; ti < 3; ti++) {
        int tau = taus[ti];
        printf("=== Evolutionary search tau=%d (12 threads) ===\n", tau);
        fflush(stdout);
        pthread_t th[12];
        EvoArg args[12];
        for (int t = 0; t < 12; t++) {
            args[t].tid = t;
            args[t].tau = tau;
            args[t].iters = 2000;
            pthread_create(&th[t], NULL, evo_worker, &args[t]);
        }
        for (int t = 0; t < 12; t++) pthread_join(th[t], NULL);
        printf("EVO_DONE tau=%d best=%d\n", tau, g_best[tau]);
        fflush(stdout);
    }
    return 0;
}
