/*
 * Wide-range (x in [-256, 255]) Beam + Evolutionary + Structured Search
 * for the Shub-Smale tau-conjecture (tau = 8..12).
 *
 * Scoring heuristics:
 *   - Distinct integer roots in [-256, 255]
 *   - Value-collision score (repeated values of g(x) enable (g - c) to add multiple roots!)
 *   - Pairwise agreement/negation between gates (enables g_i +- g_j to gain roots!)
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define MAX_TAU 14
#define NPTS 512
#define X_MIN (-256)
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

static uint64_t rng_state = 0x123456789ABCDEFULL;
static inline uint64_t xorshift64(void) {
    uint64_t x = rng_state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    rng_state = x;
    return x;
}

typedef struct {
    int op; /* 0='+', 1='-', 2='*' */
    int i;  /* 0=1, 1=x, k+1=g_k */
    int j;
} Gate;

typedef struct {
    int len;
    Gate gates[MAX_TAU];
    int max_roots;
    int last_roots;
    int score;
    uint64_t sig; /* hash of last gate */
} Candidate;

static uint32_t g_base0[NPTS], g_base1[NPTS];

static void init_globals(void) {
    for (int p = 0; p < NPTS; p++) {
        int x = X_MIN + p;
        g_base0[p] = 1;
        g_base1[p] = (x >= 0) ? (uint32_t)x : (MP - (uint32_t)(-x));
    }
}

static void print_slp(const Gate *gates, int tau, int roots) {
    printf("BEAM_FOUND tau=%d roots=%d: ", tau, roots);
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

typedef struct {
    uint32_t vals[MAX_TAU + 2][NPTS];
    uint32_t h1[MAX_TAU + 2];
    uint64_t h2[MAX_TAU + 2];
    uint32_t nh1[MAX_TAU + 2];
    uint64_t nh2[MAX_TAU + 2];
} EvalBuf;

static void eval_prefix(EvalBuf *buf, const Gate *gates, int len) {
    memcpy(buf->vals[0], g_base0, sizeof(g_base0));
    memcpy(buf->vals[1], g_base1, sizeof(g_base1));
    buf->h1[0] = 1; buf->h2[0] = 1; buf->nh1[0] = MP - 1; buf->nh2[0] = P2 - 1;
    buf->h1[1] = HASH_X1; buf->h2[1] = HASH_X2; buf->nh1[1] = MP - HASH_X1; buf->nh2[1] = P2 - HASH_X2;
    for (int d = 0; d < len; d++) {
        int idx = d + 2;
        int op = gates[d].op, i = gates[d].i, j = gates[d].j;
        uint32_t a1 = buf->h1[i], b1 = buf->h1[j];
        uint64_t a2 = buf->h2[i], b2 = buf->h2[j];
        uint32_t r1; uint64_t r2;
        if (op == 0) { r1 = madd(a1, b1); r2 = a2 + b2; if (r2 >= P2) r2 -= P2; }
        else if (op == 1) { r1 = msub(a1, b1); r2 = a2 >= b2 ? a2 - b2 : a2 + P2 - b2; }
        else { r1 = mmul(a1, b1); r2 = (a2 * b2) % P2; }
        buf->h1[idx] = r1; buf->h2[idx] = r2;
        buf->nh1[idx] = r1 == 0 ? 0 : MP - r1;
        buf->nh2[idx] = r2 == 0 ? 0 : P2 - r2;

        const uint32_t *va = buf->vals[i], *vb = buf->vals[j];
        uint32_t *vc = buf->vals[idx];
        if (op == 0) for (int p = 0; p < NPTS; p++) vc[p] = madd(va[p], vb[p]);
        else if (op == 1) for (int p = 0; p < NPTS; p++) vc[p] = msub(va[p], vb[p]);
        else for (int p = 0; p < NPTS; p++) vc[p] = mmul(va[p], vb[p]);
    }
}

/* Score a newly added gate at idx: combines roots + small-range collision potential */
static int score_gate(const EvalBuf *buf, int idx) {
    const uint32_t *v = buf->vals[idx];
    int roots = 0;
    for (int p = 0; p < NPTS; p++) roots += (v[p] == 0);

    /* Count small-window (x in [-16, 15]) value multiplicities (nonzero values repeated >= 2 times) */
    int center = -X_MIN; /* index of x=0 */
    int multi_bonus = 0;
    uint32_t small[32];
    for (int k = 0; k < 32; k++) small[k] = v[center - 16 + k];
    /* Simple pair count for repeated nonzero values */
    int pairs = 0;
    int neg_pairs = 0;
    for (int a = 0; a < 32; a++) {
        if (small[a] == 0) continue;
        for (int b = a + 1; b < 32; b++) {
            if (small[a] == small[b]) pairs++;
            else if (small[a] + small[b] == MP) neg_pairs++;
        }
    }
    if (pairs > 20) pairs = 20;
    if (neg_pairs > 20) neg_pairs = 20;
    multi_bonus = pairs * 3 + neg_pairs * 2;
    return roots * 100 + multi_bonus;
}

static int verify_roots_mod_p2(const Gate *gates, int tau) {
    static uint64_t v[MAX_TAU + 2][NPTS];
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

static int cmp_cand_desc(const void *a, const void *b) {
    const Candidate *ca = (const Candidate *)a;
    const Candidate *cb = (const Candidate *)b;
    if (cb->score != ca->score) return cb->score - ca->score;
    return cb->max_roots - ca->max_roots;
}

int main(int argc, char **argv) {
    int max_tau = 12;
    int beam_width = 4000;
    if (argc >= 2) max_tau = atoi(argv[1]);
    if (argc >= 3) beam_width = atoi(argv[2]);
    if (max_tau > MAX_TAU) max_tau = MAX_TAU;

    init_globals();
    rng_state = (uint64_t)time(NULL) ^ 0x9E3779B97F4A7C15ULL;

    int best_by_tau[MAX_TAU + 1];
    memset(best_by_tau, 0, sizeof(best_by_tau));

    Candidate *cur = (Candidate *)calloc(1, sizeof(Candidate));
    int cur_cnt = 1;
    cur[0].len = 0;
    cur[0].max_roots = 1;
    cur[0].score = 100;

    int next_cap = beam_width * 200;
    Candidate *next = (Candidate *)malloc(sizeof(Candidate) * next_cap);
    EvalBuf buf;

    for (int step = 1; step <= max_tau; step++) {
        int next_cnt = 0;
        int idx = step + 1; /* 0=1, 1=x, 2..step+1 */
        for (int c = 0; c < cur_cnt; c++) {
            eval_prefix(&buf, cur[c].gates, cur[c].len);
            for (int i = 0; i < idx; i++) {
                for (int j = i; j < idx; j++) {
                    for (int op = 0; op < 3; op++) {
                        if (op == 1 && i == j) continue;
                        uint32_t a1 = buf.h1[i], b1 = buf.h1[j];
                        uint64_t a2 = buf.h2[i], b2 = buf.h2[j];
                        uint32_t r1; uint64_t r2;
                        if (op == 0) { r1 = madd(a1, b1); r2 = a2 + b2; if (r2 >= P2) r2 -= P2; }
                        else if (op == 1) { r1 = msub(a1, b1); r2 = a2 >= b2 ? a2 - b2 : a2 + P2 - b2; }
                        else { r1 = mmul(a1, b1); r2 = (a2 * b2) % P2; }
                        if (r1 == 0 && r2 == 0) continue;
                        int dup = 0;
                        for (int m = 0; m < idx; m++) {
                            if ((r1 == buf.h1[m] && r2 == buf.h2[m]) ||
                                (r1 == buf.nh1[m] && r2 == buf.nh2[m])) {
                                dup = 1; break;
                            }
                        }
                        if (dup) continue;

                        const uint32_t *va = buf.vals[i], *vb = buf.vals[j];
                        uint32_t *vc = buf.vals[idx];
                        int roots = 0;
                        if (op == 0) {
                            for (int p = 0; p < NPTS; p++) { uint32_t v = madd(va[p], vb[p]); vc[p] = v; roots += (v == 0); }
                        } else if (op == 1) {
                            for (int p = 0; p < NPTS; p++) { uint32_t v = msub(va[p], vb[p]); vc[p] = v; roots += (v == 0); }
                        } else {
                            for (int p = 0; p < NPTS; p++) { uint32_t v = mmul(va[p], vb[p]); vc[p] = v; roots += (v == 0); }
                        }

                        if (roots >= 5 || roots > best_by_tau[step]) {
                            Gate tmp[MAX_TAU];
                            memcpy(tmp, cur[c].gates, sizeof(Gate) * cur[c].len);
                            tmp[step - 1] = (Gate){op, i, j};
                            int z2 = verify_roots_mod_p2(tmp, step);
                            if (z2 < roots) roots = z2;
                            if (roots > best_by_tau[step]) {
                                best_by_tau[step] = roots;
                                print_slp(tmp, step, roots);
                            }
                        }

                        int sc = score_gate(&buf, idx);
                        /* Also reward preserving high max_roots in the DAG */
                        int mr = roots > cur[c].max_roots ? roots : cur[c].max_roots;
                        int total_sc = sc + mr * 60 + (int)(xorshift64() % 15);

                        if (next_cnt >= next_cap) {
                            next_cap *= 2;
                            next = (Candidate *)realloc(next, sizeof(Candidate) * next_cap);
                        }
                        Candidate *nc = &next[next_cnt++];
                        nc->len = step;
                        memcpy(nc->gates, cur[c].gates, sizeof(Gate) * cur[c].len);
                        nc->gates[step - 1] = (Gate){op, i, j};
                        nc->max_roots = mr;
                        nc->last_roots = roots;
                        nc->score = total_sc;
                        uint64_t lo = r1 < (MP - r1) ? r1 : (MP - r1);
                        nc->sig = (lo << 32) ^ (r2 < (P2 - r2) ? r2 : (P2 - r2));
                    }
                }
            }
        }
        qsort(next, next_cnt, sizeof(Candidate), cmp_cand_desc);

        /* Keep top beam_width diverse candidates (limit duplicates of same final poly) */
        free(cur);
        cur = (Candidate *)malloc(sizeof(Candidate) * beam_width);
        cur_cnt = 0;
        for (int k = 0; k < next_cnt && cur_cnt < beam_width; k++) {
            /* Allow at most 2 paths with same final poly sig in beam */
            int same = 0;
            for (int m = cur_cnt - 1; m >= 0 && m >= cur_cnt - 64; m--) {
                if (cur[m].sig == next[k].sig) { same++; if (same >= 2) break; }
            }
            if (same >= 2) continue;
            cur[cur_cnt++] = next[k];
        }
        printf("STEP tau=%d best_roots=%d expanded=%d kept=%d\n", step, best_by_tau[step], next_cnt, cur_cnt);
        fflush(stdout);
    }

    free(cur);
    free(next);
    return 0;
}
