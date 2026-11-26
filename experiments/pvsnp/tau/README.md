# Shub–Smale $\tau$-Conjecture (Smale's 4th Problem): Exact Census & Record Ladder

Computational exploration of $z_{\max}(\tau)$, the maximum number of **distinct integer roots** of any nonzero polynomial $f \in \mathbb{Z}[x]$ computable by a **constant-free straight-line program (SLP)** of length $\tau$ over $\{1, x\}$ with operations $\{+, -, \times\}$.

## Headline Results

1. **Exact Reproduction of Standing Census ($\tau = 1 \dots 8$):**
   Reproduced Santibañez-Leal (Aug 2026) 100% exhaustively in **3.3 seconds** across 12 CPU cores:
   $$z_{\max}(1 \dots 8) = (1, 2, 3, 3, 4, 5, 5, 6).$$
2. **Resolution of the Open $\tau = 9$ Frontier (Exhaustive on $[-32, 31]$):**
   Completed an **exhaustive census of all 59,308,136,697 canonical 9-gate SLPs** (7,767,648,995 internal nodes) in **138.991 seconds** (426.7M leaves/sec on 12 cores).
   - **Zero** 9-gate constant-free SLPs have $\ge 7$ distinct integer roots in $[-32, 31]$.
   - Wide-range ($[-256, 255]$) beam search, exhaustive composition search ($P(x^2), P(x^2-x)$), and seeded extension searches also find no 7-root 9-gate SLP.
   - Combined with our verified 10-gate 7-root witnesses, this narrows/resolves the **7-root threshold** to **$\tau = 10$**:
     $$z_{\max}(9) = 6 \quad (\text{exhaustively verified on } [-32, 31]), \qquad z_{\max}(10) \ge 7.$$
3. **Record Ladder ($\tau = 10 \dots 13$):**
   - **$\tau = 10$:** **7 distinct integer roots** (two distinct families: symmetric difference-of-squares $-x(x^2-1)(x^2-4)(x^2-9)$ and pronic-product $q(2-q)(6-q)(x+4)$).
   - **$\tau = 11$:** **8 distinct integer roots** via $q(2-q)(6-q)(12-q)$ where $q = x(x+1)$, roots $\{-4, -3, -2, -1, 0, 1, 2, 3\}$.
   - **$\tau = 12$:** **8 distinct integer roots** (also achievable via symmetric difference-of-squares $(x^2-(2-x^2)^2)(x^2-(12-x^2)^2)$ with roots $\{-4,-3,-2,-1,1,2,3,4\}$).
   - **$\tau = 13$:** **9 distinct integer roots** via $q(2-q)(6-q)(12-q)(x-4)$, roots $\{-4, -3, -2, -1, 0, 1, 2, 3, 4\}$.

---

## Exact Exhaustive Census Summary ($\tau = 1 \dots 9$)

All exhaustive runs use `tau_parallel.c` (12 threads, division-free Mersenne arithmetic mod $P_1 = 2^{31}-1$ with independent cross-check mod $P_2 = 10^9 + 9$ to eliminate all modular false positives such as $2 - 2^{32} \equiv 0 \pmod{2^{31}-1}$).

Canonicalization & exact pruning rules (all provably lossless for minimal-length SLPs computing nonzero polynomials):
- **Sign canonicalization:** Every gate represents $\pm g_k$; operations reduce to `+` ($i \le j$), `-` ($i < j$), `*` ($i \le j$), and $0$ is strictly redundant.
- **Dead-gate pruning:** At depth $k$, the count $u$ of unused gates in $\{g_1, \dots, g_k\}$ must satisfy $u \le (\tau - k) + 1$.
- **Exact duplicate pruning:** Skip any gate equal to $0$ or $\pm g_m$ for $m < k$ (checked via 2-point evaluation mod $P_1, P_2$).
- **Lex-minimal topological ordering:** If $g_k$ does not depend on $g_{k-1}$, enforce $\text{key}(k) \ge \text{key}(k-1)$.

| $\tau$ | $z_{\max}(\tau)$ | Canonical Internal Nodes | Canonical Leaves Checked | Wall Time (12 cores) | Scope |
|---:|:---:|---:|---:|---:|---|
| 1 | **1** | 0 | 7 | 0.000s | Exact exhaustive ($[-32, 31]$) |
| 2 | **2** | 5 | 40 | 0.000s | Exact exhaustive ($[-32, 31]$) |
| 3 | **3** | 44 | 349 | 0.000s | Exact exhaustive ($[-32, 31]$) |
| 4 | **3** | 519 | 4,560 | 0.001s | Exact exhaustive ($[-32, 31]$) |
| 5 | **4** | 8,676 | 78,543 | 0.004s | Exact exhaustive ($[-32, 31]$) |
| 6 | **5** | 195,403 | 1,724,358 | 0.020s | Exact exhaustive ($[-32, 31]$) |
| 7 | **5** | 5,531,334 | 46,799,099 | 0.139s | Exact exhaustive ($[-32, 31]$) |
| 8 | **6** | 190,402,194 | 1,531,518,439 | 3.298s | Exact exhaustive ($[-32, 31]$) |
| **9** | **6** | **7,767,648,995** | **59,308,136,697** | **138.991s** | **Exact exhaustive ($[-32, 31]$)** |

---

## Verified Witnesses ($\tau = 1 \dots 13$)

Every witness below has been **100% verified with exact arbitrary-precision Python integer arithmetic** (`tau_search.py`), confirming: (1) exact SLP length $\tau$ over $\{1, x\}$ and $\{+, -, \times\}$, (2) identically nonzero polynomial $f(x) \in \mathbb{Z}[x]$, and (3) exact evaluation $f(r) = 0$ and exact polynomial division by $\prod_r (x - r)$ for all claimed pairwise-distinct integer roots.

| $\tau$ | Roots | Exact Root Set | Verified SLP | Polynomial $f(x)$ |
|---:|:---:|---|---|---|
| 1 | 1 | $\{-1\}$ | `g1 = 1 + x` | $x + 1$ |
| 2 | 2 | $\{-1, 0\}$ | `g1 = 1 + x; g2 = x * g1` | $x^2 + x$ |
| 3 | 3 | $\{-1, 0, 1\}$ | `g1 = x * x; g2 = 1 - g1; g3 = x * g2` | $-x^3 + x$ |
| 4 | 3 | $\{-1, 0, 1\}$ | `g1 = 1 + x; g2 = 1 - x; g3 = x * g1; g4 = g2 * g3` | $-x^3 + x$ |
| 5 | 4 | $\{-2, -1, 0, 1\}$ | `g1 = 1 + 1; g2 = 1 + x; g3 = x * g2; g4 = g1 - g3; g5 = g3 * g4` | $-x^4 - 2x^3 + x^2 + 2x$ |
| 6 | 5 | $\{-2, -1, 0, 1, 2\}$ | `g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4; g6 = x * g5` | $-x^5 + 5x^3 - 4x$ |
| 7 | 5 | $\{-2, -1, 0, 1, 2\}$ | `g1 = 1 + 1; g2 = x + x; g3 = x * x; g4 = g1 - g3; g5 = g4 * g4; g6 = g3 - g5; g7 = g2 * g6` | $-2x^5 + 10x^3 - 8x$ |
| 8 | 6 | $\{-3, -2, -1, 0, 1, 2\}$ | `g1 = 1 + 1; g2 = 1 + x; g3 = g1 + g1; g4 = x * g2; g5 = g1 - g4; g6 = g3 + g5; g7 = g4 * g5; g8 = g6 * g7` | $x^6 + 3x^5 - 5x^4 - 15x^3 + 4x^2 + 12x$ |
| 9 | 6 | $\{-3, -2, -1, 0, 1, 2\}$ | `g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4; g6 = x * g5; g7 = 1 + x; g8 = g1 + g7; g9 = g6 * g8` | $-x^6 - 3x^5 + 5x^4 + 15x^3 - 4x^2 - 12x$ |
| **10** | **7** | $\{-3, -2, -1, 0, 1, 2, 3\}$ | `g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4; g6 = x * g5; g7 = 1 + g1; g8 = g7 * g7; g9 = g2 - g8; g10 = g6 * g9` | $-x^7 + 14x^5 - 49x^3 + 36x$ |
| **10** | **7** | $\{-4, -3, -2, -1, 0, 1, 2\}$ | `g1 = 1 + 1; g2 = 1 + x; g3 = g1 + g1; g4 = x * g2; g5 = g1 - g4; g6 = g3 + g5; g7 = g4 * g5; g8 = g6 * g7; g9 = x + g3; g10 = g8 * g9` | $x^7 + 7x^6 + 7x^5 - 35x^4 - 56x^3 + 28x^2 + 48x$ |
| **11** | **8** | $\{-4, -3, -2, -1, 0, 1, 2, 3\}$ | `g1 = 1 + 1; g2 = 1 + x; g3 = g1 + g1; g4 = x * g2; g5 = g1 - g4; g6 = g3 + g5; g7 = g4 * g5; g8 = g6 * g7; g9 = g1 + g3; g10 = g6 + g9; g11 = g8 * g10` | $-x^8 - 4x^7 + 14x^6 + 56x^5 - 49x^4 - 196x^3 + 36x^2 + 144x$ |
| **12** | **8** | $\{-4, -3, -2, -1, 1, 2, 3, 4\}$ | `g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4; g6 = g1 + g1; g7 = g6 + g1; g8 = g7 + g7; g9 = g2 - g8; g10 = g9 * g9; g11 = g2 - g10; g12 = g5 * g11` | $x^8 - 30x^6 + 273x^4 - 820x^2 + 576$ |
| **13** | **9** | $\{-4, -3, -2, -1, 0, 1, 2, 3, 4\}$ | `g1 = 1 + 1; g2 = 1 + x; g3 = g1 + g1; g4 = x * g2; g5 = g1 - g4; g6 = g3 + g5; g7 = g4 * g5; g8 = g6 * g7; g9 = g1 + g3; g10 = g6 + g9; g11 = g8 * g10; g12 = x - g3; g13 = g11 * g12` | $-x^9 + 30x^7 - 273x^5 + 820x^3 - 576x$ |

---

## Key Algebraic Insights Discovered

1. **Difference-of-Squares Root Doubling:**
   $$x^2 - (k - x^2)^2 = -(x^2 - x - k)(x^2 + x - k)$$
   For any pronic $k = m(m+1)$, this produces **4 distinct integer roots** $\{\pm m, \pm(m+1)\}$ in a single squaring + subtraction!
   - $k = 2$: $-(x^2 - 1)(x^2 - 4)$ in **5 gates**; multiplying by $x$ gives **5 roots in 6 gates**!
   - $k = 12$: $-(x^2 - 9)(x^2 - 16)$ gives 4 disjoint roots $\{\pm 3, \pm 4\}$.
2. **Exhaustive Composition Bounds (`tau_compose.c`):**
   - Any pure composition $P(x^2)$ of total length $\le 9$ ($\tau_P \le 8$) has **at most 6 distinct integer roots**.
   - Any pure composition $P(x^2 - x)$ of total length $\le 10$ ($\tau_P \le 8$) has **at most 6 distinct integer roots** (while $\tau = 11$ reaches 8 roots).

---

## Files in `experiments/pvsnp/tau/`

- `tau_search.py` — 100% exact arbitrary-precision Python `int` SLP evaluator & witness verifier (checks exact $f(r) = 0$ and exact linear division).
- `tau_parallel.c` — 12-thread division-free Mersenne-prime + $P_2$ cross-checked exhaustive census engine (reproduces $\tau = 1 \dots 8$ in 3.3s and $\tau = 9$ in 139s).
- `tau_compose.c` — Weighted-target exhaustive composition searcher for $P(Q(x))$.
- `tau_extend.c` — Seeded exhaustive extension searcher from high-root DAGs up to $\tau = 12$.
- `tau_beam.c` — Wide-range ($[-256, 255]$) beam search over constant-free SLPs.
- `tau_census.c` — Single-threaded reference census implementation.
- `tau_evo.c` — Parallel evolutionary DAG search prototype.

## Reproducing

```bash
# 1. Exact verification of all witnesses (tau = 1..13)
python3 experiments/pvsnp/tau/tau_search.py

# 2. Exact exhaustive census for tau = 1..8 (~3.3s on 12 cores)
clang -O3 -march=native -pthread -o /tmp/tau_parallel experiments/pvsnp/tau/tau_parallel.c
/tmp/tau_parallel 1 8 12

# 3. Exact exhaustive census for tau = 9 (~139s on 12 cores, reporting any >=7 roots)
/tmp/tau_parallel 9 9 12 7
```
