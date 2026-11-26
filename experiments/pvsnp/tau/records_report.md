# Track B Record Witness Report: $\tau = 10, 11, 12, 13, 14$ (Smale's 4th Problem)

## Executive Summary

We hunted new constant-free straight-line program (SLP) lower-bound witnesses for $z_{\max}(\tau)$ (maximum distinct integer roots over $\{1, x\}$ with $\{+, -, \times\}$) across $\tau = 10, 11, 12, 13, 14$ using four complementary engines:
1. **Structured algebraic family search** ([tau_records_10_14.py](file:///Users/joe/github/gemini-neon/experiments/pvsnp/tau/tau_records_10_14.py)): shifted pronic-square quartics, sum-of-two-squares quartics, midpoint-difference families, generalized difference-of-squares, and 5-step constant chains.
2. **12-core exhaustive weighted composition search** ([tau_records_fast.c](file:///Users/joe/github/gemini-neon/experiments/pvsnp/tau/tau_records_fast.c), `compose` mode): exhaustive outer SLPs $P(y)$ up to $\tau_P = 8$ over 14 high-collision inner polynomials $Q(x)$ of cost $1 \dots 7$.
3. **12-core multi-objective diverse beam search** ([tau_records_fast.c](file:///Users/joe/github/gemini-neon/experiments/pvsnp/tau/tau_records_fast.c), `beam` mode): up to beam width $W = 40{,}000$ per depth for $\tau = 1 \dots 14$ on $[-64, 63]$.
4. **Seeded exhaustive extension & 1-/2-gate local mutation search** ([tau_records_fast.c](file:///Users/joe/github/gemini-neon/experiments/pvsnp/tau/tau_records_fast.c), `extend` and `mutate` modes): up to $3.79 \times 10^9$ leaves from elite prefixes.

### New Record Ladder ($\tau = 10 \dots 14$, plus $\tau = 15$ bonus)

Every witness below has been **100% verified in exact arbitrary-precision Python `int` arithmetic** (`eval_slp_exact`, exact `f(r) = 0`, exact linear factor division by $\prod_r (x - r)$, nonzero check, exact gate count $\tau$).

| $\tau$ | Previous Best | **New Verified Record** | Improvement | Key Construction |
|---:|:---:|:---:|:---:|---|
| **10** | $\ge 7$ | **$\ge 7$** | — | $-x(x^2-1)(x^2-4)(x^2-9)$ (roots $\{-3 \dots 3\}$); no 8-root witness found across exhaustive $P(x(x+1))$, 200M-leaf $\tau=6 \to 10$ extension, 40k beam, and mutation |
| **11** | $\ge 8$ | **$\ge 8$** | *(new family)* | **New symmetric midpoint witness** $2(x^2-1)(x^2-4)(x^2-9)(x^2-16)$ (roots $\{\pm 1, \pm 2, \pm 3, \pm 4\}$) alongside pronic $q(2-q)(6-q)(12-q)$ |
| **12** | $\ge 8$ | **$\ge 9$** | **+1 (NEW RECORD)** | **Midpoint Difference Trick:** $x \cdot (x^2-(2-x^2)^2)(x^2-16)((2-x^2)-(x^2-16))$, roots $\{-4 \dots 4\}$ |
| **13** | $\ge 9$ | **$\ge 10$** | **+1 (NEW RECORD)** | **Shifted Pronic-Square with Gate Reuse:** $q \cdot ((q-16)^2 - 14^2)((q-16)^2 - 4^2)$, roots $\{-6,-5,-4,-2,-1,0,1,3,4,5\}$ |
| **14** | *(unlisted)* | **$\ge 10$** | **Baseline set** | $q(2-q)(6-q)(12-q)(20-q)$ (roots $\{-5 \dots 4\}$) and padded $\tau=13$ witness |
| *(bonus)* **15** | *(unlisted)* | **$\ge 11$** | **Bonus** | Extending the $\tau=13$ witness by $(x-2)$ (`g14 = x - g3; g15 = g13 * g14`), roots $\{-6,-5,-4,-2,-1,0,1,2,3,4,5\}$ |

---

## Two New Algebraic Mechanisms Discovered

### 1. The Midpoint Difference Trick ($\tau = 11 \to 8$ symmetric roots, $\tau = 12 \to 9$ roots!)
In the 5-gate 4-root difference-of-squares factor $g_5 = x^2 - (2 - x^2)^2$ (roots $\pm 1, \pm 2$), we already compute $g_3 = 2 - x^2$. When we also build $g_8 = x^2 - 16$ (roots $\pm 4$), the midpoint of $2$ and $16$ is $9 = 3^2$, so a **single subtraction** gives two more roots for free:
$$g_{10} = g_3 - g_8 = (2 - x^2) - (x^2 - 16) = 18 - 2x^2 = 2(9 - x^2) \quad (\text{roots } \pm 3).$$
Multiplying $g_5 \cdot g_8 \cdot g_{10}$ gives **8 symmetric roots** $\{\pm 1, \pm 2, \pm 3, \pm 4\}$ in **11 gates** (leaving $x = 0$ free!), and multiplying by $x$ gives **9 distinct integer roots** $\{-4, -3, -2, -1, 0, 1, 2, 3, 4\}$ in **12 gates** (1 gate shorter than the previous 13-gate 9-root record!).

### 2. Shifted Pronic-Square Root Quadrupling with Intermediate Gate Reuse ($\tau = 13 \to 10$ roots!)
For $q = x(x+1)$ (pronic values $p_k = k(k+1) \in \{0, 2, 6, 12, 20, 30, \dots\}$), the center $a = 16 = 4^2 = 2^4$ has **two** symmetric pronic pairs:
$$2 \cdot 16 = 32 = 2 + 30 = 12 + 20,$$
corresponding to $d_1 = 14$ and $d_2 = 4$ (note $d_2^2 = 16 = a$ costs **0 extra gates**, and $d_1 = 16 - 2$ costs only **1 subtraction**!). Thus:
- $(q - 16)^2 - 14^2 = (q - 2)(q - 30)$ gives **4 roots** $\{-6, -2, 1, 5\}$,
- $(q - 16)^2 - 16 = (q - 12)(q - 20)$ gives **4 roots** $\{-5, -4, 3, 4\}$,
- Multiplying by the **already-computed gate** $g_2 = q$ adds **2 more roots** $\{-1, 0\}$ in **1 single gate**!

Total: **10 distinct integer roots** in **13 gates** (degree 10)!
Furthermore, because $g_3 = 2$ is already in the DAG, appending `g14 = x - g3; g15 = g13 * g14` immediately yields **11 distinct integer roots** in **15 gates**!

---

## Verified Record Witnesses (100% Exact Arithmetic)

### $\tau = 11$ — 8 Distinct Integer Roots (New Symmetric Midpoint Family)
- **Roots (8):** `[-4, -3, -2, -1, 1, 2, 3, 4]`
- **Degree:** 8
- **SLP:**
  ```
  g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4;
  g6 = g1 * g1; g7 = g6 * g6; g8 = g2 - g7; g9 = g5 * g8; g10 = g3 - g8;
  g11 = g9 * g10
  ```
- **Polynomial:** $2x^8 - 60x^6 + 546x^4 - 1640x^2 + 1152$

### $\tau = 12$ — 9 Distinct Integer Roots (**NEW RECORD**, +1 over previous 8)
- **Roots (9):** `[-4, -3, -2, -1, 0, 1, 2, 3, 4]`
- **Degree:** 9
- **SLP:**
  ```
  g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4;
  g6 = g1 * g1; g7 = g6 * g6; g8 = g2 - g7; g9 = g5 * g8; g10 = g3 - g8;
  g11 = g9 * g10; g12 = x * g11
  ```
- **Polynomial:** $2x^9 - 60x^7 + 546x^5 - 1640x^3 + 1152x$

### $\tau = 13$ — 10 Distinct Integer Roots (**NEW RECORD**, +1 over previous 9)
- **Roots (10):** `[-6, -5, -4, -2, -1, 0, 1, 3, 4, 5]`
- **Degree:** 10
- **SLP:**
  ```
  g1 = 1 + x; g2 = x * g1; g3 = 1 + 1; g4 = g3 + g3; g5 = g4 * g4;
  g6 = g2 - g5; g7 = g6 * g6; g8 = g5 - g3; g9 = g8 * g8; g10 = g7 - g9;
  g11 = g7 - g5; g12 = g10 * g11; g13 = g12 * g2
  ```
- **Polynomial:** $x^{10} + 5x^9 - 54x^8 - 246x^7 + 945x^6 + 3717x^5 - 5692x^4 - 17876x^3 + 4800x^2 + 14400x$

### $\tau = 14$ — 10 Distinct Integer Roots (Consecutive Pronic-5 Family)
- **Roots (10):** `[-5, -4, -3, -2, -1, 0, 1, 2, 3, 4]`
- **Degree:** 10
- **SLP:**
  ```
  g1 = 1 + 1; g2 = 1 + x; g3 = g1 + g1; g4 = x * g2; g5 = g1 - g4;
  g6 = g3 + g5; g7 = g4 * g5; g8 = g6 * g7; g9 = g1 + g3; g10 = g6 + g9;
  g11 = g8 * g10; g12 = g3 + g3; g13 = g10 + g12; g14 = g11 * g13
  ```
- **Polynomial:** $x^{10} + 5x^9 - 30x^8 - 150x^7 + 273x^6 + 1365x^5 - 820x^4 - 4100x^3 + 576x^2 + 2880x$

### Bonus $\tau = 15$ — 11 Distinct Integer Roots
- **Roots (11):** `[-6, -5, -4, -2, -1, 0, 1, 2, 3, 4, 5]`
- **Degree:** 11
- **SLP:**
  ```
  g1 = 1 + x; g2 = x * g1; g3 = 1 + 1; g4 = g3 + g3; g5 = g4 * g4;
  g6 = g2 - g5; g7 = g6 * g6; g8 = g5 - g3; g9 = g8 * g8; g10 = g7 - g9;
  g11 = g7 - g5; g12 = g10 * g11; g13 = g12 * g2; g14 = x - g3; g15 = g13 * g14
  ```
- **Polynomial:** $x^{11} + 3x^{10} - 64x^9 - 138x^8 + 1437x^7 + 1827x^6 - 13126x^5 - 6492x^4 + 40552x^3 + 4800x^2 - 28800x$

---

## Negative / Exhaustive Search Evidence

1. **Exhaustive pure composition bounds (`tau_records_fast compose 8 12`):**
   Exhaustively searching all canonical outer SLPs $P(y)$ of length $\tau_P \le 8$ (1.53B leaves per $Q$) over 14 inner polynomials $Q(x)$ (`x^2`, `x(x+1)`, `x^2-2`, `q-2`, `(x^2-2)^2`, `x(x^2-1)`, `x^2-(2-x^2)^2`, `q(q-2)`, `(q-4)^2`, `(x^2-5)^2`, `(x^2-10)^2`, `(q-16)^2`, `(x^2-17)^2`, `(x^2-25)^2`) found **no** pure composition beating our new ladder. Crucially, this highlights why **intermediate gate reuse** (reusing `q`, `2`, `16`, and `2 - x^2` across factors) is essential for our $\tau = 12$ and $\tau = 13$ breakthroughs.
2. **Seeded exhaustive extensions (`tau_records_fast extend`):**
   - `tau6_5r -> tau=10`: 200.6M leaves, max = 7 roots.
   - `tau8_6r -> tau=10, 11`: 4.4M leaves, max = 7, 8 roots.
   - `tau9_mid_pre -> tau=12, 13`: 2.01B leaves, max = 9, 9 roots.
   - `tau10_psq_pre -> tau=13, 14`: 3.79B leaves, max = 10, 10 roots.
   - `tau11_8r_mid -> tau=14` & `tau11_8r_q -> tau=14`: ~20M leaves each, max = 10 roots.
3. **Local 1-gate & 2-gate mutations (`tau_records_fast mutate`):**
   Over 3.7M mutations around all elite $\tau = 10 \dots 14$ witnesses confirmed local optimality of the new ladder.

## Reproducing
```bash
# Exact Python verification & structured algebraic search
python3 experiments/pvsnp/tau/tau_records_10_14.py

# C accelerator (12 threads)
clang -O3 -march=native -pthread -o /tmp/tau_records_fast experiments/pvsnp/tau/tau_records_fast.c
/tmp/tau_records_fast compose 8 12
/tmp/tau_records_fast beam 14 40000 12
/tmp/tau_records_fast extend
/tmp/tau_records_fast mutate
```
