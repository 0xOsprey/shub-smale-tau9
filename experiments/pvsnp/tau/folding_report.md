# Track B Report: Iterated Folding, High-$\tau$ Records ($\tau = 14 \dots 18$), and $m = 4$ Multiplication Root Proliferation (`2^4 = 16` Roots!)

## Executive Summary

We attacked two frontier problems on Smale's 4th Problem (the Shub–Smale $\tau$-Conjecture) via [tau_iterated_folding.py](file:///Users/joe/github/gemini-neon/experiments/pvsnp/tau/tau_iterated_folding.py), with **100% exact arbitrary-precision Python `int` verification** (`eval_slp_exact`, exact `f(r) = 0`, exact synthetic division by $\prod_r (x - r)$, nonzero check, exact $\tau$, and exact `mulCount`):

1. **OPEN DIOPHANTINE QUESTION SOLVED AFFIRMATIVELY (`m = 4` Multiplications Hits Exact Degree Ceiling `2^4 = 16` Roots!):**
   - A **4-multiplication** constant-free SLP (`mulCount = 4`) **CAN** achieve the exact degree ceiling **$2^4 = 16$ distinct integer roots** via 4-level iterated folding!
   - We discovered **6 distinct 16-root 4-level folding solutions** for $a \le 200{,}000$, arising from two primitive Gaussian-integer norm solutions ($N = 67{,}405 = 5 \cdot 13 \cdot 17 \cdot 61$ and $N = 600{,}445$).
   - The smallest pronic solution ($a = 16{,}851$) gives an all-integer-constant 4-level fold with **`mulCount = 4`**, **degree = 16**, and **16 distinct integer roots** `[-184, -180, -177, -172, -66, -51, -39, -6, 5, 38, 50, 65, 171, 176, 179, 183]`.
   - The smallest square solution ($S = 67{,}405$) gives a symmetric 4-level fold with **`mulCount = 4`**, **degree = 16**, and **16 distinct integer roots** `[-237, -227, -218, -189, -178, -141, -126, -106, 106, 126, 141, 178, 189, 218, 227, 237]`.
2. **New High-$\tau$ Record Ladder ($\tau = 16, 17, 18$) + Three New Algebraic Mechanisms:**
   - **$\tau = 15$**: new consecutive symmetric witness with all 11 roots `{-5, ..., 5}` via scaled midpoint shift `g9 + 32 = 2(25 - x^2)`.
   - **$\tau = 16$**: **$\ge 12$ roots** (**NEW RECORD**), via `pronic(a=36)` with free DAG-constant reuse `(q - 2)(q - 6)`.
   - **$\tau = 17$**: **$\ge 13$ roots** (**NEW RECORD**), via the new **`q - (x + c^2) = x^2 - c^2` Square-Extraction Trick** (+3 roots in 4 gates on the $\tau = 13$ witness!).
   - **$\tau = 18$**: **$\ge 14$ roots** (**NEW RECORD**), via the new **`(q - a) - a^2 = q - a(a+1)` Pronic-Square Self-Shift Identity** (+2 roots in 2 gates on the $\tau = 16$ witness!).

---

## Mission 2: `m = 4` Multiplications Achieves `2^4 = 16` Distinct Integer Roots

### Exact Diophantine Reduction
Consider a 4-level iterated squaring polynomial using **4 multiplications** (1 for $q(x) \in \{x(x+1), x^2\}$ and 3 for the outer squarings; all constants and doublings $2g = g + g$ use only `+` and `-`, contributing **0 multiplications**):
$$f(x) = \Big(\big((2q(x) - S)^2 - b\big)^2 - c\Big)^2 - e^2.$$
For $f(x)$ to split into 16 distinct integer roots, $S$ must have 4 valid pairs $(q_{i,1}, q_{i,2})$ summing to $S$ whose differences $D_i = |q_{i,1} - q_{i,2}|$ ($D_1 < D_2 < D_3 < D_4$) satisfy:
$$D_1^2 + D_4^2 = D_2^2 + D_3^2 = 2b.$$
For $q = x^2$ ($S = x_i^2 + y_i^2$) and $q = x(x+1)$ ($4S + 2 = (2k_{i,1}+1)^2 + (2k_{i,2}+1)^2$), substituting $D_i^2 = N^2 - 4(x_i y_i)^2$ cancels $N^2$ and reduces the 4-level folding condition to the **quartic product-sum identity**:
$$N = x_i^2 + y_i^2 \quad (i = 1, 2, 3, 4) \qquad \text{with} \qquad (x_1 y_1)^2 + (x_4 y_4)^2 = (x_2 y_2)^2 + (x_3 y_3)^2.$$

### Exhaustive Census for $a \le 200{,}000$ ($S \le 400{,}000$)
| Family | Values $q \le 400{,}000$ | Max pairs at one $S$ | $S$ with $\ge 4$ pairs | **16-root solutions** | 15-root | 14-root | 12-root (AP3) |
|---|---:|---:|---:|:---:|:---:|:---:|:---:|
| $q = x(x+1)$ | 632 | 12 | 9,589 | **3** | 0 | 0 | 0 |
| $q = x^2$ | 633 | 12 | 7,929 | **3** | 0 | 0 | 0 |

All **6 solutions** found for $a \le 200{,}000$:
1. **`q = x(x+1)`, $S = 33{,}702$ ($a = 16{,}851$)** — *primitive pronic solution* ($4S + 2 = 134{,}810 = 2 \cdot 5 \cdot 13 \cdot 17 \cdot 61$)
   - Pairs: `(30, 33672)`, `(1482, 32220)`, `(2550, 31152)`, `(4290, 29412)`
   - Half-differences: $d = [12561, 14301, 15369, 16821]$, $12561^2 + 16821^2 = 14301^2 + 15369^2 = 440{,}724{,}762 = 2 \cdot 220{,}362{,}381$.
2. **`q = x^2`, $S = 67{,}405$ ($a = 33{,}702.5$)** — *primitive square solution* ($67{,}405 = 5 \cdot 13 \cdot 17 \cdot 61$)
   - Pairs: `(11236, 56169)`, `(15876, 51529)`, `(19881, 47524)`, `(31684, 35721)`
   - Differences: $D = [4037, 27643, 35653, 44933]$, $4037^2 + 44933^2 = 27643^2 + 35653^2 = 2{,}035{,}271{,}858 = 2 \cdot 1{,}017{,}635{,}929$.
3. **`q = x^2`, $S = 134{,}810$** — $2 \times$ solution #2 (odd-square pairs of $134{,}810$).
4. **`q = x^2`, $S = 269{,}620$** — $4 \times$ solution #2.
5. **`q = x(x+1)`, $S = 300{,}222$ ($a = 150{,}111$)** — *second independent primitive solution* ($4S + 2 = 1{,}200{,}890 = 2 \cdot 600{,}445$).
   - Pairs: `(4830, 295392)`, `(25122, 275100)`, `(73170, 227052)`, `(129240, 170982)`.
6. **`q = x(x+1)`, $S = 303{,}322$ ($a = 151{,}661$)** — $9 \times$ solution #1 ($4S + 2 = 9 \cdot 134{,}810$).

### 100% Exact-Verified `m = 4` Witnesses

#### 1. Pronic 16-Root `m = 4` Witness (`mulCount = 4`, degree = 16, 16 distinct integer roots!)
$$f(x) = \Big(\big(((x(x+1) - 16851)^2 - 220362381)^2 - 2083869931842000\big)^2 - 1832844567153600^2\Big)$$
- **Exact `mulCount`:** `4` (`x*(x+1)`, `(q - 16851)^2`, `((q - 16851)^2 - 220362381)^2`, `(... - 2083869931842000)^2`; all constants synthesized by `+` only with shared powers of 2, total $\tau = 198$).
- **Exact Degree:** `16` ($= 2^4$).
- **Verified Integer Roots (16):** `[-184, -180, -177, -172, -66, -51, -39, -6, 5, 38, 50, 65, 171, 176, 179, 183]`.

#### 2. Square 16-Root `m = 4` Witness (`mulCount = 4`, degree = 16, 16 distinct integer roots!)
$$f(x) = \Big(\big(((2x^2 - 67405)^2 - 1017635929)^2 - 533470702551552000\big)^2 - 469208209191321600^2\Big)$$
- **Exact `mulCount`:** `4` (total $\tau = 218$ with add-only constants).
- **Exact Degree:** `16` ($= 2^4$).
- **Verified Integer Roots (16):** `[-237, -227, -218, -189, -178, -141, -126, -106, 106, 126, 141, 178, 189, 218, 227, 237]`.

---

## Mission 1: High-$\tau$ Record Ladder ($\tau = 14, 15, 16, 17, 18$)

### Updated Record Table (100% Exact Arithmetic Verified)

| $\tau$ | Standing Best | **New Verified Record** | Degree | `mulCount` | Key Construction |
|---:|:---:|:---:|:---:|:---:|---|
| **11** | $\ge 8$ | **$\ge 8$** | 8 | 5 | Midpoint Difference Trick (`roots = {-4..-1, 1..4}`) |
| **12** | $\ge 9$ | **$\ge 9$** | 9 | 6 | Midpoint Difference Trick $\times x$ (`roots = {-4..4}`) |
| **13** | $\ge 10$ | **$\ge 10$** | 10 | 6 | Shifted Pronic-Square `q((q-16)^2 - 14^2)((q-16)^2 - 4^2)` |
| **14** | $\ge 10$ | **$\ge 10$** | 10 | 7 | `pronic(a=36)` base $\times (q - 2)$ *(new family)* |
| **15** | $\ge 11$ | **$\ge 11$** | 11 | 8 | **New consecutive symmetric family:** `tau=12 midpoint * (g9 + 32)` (`roots = {-5..5}`) |
| **16** | *(unlisted)* | **$\ge 12$** (**NEW**) | 12 | 8 | `((q-36)^2 - 36)((q-36)^2 - 36^2)(q - 2)(q - 6)` |
| **17** | *(unlisted)* | **$\ge 13$** (**NEW**) | 13 | 8 | **Square-Extraction Trick:** `tau=13 * (x + 196) * (q - (x + 196))` |
| **18** | *(unlisted)* | **$\ge 14$** (**NEW**) | 14 | 9 | **Pronic Self-Shift Identity:** `tau=16 * ((q - 36) - 36^2)` |

### Three New Algebraic Mechanisms Discovered

1. **The Pronic-Square Self-Shift Identity ($\tau = 16 \to 18$, +2 roots in 2 gates!):**
   For ANY center $a$ where $2a$ is pronic (e.g., $a = 36$, $2a = 72 = 8 \cdot 9$), the shifted pronic-square SLP already computes both $g_7 = q - a$ and $g_{10} = a^2$ (to form $(q - a)^2 - a^2 = q(q - 2a)$). Because $a + a^2 = a(a + 1)$ is **always a pronic number**, a single subtraction yields two brand-new roots $\{a, -(a+1)\}$:
   $$g_{17} = g_7 - g_{10} = (q - 36) - 1296 = q - 1332 = (x - 36)(x + 37).$$
   Combined with the free DAG constants $2$ (`g3`) and $6$ (`g5`), the 12-gate 8-root base at $a = 36$ gains **+6 roots in 6 gates** (`(q-2)(q-6)(q-1332)`), reaching **12 roots at $\tau = 16$** and **14 roots at $\tau = 18$**!

2. **The `q - (x + c^2) = x^2 - c^2` Square-Extraction Trick ($\tau = 13 \to 17$, +3 roots in 4 gates!):**
   In any pronic-square SLP containing $g_2 = q = x^2 + x$ and a square constant $c^2$ (such as $g_9 = 14^2 = 196$ in the $\tau = 13$ witness):
   - $g_{14} = x + c^2$ gives **+1 root** ($-c^2 = -196$) in 1 gate;
   - $g_{16} = q - g_{14} = (x^2 + x) - (x + c^2) = x^2 - c^2$ gives **+2 roots** ($\pm c = \pm 14$) in 1 gate!
   Multiplying both into the $\tau = 13$ (10-root) witness yields **13 distinct integer roots at $\tau = 17$** (`mulCount = 8`)!

3. **Scaled Midpoint Extension ($\tau = 12 \to 15$, all 11 consecutive roots `{-5..5}`):**
   In the $\tau = 12$ midpoint witness (`g2 = 2`, `g7 = 16`, `g9 = 18 - 2x^2`), computing `g13 = g2 * g7 = 32` and `g14 = g9 + g13 = 50 - 2x^2 = 2(25 - x^2)` adds roots $\pm 5$, giving all **11 consecutive roots `{-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5}`** in **15 gates**!

---

## Verified High-$\tau$ Record SLPs (Exact Arithmetic)

### $\tau = 15$ — 11 Consecutive Integer Roots `[-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5]`
- **Degree:** 11, **`mulCount`:** 8
- **SLP:**
  ```
  g1 = x * x; g2 = 1 + 1; g3 = g2 - g1; g4 = g3 * g3; g5 = g1 - g4;
  g6 = g2 + g2; g7 = g6 * g6; g8 = g1 - g7; g9 = g3 - g8; g10 = g5 * g8;
  g11 = g10 * g9; g12 = x * g11; g13 = g2 * g7; g14 = g9 + g13; g15 = g12 * g14
  ```

### $\tau = 16$ — 12 Distinct Integer Roots (**NEW RECORD**)
- **Roots (12):** `[-9, -7, -6, -3, -2, -1, 0, 1, 2, 5, 6, 8]`
- **Degree:** 12, **`mulCount`:** 8
- **SLP:**
  ```
  g1 = 1 + x; g2 = x * g1; g3 = 1 + 1; g4 = 1 + g3; g5 = g3 * g4;
  g6 = g5 * g5; g7 = g2 - g6; g8 = g7 * g7; g9 = g8 - g6; g10 = g6 * g6;
  g11 = g8 - g10; g12 = g9 * g11; g13 = g2 - g3; g14 = g12 * g13;
  g15 = g2 - g5; g16 = g14 * g15
  ```

### $\tau = 17$ — 13 Distinct Integer Roots (**NEW RECORD**)
- **Roots (13):** `[-196, -14, -6, -5, -4, -2, -1, 0, 1, 3, 4, 5, 14]`
- **Degree:** 13, **`mulCount`:** 8
- **SLP:**
  ```
  g1 = 1 + x; g2 = x * g1; g3 = 1 + 1; g4 = g3 + g3; g5 = g4 * g4;
  g6 = g2 - g5; g7 = g6 * g6; g8 = g5 - g3; g9 = g8 * g8; g10 = g7 - g9;
  g11 = g7 - g5; g12 = g10 * g11; g13 = g12 * g2; g14 = x + g9;
  g15 = g13 * g14; g16 = g2 - g14; g17 = g15 * g16
  ```

### $\tau = 18$ — 14 Distinct Integer Roots (**NEW RECORD**)
- **Roots (14):** `[-37, -9, -7, -6, -3, -2, -1, 0, 1, 2, 5, 6, 8, 36]`
- **Degree:** 14, **`mulCount`:** 9
- **SLP:**
  ```
  g1 = 1 + x; g2 = x * g1; g3 = 1 + 1; g4 = 1 + g3; g5 = g3 * g4;
  g6 = g5 * g5; g7 = g2 - g6; g8 = g7 * g7; g9 = g8 - g6; g10 = g6 * g6;
  g11 = g8 - g10; g12 = g9 * g11; g13 = g2 - g3; g14 = g12 * g13;
  g15 = g2 - g5; g16 = g14 * g15; g17 = g7 - g10; g18 = g16 * g17
  ```

---

## Reproducing
```bash
python3 experiments/pvsnp/tau/tau_iterated_folding.py
```
