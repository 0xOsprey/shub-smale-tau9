# `shub-smale-tau9`: Unconditional $`z_{\max}(9) = 6`$, New Record Witnesses up to $`\tau = 15`$, and Lean 4 Certification

**Resolving the 7-Root Threshold of Smale's 4th Problem (the Shub–Smale $`\tau`$-Conjecture)**

## Overview

The **Shub–Smale $`\tau`$-conjecture** (Smale's 4th Problem) asserts that the number of distinct integer roots $`z_{\mathbb{Z}}(f)`$ of any nonzero univariate polynomial $`f \in \mathbb{Z}[x]`$ is bounded polynomially in its constant-free straight-line program (SLP) complexity $`\tau(f)`$ (using only inputs $`\{1, x\}`$ and operations $`\{+, -, \times\}`$). An affirmative resolution implies $`\mathrm{P}_{\mathbb{C}} \neq \mathrm{NP}_{\mathbb{C}}`$ in the Blum–Shub–Smale (BSS) model of computation.

In August 2026, Santibáñez-Leal established the exact census $`z_{\max}(1 \dots 8) = (1, 2, 3, 3, 4, 5, 5, 6)`$ together with $`z_{\max}(10) \ge 7`$, and in an updated revision ruled out 9-gate SLPs ending in a multiplication gate — leaving open whether additive or subtractive final gates at $`\tau = 9`$ can achieve 7 distinct integer roots.

> **Honest scope note:** This work does **not** resolve P vs NP or the full asymptotic $`\tau`$-conjecture. It settles the unrestricted $`\tau = 9`$ frontier unconditionally over all of $`\mathbb{Z}`$, introduces new finite-$`\tau`$ record witnesses for $`\tau = 11, 12, 13, 15`$, and provides a zero-`sorry` Lean 4.36.0 formalization.

---

## Main Results

1. **Unconditional $`z_{\max}(9) = 6`$ over all of $`\mathbb{Z}`$ (zero root-magnitude cutoff):**
   - Exhaustively certified all **59,308,136,697** canonical 9-gate SLPs (`7,767,648,995` internal nodes) across all final-gate operations $`\{+, -, \times\}`$ in **489.6s** on 12 CPU cores:
     - **Stage 1 (`tau_z9_unconditional.c`, 399.671s):** Certified 99.6023% of leaves via exact degree bounds, atomic product-factor union bounds, the Lean-verified Simple-Root Modular Certificate ($`\mathbb{Z} \to \mathbb{F}_p`$), and Taylor-stripped modular certificates.
     - **Stage 2 (`verify_z9_all_Z.py`, 89.928s):** Verified all **11,040,213** unique surviving polynomials in exact arbitrary-precision $`\mathbb{Z}[x]`$ via squarefree primitive PRS and exact Hensel lifting past $`2 \cdot \mathrm{CauchyBound}(g)`$ — **`0` counterexamples**.
   - Combined with $`z_{\max}(10) \ge 7`$, this settles the **7-root threshold at $`\tau = 10`$**:

```math
z_{\max}(1 \dots 9) = (1, 2, 3, 3, 4, 5, 5, 6, 6), \qquad z_{\max}(10) \ge 7.
```

2. **New Record Finite-$`\tau`$ Witnesses up to $`\tau = 15`$ (100% Lean 4 & Exact-`int` Verified):**

| $`\tau`$ | Distinct Integer Roots | Construction / Mechanism | Lean 4 Theorem |
| :---: | :---: | :--- | :--- |
| **6** | **5** (exact) | $`-x(x^2-1)(x^2-4)`$ | `tau_witness_6_five` |
| **8** | **6** (exact) | $`q(q-2)(q-6)`$, $`q = x^2 - x`$ | `tau_witness_8` |
| **9** | **6** (exact, new) | Unconditional exhaustive census over all $`\mathbb{Z}`$ | — |
| **10** | $`\ge 7`$ | $`-x(x^2-1)(x^2-4)(x^2-9)`$ & pronic | `tau_witness_10_seven` |
| **11** | $`\ge 8`$ *(new sym. family)* | Symmetric midpoint (`{-4..-1, 1..4}`) & pronic | `tau_record_11_eight_sym` |
| **12** | $`\ge 9`$ *(new record)* | **Midpoint Difference Trick** (`{-4..4}`) | `tau_record_12_nine` |
| **13** | $`\ge 10`$ *(new record)* | **Shifted Pronic-Square** (slope $`10/13 \approx 0.769`$) | `tau_record_13_ten` |
| **15** | $`\ge 11`$ *(bonus record)* | Shifted Pronic-Square $`\times (x - 2)`$ | `tau_record_15_eleven` |

3. **Machine-Verified Lean 4.36.0 Formalization (`0 sorryAx`, strictly `{propext, Classical.choice, Quot.sound}`):**
   - `Research/PvsNP/Tau/TauConjecture.lean` — Constant-free `SLP`, `ShubSmaleTauConjecture`, degree & multiplication root bounds, computable `zMaxGe_of_evalInt` witness certifier.
   - `Research/PvsNP/Tau/TauWitnesses.lean` — Verified witnesses for $`\tau = 6, 10, 11, 13`$ and 2-multiplication bound.
   - `Research/PvsNP/Tau/ModularRootBound.lean` — Unconditional proof of the **Simple-Root Modular Certificate** (`intRootCount_le_of_eval_zmod`) over all of $`\mathbb{Z}`$ and formalization of the classical pronic linear baseline `zMaxGe (3 * k) (2 * k)`.
   - `Research/PvsNP/Tau/TauRecords.lean` — Machine-verified new records for $`\tau = 11, 12, 13, 15`$.

---

## Repository Layout

- `paper/tau_conjecture_z9.tex` — Complete LaTeX paper with full proofs, census tables, soundness/collision audit, and reproducibility commands.
- `Research/PvsNP/Tau/` — Lean 4.36.0 + Mathlib v4.36.0 formalization (4 modules, 893 LOC, `0 sorry`).
- `experiments/pvsnp/tau/` — C/Python certifiers and reports (`tau_z9_unconditional.c`, `verify_z9_all_Z.py`, `tau_records_10_14.py`, `z9_unconditional_report.md`, `records_report.md`).

---

## Quick Reproduction

### 1. Build & Verify Lean 4 Proofs
```bash
lake exe cache get Research/PvsNP/Tau/TauRecords.lean
lake build Research
```

### 2. Verify All Record Witnesses ($`\tau = 1 \dots 15`$) in Exact Python `int`
```bash
python3 experiments/pvsnp/tau/tau_search.py
python3 experiments/pvsnp/tau/tau_records_10_14.py
```

### 3. Run the Unconditional $`\tau = 9`$ Census Over All of $`\mathbb{Z}`$
```bash
cd experiments/pvsnp/tau
cc -O3 -march=native -pthread tau_z9_unconditional.c -o tau_z9_unconditional
./tau_z9_unconditional 9 6 /tmp/z9_survivors.bin
python3 verify_z9_all_Z.py /tmp/z9_survivors.bin
```
