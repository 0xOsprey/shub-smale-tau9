# `shub-smale-tau9`: Hardened $`z_{\max}(9) = 6`$ Certification, Lean 4 Soundness Proofs, and Record Witnesses up to $`\tau = 18`$

**Resolving the 7-Root Threshold of Smale's 4th Problem (the Shub–Smale $`\tau`$-Conjecture)**

## Overview

The **Shub–Smale $`\tau`$-conjecture** (Smale's 4th Problem) asserts that the number of distinct integer roots $`z_{\mathbb{Z}}(f)`$ of any nonzero univariate polynomial $`f \in \mathbb{Z}[x]`$ is bounded polynomially in its constant-free straight-line program (SLP) complexity $`\tau(f)`$ (using only inputs $`\{1, x\}`$ and operations $`\{+, -, \times\}`$). An affirmative resolution implies $`\mathrm{P}_{\mathbb{C}} \neq \mathrm{NP}_{\mathbb{C}}`$ in the Blum–Shub–Smale (BSS) model of computation.

In August 2026, Santibáñez-Leal established the exact census $`z_{\max}(1 \dots 8) = (1, 2, 3, 3, 4, 5, 5, 6)`$ together with $`z_{\max}(10) \ge 7`$, and in an updated revision ruled out 9-gate SLPs ending in a multiplication gate — leaving open whether additive or subtractive final gates at $`\tau = 9`$ can achieve 7 distinct integer roots.

> **Honest scope note:** This work does **not** resolve P vs NP or the full asymptotic $`\tau`$-conjecture. It settles the unrestricted $`\tau = 9`$ frontier over all of $`\mathbb{Z}`$, introduces new finite-$`\tau`$ record witnesses for $`\tau = 11 \dots 18`$, and provides a zero-`sorry` Lean 4.36.0 formalization of canonicalization and per-leaf certificate soundness (leaving only the raw C enumeration loop outside the Lean kernel).
>
> **AI & provenance disclosure:** This repository (Lean 4 formalization, C/Rust/Python certifiers, and LaTeX draft) was developed with AI assistance (**Antigravity Harness + Gemini 4 Neon**) and audited via independent adversarial review, a separate naive Rust enumerator, `python-flint`, mutation testing, and Lean 4 kernel checks (`0 sorryAx`, standard axioms only). Every bug and overclaim found during auditing is transparently logged in [`audit/BUGS.md`](audit/BUGS.md).

---

## Main Results

1. **Hardened Exact-CRT Certification of $`z_{\max}(9) = 6`$ over all of $`\mathbb{Z}`$ (zero root-magnitude cutoff, zero hash-collision trust):**
   - Exhaustively certified all **59,308,136,697** canonical 9-gate SLPs (`7,767,649,524` total internal nodes = `529` split-prefix nodes + `7,767,648,995` worker internal nodes; see `audit/BUGS.md` item `R2`) across all final-gate operations $`\{+, -, \times\}`$:
     - **Hardened Exact-CRT Stage 1 (`experiments/pvsnp/tau/tau_certify_exact.c`, 442.6s on 8 cores / 384.2s on 12 cores):** Confirms **every** hash hit (all `1,432,372,962` internal/leaf dup hits and `207,134,139` per-item survivor dedup hits) by exact multi-point CRT over 61-bit primes (`Q > 4 * |coeff|`), recording **0 false positives** and matching all original counters bit-for-bit.
     - **Dual Independent Exact $`\mathbb{Z}[x]`$ Verification (`verify_survivors.py` + `audit/flint_roots.py`):** All **28,755,668** per-item exact-deduped survivors (corresponding to `11,040,213` globally unique survivors) passed both pure arbitrary-precision Python $`\mathbb{Z}[x]`$ Hensel lifting (`175.4s`, `0` counterexamples, `accounting_check=PASS`) and independent `python-flint` `fmpz_poly.factor()` (`max_z = 6`, `0` hits above `6`).
     - **Disjoint `-DALT_PRIMES` Cross-Check:** Re-running $\tau = 9, K = 6$ with a disjoint prime triple (`2147483629, 1000000021, 1000000033`) and disjoint evaluation points reproduced every counter on every one of the 485 work items (`per-item diff == 0`, `0` false positives). *(Earlier fixed-point Schwartz–Zippel / `<10^{-40}` probability claims were removed during audit; exact CRT confirmation eliminates hash-collision reliance deterministically.)*
     - **Independent Naive Rust Cross-Check (`audit/naive_tau`):** A deliberately naive Rust enumerator (no sign symmetry, no operand ordering, no gate-order canonicalization; exact `i128`/`BigInt` arithmetic) independently reproduced $`z_{\max}(1 \dots 7) = (1, 2, 3, 3, 4, 5, 5)`$ and matched the C enumerator's exact polynomial set $`|\mathrm{New}^\pm(\tau)|`$ for every $`\tau \le 7`$ (all `1,092,330` classes at $`\tau = 7`$: `0` missing, `0` extra). Canonical membership testing passed `1,000,000 / 1,000,000` at $`\tau = 9`$ and `200,000 / 200,000` at $`\tau = 10`$.
   - Combined with $`z_{\max}(10) \ge 7`$, this settles the **7-root threshold at $`\tau = 10`$**:

```math
z_{\max}(1 \dots 9) = (1, 2, 3, 3, 4, 5, 5, 6, 6), \qquad z_{\max}(10) \ge 7.
```

2. **New Record Finite-$`\tau`$ Witnesses up to $`\tau = 18`$ (100% Lean 4 & Exact-`int` Verified):**

| $`\tau`$ | Distinct Integer Roots | Construction / Mechanism | Lean 4 Theorem |
| :---: | :---: | :--- | :--- |
| **6** | **5** (exact) | $`-x(x^2-1)(x^2-4)`$ | `tau_witness_6_five` |
| **8** | **6** (exact) | $`q(q-2)(q-6)`$, $`q = x^2 - x`$ | `tau_witness_8` |
| **9** | **6** (exact, new) | Unconditional exhaustive census over all $`\mathbb{Z}`$ | — |
| **10** | $`\ge 7`$ | $`-x(x^2-1)(x^2-4)(x^2-9)`$ & pronic | `tau_witness_10_seven` |
| **11** | $`\ge 8`$ *(new sym. family)* | Symmetric midpoint (`{-4..-1, 1..4}`) & pronic | `tau_record_11_eight_sym` |
| **12** | $`\ge 9`$ *(new record)* | **Midpoint Difference Trick** (`{-4..4}`) | `tau_record_12_nine` |
| **13** | $`\ge 10`$ *(new record)* | **Shifted Pronic-Square** (slope $`10/13 \approx 0.769`$) | `tau_record_13_ten` |
| **15** | $`\ge 11`$ *(new record)* | Shifted Pronic-Square $`\times (x - 2)`$ | `tau_record_15_eleven` |
| **16** | $`\ge 12`$ *(new record)* | Shifted Pronic-Square ($`a = 36`$) $`\times (q-2)(q-6)`$ | `tau_record_16_twelve` |
| **17** | $`\ge 13`$ *(new record)* | **Square-Extraction Trick** ($`x + 196`$, $`x^2 - 196`$) | `tau_record_17_thirteen` |
| **18** | $`\ge 14`$ *(new record)* | **Pronic Self-Shift Identity** ($`a + a^2 = a(a+1)`$) | `tau_record_18_fourteen` |

3. **Exact Bounded-Multiplication Sharpness ($`m \in \{0, 1, 2, 3, 4\}`$):**
   - Proved in Lean 4 (`bounded_mult_exact_sharpness_four`) that the trivial degree ceiling $`\max_{\mathrm{mulCount}(P) \le m} z_{\mathbb{Z}}(P) = 2^m`$ is **exact and sharp** for all $`m \in \{0, 1, 2, 3, 4\}`$ (`1, 2, 4, 8, 16`), including an explicit **4-multiplication** 4-level iterated fold achieving **16 distinct integer roots** (`tau_four_mul_sharp`, arising from the primitive Gaussian-integer norm $`67{,}405 = 5 \cdot 13 \cdot 17 \cdot 61`$). *Caveat:* this bounds multiplication gates only (all `×` gates counted; constants are built from `1` by addition chains with zero multiplications, so `τ` is large). It is classical-in-spirit iterated folding and does not improve any finite-`τ` record.

4. **Machine-Verified Lean 4.36.0 Formalization (8 modules, 4,228 LOC, 204 theorem/lemma declarations, `0 sorryAx`, strictly `{propext, Classical.choice, Quot.sound}`):**
   - `Research/PvsNP/Tau/TauConjecture.lean` (344 LOC) — Constant-free `SLP`, `ShubSmaleTauConjecture`, degree & multiplication root bounds, computable `zMaxGe_of_evalInt` witness certifier.
   - `Research/PvsNP/Tau/TauWitnesses.lean` (114 LOC) — Verified witnesses for $`\tau = 6, 10, 11, 13`$ and 2-multiplication bound.
   - `Research/PvsNP/Tau/ModularRootBound.lean` (338 LOC) — Unconditional proof of the **Simple-Root Modular Certificate** (`intRootCount_le_of_eval_zmod`) over all of $`\mathbb{Z}`$ and formalization of the classical pronic linear baseline `zMaxGe (3 * k) (2 * k)`.
   - `Research/PvsNP/Tau/TauRecords.lean` (97 LOC) — Machine-verified new records for $`\tau = 11, 12, 13, 15`$.
   - `Research/PvsNP/Tau/BoundedMult.lean` (158 LOC) — Exact sharpness for $`m = 0, 1, 2, 3`$ (`1, 2, 4, 8` roots via `((x(x+1)-16)^2 - 106)^2 - 8100`).
   - `Research/PvsNP/Tau/FoldingRecords.lean` (350 LOC) — Zero-multiplication binary addition chains, exact sharpness for $`m = 4`$ (`16` roots), and new records for $`\tau = 16, 17, 18`$.
   - `Research/PvsNP/Tau/Canonical.lean` (1,844 LOC) — Formal soundness of all canonicalization and dead-gate pruning rules (`exists_canonical`, `deadgate_count_bound`, `unusedWires_last_gate`, `zmax9_le_six_of_checklist`, `zmax10_le_seven_of_checklist`).
   - `Research/PvsNP/Tau/CertSoundness.lean` (983 LOC) — Formal soundness of degree propagation, atomic product-mask union bound, dual-number modular evaluation, Taylor-stripped modular certificate, hash-mismatch inequality, and exact CRT zero certification.

---

## Repository Layout

- `paper/tau_conjecture_z9.pdf` & `paper/tau_conjecture_z9.tex` — Complete compiled PDF & LaTeX paper with full proofs, census tables, soundness audit, and reproducibility commands.
- `audit/` — Adversarial red-team audits (`RED_TEAM_AUDIT.md`, `RED_TEAM_AUDIT_EXACT.md`), bug/overclaim log (`BUGS.md`), Phase 1 audit report (`PHASE1_REPORT.md`), independent naive Rust enumerator (`naive_tau/`), independent `python-flint` root counter (`flint_roots.py`), and mutation/canary suite (`mutation/`).
- `reproduce/` — Tiered reproduction script (`reproduce.sh`) and expected counters (`EXPECTED_OUTPUTS.md`).
- `outreach/` — Draft correspondence and social summary (prepared for review).
- `OEIS_SUBMISSION.txt` — OEIS draft for `1, 2, 3, 3, 4, 5, 5, 6, 6`.
- `Research/PvsNP/Tau/` — Lean 4.36.0 + Mathlib v4.36.0 formalization (8 modules, 4,228 LOC, 204 theorems/lemmas, `0 sorry`).
- `experiments/pvsnp/tau/` — Hardened exact-CRT certifier (`tau_certify_exact.c`, `verify_survivors.py`, `EXACT_PIPELINE.md`) alongside original provenance files (`tau_z9_unconditional.c`, `verify_z9_all_Z.py`, `z9_unconditional_report.md`, `records_report.md`).

---

## Quick Reproduction

### 1. Build & Verify Lean 4 Proofs
```bash
lake exe cache get
lake build Research
```

### 2. Run Tiered Verification (`quick` ~3 min / `tau9` ~15 min on 12 cores)
```bash
./reproduce/reproduce.sh quick
./reproduce/reproduce.sh tau9
```
