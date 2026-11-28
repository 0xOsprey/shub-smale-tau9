# `shub-smale-tau9`: $`z_{\max}(9) = 6`$, $`z_{\max}(10) = 7`$, Records up to $`\tau = 18`$, and Lean 4 Soundness Proofs

[![Independent Lean 4 Receipt](https://img.shields.io/badge/isitsolved.com_Lean_4_Receipt-ACCEPTED-2ea043)](https://isitsolved.com/lean/receipts/31455fc47d7b)

**Settling the 7- and 8-root thresholds of Smale's 4th Problem (the Shub–Smale $`\tau`$-conjecture) over all of $`\mathbb{Z}`$.**

---

## TL;DR

- **NEW — Unconditional Lean 4 refutation of every sub-quadratic exponent $`c < 2`$:** Using a fraction-free Chirp-$`z`$ $`q`$-Pochhammer SLP and division-free Schönhage–Nussbaumer negacyclic FFT over $`\mathbb{Z}[x]`$, we prove completely inside Lean 4 (`tau_refutes_subquadratic`, `tau_subquadratic_growth`, `tau_crossover_1884_2049`):
  ```math
  z_{\max}(\tau) = \Omega\!\left(\frac{\tau^2}{\log^2 \tau \cdot (\log\log \tau)^2}\right), \qquad z_{\max}(1884) \ge 2049 > 1884,
  ```
  unconditionally refuting $`c = 1`$ and every real $`c < 2`$ in [`IIS-O-1205`](https://isitsolved.com/open/IIS-O-1205), alongside a Lean-verified $`2`$-adic exponential lower bound (`tau_padic_two_pow`: $`z_{\max}^{\mathbb{Z}_2}(4k) \ge 2^k`$) establishing a Local-vs-Global barrier and an unconditional real-root upper bound $`z_{\max}(\tau) \le 2^{\tau - (\sqrt{2}-o(1))\sqrt{\tau}}`$. See [`paper/tau_subquadratic_refutation.pdf`](paper/tau_subquadratic_refutation.pdf).
- **Exact finite-$`\tau`$ census:** Extending Santibáñez-Leal's 2026 census $`z_{\max}(1\dots 8) = (1, 2, 3, 3, 4, 5, 5, 6)`$, we establish over **all of $`\mathbb{Z}`$** (no root-magnitude cutoff, zero hash-collision reliance; published at [`iis:2611.00113`](https://isitsolved.com/journal/39b8a928ed68)):
  ```math
  z_{\max}(1 \dots 10) = (1, 2, 3, 3, 4, 5, 5, 6, 6, 7), \qquad z_{\max}(11) \ge 8.
  ```
- **Independent Lean 4 Receipt (`ACCEPTED`):** Built from source by third-party vetted node `spark-receipts` at [**isitsolved.com/lean/receipts/31455fc47d7b**](https://isitsolved.com/lean/receipts/31455fc47d7b) (`0 sorry`, `0` extra axioms beyond `{propext, Classical.choice, Quot.sound}`, `0 native_decide`; [proof map JSON](https://isitsolved.com/lean/receipts/31455fc47d7b/map.json)).
- **Constructive records:** Lean-verified witnesses pushing known finite-$`\tau`$ records through $`\tau = 18`$ ($`z_{\max}(12)\ge 9`$, $`z_{\max}(13)\ge 10`$, $`z_{\max}(15)\ge 11`$, $`z_{\max}(16)\ge 12`$, $`z_{\max}(17)\ge 13`$, $`z_{\max}(18)\ge 14`$) and exact bounded-multiplication sharpness $`\max_{\mathrm{mul}(P)\le m} z_{\mathbb{Z}}(P) = 2^m`$ for $`m \le 4`$.
- **Paper & quick audit:** Read [`paper/tau_conjecture_z9.pdf`](paper/tau_conjecture_z9.pdf), review the 5-minute external audit bundle [`audit/EXTERNAL_REVIEW_BUNDLE.md`](audit/EXTERNAL_REVIEW_BUNDLE.md), or run `./reproduce/reproduce.sh quick` (~1–3 min).

> **Honest scope note:** This work does **not** resolve P vs NP or the full asymptotic $`\tau`$-conjecture. Lean 4 proves the conditional implications `hcheck → z_max(τ) ≤ K` (where `hcheck` requires certifying all canonical gate lists of every shorter length $`1 \le n \le \tau`$), plus every per-leaf certificate and every lower-bound witness; the raw C enumeration loop (`tau_certify_exact.c`) and external `python-flint` / Python $`\mathbb{Z}[x]`$ runs remain outside the Lean kernel.
>
> **AI & provenance disclosure:** Developed with AI assistance (**Antigravity Harness + Gemini 4 Neon**) and audited via two red-team reviews, an independent naive Rust enumerator, `python-flint`, mutation testing, and an independent third-party Lean 4 build. Every bug and overclaim caught during auditing is transparently logged in [`audit/BUGS.md`](audit/BUGS.md).

---

## What Problem This Is

The **Shub–Smale $`\tau`$-conjecture** (Smale's 4th Problem; [`IIS-O-1205`](https://isitsolved.com/open/IIS-O-1205)) asks whether the number of distinct integer roots $`z_{\mathbb{Z}}(f)`$ of any nonzero univariate polynomial $`f \in \mathbb{Z}[x]`$ is bounded polynomially in its constant-free straight-line program (SLP) complexity $`\tau(f)`$ (built from $`\{1, x\}`$ using only $`\{+, -, \times\}`$). An affirmative resolution implies $`\mathrm{P}_{\mathbb{C}} \neq \mathrm{NP}_{\mathbb{C}}`$ in the Blum–Shub–Smale model.

In August/September 2026, **Felipe Santibáñez-Leal** established $`z_{\max}(1 \dots 8) = (1, 2, 3, 3, 4, 5, 5, 6)`$, proved $`z_{\max}(10) \ge 7`$, and ruled out multiplication-final 9-gate SLPs — leaving open additive/subtractive final gates at $`\tau = 9`$ and whether $`z_{\max}(10)`$ equals $`7`$ or $`8`$. This repository closes both unrestricted frontiers over all of $`\mathbb{Z}`$.

---

## Trust Boundary & Verification at a Glance

| Layer | Verified By | Status |
|---|---|---|
| Canonicalization, dead-gate bounds, checklist reduction (`zmax9_le_six_of_checklist`, `zmax10_le_seven_of_checklist`) | Lean 4.36.0 kernel + independent build ([receipt `31455fc47d7b`](https://isitsolved.com/lean/receipts/31455fc47d7b)) | **ACCEPTED** (`0 sorry`, standard axioms) |
| Per-leaf certificates (degree, product mask, dual-number mod $`p`$, Taylor-stripped mod $`p`$, exact CRT) | Lean 4.36.0 kernel + independent build ([receipt `31455fc47d7b`](https://isitsolved.com/lean/receipts/31455fc47d7b)) | **ACCEPTED** (`0 sorry`, standard axioms) |
| Lower-bound witnesses ($`\tau = 6 \dots 18`$, $`m \le 4`$ sharpness, $`z_{\max}(3k) \ge 2k`$) | Lean 4.36.0 kernel + independent build ([receipt `31455fc47d7b`](https://isitsolved.com/lean/receipts/31455fc47d7b)) | **ACCEPTED** (`0 sorry`, standard axioms) |
| Hash-collision elimination (every dup/zero & survivor hit confirmed by 61-bit multi-point CRT) | `tau_certify_exact.c` (`0` FP across `1.64B` hits at $`\tau=9`$ & `68.8B` hits at $`\tau=10`$) + full disjoint `-DALT_PRIMES` reruns | **`per-item diff == 0`** ([digests](reproduce/digests/)) |
| Survivor root counting over all $`\mathbb{Z}`$ | `python-flint` (`libflint` exact `fmpz_poly.factor()`) + pure-Python Hensel lifting (`verify_survivors.py`) | **`0` counterexamples** (`processed == nonempty`) |
| Enumeration loop completeness (`dfs()`) | Independent naive Rust enumerator ([`audit/naive_tau`](audit/naive_tau/README.md), $`\tau \le 7`$: `0` missing / `0` extra), 1.2M random canonical membership tests (`0` pruned), & mutation/canary suite | **PASS** ([`PHASE1_REPORT.md`](audit/PHASE1_REPORT.md)) |

---

## Quick Reproduction

```bash
# 1. Verify all 8 Lean 4 modules locally (4,228 LOC, 204 theorems/lemmas, 0 sorry)
lake exe cache get
lake build Research

# 2. Quick check (~1–3 min): builds C + Rust, runs naive tau<=6 cross-check & exact tau<=8
./reproduce/reproduce.sh quick

# 3. Full exact-CRT tau=1..9 K=6 + ALT_PRIMES + digest verification (~15 min on 12 cores)
./reproduce/reproduce.sh tau9

# 4. Full batched exact-CRT tau=10 K=7 + FLINT/Python verification & separate ALT_PRIMES check
./reproduce/reproduce.sh tau10
./reproduce/reproduce.sh tau10-alt
```

Expected counters and per-item SHA-256 digests are in [`reproduce/EXPECTED_OUTPUTS.md`](reproduce/EXPECTED_OUTPUTS.md) and [`reproduce/digests/`](reproduce/digests/).

---

## Detailed Results

<details>
<summary><strong>1. Exhaustive Exact-CRT Certification of z_max(9) = 6 and z_max(10) = 7</strong></summary>

- **$`\tau = 9, K = 6`$ ([`audit/PHASE1_REPORT.md`](audit/PHASE1_REPORT.md)):**
  - Certified all **59,308,136,697** candidate 9-gate leaves (a superset of all canonical 9-gate SLPs — leaf-level duplicate/zero filtering occurs inside `check_leaf`, so e.g. `1 * 1` is counted at $`\tau = 1`$; `7,767,649,524` total internal nodes = `529` split-prefix nodes + `7,767,648,995` worker internal nodes; see `audit/BUGS.md` item `R2`) across all final-gate operations $`\{+, -, \times\}`$, together with all shorter lengths $`\tau = 1 \dots 8`$ (required by `hcheck`).
  - **Exact-CRT Stage 1 (`tau_certify_exact.c`, 442.6s on 8 cores / 384.2s on 12 cores):** Confirmed all `1,432,372,962` internal/leaf dup hits and `207,134,139` per-item survivor dedup hits with **0 false positives**, matching all original counters bit-for-bit.
  - **Dual Stage 2 (`verify_survivors.py` + `audit/flint_roots.py`):** All **28,755,668** per-item exact-deduped survivor records (`11,040,213` globally unique) passed both pure-Python exact Hensel lifting (`175.4s`, `0` counterexamples) and `python-flint` (`max_z = 6`, `0` hits above `6`).
  - **Disjoint `-DALT_PRIMES` Cross-Check:** Exact `per-item diff == 0` across all `485` work items (`SHA-256: 3b03202de9631c40f9e3caf066b58ef0380353c1db3d7f88539abf2b7185eed4`).

- **$`\tau = 10, K = 7`$ ([`experiments/pvsnp/tau/z10_exact_report.md`](experiments/pvsnp/tau/z10_exact_report.md)):**
  - Certified all **2,675,837,421,376** candidate 10-gate leaves (`368,616,396,762` total internal nodes = `9,303` split-4 prefix + `368,616,387,459` worker nodes; `8,774` work items in 18 checkpointed batches; `4.85h` C time on 12 cores), combined with $`\tau = 1 \dots 9`$ already certified $`\le 6 \le 7`$.
  - **Exact-CRT Confirmation:** All `58,105,780,935` dup hits and `10,719,150,277` survivor hits confirmed with **0 false positives**.
  - **Disjoint `-DALT_PRIMES` Cross-Check:** Re-running all `8,774` work items reproduced every counter on every item (`per-item diff == 0`, `SHA-256: fead26c8984cd7ea5f297a7ff60a1158de21396f836806240f3a027acd4a8942`).
  - **Stage 2 (`audit/flint_roots.py` + `verify_survivors.py`):** All **1,333,049,433** per-item exact-deduped survivor records passed `python-flint` (`processed == nonempty`; batches 0–7 also double-checked by `verify_survivors.py`), finding **19** seven-root survivor records (per-item deduplicated; not necessarily 19 globally distinct polynomials) and **0** records with $`\ge 8`$ distinct integer roots.

- **Independent Naive Rust Cross-Check & Mutation Suite:**
  - [`audit/naive_tau`](audit/naive_tau/README.md) (no symmetries or ordering rules, exact `i128`/`BigInt` arithmetic) independently reproduced $`z_{\max}(1 \dots 7) = (1, 2, 3, 3, 4, 5, 5)`$ and matched the C enumerator's exact polynomial set $`|\mathrm{New}^\pm(\tau)|`$ for every $`\tau \le 7`$ (all `1,092,330` classes at $`\tau = 7`$: `0` missing, `0` extra).
  - Canonical membership tests passed `1,000,000 / 1,000,000` at $`\tau = 9`$ and `200,000 / 200,000` at $`\tau = 10`$.
  - Mutation & canary suite ([`audit/mutation/MUTATION_REPORT.md`](audit/mutation/MUTATION_REPORT.md)): 4/4 canaries detected; 4/4 rule-disabling mutants changed counts while preserving `missing = 0, extra = 0`; 4/4 non-equivalent planted bugs caught.

</details>

<details>
<summary><strong>2. Verified Record Finite-τ Witnesses up to τ = 18 (100% Lean 4 Kernel-Checked)</strong></summary>

| $`\tau`$ | Distinct Integer Roots | Construction / Mechanism | Lean 4 Theorem |
| :---: | :---: | :--- | :--- |
| **6** | **5** (exact) | $`-x(x^2-1)(x^2-4)`$ | `tau_witness_6_five` |
| **8** | **6** (exact) | $`q(q-2)(q-6)`$, $`q = x^2 - x`$ | `tau_witness_8` |
| **9** | **6** (exact, new) | Exact-CRT exhaustive census over all $`\mathbb{Z}`$ | `zmax9_le_six_of_checklist` *(conditional)* |
| **10** | **7** (exact, new) | $`-x(x^2-1)(x^2-4)(x^2-9)`$ & exact-CRT census | `tau_witness_10_seven`, `zmax10_le_seven_of_checklist` |
| **11** | $`\ge 8`$ *(new sym. family)* | Symmetric midpoint (`{-4..-1, 1..4}`) & pronic | `tau_record_11_eight_sym` |
| **12** | $`\ge 9`$ *(new record)* | **Midpoint Difference Trick** (`{-4..4}`) | `tau_record_12_nine` |
| **13** | $`\ge 10`$ *(new record)* | **Shifted Pronic-Square** (slope $`10/13 \approx 0.769`$) | `tau_record_13_ten` |
| **15** | $`\ge 11`$ *(new record)* | Shifted Pronic-Square $`\times (x - 2)`$ | `tau_record_15_eleven` |
| **16** | $`\ge 12`$ *(new record)* | Shifted Pronic-Square ($`a = 36`$) $`\times (q-2)(q-6)`$ | `tau_record_16_twelve` |
| **17** | $`\ge 13`$ *(new record)* | **Square-Extraction Trick** ($`x + 196`$, $`x^2 - 196`$) | `tau_record_17_thirteen` |
| **18** | $`\ge 14`$ *(new record)* | **Pronic Self-Shift Identity** ($`a + a^2 = a(a+1)`$) | `tau_record_18_fourteen` |

</details>

<details>
<summary><strong>3. Exact Bounded-Multiplication Sharpness (m ≤ 4)</strong></summary>

Proved in Lean 4 (`bounded_mult_exact_sharpness_four`) that the trivial degree ceiling $`\max_{\mathrm{mulCount}(P) \le m} z_{\mathbb{Z}}(P) = 2^m`$ is **exact and sharp** for all $`m \in \{0, 1, 2, 3, 4\}`$ (`1, 2, 4, 8, 16`), including an explicit **4-multiplication** 4-level iterated fold achieving **16 distinct integer roots** (`tau_four_mul_sharp`, arising from the primitive Gaussian-integer norm $`67{,}405 = 5 \cdot 13 \cdot 17 \cdot 61`$). *Caveat:* this bounds multiplication gates only (constants are built from `1` by zero-multiplication addition chains, so `τ` is large); it is classical-in-spirit iterated folding and does not improve any finite-$`\tau`$ record.

</details>

<details>
<summary><strong>4. Lean 4.36.0 Modules (11 modules, 8,228 LOC, 293 theorems/lemmas, 0 sorry)</strong></summary>

Independently built & verified at [isitsolved.com/lean/receipts/31455fc47d7b](https://isitsolved.com/lean/receipts/31455fc47d7b) (plus new receipt for the 3 asymptotic modules below):

- [`Research/PvsNP/Tau/TauConjecture.lean`](Research/PvsNP/Tau/TauConjecture.lean) (344 LOC) — Constant-free `SLP`, `ShubSmaleTauConjecture`, degree & multiplication root bounds, computable `zMaxGe_of_evalInt` witness certifier.
- [`Research/PvsNP/Tau/TauWitnesses.lean`](Research/PvsNP/Tau/TauWitnesses.lean) (114 LOC) — Verified witnesses for $`\tau = 6, 10, 11, 13`$ and 2-multiplication bound.
- [`Research/PvsNP/Tau/ModularRootBound.lean`](Research/PvsNP/Tau/ModularRootBound.lean) (338 LOC) — Simple-Root Modular Certificate (`intRootCount_le_of_eval_zmod`) and pronic linear baseline `zMaxGe (3 * k) (2 * k)`.
- [`Research/PvsNP/Tau/TauRecords.lean`](Research/PvsNP/Tau/TauRecords.lean) (97 LOC) — Verified new records for $`\tau = 11, 12, 13, 15`$.
- [`Research/PvsNP/Tau/BoundedMult.lean`](Research/PvsNP/Tau/BoundedMult.lean) (158 LOC) — Exact sharpness for $`m = 0, 1, 2, 3`$.
- [`Research/PvsNP/Tau/FoldingRecords.lean`](Research/PvsNP/Tau/FoldingRecords.lean) (350 LOC) — Zero-multiplication addition chains, exact sharpness for $`m = 4`$ (`16` roots), and records for $`\tau = 16, 17, 18`$.
- [`Research/PvsNP/Tau/Canonical.lean`](Research/PvsNP/Tau/Canonical.lean) (1,844 LOC) — Formal soundness of all canonicalization and dead-gate pruning rules (`exists_canonical`, `deadgate_count_bound`, `unusedWires_last_gate`, `zmax9_le_six_of_checklist`, `zmax10_le_seven_of_checklist`).
- [`Research/PvsNP/Tau/CertSoundness.lean`](Research/PvsNP/Tau/CertSoundness.lean) (983 LOC) — Formal soundness of degree propagation, atomic product-mask union bound, dual-number modular evaluation, Taylor-stripped modular certificate, hash-mismatch inequality, and exact CRT zero certification.
- [`Research/PvsNP/Tau/ChirpZ.lean`](Research/PvsNP/Tau/ChirpZ.lean) (1,624 LOC) — Compositional `CanBuild` SLP framework, fraction-free $`q`$-binomial theorem, Bluestein Chirp-$`z`$ identity, division-free Karatsuba multiplication, `tau_karatsuba_growth`, and `tau_refutes_linear`.
- [`Research/PvsNP/Tau/SubquadraticRefutation.lean`](Research/PvsNP/Tau/SubquadraticRefutation.lean) (2,100 LOC) — Division-free Schönhage–Nussbaumer negacyclic FFT over $`\mathbb{Z}[x]`$, `tau_subquadratic_growth`, `tau_refutes_subquadratic` (all real $`c < 2`$), and concrete finite crossover `tau_crossover_1884_2049` (`zMaxGe 1884 2049`).
- [`Research/PvsNP/Tau/PadicBarrier.lean`](Research/PvsNP/Tau/PadicBarrier.lean) (276 LOC) — Explicit length-$`4k`$ SLP family and Hensel preimage tree proving `tau_padic_two_pow` ($`2^k`$ distinct roots in $`\mathbb{Z}_2`$).

</details>

<details>
<summary><strong>5. Repository Layout</strong></summary>

- [`paper/tau_conjecture_z9.pdf`](paper/tau_conjecture_z9.pdf) & [`paper/tau_conjecture_z9.tex`](paper/tau_conjecture_z9.tex) — Compiled PDF & LaTeX paper covering $`z_{\max}(9) = 6`$, $`z_{\max}(10) = 7`$, records up to $`\tau = 18`$, and Lean 4 proofs.
- [`audit/`](audit/) — Red-team audits (`RED_TEAM_AUDIT.md`, `RED_TEAM_AUDIT_EXACT.md`), bug/overclaim log (`BUGS.md`), Phase 1 audit report (`PHASE1_REPORT.md`), external review bundle (`EXTERNAL_REVIEW_BUNDLE.md`), naive Rust enumerator (`naive_tau/`), `python-flint` root counter (`flint_roots.py`), and mutation suite (`mutation/`).
- [`reproduce/`](reproduce/) — Tiered reproduction script (`reproduce.sh`), expected counters (`EXPECTED_OUTPUTS.md`), and per-item digests (`digests/`).
- [`Research/PvsNP/Tau/`](Research/PvsNP/Tau/) — Lean 4.36.0 + Mathlib v4.36.0 formalization (8 modules, 4,228 LOC, 204 theorems/lemmas).
- [`experiments/pvsnp/tau/`](experiments/pvsnp/tau/) — Hardened exact-CRT certifier (`tau_certify_exact.c`, `verify_survivors.py`, `EXACT_PIPELINE.md`, `z10_exact_report.md`) plus original provenance files (`tau_z9_unconditional.c`, `verify_z9_all_Z.py`, `z9_unconditional_report.md`).
- [`OEIS_SUBMISSION.txt`](OEIS_SUBMISSION.txt) — OEIS draft for `1, 2, 3, 3, 4, 5, 5, 6, 6, 7`.
- [`outreach/`](outreach/) — Draft correspondence and social summary (prepared for review).

</details>
