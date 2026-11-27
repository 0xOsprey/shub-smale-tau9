# Phase 1 Adversarial Audit Report ($z_{\max}(9) = 6$)

**Overall Verdict:** **PASS.** Every mathematical and computational check of the $z_{\max}(9) = 6$ claim passed cleanly. Zero hash false positives occurred across all $1.64 \times 10^9$ exact CRT confirmations at $\tau = 9$, and every survivor passed two independent exact $\mathbb{Z}[x]$ verifiers (`verify_survivors.py` and `python-flint`) with zero counterexamples. Every bug, gap, and overclaim found in the original codebase and documentation is logged in [BUGS.md](file:///tmp/shub-smale-tau9/audit/BUGS.md).

---

## 1. Independent Red-Team Audits

- **First-pass audit of original code** ([RED_TEAM_AUDIT.md](file:///tmp/shub-smale-tau9/audit/RED_TEAM_AUDIT.md)): Read `tau_z9_unconditional.c` (996 lines), `verify_z9_all_Z.py` (421 lines), `paper/tau_conjecture_z9.tex`, `README.md`, and `z9_unconditional_report.md` line by line.
  - Core math at $K = 6$ held (`cert_deg`, `cert_prod`, `cert_p1`, `cert_taylor`, `cert_fallback`, Hensel/Cauchy).
  - Found real bugs/gaps in the original code & docs: hash-only dup/zero pruning and survivor dedup (`F1`, `F2`), invalid fixed-point Schwartz–Zippel / `<10^-40` probability claims (`F3`), unproven "provably lossless" claims (`F4`), `K=0` CLI unsoundness (`R1`), `nodes_visited` prefix undercount by 44 / 529 (`R2`), unchecked `nthreads<=0` / `tau` bounds / I/O errors (`R3`), missing verifier accounting assert (`R4`), stale/wrong repo stats (`R5`), and verifier prose mismatch (`R6`).
- **Second-pass audit of hardened pipeline** ([RED_TEAM_AUDIT_EXACT.md](file:///tmp/shub-smale-tau9/audit/RED_TEAM_AUDIT_EXACT.md)): Audited `tau_certify_exact.c`, `verify_survivors.py`, and `EXACT_PIPELINE.md`.
  - **0 CRITICAL soundness bugs** (exact CRT confirm-on-hit, 40 hard-coded 61-bit primes independently verified prime & distinct, lazy `eval_q0` cache invalidation, exact survivor dedup, `-DEXTRA_PRIMES`, `--membership`, and `verify_survivors.py` math all passed).
  - Found 3 moderate operational bugs in checkpoint/resume & CLI (`E1`, `E2`, `E3`), all immediately fixed and regression-tested.

---

## 2. Independent Naive Rust Enumerator & Dump Cross-Check ($\tau = 1 \dots 7$)

Crate: [audit/naive_tau](file:///tmp/shub-smale-tau9/audit/naive_tau/README.md) (written from scratch without reading `experiments/`, `paper/`, or `Research/`; no sign symmetry, no operand ordering, no gate-order canonicalization; exact `i128` + `BigInt` arithmetic; `python-flint` root counting).

| $\tau$ | Naive $|L_\tau|$ | Naive $|\mathrm{New}(\tau)|$ | Naive $|\mathrm{New}^\pm(\tau)|$ | C Dump $|\mathrm{DumpSet}^\pm|$ | Missing (`New± \ Dump`) | Extra (`Dump \ ∪New±`) | Naive $z_{\max}(\tau)$ | Verdict |
|---:|---:|---:|---:|---:|---:|---:|---:|:---:|
| 1 | 6 | 6 | 5 | 5 | **0** | **0** | **1** | PASS |
| 2 | 59 | 27 | 20 | 21 | **0** | **0** | **2** | PASS |
| 3 | 805 | 150 | 104 | 127 | **0** | **0** | **3** | PASS |
| 4 | 15,144 | 1,084 | 716 | 842 | **0** | **0** | **3** | PASS |
| 5 | 377,992 | 10,134 | 6,409 | 7,254 | **0** | **0** | **4** | PASS |
| 6 | 12,008,914 | 122,339 | 74,275 | 81,529 | **0** | **0** | **5** | PASS |
| 7 | 469,476,460 | 1,866,020 | 1,092,330 | 1,173,859 | **0** | **0** | **5** | PASS |

- Reproduces $z_{\max}(1 \dots 7) = (1, 2, 3, 3, 4, 5, 5)$ independently.
- Naive state-set enumeration at $\tau = 8$ is documented as infeasible within 20 GB RAM / 1.5h (`|L_7| = 469.5M` states alone takes 15 GB; see `audit/naive_tau/results/tau8_infeasibility.json`).

---

## 3. Canonical Membership Tests ($\tau = 9, 10$)

Generated uniformly diverse random canonical SLPs via `naive_tau random-canonical` (exact arithmetic) and tested against `tau_certify_exact --membership`:
- **$\tau = 9$**: `1,000,000 / 1,000,000` FOUND, **`0` pruned** (100.000%).
- **$\tau = 10$**: `200,000 / 200,000` FOUND, **`0` pruned** (100.000%).

---

## 4. Exact-CRT $\tau = 1 \dots 9$ ($K = 6$) & Independent Survivor Verification

`tau_certify_exact` confirms every hash hit (internal dup/zero, leaf dup/zero, survivor dedup) using exact multi-point CRT over 61-bit primes (`Q > 4 * |coeff|`).

### $\tau = 9, K = 6$ Comparison (Original vs Exact-CRT vs Exact-CRT `ALT_PRIMES`)

| Metric | Original (`tau_z9_unconditional.c`) | Exact-CRT (`tau9_exact`, 8t) | Exact-CRT `ALT_PRIMES` (`tau9_alt`, 12t) | Diff |
|---|---:|---:|---:|:---:|
| Wall time | 399.671s (12t) | 442.572s (8t) | 384.213s (12t) | — |
| `nodes_visited` (+529 prefix) | 7,767,648,995 | 7,767,648,995 (total 7,767,649,524) | 7,767,648,995 (total 7,767,649,524) | **0** |
| `leaves_checked` | 59,308,136,697 | 59,308,136,697 | 59,308,136,697 | **0** |
| `cert_deg` | 44,427,829,968 | 44,427,829,968 | 44,427,829,968 | **0** |
| `cert_prod` | 6,343,706,401 | 6,343,706,401 | 6,343,706,401 | **0** |
| `cert_p31` | 4,178,330,044 | 4,178,330,044 | 4,178,330,044 | **0** |
| `cert_taylor31` | 2,991,794,570 | 2,991,794,570 | 2,991,794,570 | **0** |
| `cert_dup_zero` | 221,875,029 | 221,875,029 | 221,875,029 | **0** |
| `cert_p19` / `p23` / `p29` | 675,427,005 / 213,548,025 / 19,735,848 | 675,427,005 / 213,548,025 / 19,735,848 | 675,427,005 / 213,548,025 / 19,735,848 | **0** |
| `survivors_raw` | 235,889,807 | 235,889,807 | 235,889,807 | **0** |
| `survivors_uniq` (per-item) | (11,040,213 global) | 28,755,668 | 28,755,668 | **0** |
| `dup_hash_hits` (`false_pos`) | n/a | 1,432,372,962 (**0**) | 1,432,372,962 (**0**) | **0** |
| `surv_hash_hits` (`false_pos`) | n/a | 207,134,139 (**0**) | 207,134,139 (**0**) | **0** |
| Per-item `done.tsv` diff | — | — | exact match across all 485 items | **0** |

Because every single one of the `1,432,372,962` dup hits and `207,134,139` survivor hits was exact-CRT confirmed with **0 false positives**, this **deterministically proves** that the original hash pruning at $\tau = 9$ lost zero subtrees and zero survivors.

### Exact Survivor Verification (`verify_survivors.py` + `audit/flint_roots.py`)

| $\tau$ ($K=6$) | Survivors Verified | `verify_survivors.py` CE (`max_exact_hensel`) | `flint_roots.py` hits (`max_z`) | Accounting Check |
|---:|---:|---:|---:|:---:|
| 5 | 2 | 0 (0) | 0 (`max_z=3`) | PASS |
| 6 | 172 | 0 (3) | 0 (`max_z=3`) | PASS |
| 7 | 9,237 | 0 (3) | 0 (`max_z=4`) | PASS |
| 8 | 342,991 | 0 (4) | 0 (`max_z=5`) | PASS |
| **9** | **28,755,668** (per-item deduped) | **0** (`5`; `deg=3,255,332`, `sqf_deg=9,315,446`, `sqf_mod=15,506,965`, `hensel_ok=677,925`) | **0** (`max_z=6`: 65 six-root polys, 0 with $\ge 7$) | **PASS** (`28755668 == 28755668`) |

---

## 5. Mutation & Canary Suite

Full results in [MUTATION_REPORT.md](file:///tmp/shub-smale-tau9/audit/mutation/MUTATION_REPORT.md):
- **Canaries (4/4 PASS):** `tau=6 K=4` (5-root), `tau=8 K=5` (6-root), `tau=10 K=6` on canonical `slpWitness10` prefix (7-root), and synthetic `x(x-31)` at `tau=8 K=1` (2-root double mod 31).
- **Rule-disabling mutants (4/4 PASS):** `MUT_NO_DEADGATE`, `MUT_NO_KEYORDER`, `MUT_NO_SIGNCANON`, `MUT_NO_DUP` all altered node/leaf counts while preserving `missing=0, extra=0` on `eval-dump`.
- **Planted bugs (4/4 non-equivalent DETECTED + 1 equivalent mutant proved):** `BUG_DEADGATE_OFF_BY_ONE`, `BUG_NO_SQUARE`, `BUG_SKIP_SUB_INPUTS` caught by both `eval-dump` and `--membership`; `BUG_IGNORE_DOUBLES` caught by the `x(x-31)` canary; `BUG_TAYLOR_M0` proved equivalent because `cm % p == 0` already rejects `m == 0` whenever `f(r_b) ≡ 0 (mod p)`.

---

## 6. Lean 4 Formalization (Phase 2 — Already Complete)

- [Canonical.lean](file:///Users/joe/github/gemini-neon/Research/PvsNP/Tau/Canonical.lean) (1,844 LOC): `exists_canonical`, `deadgate_count_bound`, `unusedWires_last_gate`, `zmax_le_of_checklist`, `zmax9_le_six_of_checklist`, `zmax10_le_seven_of_checklist`.
- [CertSoundness.lean](file:///Users/joe/github/gemini-neon/Research/PvsNP/Tau/CertSoundness.lean) (983 LOC): degree-bound propagation, atomic product-mask union bound, dual-number modular derivative evaluation, Taylor-residue certificate, hash-mismatch `≠`, and CRT exact-zero certification.
- **0 `sorry`, 0 `admit`, strictly `{propext, Classical.choice, Quot.sound}`.**
