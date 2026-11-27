# Exact $\mathbb{Z}$-Wide Certification of $z_{\max}(10) = 7$ (Shub–Smale $\tau$-Conjecture)

## Executive Summary

Extending our hardened exact-CRT pipeline to $\tau = 10$ with $K = 7$, we have exhaustively certified over **all of $\mathbb{Z}$** (zero root-magnitude bound, zero hash-collision trust) that **no nonzero polynomial computable by a constant-free straight-line program (SLP) of length $\tau \le 10$ over $\{1, x\}$ and $\{+, -, \times\}$ has $\ge 8$ distinct integer roots**:

$$z_{\max}(1 \dots 10) = (1, 2, 3, 3, 4, 5, 5, 6, 6, 7), \qquad z_{\max}(11) \ge 8.$$

Combined with the Lean 4 machine-verified 10-gate 7-root witnesses (`tau_witness_10_seven`, `tau_witness_10_seven_pronic`) and 11-gate 8-root witnesses (`tau_witness_11_eight`, `tau_record_11_eight_sym`), this settles **both the 7-root threshold (at $\tau = 10$) and the 8-root threshold (at $\tau = 11$)** of Smale's 4th Problem.

---

## Exact Breakdown for $\tau = 10$ ($K = 7$)

Executed on 12 CPU cores (Apple M3 Pro) across all **8,774** `--split 4` work items in 18 checkpointed batches (`500` items/batch, peak disk `< 20 GB`, C search wall time `17,449.9s = 4.85h`):

- **Total canonical internal nodes:** `368,616,396,762` (`9,303` split-4 prefix nodes + `368,616,387,459` worker internal nodes)
- **Total candidate 10-gate leaves checked (superset of all canonical 10-gate SLPs):** **`2,675,837,421,376`** (`45.1×` larger than $\tau = 9$; leaf-level duplicate/zero filtering occurs inside `check_leaf` after fast bounds, so non-canonical leaf duplicates such as `1 * 1` at $\tau = 1$ are included in `leaves_checked`)

| Certification Mechanism | Leaves Certified | Share of Total |
|---|---:|---:|
| Exact degree bound (`deg_ub <= 7`) | 1,956,601,429,194 | 73.1211% |
| Atomic product-factor union bound (`cert_prod`) | 301,560,591,276 | 11.2698% |
| Simple-Root Modular Certificate mod $p_1 = 31$ | 221,045,840,732 | 8.2608% |
| Exact Taylor-stripped Certificate mod $p_1 = 31$ | 137,831,162,613 | 5.1510% |
| Zero / duplicate gate (`cert_dup_zero`) | 9,737,432,438 | 0.3639% |
| Fallback Simple-Root / Taylor mod $p_2 = 19$ | 28,243,748,808 | 1.0555% |
| Fallback Simple-Root / Taylor mod $p_3 = 23$ | 7,799,738,507 | 0.2915% |
| Fallback Simple-Root / Taylor mod $p_4 = 29$ | 965,278,098 | 0.0361% |
| Passed to exact $\mathbb{Z}[x]$ verifier (`survivors_raw`) | 12,052,199,710 | 0.4504% |
| **Total (exact conservation check)** | **2,675,837,421,376** | **100.0000%** |

### Zero Hash-Collision Trust (Exact Multi-Point CRT Confirmation + Disjoint `-DALT_PRIMES` Cross-Check)

Every hash hit was deterministically confirmed via multi-point evaluation over 61-bit primes with combined modulus $Q > 4 \cdot \max |c_k|$ (Lean: `poly_eq_zero_of_crt_eval`):
- `dup_hash_hits = 58,105,780,935` -> `58,105,780,935` exact-CRT confirmed, **`0` false positives**
- `zero_hash_hits = 0` -> **`0` false positives**
- `surv_hash_hits = 10,719,150,277` -> `10,719,150,277` exact-CRT confirmed, **`0` false positives**
- **Full 8,774-item `-DALT_PRIMES` cross-check (`P1'=2147483629, P2'=1000000021, P3'=1000000033`):** Re-running all 18 batches (all 8,774 work items) with disjoint hash primes and evaluation points reproduced **every single counter on every single one of the 8,774 work items** (`per-item diff == 0`, `0` false positives), including an unintentional real-world power-cycle resume test at item `8,527 / 8,774`!

### Exact $\mathbb{Z}[x]$ Survivor Verification (`audit/flint_roots.py` + `verify_survivors.py`)

All **`1,333,049,433`** per-item exact-deduped survivors across all 18 batches were verified by `audit/flint_roots.py` (`python-flint 0.9.0` exact `fmpz_poly.factor()`), with batches `0..7` (`0..4000`, `~200M` survivors) additionally double-verified by pure-Python `verify_survivors.py` (100% agreement, `0` counterexamples):

| Distinct Integer Roots $z_{\mathbb{Z}}(f)$ | Survivors (FLINT exact) |
|---:|---:|
| 0 | 131,545,405 |
| 1 | 724,188,908 |
| 2 | 356,137,666 |
| 3 | 109,874,319 |
| 4 | 5,102,526 |
| 5 | 259,635 |
| 6 | 7,670 |
| **7** | **19** |
| **$\ge 8$** | **0** |
| Skipped (`exact deg <= 7`) | 5,933,285 |
| **Total (`processed == nonempty`)** | **1,333,049,433** |

- Finding **19** seven-root survivor records (per-item deduplicated across the 8,774 work items, so not necessarily 19 globally distinct polynomials; `max_z = 7`, `hits = 0` above 7) serves as a live in-search canary confirming that high-root $\tau = 10$ polynomials pass through the C pipeline to exact verification.

### Formal Verification Boundary (Lean 4.36.0)

`Research/PvsNP/Tau/Canonical.lean` (`zmax10_le_seven_of_checklist`) and `Research/PvsNP/Tau/CertSoundness.lean` (`0 sorry`, strictly `{propext, Classical.choice, Quot.sound}`) formally prove the conditional implication `hcheck → ∀ t ≤ 10, ∀ P : SLP t, P.evalPoly ≠ 0 → intRootCount P.evalPoly ≤ 7`, where `hcheck` requires certifying all canonical gate lists of **every** length $1 \le n \le 10$ (here supplied externally by the $\tau = 1 \dots 9$ certification with $K = 6 \le 7$ plus this $\tau = 10$ run with $K = 7$). The raw C enumeration loop and FLINT/Python execution remain outside the Lean kernel. Per-item counts and SHA-256 digests are published in [`reproduce/digests/`](../../../reproduce/digests/).
