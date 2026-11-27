# Exact $\mathbb{Z}$-Wide Certification of $z_{\max}(10) = 7$ (Shub–Smale $\tau$-Conjecture)

## Executive Summary

Extending our hardened exact-CRT pipeline to $\tau = 10$ with $K = 7$, we have exhaustively certified over **all of $\mathbb{Z}$** (zero root-magnitude bound, zero hash-collision trust) that **no nonzero polynomial computable by a constant-free straight-line program (SLP) of length $\tau \le 10$ over $\{1, x\}$ and $\{+, -, \times\}$ has $\ge 8$ distinct integer roots**:

$$z_{\max}(1 \dots 10) = (1, 2, 3, 3, 4, 5, 5, 6, 6, 7), \qquad z_{\max}(11) \ge 8.$$

Combined with the Lean 4 machine-verified 10-gate 7-root witnesses (`tau_witness_10_seven`, `tau_witness_10_seven_pronic`) and 11-gate 8-root witnesses (`tau_witness_11_eight`, `tau_record_11_eight_sym`), this settles **both the 7-root threshold (at $\tau = 10$) and the 8-root threshold (at $\tau = 11$)** of Smale's 4th Problem.

---

## Exact Breakdown for $\tau = 10$ ($K = 7$)

Executed on 12 CPU cores (Apple M3 Pro) across all **8,774** `--split 4` work items in 18 checkpointed batches (`500` items/batch, peak disk `< 20 GB`, C search wall time `17,449.9s = 4.85h`):

- **Total canonical internal nodes:** `368,616,396,762` (`9,303` split-4 prefix nodes + `368,616,387,459` worker internal nodes)
- **Total canonical 10-gate leaves checked:** **`2,675,837,421,376`** (`45.1×` larger than $\tau = 9$)

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

### Zero Hash-Collision Trust (Exact Multi-Point CRT Confirmation)

Every hash hit was deterministically confirmed via multi-point evaluation over 61-bit primes with combined modulus $Q > 4 \cdot \max |c_k|$ (Lean: `poly_eq_zero_of_crt_eval`):
- `dup_hash_hits = 58,105,780,935` -> `58,105,780,935` exact-CRT confirmed, **`0` false positives**
- `zero_hash_hits = 0` -> **`0` false positives**
- `surv_hash_hits = 10,719,150,277` -> `10,719,150,277` exact-CRT confirmed, **`0` false positives**

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

- Finding **19** exact 7-root polynomials in the wild (`max_z = 7`, `hits = 0` above 7) serves as a live in-search canary confirming that high-root $\tau = 10$ polynomials pass through the C pipeline to exact verification.

### Formal Verification Boundary (Lean 4.36.0)

`Research/PvsNP/Tau/Canonical.lean` (`zmax10_le_seven_of_checklist`) and `Research/PvsNP/Tau/CertSoundness.lean` (`0 sorry`, strictly `{propext, Classical.choice, Quot.sound}`) formally prove that if the canonical checklist up to $\tau = 10$ is complete with $\le 7$ roots per polynomial, then $z_{\max}(10) \le 7$ over all of $\mathbb{Z}$. Only the raw C enumeration loop and FLINT/Python execution remain outside the Lean kernel.
