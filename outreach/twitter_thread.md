# Draft Twitter / X Thread (PREPARE ONLY — DO NOT POST AUTOMATICALLY)

> **Reminder:** Consider emailing Santibáñez-Leal first and waiting for a reply before posting publicly. Update with the exact $z_{\max}(10)$ result once Phase 3 completes.

---

**Tweet 1/7 (Scope & AI Disclosure Up Front):**
We audited and hardened our computational proof of $z_{\max}(9) = 6$ and settled the next exact value **$z_{\max}(10) = 7$** for the Shub–Smale $\tau$-conjecture (Smale's 4th Problem), extending Santibáñez-Leal's 2026 census $z_{\max}(1\dots 8)=(1,2,3,3,4,5,5,6)$.

Up front:
1. This does NOT resolve P vs NP or the asymptotic $\tau$-conjecture.
2. It was developed with AI assistance (Antigravity + Gemini 4 Neon), so we tried to break it with an adversarial audit, an independent Rust enumerator, FLINT, and Lean 4 proofs.

Repo: https://github.com/0xOsprey/shub-smale-tau9

**Tweet 2/6 (What We Fixed After Auditing Ourselves):**
Our first C enumerator relied on unverified hash-based duplicate pruning and called its pruning rules "provably lossless" without formal proofs.

Our own red-team audit also caught real bugs & overclaims (all logged in `audit/BUGS.md`):
- Invalid fixed-point Schwartz–Zippel collision probability claims (removed)
- An off-by-prefix `nodes_visited` undercount (+529 nodes at $\tau=9$)
- A CLI `K=0` edge case & unchecked I/O returns
- Stale Lean module/theorem counts in the draft paper

**Tweet 3/6 (Zero Hash-Collision Trust):**
We replaced hash-only pruning with exact multi-point CRT confirmation over 61-bit primes on every hash hit (`tau_certify_exact.c`).

Re-running all 59,308,136,697 canonical 9-gate SLPs (442s on 8 cores, +13.6% overhead):
- 1,432,372,962 dup hash hits -> 100% exact-CRT confirmed, **0 false positives**
- 207,134,139 survivor hits -> 100% exact-CRT confirmed, **0 false positives**
- Disjoint `-DALT_PRIMES` cross-check: **per-item `diff == 0`** across all 485 work items
- All 28,755,668 per-item survivors verified by BOTH pure-Python exact $\mathbb{Z}[x]$ Hensel lifting AND `python-flint`: **0 counterexamples** (`max_z = 6`).

**Tweet 4/6 (Independent Naive Cross-Check & Mutation Testing):**
To test the pruning rules themselves without shared code:
- A deliberately naive Rust enumerator (no symmetries, no ordering rules, exact `i128`/`BigInt` arithmetic) independently reproduced $z_{\max}(1\dots 7) = (1,2,3,3,4,5,5)$ and matched the C enumerator's exact polynomial set $|\mathrm{New}^\pm(\tau)|$ for every $\tau \le 7$ (all 1,092,330 classes at $\tau=7$: **0 missing, 0 extra**).
- 1,000,000 random canonical $\tau=9$ SLPs and 200,000 at $\tau=10$: **100% found, 0 pruned**.
- Canary + mutation suite: all 4 canaries (5-, 6-, 7-root, and double-root mod 31) detected; all non-equivalent planted bugs caught.

**Tweet 5/6 (Formal Soundness in Lean 4):**
We formalized the soundness of every canonicalization rule (sign symmetry, dead-gate bounds, duplicate/zero elimination, lex-minimal topological ordering) and every per-leaf certificate (degree, product mask, dual-number modular, Taylor-stripped, CRT) in Lean 4.36.0 (`Canonical.lean` + `CertSoundness.lean`):
- 8 modules, 4,228 LOC, 204 theorems/lemmas, **0 `sorry`**, strictly `{propext, Classical.choice, Quot.sound}`.
- Main theorem `zmax9_le_six_of_checklist`: if the canonical checklist is complete, $z_{\max}(9) \le 6$. Only the raw C enumeration loop remains outside the Lean kernel.

**Tweet 6/7 (New Exact Result: $z_{\max}(10) = 7$):**
Running the hardened exact-CRT pipeline on $\tau = 10, K = 7$ (all **2,675,837,421,376** canonical 10-gate SLPs across 8,774 checkpointed work items):
- 58.1B dup hits + 10.7B survivor hits -> 100% exact-CRT confirmed, **0 false positives**
- Disjoint `-DALT_PRIMES` rerun across all 8,774 work items: **per-item `diff == 0`**
- All 1,333,049,433 per-item survivors verified by `python-flint`: **19** exact 7-root polynomials, **0** with $\ge 8$ roots.

Exact sequence: $z_{\max}(1\dots 10) = (1, 2, 3, 3, 4, 5, 5, 6, 6, 7)$, $z_{\max}(11) \ge 8$.

**Tweet 7/7 (Reproduce It Yourself & Credit):**
Full credit to Santibáñez-Leal (2026) for $z_{\max}(1\dots 8)$, $z_{\max}(10)\ge 7$, and ruling out $\times$-final $\tau=9$.
Everything—including a tiered reproduction script (`reproduce/reproduce.sh`), full bug log (`audit/BUGS.md`), and Lean proofs (`zmax9_le_six_of_checklist`, `zmax10_le_seven_of_checklist`)—is MIT-licensed and open for independent verification.
