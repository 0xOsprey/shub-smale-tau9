# Exact-Confirmed Hardened Pipeline for the Shub–Smale $\tau$-Conjecture

This document describes the hardened exhaustive-search and exact-verification pipeline consisting of:
- `tau_certify_exact.c`: exact-confirmed C exhaustive certifier (hardened from `tau_z9_unconditional.c` without modifying the original).
- `verify_survivors.py`: resumable, format-agnostic exact $\mathbb{Z}[x]$ survivor certifier (hardened from `verify_z9_all_Z.py` without modifying the original).

All binaries are built in `/Users/joe/github/gemini-neon/runs/bin/` using `cc -O3 -march=native -pthread` (Apple M3 Pro, 12 cores, 36 GB RAM).

---

## 1. Exact Multi-Prime CRT Identity Lemma

In the original `tau_z9_unconditional.c`, internal duplicate/zero pruning, leaf duplicate/zero filtering, and survivor deduplication fired on hash equality alone (2-point hash mod $2^{31}-1$ and $10^9+9$; 3-prime hash for survivors). A hash collision between two distinct polynomials could silently prune a genuine subtree or merge distinct survivors.

In `tau_certify_exact.c`, hashes act **strictly as a prefilter**. Every hash hit triggers an exact $\mathbb{Z}[x]$ polynomial identity test confirming $a \equiv 0$ or $a \equiv \pm b$ before any pruning or deduplication occurs. Any false positive increments `*_false_positive` and is **not** pruned or merged.

### Degree and $L_1$-Norm Bounds
For each wire $w$ ($w=0$ is $1$, $w=1$ is $x$, $w=d+2$ is gate $d$), we maintain:
- Exact degree upper bound $\mathrm{deg\_ub}(w)$:
  - $\mathrm{deg\_ub}(0)=0,\ \mathrm{deg\_ub}(1)=1$
  - $\mathrm{deg\_ub}(a \pm b) = \max(\mathrm{deg\_ub}(a), \mathrm{deg\_ub}(b))$
  - $\mathrm{deg\_ub}(a \cdot b) = \mathrm{deg\_ub}(a) + \mathrm{deg\_ub}(b)$
- Exact $\log_2$ $L_1$-coefficient-norm bound $\mathrm{nb}(w)$ such that $\|w\|_1 = \sum_k |c_k(w)| \le 2^{\mathrm{nb}(w)}$:
  - $\mathrm{nb}(0)=0,\ \mathrm{nb}(1)=0$
  - $\mathrm{nb}(a \pm b) = \max(\mathrm{nb}(a), \mathrm{nb}(b)) + 1$
  - $\mathrm{nb}(a \cdot b) = \mathrm{nb}(a) + \mathrm{nb}(b)$

### Lemma (Exact Multi-Prime CRT Identity Test)
Let $a, b \in \mathbb{Z}[x]$ be two SLP wires with degree upper bounds $\mathrm{deg\_ub}(a), \mathrm{deg\_ub}(b)$ and $L_1$-norm bounds $2^{\mathrm{nb}(a)}, 2^{\mathrm{nb}(b)}$, and let $s \in \{+1, -1\}$ (or $b=0$ for zero testing). Define $h = a - s b$, $D = \max(\mathrm{deg\_ub}(a), \mathrm{deg\_ub}(b))$, and $N = \max(\mathrm{nb}(a), \mathrm{nb}(b))$.
Let $q_0, \dots, q_{r-1}$ be $r$ distinct primes satisfying $D < q_m < 2^{61}$ and $q_m > 2^{60}$ for all $m$, with
$$r = \left\lfloor \frac{N + 2}{60} \right\rfloor + 1 \implies \sum_{m=0}^{r-1} \log_2(q_m) > 60r \ge N + 3.$$
If $h(t) \equiv 0 \pmod{q_m}$ for all $t \in \{0, 1, \dots, D\}$ and all $m \in \{0, \dots, r-1\}$, then $h = 0$ identically in $\mathbb{Z}[x]$.

**Proof.**
1. For each prime $q_m$, $\deg(h \bmod q_m) \le \deg(h) \le D < q_m$. Since $h \bmod q_m \in \mathbb{F}_{q_m}[x]$ has $D+1$ distinct roots $\{0, 1, \dots, D\}$, we must have $h \equiv 0 \pmod{q_m}$ (every coefficient $c_k(h)$ is divisible by $q_m$).
2. By the Chinese Remainder Theorem, every coefficient $c_k(h)$ is divisible by $Q = \prod_{m=0}^{r-1} q_m > 2^{60r}$.
3. On the other hand, $|c_k(h)| \le \|h\|_1 \le \|a\|_1 + \|b\|_1 \le 2^{\mathrm{nb}(a)} + 2^{\mathrm{nb}(b)} \le 2^{N+1} < 2^{60r - 1} < Q / 2$.
4. The only integer in $(-Q/2, Q/2)$ divisible by $Q$ is $0$. Hence $c_k(h) = 0$ for all $k$, so $h = 0$ in $\mathbb{Z}[x]$. $\square$

### Primality Verification of the 40 Hard-Coded 61-bit Primes
`tau_certify_exact.c` embeds 40 distinct primes $2^{60} < q_m < 2^{61}$ (giving $>2400$ CRT bits, covering up to `MAX_TAU = 12` where $\max \mathrm{nb} \le 2^{11} = 2048$). The first prime is the Mersenne prime $q_0 = 2^{61}-1 = 2305843009213693951$, enabling division-free modular multiplication and lazy per-depth evaluation caching (`eval_q0` for $D \le 64$).

All 40 primes were generated and verified via deterministic 64-bit Miller–Rabin using the 12-base set $\{2,3,5,7,11,13,17,19,23,29,31,37\}$ (known deterministic for all $n < 3.317 \times 10^{24} \gg 2^{64}$):
```python
def is_prime_mr64(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n == p: return True
        if n % p == 0: return False
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1: break
        else:
            return False
    return True
```
Range of hard-coded primes: `EXACT_PRIMES[0] = 2305843009213693951ULL` down to `EXACT_PRIMES[39] = 2305843009213692139ULL`.

---

## 2. Audit Findings & Bugs in Original Code

### ASan + UBSan on Original `tau_z9_unconditional.c`
Compiled with:
```bash
cc -O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer -pthread \
   /tmp/shub-smale-tau9/experiments/pvsnp/tau/tau_z9_unconditional.c \
   -o /Users/joe/github/gemini-neon/runs/bin/tau_z9_orig_asan
```
Ran `tau = 1..7` with `K = 6`, 4 threads:
- **Runtime sanitizer findings**: 0 ASan errors, 0 UBSan errors.
- **Compiler warnings**: 2 `-Wdeprecated-declarations` warnings on `sprintf` (lines 182, 185).

### Code Audit Findings (Original `tau_z9_unconditional.c` and `verify_z9_all_Z.py`)
1. **Unverified hash-based pruning & survivor dedup (soundness gap)**: `compute_hash_and_check_dup` and `record_survivor` relied purely on 2-prime / 3-prime hashes without exact polynomial confirmation. Fixed in `tau_certify_exact.c`.
2. **Prefix replay bug in `worker_fn`**: `worker_fn` called `compute_hash_and_check_dup(&ctx, idx, g.op, g.i, g.j, &r1, &r2)` during prefix replay and ignored its return value. Under any mode where a prefix gate could be flagged as dup/zero (or when counting hash hits), this would either leave `r1, r2` uninitialized or corrupt hit counters. Fixed by introducing `compute_hash_only` for prefix replay.
3. **Unvalidated CLI arguments**:
   - `tau` had no bounds check (`tau < 1` or `tau > MAX_TAU` caused stack out-of-bounds access / UB). Fixed: enforce `1 <= tau <= MAX_TAU`.
   - `K == 0` was accepted (`K < 0 || K >= 19`). Fixed: enforce `1 <= K < 19`.
   - `nthreads <= 0` was silently accepted (spawned 0 threads and reported 0 leaves!). Fixed: enforce `nthreads >= 1`.
4. **Unchecked allocations and I/O**: `calloc`, `realloc`, `fprintf`, `fclose` return values were unchecked. Fixed with explicit `die_oom` / `die_io` checks.
5. **Missing `nodes_visited` in `collect_work`**: For `tau >= 5`, `collect_work` did not increment `nodes_visited`, omitting the internal nodes at `depth < split_depth` (`+44` nodes for `tau = 5,6,7` at `split=2`; `+529` nodes for `tau = 8,9` at `split=3`). In `tau_certify_exact.c`, `nodes_visited` keeps the exact original semantics for direct diffing, and `prefix_nodes` / `nodes_total = nodes_visited + prefix_nodes` are also explicitly printed.
6. **Hardcoded `WorkItem.prefix[3]` and `certify_slp_mod_p` `[48]` buffer**: `prefix[3]` prevented `--split > 3`; `v[MAX_TAU+2][48]` would overflow for fallback prime `53` under `-DEXTRA_PRIMES`. Fixed: `prefix[MAX_SPLIT]` and `[64]` per-prime arrays.
7. **Stale comments**:
   - Header comment claimed fallback primes `{31, 19, 23, 29, 37, 41, 43}`, while `FALLBACK_PRIMES` only contained `{19, 23, 29}`.
   - `exact_taylor_at` comment claimed `mod t^8`, `0 <= m < 8`, `m >= 8`, and `8 * LIM^2 < 2^127`, while `TAYLOR_DEG` was `12` (`12 * (10^17)^2 = 1.2e35 < 2^127` is still overflow-safe).
8. **Original `verify_z9_all_Z.py`**:
   - Fixed `PRIMES = small_primes(2000)` could raise `RuntimeError` if a squarefree polynomial had discriminant divisible by all primes up to 2000. Fixed in `verify_survivors.py` with unbounded `iter_primes()`.
   - No explicit accounting assertion (`processed == total`), no compact format support, no shard directory support, no resume state, no `--out` counterexample file. All added in `verify_survivors.py`.

---

## 3. Build Commands & Compile Flags

All builds pass with `-Wall -Wextra -Werror` and zero warnings:

```bash
SRC=/tmp/shub-smale-tau9/experiments/pvsnp/tau/tau_certify_exact.c
BIN=/Users/joe/github/gemini-neon/runs/bin

# Standard production build
cc -Wall -Wextra -Werror -O3 -march=native -pthread "$SRC" -o "$BIN/tau_certify_exact"

# ASan + UBSan build
cc -Wall -Wextra -Werror -O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer -pthread \
   "$SRC" -o "$BIN/tau_certify_exact_asan"

# Extra fallback primes {19,23,29,37,41,43,47,53} (default OFF for tau=9 comparability)
cc -Wall -Wextra -Werror -O3 -march=native -pthread -DEXTRA_PRIMES "$SRC" -o "$BIN/tau_certify_exact_extra"

# Alternate hash prime triple (cross-check)
cc -Wall -Wextra -Werror -O3 -march=native -pthread -DALT_PRIMES "$SRC" -o "$BIN/tau_certify_exact_alt"

# Dump all non-dup/non-zero leaves in compact format (certificates disabled)
cc -Wall -Wextra -Werror -O3 -march=native -pthread -DDUMP_LEAVES "$SRC" -o "$BIN/tau_certify_exact_dump"
```

### Mutation & Bug-Injection Flags (All Verified Clean under `-Wall -Wextra -Werror`)
| Flag | Category | Behavior |
|---|---|---|
| `-DMUT_NO_DEADGATE` | Rule-disabling | Disables dead-gate pruning at internal nodes and leaves |
| `-DMUT_NO_KEYORDER` | Rule-disabling | Disables lex-minimal key ordering for independent gates |
| `-DMUT_NO_SIGNCANON` | Rule-disabling | Allows any operand order `(i, j)` (still forbids `sub` with `i == j`) |
| `-DMUT_NO_DUP` | Rule-disabling | Disables internal dup/zero pruning (leaf dup/zero unchanged) |
| `-DBUG_DEADGATE_OFF_BY_ONE` | Planted bug | Sets `max_unused_after = rem_after` instead of `rem_after + 1` |
| `-DBUG_NO_SQUARE` | Planted bug | Skips `mul` with `i == j` |
| `-DBUG_SKIP_SUB_INPUTS` | Planted bug | Skips `sub` when both operands `< 2` |
| `-DBUG_TAYLOR_M0` | Planted bug | Accepts `m == 0` in `certify_taylor_roots` |
| `-DBUG_IGNORE_DOUBLES` | Planted bug | Simple-root modular check ignores double roots |

---

## 4. CLI Usage

### `tau_certify_exact`
```bash
tau_certify_exact <tau> <K> [nthreads] [survivor_file] [options]
  --threads N          Worker threads (default 12, >= 1)
  --split D            Work-item split depth (0 <= D < tau)
  --items A:B          Process only work-item indices [A, B)
  --sample FRAC SEED   Deterministic SplitMix64 subset of work items
  --checkpoint DIR     Resumable mode: fsync'd DIR/done.tsv + atomic DIR/surv/<id>.txt (compact)
  --prefix "a0.1 ..."  Explore only paths starting with compact prefix (validated by all rules)
  --compact            Write single survivor file in compact format (<n> <op><i>.<j> ...)
  --membership FILE    Trace each compact SLP in FILE and report FOUND vs PRUNED-AT depth d by rule R
```

### `verify_survivors.py`
```bash
/Users/joe/github/gemini-neon/.venv-tau/bin/python3 verify_survivors.py \
  <file_or_dir>... -K <K> [--workers N] [--dedup] [--resume-state STATE.json] [--out CE.txt]
# Built-in self-test:
/Users/joe/github/gemini-neon/.venv-tau/bin/python3 verify_survivors.py --self-test
```

---

## 5. Verification Results (`tau = 1..8`, `K = 6`)

### Exact Counter Comparison: `tau_certify_exact` vs Original `tau_z9_unconditional.c`
Every counter (`nodes_visited`, `leaves_checked`, `cert_deg`, `cert_prod`, `cert_p31`, `cert_taylor31`, `cert_dup_zero`, `cert_p19`, `cert_p23`, `cert_p29`, `survivors_raw`, `survivors_uniq`) matched the original **bit-for-bit** across all $\tau \in \{1, \dots, 8\}$, with **zero** false positives (`dup_false_positive = zero_false_positive = surv_false_positive = 0`) and `conservation_check = PASS` on every run:

| $\tau$ | `nodes_visited` (`+prefix`) | `leaves_checked` | `cert_deg` | `cert_prod` | `cert_p31` | `cert_taylor31` | `cert_dup_zero` | `cert_p19/23/29` | `survivors_raw` | `survivors_uniq` | `dup_hits` (FP) | `surv_hits` (FP) |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 0 | 7 | 7 | 0 | 0 | 0 | 0 | 0 / 0 / 0 | 0 | 0 | 0 (0) | 0 (0) |
| 2 | 5 | 40 | 40 | 0 | 0 | 0 | 0 | 0 / 0 / 0 | 0 | 0 | 2 (0) | 0 (0) |
| 3 | 44 | 349 | 348 | 1 | 0 | 0 | 0 | 0 / 0 / 0 | 0 | 0 | 26 (0) | 0 (0) |
| 4 | 519 | 4,560 | 4,499 | 53 | 4 | 3 | 0 | 0 / 1 / 0 | 0 | 0 | 236 (0) | 0 (0) |
| 5 | 8,676 (+44) | 78,543 | 75,669 | 2,122 | 321 | 333 | 17 | 44 / 35 / 0 | 2 | 2 | 3,158 (0) | 0 (0) |
| 6 | 195,403 (+44) | 1,724,358 | 1,596,277 | 80,425 | 19,862 | 20,856 | 1,353 | 3,841 / 1,261 / 7 | 476 | 172 | 57,001 (0) | 304 (0) |
| 7 | 5,531,334 (+44) | 46,799,099 | 40,954,686 | 3,152,268 | 1,164,635 | 1,107,787 | 79,491 | 221,890 / 70,151 / 2,516 | 45,675 | 9,237 | 1,347,164 (0) | 36,438 (0) |
| 8 | 190,402,194 (+529) | 1,531,518,439 | 1,248,087,245 | 134,354,537 | 68,502,413 | 56,713,305 | 4,227,185 | 12,071,526 / 3,857,054 / 252,752 | 3,452,422 | 342,991 | 39,947,616 (0) | 3,109,431 (0) |

*Note*: `zero_hash_hits = 0` for all canonical runs because `sub` forbids `i == j` and any pair of earlier wires with $a = \pm b$ is already pruned as a duplicate.

### Apples-to-Apples Performance (`tau = 8`, `K = 6`, 6 threads)
- Original `tau_z9_orig`: **9.268s** (165.2M leaves/s)
- Hardened `tau_certify_exact`: **10.533s** (145.4M leaves/s)
- **Overhead**: **1.136x** (+13.6%) while performing **43,057,047** exact CRT polynomial identity confirmations.

### Additional Tests Passed
- **ASan + UBSan on `tau_certify_exact`**: `tau = 1..7` clean (0 errors).
- **Checkpoint + Resume (`tau = 6`, `split = 2`, 39 items)**: ran `--items 0:20`, then resumed full run (`resumed = 20`); aggregated totals matched uninterrupted run identically (`leaves = 1,724,358`, `survivors_raw = 476`). `verify_survivors.py --dedup` on the 14 compact shard files (`244` per-item unique lines) deduped `72` cross-item duplicates to `172` unique polynomials, matching the global run.
- **`-DEXTRA_PRIMES` (`tau = 6`)**: reduced `survivors_uniq` from `172` to `166` (6 certified by `p = 41`).
- **`-DALT_PRIMES` (`tau = 6`)**: bit-for-bit identical counters to default primes.
- **`-DDUMP_LEAVES` + `--membership` (`tau = 4`)**: dumped `842` unique non-dup/non-zero leaves in compact format; `--membership` confirmed `found = 842, pruned = 0`.
- **`verify_survivors.py`**:
  - `--self-test`: PASSED (10-gate 7-root witness in both legacy and compact formats + $\pm 10^9$ multiplicity Hensel test).
  - `tau = 7` (`9,237` survivors, 6 workers): **0.129s**, 0 counterexamples, `max_exact_hensel = 3`, `accounting_check = PASS`.
  - `tau = 8` (`342,991` survivors, 6 workers): **2.095s**, 0 counterexamples (`deg=51334, sqf_deg=122939, sqf_mod=160548, hensel_ok=8170`), `max_exact_hensel = 4`, `accounting_check = PASS`.

---

## 6. Residual Trust Assumptions

With exact CRT confirmation eliminating all hash-collision assumptions, the remaining trusted base is:
1. **Mathematical soundness of canonicalization & modular/Taylor certificates**:
   - Losslessness of sign canonicalization, dead-gate pruning, lex-key ordering, and exact dup/zero pruning (independently audited against the naive Rust enumerator in `audit/naive_tau/` and mutation tests).
   - Soundness of degree bound, atomic product-factor union bound, simple-root modular certificate mod $p$, and Taylor-stripped certificate at $\{0, \pm 1, \pm 2, \pm 3\}$.
2. **Exact survivor verifier (`verify_survivors.py`)**:
   - Primitive PRS GCD, squarefree factorization, Cauchy root bound, and Hensel lifting in Python arbitrary-precision integers (independently cross-checked against FLINT in `audit/flint_roots.py`).
3. **Platform & toolchain**: C compiler (`clang`), Python interpreter, OS filesystem (`fsync`/`rename`), and CPU hardware.
