# Second-Pass Adversarial Red-Team Audit Report (Hardened Pipeline)

(Output of the second-pass read-only red-team subagent auditing `tau_certify_exact.c`, `verify_survivors.py`, and `EXACT_PIPELINE.md`.)

**Overall verdict:** **0 CRITICAL soundness bugs.** The core exact CRT identity test, lazy `eval_q0` cache invalidation, exact survivor deduplication, `-DEXTRA_PRIMES`, `--membership`, and `verify_survivors.py` mathematical core are all **sound**. However, there are **3 MODERATE** operational/crash bugs in checkpoint/resume and CLI edge cases, plus **3 MINOR** hardening gaps.

## Summary of Findings

1. **Exact CRT Confirm-on-Hit Test — OK**
   - `deg_ub` (`uint16_t`, max `4096`), `nb` (`uint32_t`, max `2048`), 40 hard-coded primes in `(2^60, 2^61)` (independently verified 40/40 prime & distinct via 12-base deterministic 64-bit Miller-Rabin), CRT margin `Q > 4 * |c_k(h)|`, `m61_*` and `mq_*` arithmetic, lazy `eval_q0` cache invalidation across every `path[depth]` write, and exact survivor dedup (`exact_slps_equal_upto_sign`) are all sound.
2. **`-DEXTRA_PRIMES` — OK**
   - `[64]` array bounds hold max prime `53`; `dbl_mask` bits `0..6` match `{0,1,-1,2,-2,3,-3}` and are pairwise distinct for all `p >= 19`; `K < 19` guard forces nonzero `f mod p`; no `uint8_t`/`int` overflow.
3. **Checkpoint / Resume (`--checkpoint`, `--items`, `--sample`, `--split`, `--prefix`) — MODERATE (3 bugs)**
   - **[MODERATE-1]** Partial `done.tsv` line on crash + `fopen(..., "a")` append causes silent row corruption & skipped items; `parse_done_row` does not verify EOL after the `nf`-th field (also breaks cross-build resume between default and `-DEXTRA_PRIMES`).
   - **[MODERATE-2]** `--prefix` of length `tau` combined with `--checkpoint DIR` leaves `g_surv.tab == NULL` and segfaults on a surviving leaf.
   - **[MODERATE-3]** No metadata header in `done.tsv` to validate `(tau, K, split_depth, prefix, EXTRA_PRIMES, ALT_PRIMES)` on resume.
   - **[MINOR-1]** `--sample 0.0 SEED` still selects an item if `h == 0` (prob `2^-64`).
4. **`--membership` Mode — OK**
   - `trace_gates` mirrors `dfs` + `check_leaf` pruning identically at both internal and leaf depths under all `MUT_*` / `BUG_*` flags.
5. **`verify_survivors.py` — OK (1 MODERATE usability footgun, 2 MINOR nits)**
   - Compact/legacy parsing, exact `--dedup`, `iter_primes()`, PRS/sqf/Cauchy/Hensel, exception propagation, and `processed == total` accounting assertions are sound.
   - **[MODERATE-4]** Passing a directory with 0 `*.txt` files (e.g., checkpoint root `DIR` instead of `DIR/surv/`) silently prints `0 survivors -> 100% CERTIFIED` and exits 0.
   - **[MINOR-2]** `parse_and_eval_compact` does not reject negative wire indices.
   - **[MINOR-3]** `--resume-state` validates `(n_lines, num_chunks, K)` but not input paths or `--dedup`.
