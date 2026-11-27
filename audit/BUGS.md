# Audit bug / overclaim log

Every bug, gap, or overclaim found, including ones that weaken the claim.
Status legend: PLANNER-FOUND, CONFIRMED, REFUTED, FIXED.

| ID | Kind | Description | Status |
|----|------|-------------|--------|
| F1 | Gap | Internal/leaf dup/zero pruning (`compute_hash_and_check_dup`, lines 271-299; leaf at 637) fires on 2-point hash equality. A collision would silently drop a genuine subtree. True duplicates always hash-match, so an exact confirm-on-hit makes the pruning sound. | CONFIRMED (red team) |
| F2 | Gap | Survivor dedup (`record_survivor`, lines 210-244) uses a 3-prime fingerprint; a collision silently drops a survivor before exact verification. `-DALT_PRIMES` only compared 12 aggregate counters, not survivor sets. | CONFIRMED (red team) |
| F3 | Overclaim | "Schwartz-Zippel d^2/(P1P2)", "<10^-16", "<10^-13", and "<10^-40" collision statements are invalid: evaluation points are fixed, not random, and degree factors (d up to 512 at leaves) were dropped (README l.23, paper l.246-247, z9 report l.113-115). | CONFIRMED (red team) |
| F4 | Overclaim | "Provably lossless" / "unconditionally proved" framing has no formal proof for canonicalization rules, `cert_taylor`, `cert_prod`, C/Python code, or collision-freeness. | CONFIRMED (red team) |
| F5 | Doc | Header comment in `tau_z9_unconditional.c` l.8 lists fallback primes {37,41,43}; code uses only {19,23,29}. Lines 380-385 say `mod t^8`, `m>=8`, `8*LIM^2` while `TAYLOR_DEG=12`. | CONFIRMED (red team) |
| F6 | Doc | Taylor-certificate justification in report/paper ("p >= 19 > 6 = max|r-r'|") is not the core argument; correct one: f=(x-b)^m g, g(b)!=0 mod p => no integer root s!=b with s==b mod p. | CONFIRMED (red team) |
| F7 | Doc | Leaf-dup rule makes tau=9 depend on tau=1..8 runs with same K, but reproducibility snippets run only tau=9. | CONFIRMED (red team) |
| F8 | Doc | "Matches tau_parallel.c to the exact integer" is not an independent check (shared lineage & shared `nodes_visited` undercount bug). | CONFIRMED (red team) |
| R1 | Bug (CLI) | `K = 0` is permitted (`tau_z9_unconditional.c:900`), yet `cert_dup_zero` prunes `1*x = x` assuming z_max(0) = 1 <= K. Unsound at K=0 (does not affect K=6). | CONFIRMED (red team) |
| R2 | Bug (Telemetry) | `collect_work` (`771-827`) never increments `nodes_visited`, undercounting internal nodes by 44 (tau=5..7) and 529 (tau=8..9). True tau=9 internal nodes = 7,767,649,524, not 7,767,648,995. | CONFIRMED (red team) |
| R3 | Bug (CLI/IO) | `nthreads <= 0` (`897, 947`) silently spawns 0 threads for tau>=5; no CLI bounds check on `tau < 1` or `tau > MAX_TAU`; `calloc`/`realloc`/`fprintf`/`fclose` errors unchecked (`969`). | CONFIRMED (red team) |
| R4 | Gap (Verifier) | `verify_z9_all_Z.py` does not assert `sum(tot.values()) == n` or compare `n` against C's `survivors_uniq`. | CONFIRMED (red team) |
| R5 | Overclaim/Doc | `paper/tau_conjecture_z9.tex:49` claims "706 public theorems in 42 modules" (copied from parent workspace `gemini-neon`; the public `shub-smale-tau9` repo has 6 modules, 80 theorem/lemma decls). `README.md:63` says "4 modules, 893 LOC" (actual: 6 modules, 1,401 LOC); `README.md:1,11,30` says "up to tau=15" while table goes to tau=18. | CONFIRMED (red team) |
| R6 | Doc | `paper/tau_conjecture_z9.tex:150` misdescribes `verify_z9_all_Z.py`: claims code checks `p ∤ lc(g)` and squarefreeness in F_p[x] and divides Cauchy bound by `|lc(g)|` (code doesn't, though math is still sound). | CONFIRMED (red team) |
| E1 | Bug (Ckpt) | Second-pass audit of `tau_certify_exact.c`: partial `done.tsv` line on crash + `parse_done_row` not checking trailing EOL; no `# meta` header validation on resume. | FIXED (`tau_certify_exact.c`) |
| E2 | Bug (CLI) | Second-pass audit of `tau_certify_exact.c`: `--prefix` of length `tau` under `--checkpoint` segfaulted on surviving leaf; `--sample 0.0` edge case. | FIXED (`tau_certify_exact.c`) |
| E3 | Bug (CLI) | Second-pass audit of `verify_survivors.py`: passing a directory with 0 `*.txt` files (e.g. checkpoint root instead of `surv/`) silently reported `0 survivors -> 100% CERTIFIED`; negative compact wire indices unchecked. | FIXED (`verify_survivors.py`) |
