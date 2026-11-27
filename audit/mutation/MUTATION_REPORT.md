# Mutation & Canary Test Report

Script: [run_mutations.sh](file:///tmp/shub-smale-tau9/audit/mutation/run_mutations.sh)

## 1. Canaries (Unmodified `tau_certify_exact`)

Every known counterexample was detected by both `verify_survivors.py` (exact Python `Z[x]`) and `audit/flint_roots.py` (independent `python-flint` `fmpz_poly.factor()`):

| Canary | Config | `survivors_uniq` | `verify_survivors.py` CE | `flint_roots.py` hits | Witness roots | Verdict |
|---|---|---:|---:|---:|---|---|
| `tau=6, K=4` | full search | 597 | 2 (exit 2) | 2 (`max_z=5`) | `{-2,-1,0,1,2}` | **PASS** |
| `tau=8, K=5` | full search | 473,048 | 4 (exit 2) | 4 (`max_z=6`) | `{-3,-2,-1,0,1,2}`, `{-2,-1,0,1,2,3}` | **PASS** |
| `tau=10, K=6` | `--prefix "a0.0 a0.2 m1.1 s2.4 m3.3 s4.6 m5.5"` (`slpWitness10`) | 2 | 2 (exit 2) | 2 (`max_z=7`) | `{-3,-2,-1,0,1,2,3}` | **PASS** |
| `tau=8, K=1` | `--prefix "a0.0 a2.2 a3.3 a4.4 a5.5 s0.6 a1.7"` (`x(x-31)`) | 1 | 1 (exit 2) | — | `{0, 31}` | **PASS** |

## 2. Rule-Disabling Mutants (`tau=4`, `-DDUMP_LEAVES`)

Baseline `tau=4`: `nodes_visited = 519`, `leaves_checked = 4,560`, `|DumpSet±| = 842`, `|New±(4)| = 716`.

| Mutant | `nodes_visited` | `leaves_checked` | `|DumpSet±|` | `missing` (`New±(4) \ Dump`) | `extra` | Verdict |
|---|---:|---:|---:|---:|---:|---|
| Baseline | 519 | 4,560 | 842 | 0 | 0 | — |
| `MUT_NO_DEADGATE` | 529 | 19,400 | 845 | 0 | 0 | **PASS** (counts changed, set exact) |
| `MUT_NO_KEYORDER` | 854 | 5,865 | 842 | 0 | 0 | **PASS** (counts changed, set exact) |
| `MUT_NO_SIGNCANON` | 1,800 | 32,300 | 842 | 0 | 0 | **PASS** (counts changed, set exact) |
| `MUT_NO_DUP` | 1,519 | 11,984 | 845 | 0 | 0 | **PASS** (counts changed, set exact) |

## 3. Planted Bugs

| Planted Bug | Detection Mechanism | Observed Effect | Verdict |
|---|---|---|---|
| `BUG_DEADGATE_OFF_BY_ONE` | `eval-dump` (`tau=5`) & `--membership` (`tau=9`, 5k) | `missing = 51` (exit 1); `3,690 / 5,000` canonical SLPs pruned | **DETECTED** |
| `BUG_NO_SQUARE` | `eval-dump` (`tau=5`) & `--membership` (`tau=9`, 5k) | `missing = 4,155` (exit 1); `4,028 / 5,000` canonical SLPs pruned | **DETECTED** |
| `BUG_SKIP_SUB_INPUTS` | `eval-dump` (`tau=5`) & `--membership` (`tau=9`, 5k) | `missing = 847` (exit 1); `1,628 / 5,000` canonical SLPs pruned | **DETECTED** |
| `BUG_IGNORE_DOUBLES` | Synthetic mod-31 double-root canary `x(x-31)` (`tau=8, K=1`) | Clean finds `roots=2 [0,31]` (exit 2); mutant falsely certifies via `cert_p31=1` (`survivors=0`, exit 0). Also drops `tau=8 K=5` survivors `473,048 -> 2,853`. | **DETECTED** |
| `BUG_TAYLOR_M0` | Mathematical equivalence analysis | **Equivalent mutant:** `dbl_mask` only sets bit `b` when `f(r_b) ≡ 0 (mod p)`. Whenever `m == 0`, `c_m = f(r_b)` satisfies `c_m % p == 0`, so the immediately following guard `if ((cm % p) == 0) return 0;` already unconditionally rejects `m == 0`. All counters are provably identical. | **EQUIVALENT MUTANT** |
