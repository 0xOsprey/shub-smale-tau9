#!/usr/bin/env bash
set -euo pipefail

REPO=/tmp/shub-smale-tau9
SRC=$REPO/experiments/pvsnp/tau/tau_certify_exact.c
VERIFY=$REPO/experiments/pvsnp/tau/verify_survivors.py
FLINT=$REPO/audit/flint_roots.py
PY=/Users/joe/github/gemini-neon/.venv-tau/bin/python3
BIN=/Users/joe/github/gemini-neon/runs/bin
NAIVE=$BIN/naive_tau
EXACT=$BIN/tau_certify_exact
MUTDIR=/Users/joe/github/gemini-neon/runs/mut
mkdir -p "$MUTDIR"

CC="cc -O3 -march=native -pthread -Wall -Wextra"

run_expect_ce() {
  set +e
  "$@"
  local rc=$?
  set -e
  echo "  -> exit_code=$rc (expect nonzero when CE present)"
}

echo "============================================================"
echo "1. CANARY TESTS (unmodified tau_certify_exact)"
echo "============================================================"

echo "--- Canary 1a: tau=6 K=4 (expect >=1 5-root counterexample) ---"
"$EXACT" 6 4 6 "$MUTDIR/canary_tau6_k4.txt" --compact
run_expect_ce "$PY" "$VERIFY" "$MUTDIR/canary_tau6_k4.txt" 4 --workers 6 --out "$MUTDIR/canary_tau6_k4_ce.txt"
run_expect_ce "$PY" "$FLINT" "$MUTDIR/canary_tau6_k4.txt" 4 --workers 6

echo "--- Canary 1b: tau=8 K=5 (expect >=1 6-root counterexample) ---"
"$EXACT" 8 5 6 "$MUTDIR/canary_tau8_k5.txt" --compact
run_expect_ce "$PY" "$VERIFY" "$MUTDIR/canary_tau8_k5.txt" 5 --workers 6 --out "$MUTDIR/canary_tau8_k5_ce.txt"
run_expect_ce "$PY" "$FLINT" "$MUTDIR/canary_tau8_k5.txt" 5 --workers 6

echo "--- Canary 1c: tau=10 K=6 with canonical slpWitness10 prefix (expect 7-root counterexample) ---"
"$EXACT" 10 6 6 "$MUTDIR/canary_tau10_k6.txt" --compact --prefix "a0.0 a0.2 m1.1 s2.4 m3.3 s4.6 m5.5"
run_expect_ce "$PY" "$VERIFY" "$MUTDIR/canary_tau10_k6.txt" 6 --workers 6 --out "$MUTDIR/canary_tau10_k6_ce.txt"
run_expect_ce "$PY" "$FLINT" "$MUTDIR/canary_tau10_k6.txt" 6 --workers 6

echo "============================================================"
echo "2. RULE-DISABLING MUTANTS (tau=4 dump cross-check)"
echo "============================================================"
# Baseline tau=4: nodes_visited=519, leaves_checked=4560
for M in MUT_NO_DEADGATE MUT_NO_KEYORDER MUT_NO_SIGNCANON MUT_NO_DUP; do
  echo "--- Mutant: $M (tau=4) ---"
  $CC -DDUMP_LEAVES -D"$M" "$SRC" -o "$MUTDIR/bin_${M}"
  "$MUTDIR/bin_${M}" 4 6 6 "$MUTDIR/dump_${M}_tau4.txt" --compact
  "$NAIVE" --threads 6 eval-dump "$MUTDIR/dump_${M}_tau4.txt" 4
done

echo "============================================================"
echo "3. PLANTED BUGS (must be DETECTED)"
echo "============================================================"

# Slice 5000 random canonical tau=9 SLPs for fast membership detection
head -n 5000 "$MUTDIR/rand_canon_tau9.txt" > "$MUTDIR/rand_canon_tau9_5k.txt"

for B in BUG_DEADGATE_OFF_BY_ONE BUG_NO_SQUARE BUG_SKIP_SUB_INPUTS; do
  echo "--- Planted Bug (search/pruning): $B ---"
  $CC -DDUMP_LEAVES -D"$B" "$SRC" -o "$MUTDIR/bin_${B}_dump"
  "$MUTDIR/bin_${B}_dump" 5 6 6 "$MUTDIR/dump_${B}_tau5.txt" --compact
  set +e
  "$NAIVE" --threads 6 eval-dump "$MUTDIR/dump_${B}_tau5.txt" 5
  rc=$?
  set -e
  echo "eval-dump exit code for $B = $rc (expect nonzero / missing > 0)"

  $CC -D"$B" "$SRC" -o "$MUTDIR/bin_${B}"
  "$MUTDIR/bin_${B}" 9 6 6 --membership "$MUTDIR/rand_canon_tau9_5k.txt" | tail -n 5
done

for B in BUG_TAYLOR_M0 BUG_IGNORE_DOUBLES; do
  echo "--- Planted Bug (certificate): $B ---"
  $CC -D"$B" "$SRC" -o "$MUTDIR/bin_${B}"
  echo "  [tau=6 K=4 canary]"
  "$MUTDIR/bin_${B}" 6 4 6 "$MUTDIR/surv_${B}_tau6_k4.txt" --compact
  run_expect_ce "$PY" "$VERIFY" "$MUTDIR/surv_${B}_tau6_k4.txt" 4 --workers 6
  echo "  [tau=8 K=5 canary]"
  "$MUTDIR/bin_${B}" 8 5 6 "$MUTDIR/surv_${B}_tau8_k5.txt" --compact
  run_expect_ce "$PY" "$VERIFY" "$MUTDIR/surv_${B}_tau8_k5.txt" 5 --workers 6
  echo "  [tau=10 K=6 slpWitness10 prefix canary]"
  "$MUTDIR/bin_${B}" 10 6 6 "$MUTDIR/surv_${B}_tau10_k6.txt" --compact --prefix "a0.0 a0.2 m1.1 s2.4 m3.3 s4.6 m5.5"
  run_expect_ce "$PY" "$VERIFY" "$MUTDIR/surv_${B}_tau10_k6.txt" 6 --workers 6
done

echo "--- Synthetic mod-31 double-root canary: x*(x-31) at tau=8 K=1 (kills BUG_IGNORE_DOUBLES) ---"
"$EXACT" 8 1 1 "$MUTDIR/canary_x31_clean.txt" --compact --prefix "a0.0 a2.2 a3.3 a4.4 a5.5 s0.6 a1.7"
run_expect_ce "$PY" "$VERIFY" "$MUTDIR/canary_x31_clean.txt" 1 --workers 1
"$MUTDIR/bin_BUG_IGNORE_DOUBLES" 8 1 1 "$MUTDIR/canary_x31_bug.txt" --compact --prefix "a0.0 a2.2 a3.3 a4.4 a5.5 s0.6 a1.7"
run_expect_ce "$PY" "$VERIFY" "$MUTDIR/canary_x31_bug.txt" 1 --workers 1

echo "=== MUTATION SUITE FINISHED ==="
