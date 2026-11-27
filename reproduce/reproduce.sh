#!/usr/bin/env bash
# Minimal tiered reproduction script for shub-smale-tau9
#
# Usage:
#   ./reproduce/reproduce.sh quick      # ~1-3 min: build C+Rust, tau=1..6 naive cross-check, tau=1..8 exact + verify
#   ./reproduce/reproduce.sh tau9       # ~15 min (12 cores): exact tau=1..9 K=6 + ALT_PRIMES + Python/FLINT verify + digest check
#   ./reproduce/reproduce.sh tau10      # ~9-12h (12 cores, <15 GB peak disk): batched exact tau=10 K=7 + FLINT/Python verify + digest check
#   ./reproduce/reproduce.sh tau10-alt  # ~5h (12 cores): batched disjoint -DALT_PRIMES tau=10 K=7 cross-check (per-item diff == 0)
#
# Environment variables:
#   THREADS=12           Worker threads/processes (default: 12)
#   PYTHON=python3       Python interpreter (set to venv with python-flint to enable FLINT verification)
#   VERIFIER=auto        For tau10: auto (flint if importable else python), flint, python, or both
#   WORKDIR=/tmp/...     Scratch/checkpoint directory (default: /tmp/shub_smale_repro)
#
# Note on mathematical prerequisite: Lean's `zmax_le_of_checklist` requires `hcheck` across ALL
# lengths 1 <= n <= tau (since leaf-duplicate pruning relies on shorter lengths). Thus certifying
# z_max(9) <= 6 requires running tau=1..9 (done by `tau9`), and z_max(10) <= 7 requires tau=1..9
# (certified <= 6 <= 7) plus tau=10 (`tau10`).
set -euo pipefail

TIER="${1:-quick}"
THREADS="${THREADS:-12}"
PYTHON="${PYTHON:-python3}"
VERIFIER="${VERIFIER:-auto}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WORKDIR="${WORKDIR:-/tmp/shub_smale_repro}"
mkdir -p "$WORKDIR/bin" "$WORKDIR/dumps" "$WORKDIR/tau9" "$WORKDIR/tau9_alt"

CC_FLAGS="-O3 -march=native -pthread -Wall -Wextra -Werror"

build_c() {
  echo "=== Building hardened C certifiers ==="
  cc $CC_FLAGS "$ROOT/experiments/pvsnp/tau/tau_certify_exact.c" -o "$WORKDIR/bin/tau_certify_exact"
  cc $CC_FLAGS -DALT_PRIMES "$ROOT/experiments/pvsnp/tau/tau_certify_exact.c" -o "$WORKDIR/bin/tau_certify_exact_alt"
  cc $CC_FLAGS -DDUMP_LEAVES "$ROOT/experiments/pvsnp/tau/tau_certify_exact.c" -o "$WORKDIR/bin/tau_certify_exact_dump"
}

build_rust() {
  echo "=== Building & testing independent naive Rust enumerator ==="
  (cd "$ROOT/audit/naive_tau" && cargo test --release && cargo build --release)
  cp "$ROOT/audit/naive_tau/target/release/naive_tau" "$WORKDIR/bin/naive_tau"
}

has_flint() {
  "$PYTHON" -c "import flint" >/dev/null 2>&1
}

# Strictly collect and validate survivor shards for [A, E) against done.tsv.
# Rejects any missing item row in done.tsv, any missing shard with expected > 0,
# and any per-item or batch-total line-count mismatch.
collect_and_check_shards() {
  local done_tsv="$1"
  local surv_dir="$2"
  local a="$3"
  local e="$4"
  local out_file="$5"

  "$PYTHON" - "$done_tsv" "$surv_dir" "$a" "$e" "$out_file" <<'PYEOF'
import os, sys

done_tsv, surv_dir, a, e, out_file = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
expected = {}
with open(done_tsv, "r") as fp:
    for line in fp:
        if line.startswith("#") or not line.strip():
            continue
        cols = line.strip().split("\t")
        iid = int(cols[0])
        if a <= iid < e:
            if iid in expected:
                sys.exit(f"ERROR: duplicate item_id {iid} in {done_tsv}")
            expected[iid] = int(cols[12])

missing_rows = [iid for iid in range(a, e) if iid not in expected]
if missing_rows:
    sys.exit(f"ERROR: missing {len(missing_rows)} item rows in {done_tsv} for [{a},{e}), first={missing_rows[:5]}")

total_expected = 0
total_written = 0
with open(out_file, "w") as out_fp:
    for iid in range(a, e):
        exp = expected[iid]
        total_expected += exp
        shard = os.path.join(surv_dir, f"{iid}.txt")
        if exp > 0 and not os.path.isfile(shard):
            sys.exit(f"ERROR: missing survivor shard {shard} (done.tsv expects {exp} records)!")
        if os.path.isfile(shard):
            cnt = 0
            with open(shard, "r") as sfp:
                for l in sfp:
                    if l.strip():
                        out_fp.write(l)
                        cnt += 1
            if cnt != exp:
                sys.exit(f"ERROR: shard {shard} line count {cnt} != done.tsv expected {exp}!")
            total_written += cnt
        else:
            if exp != 0:
                sys.exit(f"ERROR: internal mismatch for item {iid}")

if total_written != total_expected:
    sys.exit(f"ERROR: batch total {total_written} != expected {total_expected}!")
print(total_written)
PYEOF
}

# Verify full done.tsv completeness, conservation, 0 false positives, and published digest match.
verify_done_tsv_global() {
  local done_tsv="$1"
  local total_items="$2"
  local ref_gz="$3"

  "$PYTHON" - "$done_tsv" "$total_items" "$ref_gz" <<'PYEOF'
import gzip, sys

done_tsv, total_items, ref_gz = sys.argv[1], int(sys.argv[2]), sys.argv[3]
rows = {}
with open(done_tsv, "r") as fp:
    for line in fp:
        if line.startswith("#") or not line.strip():
            continue
        cols = [int(x) for x in line.strip().split("\t")]
        iid = cols[0]
        if iid in rows:
            sys.exit(f"ERROR: duplicate item_id {iid} in {done_tsv}")
        rows[iid] = cols

if len(rows) != total_items or set(rows.keys()) != set(range(total_items)):
    sys.exit(f"ERROR: {done_tsv} has {len(rows)} items, expected exact 0..{total_items - 1}")

sums = [sum(v[i] for v in rows.values()) for i in range(1, 22)]
leaves = sums[1]
leaf_sum = sum(sums[2:11])
if leaf_sum != leaves:
    sys.exit(f"ERROR: conservation failed ({leaf_sum} != {leaves})")
if sums[14] != 0 or sums[17] != 0 or sums[20] != 0:
    sys.exit(f"ERROR: nonzero false positives: dup_fp={sums[14]} zero_fp={sums[17]} surv_fp={sums[20]}")

if ref_gz:
    ref_rows = {}
    with gzip.open(ref_gz, "rt") as gfp:
        for line in gfp:
            if line.startswith("#") or not line.strip():
                continue
            cols = [int(x) for x in line.strip().split("\t")]
            ref_rows[cols[0]] = cols
    if rows != ref_rows:
        mismatches = [k for k in range(total_items) if rows.get(k) != ref_rows.get(k)]
        sys.exit(f"ERROR: per-item mismatch vs published digest {ref_gz}: {len(mismatches)} items differ (first={mismatches[:5]})")
    print(f"GLOBAL_CHECK PASS: {total_items}/{total_items} items, leaves={leaves}, surv_uniq={sums[11]}, FP=0, matches published digest {ref_gz}")
else:
    print(f"GLOBAL_CHECK PASS: {total_items}/{total_items} items, leaves={leaves}, surv_uniq={sums[11]}, FP=0")
PYEOF
}

case "$TIER" in
  quick)
    build_c
    build_rust
    echo "=== Self-testing verify_survivors.py ==="
    "$PYTHON" "$ROOT/experiments/pvsnp/tau/verify_survivors.py" --self-test
    echo "=== Dump cross-check tau=1..6 against independent naive Rust enumerator ==="
    for t in 1 2 3 4 5 6; do
      "$WORKDIR/bin/tau_certify_exact_dump" "$t" 6 "$THREADS" "$WORKDIR/dumps/tau${t}.txt" --compact
      "$WORKDIR/bin/naive_tau" --threads "$THREADS" eval-dump "$WORKDIR/dumps/tau${t}.txt" "$t"
    done
    echo "=== Exact-CRT tau=1..8 K=6 + exact Z[x] verification ==="
    for t in 1 2 3 4 5 6 7 8; do
      "$WORKDIR/bin/tau_certify_exact" "$t" 6 "$THREADS" "$WORKDIR/tau9/surv_tau${t}.txt" --compact
      if [ -s "$WORKDIR/tau9/surv_tau${t}.txt" ]; then
        "$PYTHON" "$ROOT/experiments/pvsnp/tau/verify_survivors.py" "$WORKDIR/tau9/surv_tau${t}.txt" 6 --workers "$THREADS"
      fi
    done
    echo "=== QUICK REPRODUCTION PASSED ==="
    ;;

  tau9)
    build_c
    echo "=== Running exact-CRT tau=1..8 K=6 (required by hcheck for all lengths 1..9) ==="
    for t in 1 2 3 4 5 6 7 8; do
      "$WORKDIR/bin/tau_certify_exact" "$t" 6 "$THREADS" "$WORKDIR/tau9/surv_tau${t}.txt" --compact
      if [ -s "$WORKDIR/tau9/surv_tau${t}.txt" ]; then
        "$PYTHON" "$ROOT/experiments/pvsnp/tau/verify_survivors.py" "$WORKDIR/tau9/surv_tau${t}.txt" 6 --workers "$THREADS"
      fi
    done
    echo "=== Running exact-CRT tau=9 K=6 (checkpointed) ==="
    "$WORKDIR/bin/tau_certify_exact" 9 6 "$THREADS" --checkpoint "$WORKDIR/tau9"
    verify_done_tsv_global "$WORKDIR/tau9/done.tsv" 485 "$ROOT/reproduce/digests/tau9_k6_items.tsv.gz"
    N9=$(collect_and_check_shards "$WORKDIR/tau9/done.tsv" "$WORKDIR/tau9/surv" 0 485 "$WORKDIR/tau9/all_surv.txt")
    echo "=== Verifying all $N9 tau=9 survivor records in exact Z[x] ==="
    "$PYTHON" "$ROOT/experiments/pvsnp/tau/verify_survivors.py" "$WORKDIR/tau9/all_surv.txt" 6 --workers "$THREADS"
    if has_flint; then
      echo "=== Cross-checking all $N9 tau=9 survivor records via python-flint ==="
      "$PYTHON" "$ROOT/audit/flint_roots.py" "$WORKDIR/tau9/all_surv.txt" 6 --workers "$THREADS" > "$WORKDIR/tau9/flint.log"
      cat "$WORKDIR/tau9/flint.log"
      grep -q "processed=${N9} " "$WORKDIR/tau9/flint.log"
      grep -q "hits=0 K=6" "$WORKDIR/tau9/flint.log"
    else
      echo "NOTE: python-flint not installed in $PYTHON; skipping optional FLINT cross-check."
    fi
    rm -f "$WORKDIR/tau9/all_surv.txt"
    echo "=== Running independent ALT_PRIMES cross-check (tau=9) ==="
    "$WORKDIR/bin/tau_certify_exact_alt" 9 6 "$THREADS" --checkpoint "$WORKDIR/tau9_alt"
    diff <(grep -v '^#' "$WORKDIR/tau9/done.tsv" | sort -n) <(grep -v '^#' "$WORKDIR/tau9_alt/done.tsv" | sort -n)
    echo "=== TAU=9 FULL REPRODUCTION PASSED (per-item diff == 0, digest matched) ==="
    ;;

  tau10)
    build_c
    MODE="$VERIFIER"
    if [ "$MODE" = "auto" ]; then
      if has_flint; then MODE="flint"; else MODE="python"; fi
    fi
    if [ "$MODE" = "flint" ] || [ "$MODE" = "both" ]; then
      has_flint || { echo "ERROR: VERIFIER=$MODE requires python-flint in $PYTHON" >&2; exit 1; }
    fi
    echo "=== Running batched exact-CRT tau=10 K=7 (500-item batches, verifier=$MODE) ==="
    echo "NOTE: Full z_max(10) <= 7 certification also requires tau=1..9 (verified by ./reproduce/reproduce.sh tau9)."
    mkdir -p "$WORKDIR/tau10/surv" "$WORKDIR/tau10/logs"

    for ((A=0; A<8774; A+=500)); do
      E=$((A + 500)); [ "$E" -gt 8774 ] && E=8774
      TAG="${A}_${E}"
      DONE_FLAG="$WORKDIR/tau10/logs/batch_${TAG}.DONE"
      if [ -f "$DONE_FLAG" ]; then
        echo "[BATCH $TAG] .DONE present; will still verify global done.tsv & logs at end."
        continue
      fi

      "$WORKDIR/bin/tau_certify_exact" 10 7 "$THREADS" --split 4 --items "${A}:${E}" --checkpoint "$WORKDIR/tau10" \
        > "$WORKDIR/tau10/logs/batch_${TAG}_c.log"

      BATCH="$WORKDIR/tau10/batch_${TAG}_surv.txt"
      NLINES=$(collect_and_check_shards "$WORKDIR/tau10/done.tsv" "$WORKDIR/tau10/surv" "$A" "$E" "$BATCH")
      echo "[BATCH $TAG] verified per-item shard counts: total_records=$NLINES"

      if [ "$NLINES" -gt 0 ]; then
        if [ "$MODE" = "flint" ] || [ "$MODE" = "both" ]; then
          "$PYTHON" "$ROOT/audit/flint_roots.py" "$BATCH" 7 --workers "$THREADS" \
            > "$WORKDIR/tau10/logs/batch_${TAG}_flint.log"
          cat "$WORKDIR/tau10/logs/batch_${TAG}_flint.log"
          grep -q "processed=${NLINES} " "$WORKDIR/tau10/logs/batch_${TAG}_flint.log"
          if ! grep -q "hits=0 K=7" "$WORKDIR/tau10/logs/batch_${TAG}_flint.log"; then
            echo "!!! FLINT REPORTED HITS > 0 (>=8 ROOTS) IN BATCH $TAG !!!" >&2
            grep '^HIT ' "$WORKDIR/tau10/logs/batch_${TAG}_flint.log" | awk -F' \\| ' '{print $3}' > "$WORKDIR/tau10/logs/batch_${TAG}_hits.txt"
            "$PYTHON" "$ROOT/experiments/pvsnp/tau/verify_survivors.py" "$WORKDIR/tau10/logs/batch_${TAG}_hits.txt" 7 --workers "$THREADS" --out "$WORKDIR/tau10/logs/batch_${TAG}_ce.txt" || true
            exit 42
          fi
        fi
        if [ "$MODE" = "python" ] || [ "$MODE" = "both" ]; then
          "$PYTHON" "$ROOT/experiments/pvsnp/tau/verify_survivors.py" "$BATCH" 7 --workers "$THREADS" --out "$WORKDIR/tau10/logs/batch_${TAG}_ce.txt" \
            > "$WORKDIR/tau10/logs/batch_${TAG}_verify.log"
          cat "$WORKDIR/tau10/logs/batch_${TAG}_verify.log"
          grep -q "processed=${NLINES} == total=${NLINES}" "$WORKDIR/tau10/logs/batch_${TAG}_verify.log"
          grep -q "COUNTEREXAMPLE  = 0" "$WORKDIR/tau10/logs/batch_${TAG}_verify.log"
        fi
      fi

      rm -f "$BATCH"
      for ((id=A; id<E; id++)); do rm -f "$WORKDIR/tau10/surv/${id}.txt"; done
      printf "verified_records=%s mode=%s finished=%s\n" "$NLINES" "$MODE" "$(date '+%Y-%m-%dT%H:%M:%S')" > "$DONE_FLAG"
    done

    # Never trust .DONE alone: validate all 8,774 rows in done.tsv, conservation, 0 FP,
    # match against published per-item digest, and confirm all 18 batch logs passed with exact counts!
    verify_done_tsv_global "$WORKDIR/tau10/done.tsv" 8774 "$ROOT/reproduce/digests/tau10_k7_items.tsv.gz"
    "$PYTHON" - "$WORKDIR/tau10" <<'PYEOF'
import os, re, sys
root = sys.argv[1]
done_tsv = os.path.join(root, "done.tsv")
exp_by_item = {}
with open(done_tsv) as fp:
    for line in fp:
        if line.startswith("#") or not line.strip(): continue
        cols = line.strip().split("\t")
        exp_by_item[int(cols[0])] = int(cols[12])
tot_verified = 0
for a in range(0, 8774, 500):
    e = min(a + 500, 8774)
    tag = f"{a}_{e}"
    exp = sum(exp_by_item[i] for i in range(a, e))
    flint_log = os.path.join(root, "logs", f"batch_{tag}_flint.log")
    py_log = os.path.join(root, "logs", f"batch_{tag}_verify.log")
    ok = False
    if exp == 0:
        ok = True
    if os.path.isfile(flint_log):
        txt = open(flint_log).read()
        if f"processed={exp} " in txt and "hits=0 K=7" in txt:
            ok = True
    if os.path.isfile(py_log):
        txt = open(py_log).read()
        if f"processed={exp} == total={exp}" in txt and "COUNTEREXAMPLE  = 0" in txt:
            ok = True
    if not ok:
        sys.exit(f"ERROR: batch {tag} lacks a passing verification log for all {exp} expected records!")
    tot_verified += exp
print(f"ALL_18_BATCH_LOGS PASS: total_verified_records={tot_verified} (0 counterexamples)")
PYEOF
    echo "=== TAU=10 PRIMARY REPRODUCTION PASSED (run ./reproduce/reproduce.sh tau10-alt for disjoint ALT_PRIMES cross-check) ==="
    ;;

  tau10-alt)
    build_c
    echo "=== Running disjoint -DALT_PRIMES tau=10 K=7 cross-check (8,774 items, 500-item batches) ==="
    mkdir -p "$WORKDIR/tau10_alt/surv" "$WORKDIR/tau10_alt/logs"
    for ((A=0; A<8774; A+=500)); do
      E=$((A + 500)); [ "$E" -gt 8774 ] && E=8774
      TAG="${A}_${E}"
      DONE_FLAG="$WORKDIR/tau10_alt/logs/batch_${TAG}.DONE"
      [ -f "$DONE_FLAG" ] && continue
      "$WORKDIR/bin/tau_certify_exact_alt" 10 7 "$THREADS" --split 4 --items "${A}:${E}" --checkpoint "$WORKDIR/tau10_alt" \
        > "$WORKDIR/tau10_alt/logs/batch_${TAG}_c.log"
      for ((id=A; id<E; id++)); do rm -f "$WORKDIR/tau10_alt/surv/${id}.txt"; done
      date '+%Y-%m-%dT%H:%M:%S' > "$DONE_FLAG"
    done
    verify_done_tsv_global "$WORKDIR/tau10_alt/done.tsv" 8774 "$ROOT/reproduce/digests/tau10_k7_items.tsv.gz"
    if [ -f "$WORKDIR/tau10/done.tsv" ]; then
      diff <(grep -v '^#' "$WORKDIR/tau10/done.tsv" | sort -n) <(grep -v '^#' "$WORKDIR/tau10_alt/done.tsv" | sort -n)
    fi
    echo "=== TAU=10 ALT_PRIMES CROSS-CHECK PASSED (8,774/8,774 items exact per-item diff == 0) ==="
    ;;

  *)
    echo "Usage: $0 {quick|tau9|tau10|tau10-alt}" >&2
    exit 1
    ;;
esac
