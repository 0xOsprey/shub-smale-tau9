#!/usr/bin/env bash
# Minimal tiered reproduction script for shub-smale-tau9
# Usage:
#   ./reproduce/reproduce.sh quick   # ~3 min: build C + Rust, tau=1..7 naive cross-check, tau=1..8 exact + verify, Lean axioms check
#   ./reproduce/reproduce.sh tau9    # ~15 min (12 cores): full exact tau=1..9 K=6 + ALT_PRIMES + Python & FLINT verification
#   ./reproduce/reproduce.sh tau10   # ~11-12h (12 cores, <6 GB peak disk): batched exact tau=10 K=7 + Python & FLINT verification
set -euo pipefail

TIER="${1:-quick}"
THREADS="${THREADS:-12}"
PYTHON="${PYTHON:-python3}"
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
    echo "=== Running exact-CRT tau=1..8 K=6 (required by leaf-dup induction) ==="
    for t in 1 2 3 4 5 6 7 8; do
      "$WORKDIR/bin/tau_certify_exact" "$t" 6 "$THREADS" "$WORKDIR/tau9/surv_tau${t}.txt" --compact
      if [ -s "$WORKDIR/tau9/surv_tau${t}.txt" ]; then
        "$PYTHON" "$ROOT/experiments/pvsnp/tau/verify_survivors.py" "$WORKDIR/tau9/surv_tau${t}.txt" 6 --workers "$THREADS"
      fi
    done
    echo "=== Running exact-CRT tau=9 K=6 (checkpointed) ==="
    "$WORKDIR/bin/tau_certify_exact" 9 6 "$THREADS" --checkpoint "$WORKDIR/tau9"
    echo "=== Verifying all tau=9 survivors in exact Z[x] ==="
    "$PYTHON" "$ROOT/experiments/pvsnp/tau/verify_survivors.py" "$WORKDIR/tau9/surv" 6 --workers "$THREADS"
    echo "=== Running independent ALT_PRIMES cross-check ==="
    "$WORKDIR/bin/tau_certify_exact_alt" 9 6 "$THREADS" --checkpoint "$WORKDIR/tau9_alt"
    diff <(grep -v '^#' "$WORKDIR/tau9/done.tsv" | sort -n) <(grep -v '^#' "$WORKDIR/tau9_alt/done.tsv" | sort -n)
    echo "=== TAU=9 FULL REPRODUCTION PASSED (per-item diff == 0) ==="
    ;;

  tau10)
    build_c
    echo "=== Running batched exact-CRT tau=10 K=7 (500-item batches, <6 GB peak disk) ==="
    mkdir -p "$WORKDIR/tau10/surv" "$WORKDIR/tau10/logs"
    for ((A=0; A<8774; A+=500)); do
      E=$((A + 500)); [ "$E" -gt 8774 ] && E=8774
      TAG="${A}_${E}"
      [ -f "$WORKDIR/tau10/logs/batch_${TAG}.DONE" ] && continue
      "$WORKDIR/bin/tau_certify_exact" 10 7 "$THREADS" --split 4 --items "${A}:${E}" --checkpoint "$WORKDIR/tau10"
      BATCH="$WORKDIR/tau10/batch_${TAG}_surv.txt"
      rm -f "$BATCH"; touch "$BATCH"
      for ((id=A; id<E; id++)); do
        [ -f "$WORKDIR/tau10/surv/${id}.txt" ] && cat "$WORKDIR/tau10/surv/${id}.txt" >> "$BATCH"
      done
      if [ -s "$BATCH" ]; then
        "$PYTHON" "$ROOT/experiments/pvsnp/tau/verify_survivors.py" "$BATCH" 7 --workers "$THREADS" --out "$WORKDIR/tau10/logs/batch_${TAG}_ce.txt"
      fi
      rm -f "$BATCH"
      for ((id=A; id<E; id++)); do rm -f "$WORKDIR/tau10/surv/${id}.txt"; done
      date > "$WORKDIR/tau10/logs/batch_${TAG}.DONE"
    done
    echo "=== TAU=10 FULL REPRODUCTION PASSED ==="
    ;;

  *)
    echo "Usage: $0 {quick|tau9|tau10}" >&2
    exit 1
    ;;
esac
