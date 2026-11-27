#!/usr/bin/env python3
"""Independent exact integer-root counter using python-flint (fmpz_poly).

Supported input line formats (auto-detected per line):
  1. Bare polynomial (prefixed with 'P '):
       P <c0> <c1> ... <cd>     (ascending degree integer coefficients)
  2. COMPACT SLP format:
       <n> <op><i>.<j> ...      (op in {a,s,m}; wire 0=1, 1=x, k+2=gate k)
  3. Legacy SLP format:
       <h1 h2 h3> | g1 = ...; g2 = ...; ...   (1-based g<k> = wire k+1)
     or just:
       g1 = ...; g2 = ...; ...

Usage:
  python3 flint_roots.py FILE K [--workers N] [--chunk-size M] [--exact-all]

Counts DISTINCT integer roots of each nonzero polynomial using FLINT's exact
fmpz_poly.factor() (degree-1 factors with leading coeff +/-1, including x).
When --exact-all is NOT set, polynomials with degree <= K are soundly skipped
(a nonzero polynomial of degree d has at most d distinct integer roots) and
counted in the deg<=K prefilter rule.

Outputs:
  HIT <count> | <c0 c1 ...> | <original line>   for every poly with count > K
  HIST <z> <count>                              histogram of exact root counts
  SUMMARY ...                                   totals and prefilter counts
Asserts processed_count == total_nonempty_lines (fails loudly otherwise).
"""

import argparse
import os
import re
import sys
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
import flint
from flint import fmpz_poly

_ONE = fmpz_poly([1])
_X = fmpz_poly([0, 1])

_LEGACY_GATE_RE = re.compile(
    r"^\s*g(\d+)\s*=\s*([^\s+\-*]+)\s*([+\-*])\s*([^\s+\-*]+)\s*$"
)


def _eval_compact(tokens):
    n = int(tokens[0])
    if len(tokens) != n + 1:
        raise ValueError(f"COMPACT expected {n} gate tokens, got {len(tokens) - 1}")
    wires = [_ONE, _X]
    for k in range(n):
        tok = tokens[k + 1]
        op = tok[0]
        i_str, j_str = tok[1:].split(".")
        i = int(i_str)
        j = int(j_str)
        if i >= k + 2 or j >= k + 2 or i < 0 or j < 0:
            raise ValueError(f"wire index out of range at gate {k}: {tok}")
        a = wires[i]
        b = wires[j]
        if op == "a":
            wires.append(a + b)
        elif op == "s":
            wires.append(a - b)
        elif op == "m":
            wires.append(a * b)
        else:
            raise ValueError(f"unknown op in token {tok}")
    return wires[-1]


def _parse_legacy_operand(tok, wires):
    if tok == "1":
        return _ONE
    if tok == "x":
        return _X
    if tok.startswith("g"):
        idx = int(tok[1:])
        if idx < 1 or idx + 1 >= len(wires):
            raise ValueError(f"legacy wire g{idx} out of range (have {len(wires) - 2} gates)")
        return wires[idx + 1]
    raise ValueError(f"unknown legacy operand: {tok}")


def _eval_legacy(line):
    rhs = line.split("|", 1)[1] if "|" in line else line
    stmts = [s.strip() for s in rhs.split(";") if s.strip()]
    if not stmts:
        raise ValueError(f"empty legacy SLP: {line!r}")
    wires = [_ONE, _X]
    for expected_idx, stmt in enumerate(stmts, start=1):
        m = _LEGACY_GATE_RE.match(stmt)
        if not m:
            raise ValueError(f"cannot parse legacy gate: {stmt!r}")
        gidx = int(m.group(1))
        if gidx != expected_idx:
            raise ValueError(f"expected g{expected_idx}, got g{gidx} in {stmt!r}")
        a = _parse_legacy_operand(m.group(2), wires)
        op = m.group(3)
        b = _parse_legacy_operand(m.group(4), wires)
        if op == "+":
            wires.append(a + b)
        elif op == "-":
            wires.append(a - b)
        elif op == "*":
            wires.append(a * b)
        else:
            raise ValueError(f"unknown legacy op {op!r}")
    return wires[-1]


def parse_line_to_poly(line):
    """Parse one non-empty stripped line into a flint.fmpz_poly."""
    if line.startswith("P "):
        coeffs = [int(c) for c in line[2:].split()]
        if not coeffs:
            raise ValueError("empty P line")
        return fmpz_poly(coeffs)
    if "|" in line or "=" in line:
        return _eval_legacy(line)
    tokens = line.split()
    if not tokens:
        raise ValueError("empty line")
    # Distinguish COMPACT (`<n> a0.1 ...` or `0`) from bare coeff list (`-1 0 1`)
    if len(tokens) == 1:
        n = int(tokens[0])
        if n == 0:
            return _X
        return fmpz_poly([n])
    t1 = tokens[1]
    if len(t1) >= 4 and t1[0] in ("a", "s", "m") and "." in t1:
        return _eval_compact(tokens)
    return fmpz_poly([int(c) for c in tokens])


def count_distinct_int_roots(p):
    """Exact number of distinct integer roots of nonzero fmpz_poly p.

    Uses FLINT's exact irreducible factorization over Z[x]:
    every linear irreducible factor (a*x + b) with |a| == 1 gives one unique
    integer root -b/a (distinct because factor() returns distinct irreducibles).
    """
    if not p:
        return 0
    if p.degree() <= 0:
        return 0
    _, factors = p.factor()
    cnt = 0
    for fac, _exp in factors:
        if fac.degree() == 1:
            # fac(x) = c0 + c1*x; integer root iff c1 divides c0, and since fac is
            # primitive over Z (content 1), that is equivalent to |c1| == 1.
            c1 = int(fac[1])
            if c1 == 1 or c1 == -1:
                cnt += 1
    return cnt


def poly_coeffs_str(p):
    if not p:
        return "0"
    d = p.degree()
    return " ".join(str(int(p[i])) for i in range(d + 1))


def _process_chunk(args):
    lines, k, exact_all = args
    processed = 0
    zero_count = 0
    skipped_deg = 0
    factored = 0
    hist = Counter()
    hits = []
    for raw_line in lines:
        line = raw_line.strip()
        if not line:
            continue
        p = parse_line_to_poly(line)
        processed += 1
        if not p:
            zero_count += 1
            if exact_all:
                hist[0] += 1
            continue
        deg = p.degree()
        if not exact_all and deg <= k:
            skipped_deg += 1
            continue
        z = count_distinct_int_roots(p)
        factored += 1
        hist[z] += 1
        if z > k:
            hits.append((z, poly_coeffs_str(p), line))
    return processed, zero_count, skipped_deg, factored, dict(hist), hits


def _chunk_reader(path, chunk_size):
    buf = []
    nonempty = 0
    with open(path, "r", encoding="utf-8") as fh:
        for line in fh:
            if line.strip():
                nonempty += 1
                buf.append(line)
                if len(buf) >= chunk_size:
                    yield buf
                    buf = []
    if buf:
        yield buf
    yield ("__TOTAL__", nonempty)


def main():
    ap = argparse.ArgumentParser(description="Independent exact integer-root counter via python-flint")
    ap.add_argument("file", help="Input file (P coeffs, COMPACT SLP, or legacy SLP)")
    ap.add_argument("k", type=int, help="Threshold K: report every polynomial with z(f) > K")
    ap.add_argument("--workers", type=int, default=min(6, os.cpu_count() or 1), help="Number of worker processes (default <= 6)")
    ap.add_argument("--chunk-size", type=int, default=4096, help="Lines per worker chunk")
    ap.add_argument("--exact-all", action="store_true", help="Disable deg<=K prefilter and count every polynomial")
    args = ap.parse_args()

    workers = max(1, min(args.workers, 12))
    total_nonempty = 0
    total_processed = 0
    total_zero = 0
    total_skipped_deg = 0
    total_factored = 0
    total_hist = Counter()
    all_hits = []

    def handle_result(res):
        nonlocal total_processed, total_zero, total_skipped_deg, total_factored
        processed, zero_count, skipped_deg, factored, hist, hits = res
        total_processed += processed
        total_zero += zero_count
        total_skipped_deg += skipped_deg
        total_factored += factored
        for z, cnt in hist.items():
            total_hist[z] += cnt
        all_hits.extend(hits)

    if workers == 1:
        for item in _chunk_reader(args.file, args.chunk_size):
            if isinstance(item, tuple) and item[0] == "__TOTAL__":
                total_nonempty = item[1]
            else:
                handle_result(_process_chunk((item, args.k, args.exact_all)))
    else:
        max_inflight = workers * 4
        inflight = []
        with ProcessPoolExecutor(max_workers=workers) as ex:
            for item in _chunk_reader(args.file, args.chunk_size):
                if isinstance(item, tuple) and item[0] == "__TOTAL__":
                    total_nonempty = item[1]
                    continue
                fut = ex.submit(_process_chunk, (item, args.k, args.exact_all))
                inflight.append(fut)
                if len(inflight) >= max_inflight:
                    handle_result(inflight.pop(0).result())
            for fut in inflight:
                handle_result(fut.result())

    assert total_processed == total_nonempty, (
        f"ASSERTION FAILED: processed {total_processed} != nonempty lines {total_nonempty}"
    )

    max_z = max(total_hist.keys()) if total_hist else 0
    for z in sorted(total_hist.keys()):
        print(f"HIST {z} {total_hist[z]}")
    for z, coeffs, orig_line in all_hits:
        print(f"HIT {z} | {coeffs} | {orig_line}")
    print(
        f"SUMMARY nonempty={total_nonempty} processed={total_processed} "
        f"zero={total_zero} skipped_deg_le_K={total_skipped_deg} "
        f"factored={total_factored} max_z={max_z} hits={len(all_hits)} K={args.k}"
    )


if __name__ == "__main__":
    main()
