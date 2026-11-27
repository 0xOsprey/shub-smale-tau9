#!/usr/bin/env python3
"""
Exact Z-wide root certifier for survivor SLPs from tau_certify_exact.c
(and legacy tau_z9_unconditional.c).

Zero external dependencies (pure arbitrary-precision Python int arithmetic).
For every survivor SLP:
  1. Parses legacy ('h1 h2 h3 | g1 = ...') OR compact ('<n> a0.1 m2.2 ...') format
     and constructs the exact polynomial f(x) in Z[x].
  2. Strips x = 0 roots and computes the exact primitive squarefree part
     g(x) = f_1(x) / gcd_{Q[x]}(f_1(x), f_1'(x)) via exact primitive PRS
     with verified zero remainder.
  3. Certifies #Z_roots(f) <= K unconditionally over ALL of Z via:
     - Degree bound: deg(g) + has_zero_root <= K, OR
     - Simple-Root Modular Certificate on squarefree g mod p, OR
     - Exact Hensel lifting from F_p to M = p^{2^m} > 2 * CauchyBound(g),
       which finds 100% of all integer roots in Z with zero magnitude bound.

Features:
  - Accepts single files, multiple files, or shard directories (all *.txt).
  - Optional exact polynomial deduplication up to sign (--dedup).
  - Multiprocessing with chunking (--workers, --chunk-size).
  - Resumable verification state (--resume-state STATE.json).
  - Writes counterexamples to --out FILE.
  - Strict accounting: asserts processed_lines == total_lines (no swallowed errors).
  - Built-in --self-test (10-gate 7-root witness + +-10^9 multiplicity Hensel test).
"""

import argparse
import glob
import json
import math
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed


# --- Exact Z[x] polynomial arithmetic (list of ints [c0, c1, ..., cd]) ---

def poly_trim(a):
    while a and a[-1] == 0:
        a.pop()
    return a


def poly_add(a, b):
    n = max(len(a), len(b))
    res = [0] * n
    for i in range(len(a)):
        res[i] += a[i]
    for i in range(len(b)):
        res[i] += b[i]
    return poly_trim(res)


def poly_sub(a, b):
    n = max(len(a), len(b))
    res = [0] * n
    for i in range(len(a)):
        res[i] += a[i]
    for i in range(len(b)):
        res[i] -= b[i]
    return poly_trim(res)


def poly_mul(a, b):
    if not a or not b:
        return []
    res = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                if bj:
                    res[i + j] += ai * bj
    return poly_trim(res)


def poly_deriv(a):
    if len(a) <= 1:
        return []
    return poly_trim([i * a[i] for i in range(1, len(a))])


def poly_content(a):
    g = 0
    for c in a:
        g = math.gcd(g, abs(c))
        if g == 1:
            return 1
    return g


def poly_primitive(a):
    a = poly_trim(list(a))
    if not a:
        return []
    g = poly_content(a)
    if a[-1] < 0:
        g = -g
    return [c // g for c in a]


def poly_sign_canon(a):
    """Canonicalize polynomial up to sign (leading coefficient > 0)."""
    a = poly_trim(list(a))
    if not a:
        return ()
    if a[-1] < 0:
        return tuple(-c for c in a)
    return tuple(a)


def poly_pseudo_rem(a, b):
    """Exact pseudo-remainder of a by b in Z[x], returning primitive remainder."""
    a = poly_trim(list(a))
    b = poly_trim(list(b))
    if not b:
        raise ZeroDivisionError("poly_pseudo_rem by zero")
    da = len(a) - 1
    db = len(b) - 1
    if da < db:
        return poly_primitive(a)
    lc_b = b[-1]
    while len(a) - 1 >= db and a:
        shift = len(a) - 1 - db
        lc_a = a[-1]
        g = math.gcd(abs(lc_a), abs(lc_b))
        ma = lc_b // g
        mb = lc_a // g
        for i in range(len(a)):
            a[i] *= ma
        for i in range(db + 1):
            a[shift + i] -= mb * b[i]
        poly_trim(a)
        if a:
            c = poly_content(a)
            if c > 1:
                a = [x // c for x in a]
    return poly_primitive(a)


def poly_gcd(a, b):
    """Exact primitive GCD in Z[x]."""
    a = poly_primitive(a)
    b = poly_primitive(b)
    if not a:
        return b
    if not b:
        return a
    if len(a) < len(b):
        a, b = b, a
    while b:
        if len(b) == 1:
            return [1]
        r = poly_pseudo_rem(a, b)
        a, b = b, r
    return poly_primitive(a)


def poly_exact_div(a, b):
    """Exact division a / b in Z[x] (b primitive, divides a in Q[x] and Z[x])."""
    a = list(a)
    b = poly_trim(list(b))
    da = len(a) - 1
    db = len(b) - 1
    assert db >= 0 and da >= db
    lc_b = b[-1]
    q = [0] * (da - db + 1)
    for k in range(da - db, -1, -1):
        coeff = a[k + db]
        assert coeff % lc_b == 0, f"Non-exact division: {coeff} % {lc_b} != 0"
        qk = coeff // lc_b
        q[k] = qk
        if qk:
            for j in range(db + 1):
                a[k + j] -= qk * b[j]
    assert all(c == 0 for c in a), "Nonzero remainder in exact division!"
    return poly_trim(q)


def poly_sqf_part(a):
    """Return exact primitive squarefree part of nonzero polynomial a in Z[x]."""
    p = poly_primitive(a)
    if len(p) <= 2:
        return p
    dp = poly_deriv(p)
    g = poly_gcd(p, dp)
    if len(g) == 1:
        return p
    return poly_primitive(poly_exact_div(p, g))


def poly_eval_mod(a, x, mod):
    res = 0
    for c in reversed(a):
        res = (res * x + c) % mod
    return res


def poly_eval(a, x):
    res = 0
    for c in reversed(a):
        res = res * x + c
    return res


def small_primes(limit=2000):
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(limit ** 0.5) + 1):
        if sieve[i]:
            for j in range(i * i, limit + 1, i):
                sieve[j] = False
    return [i for i in range(17, limit + 1) if sieve[i]]


PRIMES = small_primes(2000)


def _is_prime_simple(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def iter_primes():
    """Yield precomputed primes >= 17, then continue indefinitely if needed."""
    for p in PRIMES:
        yield p
    cand = PRIMES[-1] + 2
    while True:
        if _is_prime_simple(cand):
            yield cand
        cand += 2


def exact_integer_roots_sqf(g, p, roots_mod_p):
    """Find ALL exact integer roots of squarefree primitive g in Z[x]
    by Hensel-lifting every simple root a in roots_mod_p past 2 * CauchyBound(g)."""
    if len(g) <= 1:
        return []
    # Every integer root r satisfies |r| <= 1 + max_{i < d} |c_i| (since |lc(g)| >= 1)
    cauchy_bound = 1 + max(abs(c) for c in g[:-1])
    target_mod = 2 * cauchy_bound + 1
    dg = poly_deriv(g)

    exact_roots = []
    for a in roots_mod_p:
        r = a
        m = p
        while m <= target_mod:
            m2 = m * m
            val = poly_eval_mod(g, r, m2)
            der = poly_eval_mod(dg, r, m2)
            inv = pow(der, -1, m2)
            r = (r - val * inv) % m2
            m = m2
        # Centered representative in (-m/2, m/2]
        cand = r if r <= m // 2 else r - m
        if abs(cand) <= cauchy_bound and poly_eval(g, cand) == 0:
            exact_roots.append(cand)
    return sorted(set(exact_roots))


def certify_poly(f, K):
    """
    Unconditionally certify #Z_roots(f) <= K over ALL of Z.
    Returns (status, bound_or_exact_count, details):
      status in {"zero", "deg", "sqf_deg", "sqf_mod", "hensel_ok", "COUNTEREXAMPLE"}
    """
    f = poly_trim(f)
    if not f:
        return ("zero", 0, None)
    if len(f) - 1 <= K:
        return ("deg", len(f) - 1, None)

    has_zero = 0
    idx = 0
    while idx < len(f) and f[idx] == 0:
        idx += 1
    if idx > 0:
        has_zero = 1
        f = f[idx:]

    if len(f) - 1 + has_zero <= K:
        return ("deg", len(f) - 1 + has_zero, None)

    # Exact primitive squarefree part
    g = poly_sqf_part(f)
    if len(g) - 1 + has_zero <= K:
        return ("sqf_deg", len(g) - 1 + has_zero, None)

    # Simple-Root Modular Certificate on squarefree g
    dg = poly_deriv(g)
    for p in iter_primes():
        gp = [c % p for c in g]
        if not any(gp):
            continue
        dgp = [c % p for c in dg]
        roots_p = []
        has_double = False
        nonzero = False
        for a in range(p):
            v = poly_eval_mod(gp, a, p)
            if v == 0:
                dv = poly_eval_mod(dgp, a, p)
                if dv == 0:
                    has_double = True
                    break
                roots_p.append(a)
            else:
                nonzero = True
        if nonzero and not has_double:
            if len(roots_p) + has_zero <= K:
                return ("sqf_mod", len(roots_p) + has_zero, p)
            # Exact Hensel lifting to get the EXACT integer root set over all Z
            exact = exact_integer_roots_sqf(g, p, roots_p)
            if has_zero:
                exact = sorted(set(exact + [0]))
            if len(exact) <= K:
                return ("hensel_ok", len(exact), exact)
            else:
                return ("COUNTEREXAMPLE", len(exact), exact)

    raise RuntimeError("Unreachable: iter_primes() exhausted")


def parse_and_eval_compact(line):
    """Parse compact format '<n> <op><i>.<j> ...' (op in a/s/m, 0=1, 1=x, k+2=gate k)."""
    parts = line.strip().split()
    n = int(parts[0])
    if len(parts) != n + 1:
        raise ValueError(f"Compact SLP expected {n} gates, got {len(parts) - 1}: {line}")
    wires = [[1], [0, 1]]
    for tok in parts[1:]:
        op = tok[0]
        i_str, j_str = tok[1:].split(".")
        i, j = int(i_str), int(j_str)
        if i < 0 or j < 0 or i >= len(wires) or j >= len(wires):
            raise ValueError(f"Wire index out of range ({i}, {j}) for len={len(wires)} in {line}")
        va, vb = wires[i], wires[j]
        if op == "a":
            wires.append(poly_add(va, vb))
        elif op == "s":
            wires.append(poly_sub(va, vb))
        elif op == "m":
            wires.append(poly_mul(va, vb))
        else:
            raise ValueError(f"Unknown compact op '{op}' in {tok}")
    return wires[-1]


def parse_and_eval_legacy(line):
    """Parse legacy format '<h1 h2 h3> | g1 = ...; g2 = ...' or 'g1 = ...; g2 = ...'."""
    if "|" in line:
        _, slp_str = line.split("|", 1)
    else:
        slp_str = line
    env = {"1": [1], "x": [0, 1]}
    last_name = None
    for part in slp_str.strip().split(";"):
        part = part.strip()
        if not part:
            continue
        lhs, rhs = part.split("=")
        lhs = lhs.strip()
        tokens = rhs.strip().split()
        a_tok, op, b_tok = tokens[0], tokens[1], tokens[2]
        va, vb = env[a_tok], env[b_tok]
        if op == "+":
            env[lhs] = poly_add(va, vb)
        elif op == "-":
            env[lhs] = poly_sub(va, vb)
        elif op == "*":
            env[lhs] = poly_mul(va, vb)
        else:
            raise ValueError(f"Unknown op: {op}")
        last_name = lhs
    if last_name is None:
        raise ValueError(f"Empty legacy SLP line: {line}")
    return env[last_name]


def parse_and_eval_slp(line):
    """Auto-detect and parse either legacy or compact SLP format."""
    s = line.strip()
    if "=" in s:
        return parse_and_eval_legacy(s)
    return parse_and_eval_compact(s)


STATUS_KEYS = ["zero", "deg", "sqf_deg", "sqf_mod", "hensel_ok", "COUNTEREXAMPLE"]


def verify_chunk(args):
    chunk_id, lines, K = args
    counts = {k: 0 for k in STATUS_KEYS}
    max_exact = 0
    counterexamples = []
    processed = 0
    for line in lines:
        s = line.strip()
        if not s:
            continue
        f = parse_and_eval_slp(s)
        status, cnt, details = certify_poly(f, K)
        counts[status] += 1
        processed += 1
        if status == "hensel_ok" and cnt > max_exact:
            max_exact = cnt
        if status == "COUNTEREXAMPLE":
            counterexamples.append([s, cnt, details])
    return chunk_id, processed, counts, max_exact, counterexamples


def collect_input_files(paths):
    files = []
    for p in paths:
        if os.path.isdir(p):
            matched = sorted(glob.glob(os.path.join(p, "*.txt")))
            files.extend(matched)
        elif os.path.isfile(p):
            files.append(p)
        else:
            raise FileNotFoundError(f"Input path not found: {p}")
    return files


def save_state_atomic(path, state):
    tmp = path + ".tmp"
    with open(tmp, "w") as fp:
        json.dump(state, fp)
        fp.flush()
        os.fsync(fp.fileno())
    os.replace(tmp, path)


def self_test():
    # Test 1a: 10-gate 7-root witness in legacy format MUST be COUNTEREXAMPLE for K=6, ok for K=7
    w10_legacy = (
        "g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; "
        "g5 = g2 - g4; g6 = x * g5; g7 = 1 + g1; g8 = g7 * g7; "
        "g9 = g2 - g8; g10 = g6 * g9"
    )
    f10 = parse_and_eval_slp(w10_legacy)
    st6, c6, det6 = certify_poly(f10, 6)
    assert st6 == "COUNTEREXAMPLE" and c6 == 7 and det6 == [-3, -2, -1, 0, 1, 2, 3], (st6, c6, det6)
    st7, c7, _ = certify_poly(f10, 7)
    assert st7 != "COUNTEREXAMPLE" and c7 <= 7, (st7, c7)

    # Test 1b: Same 10-gate 7-root witness in compact format
    w10_compact = "10 a0.0 m1.1 s2.3 m4.4 s3.5 m1.6 a0.2 m8.8 s3.9 m7.10"
    f10_c = parse_and_eval_slp(w10_compact)
    assert f10_c == f10, (f10_c, f10)
    st6c, c6c, det6c = certify_poly(f10_c, 6)
    assert st6c == "COUNTEREXAMPLE" and c6c == 7 and det6c == [-3, -2, -1, 0, 1, 2, 3], (st6c, c6c, det6c)

    # Test 2: Huge integer roots at +-10^9 with multiplicity
    big_roots = [-10**9, 123456789, 10**9]
    f_big = [1]
    for r, mult in [(-10**9, 3), (123456789, 1), (10**9, 2)]:
        for _ in range(mult):
            f_big = poly_mul(f_big, [-r, 1])
    st_big, c_big, det_big = certify_poly(f_big, 2)
    assert st_big == "COUNTEREXAMPLE" and c_big == 3 and det_big == big_roots, (st_big, c_big, det_big)
    st_big3, c_big3, _ = certify_poly(f_big, 3)
    assert st_big3 != "COUNTEREXAMPLE", (st_big3, c_big3)

    # Test 3: Sign-canonical dedup check
    assert poly_sign_canon([1, -2, 1]) == poly_sign_canon([-1, 2, -1])

    print("SELF-TEST PASSED (10-gate 7-root witness legacy+compact + +-10^9 multiplicity Hensel test)")


def main():
    ap = argparse.ArgumentParser(description="Exact Z-wide root certifier for survivor SLPs")
    ap.add_argument("inputs", nargs="*", help="Survivor file(s) or shard directory(ies) (*.txt)")
    ap.add_argument("-K", "--bound", type=int, default=None, help="Root bound K (or pass as last positional arg)")
    ap.add_argument("--workers", type=int, default=12, help="Number of worker processes (default 12)")
    ap.add_argument("--chunk-size", type=int, default=0, help="Lines per chunk (0 = auto)")
    ap.add_argument("--dedup", action="store_true", help="Exact-dedup polynomials up to sign across all inputs before certifying")
    ap.add_argument("--resume-state", type=str, default=None, help="JSON state file for resumable verification")
    ap.add_argument("--out", type=str, default=None, help="Write counterexamples to this file")
    ap.add_argument("--self-test", action="store_true", help="Run built-in self-tests and exit")
    args = ap.parse_args()

    if args.self_test:
        self_test()
        return

    # Support legacy positional syntax: verify_survivors.py <file_or_dir> <K> [workers]
    inputs = list(args.inputs)
    K = args.bound
    workers = args.workers

    if K is None:
        # Check if trailing positional args are integers (K [workers])
        if len(inputs) >= 3 and inputs[-1].isdigit() and inputs[-2].isdigit():
            workers = int(inputs.pop())
            K = int(inputs.pop())
        elif len(inputs) >= 2 and inputs[-1].isdigit():
            K = int(inputs.pop())
        else:
            ap.error("Must specify root bound K (via -K/--bound or positional argument)")

    if not inputs:
        ap.error("Must specify at least one input file or shard directory")
    if workers < 1:
        ap.error("--workers must be >= 1")

    t0 = time.monotonic()
    files = collect_input_files(inputs)
    if not files:
        for p in inputs:
            if os.path.isdir(p) and os.path.isdir(os.path.join(p, "surv")):
                ap.error(f"Directory '{p}' has no top-level *.txt files; did you mean '{os.path.join(p, 'surv')}'?")
        ap.error(f"No input *.txt files found in {inputs}")
    raw_lines = []
    for fpath in files:
        with open(fpath, "r") as fp:
            for l in fp:
                s = l.strip()
                if s and not s.startswith("#"):
                    raw_lines.append(s)

    total_raw_lines = len(raw_lines)
    dedup_skipped = 0

    if args.dedup and total_raw_lines > 0:
        seen = set()
        uniq_lines = []
        for s in raw_lines:
            canon = poly_sign_canon(parse_and_eval_slp(s))
            if canon in seen:
                dedup_skipped += 1
            else:
                seen.add(canon)
                uniq_lines.append(s)
        lines = uniq_lines
    else:
        lines = raw_lines

    n = len(lines)
    if n == 0:
        print(f"VERIFY {inputs} K={K}: 0 survivors (files={len(files)}) -> 100% CERTIFIED <= {K} roots over ALL Z (0.000s)")
        return

    if args.chunk_size > 0:
        chunk_size = args.chunk_size
    else:
        chunk_size = max(1, min(2000, (n + workers * 4 - 1) // (workers * 4)))

    chunks = [(cid, lines[i:i + chunk_size], K)
              for cid, i in enumerate(range(0, n, chunk_size))]
    num_chunks = len(chunks)

    # Load or initialize resume state
    done_chunks = set()
    tot = {k: 0 for k in STATUS_KEYS}
    max_exact = 0
    all_ce = []
    processed_total = 0

    if args.resume_state and os.path.exists(args.resume_state):
        with open(args.resume_state, "r") as fp:
            st = json.load(fp)
        if st.get("n_lines") != n or st.get("num_chunks") != num_chunks or st.get("K") != K:
            raise RuntimeError(
                f"Resume state mismatch: state has n={st.get('n_lines')}, chunks={st.get('num_chunks')}, K={st.get('K')}; "
                f"current run has n={n}, chunks={num_chunks}, K={K}"
            )
        done_chunks = set(st["done_chunks"])
        tot = {k: int(st["counts"][k]) for k in STATUS_KEYS}
        max_exact = int(st["max_exact"])
        all_ce = list(st["counterexamples"])
        processed_total = int(st["processed_total"])
        print(f"RESUMED from {args.resume_state}: {len(done_chunks)}/{num_chunks} chunks ({processed_total}/{n} lines) already done",
              file=sys.stderr)

    pending = [ch for ch in chunks if ch[0] not in done_chunks]

    def record_result(cid, proc, counts, me, ce):
        nonlocal max_exact, processed_total
        done_chunks.add(cid)
        processed_total += proc
        for k in STATUS_KEYS:
            tot[k] += counts[k]
        if me > max_exact:
            max_exact = me
        all_ce.extend(ce)
        if args.resume_state:
            save_state_atomic(args.resume_state, {
                "K": K,
                "n_lines": n,
                "num_chunks": num_chunks,
                "done_chunks": sorted(done_chunks),
                "processed_total": processed_total,
                "counts": tot,
                "max_exact": max_exact,
                "counterexamples": all_ce,
            })

    if workers <= 1 or len(pending) <= 1:
        for ch in pending:
            cid, proc, counts, me, ce = verify_chunk(ch)
            record_result(cid, proc, counts, me, ce)
    else:
        with ProcessPoolExecutor(max_workers=workers) as ex:
            futs = [ex.submit(verify_chunk, ch) for ch in pending]
            for fut in as_completed(futs):
                # Re-raises any worker exception immediately (never swallowed)
                cid, proc, counts, me, ce = fut.result()
                record_result(cid, proc, counts, me, ce)

    # Strict accounting assertion
    status_sum = sum(tot.values())
    assert processed_total == n, f"ACCOUNTING MISMATCH: processed={processed_total} != total={n}"
    assert status_sum == n, f"STATUS SUM MISMATCH: sum={status_sum} != total={n}"
    assert len(done_chunks) == num_chunks, f"CHUNK MISMATCH: done={len(done_chunks)} != {num_chunks}"

    if args.out:
        with open(args.out, "w") as fp:
            for line, cnt, roots in all_ce:
                fp.write(f"roots={cnt} {roots} | {line}\n")

    dt = time.monotonic() - t0
    print(f"VERIFY files={len(files)} K={K} raw_lines={total_raw_lines} verified={n} "
          f"dedup_skipped={dedup_skipped} time={dt:.3f}s")
    for k in STATUS_KEYS:
        print(f"  {k:15s} = {tot[k]}")
    print(f"  max_exact_hensel = {max_exact}")
    print(f"  accounting_check = PASS (processed={processed_total} == total={n})")

    if all_ce:
        print(f"  !!! FOUND {len(all_ce)} COUNTEREXAMPLES (> {K} roots) !!!")
        for line, cnt, roots in all_ce[:10]:
            print(f"    roots={cnt} {roots}: {line}")
        sys.exit(2)
    else:
        print(f"  RESULT: 100% CERTIFIED ALL {n} SURVIVORS HAVE <= {K} DISTINCT INTEGER ROOTS OVER ALL Z!")


if __name__ == "__main__":
    main()
