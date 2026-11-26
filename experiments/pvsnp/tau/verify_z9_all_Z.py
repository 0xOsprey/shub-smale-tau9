#!/usr/bin/env python3
"""
Exact Z-wide root certifier for survivor SLPs from tau_z9_unconditional.c.

Zero external dependencies (pure arbitrary-precision Python int arithmetic).
For every survivor SLP:
  1. Constructs the exact polynomial f(x) in Z[x].
  2. Strips x = 0 roots and computes the exact primitive squarefree part
     g(x) = f_1(x) / gcd_{Q[x]}(f_1(x), f_1'(x)) via exact primitive PRS
     with verified zero remainder.
  3. Certifies #Z_roots(f) <= K unconditionally over ALL of Z via:
     - Degree bound: deg(g) + has_zero_root <= K, OR
     - Simple-Root Modular Certificate on squarefree g mod p, OR
     - Exact Hensel lifting from F_p to M = p^{2^m} > 2 * CauchyBound(g),
       which finds 100% of all integer roots in Z with zero magnitude bound.
"""

import math
import sys
import time
from concurrent.futures import ProcessPoolExecutor


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
            # Keep coefficients small by dividing out content
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
    for p in PRIMES:
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
            # Otherwise, do exact Hensel lifting to get the EXACT integer root set over all Z!
            exact = exact_integer_roots_sqf(g, p, roots_p)
            if has_zero:
                exact = sorted(set(exact + [0]))
            if len(exact) <= K:
                return ("hensel_ok", len(exact), exact)
            else:
                return ("COUNTEREXAMPLE", len(exact), exact)

    raise RuntimeError("Exhausted primes up to 2000 without finding a good prime for squarefree g!")


def parse_and_eval_slp(line):
    """Parse a survivor line '<h1 h2 h3> | g1 = ...; g2 = ...' and return exact Z[x] poly."""
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
    return env[last_name]


def verify_chunk(args):
    lines, K = args
    counts = {
        "zero": 0, "deg": 0, "sqf_deg": 0, "sqf_mod": 0,
        "hensel_ok": 0, "COUNTEREXAMPLE": 0,
    }
    max_exact = 0
    counterexamples = []
    for line in lines:
        line = line.strip()
        if not line:
            continue
        f = parse_and_eval_slp(line)
        status, cnt, details = certify_poly(f, K)
        counts[status] += 1
        if status == "hensel_ok" and cnt > max_exact:
            max_exact = cnt
        if status == "COUNTEREXAMPLE":
            counterexamples.append((line, cnt, details))
    return counts, max_exact, counterexamples


def self_test():
    # Test 1: 10-gate 7-root witness MUST be detected as COUNTEREXAMPLE for K=6, certified for K=7
    w10 = "g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4; g6 = x * g5; g7 = 1 + g1; g8 = g7 * g7; g9 = g2 - g8; g10 = g6 * g9"
    f10 = parse_and_eval_slp(w10)
    st6, c6, det6 = certify_poly(f10, 6)
    assert st6 == "COUNTEREXAMPLE" and c6 == 7 and det6 == [-3, -2, -1, 0, 1, 2, 3], (st6, c6, det6)
    st7, c7, _ = certify_poly(f10, 7)
    assert st7 != "COUNTEREXAMPLE" and c7 <= 7, (st7, c7)

    # Test 2: Huge integer roots outside [-32, 31], plus multiplicity: (x - 10^9)^2 * (x + 10^9)^3 * (x - 123456789)
    big_roots = [-10**9, 123456789, 10**9]
    f_big = [1]
    for r, mult in [(-10**9, 3), (123456789, 1), (10**9, 2)]:
        for _ in range(mult):
            f_big = poly_mul(f_big, [-r, 1])
    st_big, c_big, det_big = certify_poly(f_big, 2)
    assert st_big == "COUNTEREXAMPLE" and c_big == 3 and det_big == big_roots, (st_big, c_big, det_big)
    st_big3, c_big3, _ = certify_poly(f_big, 3)
    assert st_big3 != "COUNTEREXAMPLE", (st_big3, c_big3)
    print("SELF-TEST PASSED (10-gate 7-root witness + 10^9 multiplicity Hensel test)")


def main():
    if len(sys.argv) >= 2 and sys.argv[1] == "--self-test":
        self_test()
        return

    if len(sys.argv) < 3:
        print(f"Usage: {sys.argv[0]} <survivors_file> <K> [workers=12]")
        sys.exit(1)

    surv_file = sys.argv[1]
    K = int(sys.argv[2])
    workers = int(sys.argv[3]) if len(sys.argv) >= 4 else 12

    t0 = time.monotonic()
    with open(surv_file, "r") as fp:
        lines = [l for l in fp if l.strip()]
    n = len(lines)
    if n == 0:
        print(f"VERIFY {surv_file} K={K}: 0 survivors -> 100% CERTIFIED <= {K} roots over ALL Z (0.000s)")
        return

    chunk_size = max(1, (n + workers * 4 - 1) // (workers * 4))
    chunks = [(lines[i:i + chunk_size], K) for i in range(0, n, chunk_size)]

    tot = {"zero": 0, "deg": 0, "sqf_deg": 0, "sqf_mod": 0, "hensel_ok": 0, "COUNTEREXAMPLE": 0}
    max_exact = 0
    all_ce = []

    if workers <= 1 or n < 200:
        for ch in chunks:
            c, me, ce = verify_chunk(ch)
            for k, v in c.items():
                tot[k] += v
            if me > max_exact:
                max_exact = me
            all_ce.extend(ce)
    else:
        with ProcessPoolExecutor(max_workers=workers) as ex:
            for c, me, ce in ex.map(verify_chunk, chunks):
                for k, v in c.items():
                    tot[k] += v
                if me > max_exact:
                    max_exact = me
                all_ce.extend(ce)

    dt = time.monotonic() - t0
    print(f"VERIFY {surv_file} K={K} total_survivors={n} time={dt:.3f}s")
    for k in ["zero", "deg", "sqf_deg", "sqf_mod", "hensel_ok", "COUNTEREXAMPLE"]:
        print(f"  {k:15s} = {tot[k]}")
    print(f"  max_exact_hensel = {max_exact}")
    if all_ce:
        print(f"  !!! FOUND {len(all_ce)} COUNTEREXAMPLES (> {K} roots) !!!")
        for line, cnt, roots in all_ce[:10]:
            print(f"    roots={cnt} {roots}: {line}")
        sys.exit(2)
    else:
        print(f"  RESULT: 100% CERTIFIED ALL {n} SURVIVORS HAVE <= {K} DISTINCT INTEGER ROOTS OVER ALL Z!")


if __name__ == "__main__":
    main()
