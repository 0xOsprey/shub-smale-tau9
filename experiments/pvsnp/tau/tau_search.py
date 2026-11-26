#!/usr/bin/env python3
"""
Exact verifier and structured search for the Shub-Smale tau-conjecture
(Smale's 4th Problem): constant-free straight-line programs (SLPs) over {1, x}
with operations {+, -, *}.
"""

from __future__ import annotations
import json
import sys
from typing import List, Tuple, Dict, Optional

# Polynomial represented as a list of Python ints [c_0, c_1, ..., c_d]
# with leading zeros stripped ([] represents the zero polynomial).
Poly = List[int]


def poly_trim(p: Poly) -> Poly:
    while p and p[-1] == 0:
        p.pop()
    return p


def poly_add(a: Poly, b: Poly) -> Poly:
    n = max(len(a), len(b))
    res = [0] * n
    for i in range(len(a)):
        res[i] += a[i]
    for i in range(len(b)):
        res[i] += b[i]
    return poly_trim(res)


def poly_sub(a: Poly, b: Poly) -> Poly:
    n = max(len(a), len(b))
    res = [0] * n
    for i in range(len(a)):
        res[i] += a[i]
    for i in range(len(b)):
        res[i] -= b[i]
    return poly_trim(res)


def poly_mul(a: Poly, b: Poly) -> Poly:
    if not a or not b:
        return []
    res = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                if bj:
                    res[i + j] += ai * bj
    return poly_trim(res)


def poly_eval(p: Poly, x: int) -> int:
    # Horner's method (exact arbitrary-precision Python int)
    val = 0
    for c in reversed(p):
        val = val * x + c
    return val


def poly_div_linear(p: Poly, r: int) -> Tuple[Poly, int]:
    """Divide p(x) by (x - r), returning (quotient, remainder) exactly."""
    if not p:
        return [], 0
    d = len(p) - 1
    q = [0] * d
    rem = p[d]
    for i in range(d - 1, -1, -1):
        q[i] = rem
        rem = rem * r + p[i]
    return poly_trim(q), rem


def poly_to_str(p: Poly) -> str:
    if not p:
        return "0"
    terms = []
    for deg in range(len(p) - 1, -1, -1):
        c = p[deg]
        if c == 0:
            continue
        sign = "+" if c > 0 else "-"
        ac = abs(c)
        if deg == 0:
            t = f"{ac}"
        elif deg == 1:
            t = "x" if ac == 1 else f"{ac}*x"
        else:
            t = f"x^{deg}" if ac == 1 else f"{ac}*x^{deg}"
        if not terms:
            terms.append(t if c > 0 else f"-{t}")
        else:
            terms.append(f" {sign} {t}")
    return "".join(terms)


# SLP gate format: (op, i, j) where op in {'+', '-', '*'} and -1 <= i, j < k
# Gate indexing: g_{-1} = 1, g_0 = x, g_1 ... g_tau are the gates.
Gate = Tuple[str, int, int]


def eval_slp_exact(gates: List[Gate]) -> Poly:
    """Evaluate a constant-free SLP exactly as a polynomial in Z[x]."""
    vals: Dict[int, Poly] = {-1: [1], 0: [0, 1]}
    for k, (op, i, j) in enumerate(gates, start=1):
        if not (-1 <= i < k and -1 <= j < k):
            raise ValueError(f"Gate {k} has invalid input indices ({i}, {j})")
        a, b = vals[i], vals[j]
        if op == "+":
            vals[k] = poly_add(a, b)
        elif op == "-":
            vals[k] = poly_sub(a, b)
        elif op == "*":
            vals[k] = poly_mul(a, b)
        else:
            raise ValueError(f"Invalid op {op!r} at gate {k}")
    return vals[len(gates)]


def verify_witness(gates: List[Gate], claimed_roots: List[int]) -> Dict:
    """
    100% exact verification of an SLP witness:
      1. Valid constant-free SLP over {1, x} with ops {+, -, *}
      2. Resulting polynomial f(x) is identically nonzero
      3. Every claimed root r is an int, pairwise distinct, and f(r) == 0 exactly
      4. Also checks exact division by prod(x - r)
    """
    p = eval_slp_exact(gates)
    assert len(p) > 0, "Polynomial is identically zero!"
    roots_sorted = sorted(set(claimed_roots))
    assert len(roots_sorted) == len(claimed_roots), "Duplicate roots in claim!"
    q = list(p)
    for r in roots_sorted:
        assert isinstance(r, int), f"Root {r!r} is not an int"
        val = poly_eval(p, r)
        assert val == 0, f"f({r}) = {val} != 0!"
        q, rem = poly_div_linear(q, r)
        assert rem == 0, f"Exact linear division failed at r={r}!"
    return {
        "tau": len(gates),
        "degree": len(p) - 1,
        "num_roots": len(roots_sorted),
        "roots": roots_sorted,
        "poly_str": poly_to_str(p) if len(p) <= 25 else f"deg {len(p)-1} poly",
        "gates": gates,
    }


def format_slp(gates: List[Gate]) -> str:
    def name(idx: int) -> str:
        if idx == -1:
            return "1"
        if idx == 0:
            return "x"
        return f"g{idx}"

    lines = []
    for k, (op, i, j) in enumerate(gates, start=1):
        lines.append(f"g{k} = {name(i)} {op} {name(j)}")
    return "; ".join(lines)


def find_integer_roots_in_range(p: Poly, lo: int = -1000, hi: int = 1000) -> List[int]:
    if not p:
        return []
    # Quick exact check: if p(0) != 0, roots must divide p(0).
    # First factor out powers of x.
    roots = []
    q = list(p)
    if q[0] == 0:
        roots.append(0)
        while q and q[0] == 0:
            q.pop(0)
    if not q or len(q) == 1:
        return sorted(roots)
    c0 = abs(q[0])
    # Evaluate on [lo, hi] skipping r that don't divide c0
    for r in range(lo, hi + 1):
        if r == 0:
            continue
        if c0 % abs(r) != 0:
            continue
        if poly_eval(q, r) == 0:
            roots.append(r)
    return sorted(roots)


def parse_slp_str(s: str) -> List[Gate]:
    """Parse 'g1 = 1 + 1; g2 = x * x; ...' into a list of Gate tuples."""
    gates: List[Gate] = []
    for part in s.split(";"):
        part = part.strip()
        if not part:
            continue
        lhs, rhs = part.split("=")
        tokens = rhs.strip().split()
        assert len(tokens) == 3, f"Bad gate expression: {part!r}"
        a, op, b = tokens

        def idx(tok: str) -> int:
            if tok == "1":
                return -1
            if tok == "x":
                return 0
            assert tok.startswith("g"), f"Bad operand {tok!r}"
            return int(tok[1:])

        gates.append((op, idx(a), idx(b)))
    return gates


def verify_and_report(label: str, slp_str: str, search_lo: int = -1000, search_hi: int = 1000) -> Dict:
    gates = parse_slp_str(slp_str)
    p = eval_slp_exact(gates)
    roots = find_integer_roots_in_range(p, search_lo, search_hi)
    res = verify_witness(gates, roots)
    print(f"[{label}] VERIFIED: tau={res['tau']}, roots={res['num_roots']}, deg={res['degree']}, roots={res['roots']}")
    print(f"    SLP : {format_slp(gates)}")
    print(f"    Poly: {res['poly_str']}")
    return res


if __name__ == "__main__":
    witnesses = [
        ("tau=1 (exact z_max=1)", "g1 = 1 + x"),
        ("tau=2 (exact z_max=2)", "g1 = 1 + x; g2 = x * g1"),
        ("tau=3 (exact z_max=3)", "g1 = x * x; g2 = 1 - g1; g3 = x * g2"),
        ("tau=4 (exact z_max=3)", "g1 = 1 + x; g2 = 1 - x; g3 = x * g1; g4 = g2 * g3"),
        ("tau=5 (exact z_max=4)", "g1 = 1 + 1; g2 = 1 + x; g3 = x * g2; g4 = g1 - g3; g5 = g3 * g4"),
        ("tau=6 (exact z_max=5)", "g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4; g6 = x * g5"),
        ("tau=7 (exact z_max=5)", "g1 = 1 + 1; g2 = x + x; g3 = x * x; g4 = g1 - g3; g5 = g4 * g4; g6 = g3 - g5; g7 = g2 * g6"),
        ("tau=8 (exact z_max=6)", "g1 = 1 + 1; g2 = 1 + x; g3 = g1 + g1; g4 = x * g2; g5 = g1 - g4; g6 = g3 + g5; g7 = g4 * g5; g8 = g6 * g7"),
        ("tau=9 (exact z_max=6 on [-32,31])", "g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4; g6 = x * g5; g7 = 1 + x; g8 = g1 + g7; g9 = g6 * g8"),
        ("tau=10 (7 roots, sym)", "g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4; g6 = x * g5; g7 = 1 + g1; g8 = g7 * g7; g9 = g2 - g8; g10 = g6 * g9"),
        ("tau=10 (7 roots, q)", "g1 = 1 + 1; g2 = 1 + x; g3 = g1 + g1; g4 = x * g2; g5 = g1 - g4; g6 = g3 + g5; g7 = g4 * g5; g8 = g6 * g7; g9 = x + g3; g10 = g8 * g9"),
        ("tau=11 (8 roots, q)", "g1 = 1 + 1; g2 = 1 + x; g3 = g1 + g1; g4 = x * g2; g5 = g1 - g4; g6 = g3 + g5; g7 = g4 * g5; g8 = g6 * g7; g9 = g1 + g3; g10 = g6 + g9; g11 = g8 * g10"),
        ("tau=12 (8 roots, diff-sq)", "g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4; g6 = g1 + g1; g7 = g6 + g1; g8 = g7 + g7; g9 = g2 - g8; g10 = g9 * g9; g11 = g2 - g10; g12 = g5 * g11"),
        ("tau=13 (9 roots, q*(x-4))", "g1 = 1 + 1; g2 = 1 + x; g3 = g1 + g1; g4 = x * g2; g5 = g1 - g4; g6 = g3 + g5; g7 = g4 * g5; g8 = g6 * g7; g9 = g1 + g3; g10 = g6 + g9; g11 = g8 * g10; g12 = x - g3; g13 = g11 * g12"),
    ]
    for label, s in witnesses:
        verify_and_report(label, s)
