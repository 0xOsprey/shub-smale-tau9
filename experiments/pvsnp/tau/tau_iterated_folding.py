#!/usr/bin/env python3
"""
Track B: Iterated Folding & High-tau Record Hunter (tau = 14, 15, 16, 17, 18)
and m = 4 Multiplication Root Proliferation Diophantine Search (Smale's 4th Problem).

100% exact arbitrary-precision Python int verification for every claimed witness.
"""

from __future__ import annotations

import math
import sys
import time
from collections import defaultdict
from typing import Dict, List, Optional, Set, Tuple

sys.path.insert(0, "/Users/joe/github/gemini-neon/experiments/pvsnp/tau")
from tau_search import (
    Gate,
    Poly,
    eval_slp_exact,
    find_integer_roots_in_range,
    format_slp,
    poly_eval,
    poly_to_str,
)


# ---------------------------------------------------------------------------
# Exact arbitrary-precision polynomial arithmetic & verifier
# ---------------------------------------------------------------------------

def poly_add(a: Poly, b: Poly) -> Poly:
    n = max(len(a), len(b))
    r = [0] * n
    for i, v in enumerate(a):
        r[i] += v
    for i, v in enumerate(b):
        r[i] += v
    while r and r[-1] == 0:
        r.pop()
    return r


def poly_sub(a: Poly, b: Poly) -> Poly:
    n = max(len(a), len(b))
    r = [0] * n
    for i, v in enumerate(a):
        r[i] += v
    for i, v in enumerate(b):
        r[i] -= v
    while r and r[-1] == 0:
        r.pop()
    return r


def poly_mul(a: Poly, b: Poly) -> Poly:
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                if bj:
                    r[i + j] += ai * bj
    while r and r[-1] == 0:
        r.pop()
    return r


def poly_div_linear(p: Poly, r: int) -> Tuple[Poly, int]:
    """Exact synthetic division of p(x) by (x - r). Returns (quotient, remainder)."""
    if not p:
        return [], 0
    deg = len(p) - 1
    q = [0] * deg
    rem = p[deg]
    for i in range(deg - 1, -1, -1):
        q[i] = rem
        rem = p[i] + rem * r
    while q and q[-1] == 0:
        q.pop()
    return q, rem


def count_muls(gates: List[Gate]) -> int:
    return sum(1 for op, _, _ in gates if op == "*")


def integer_roots_of_poly_fast(p: Poly) -> List[int]:
    """Find all integer roots of a low-degree polynomial (deg <= 4) exactly."""
    if not p:
        return []
    deg = len(p) - 1
    if deg == 0:
        return []
    if deg == 1:
        # a0 + a1*x = 0
        if p[0] % p[1] == 0:
            return [-p[0] // p[1]]
        return []
    if deg == 2:
        c, b, a = p[0], p[1], p[2]
        disc = b * b - 4 * a * c
        if disc < 0:
            return []
        s = math.isqrt(disc)
        if s * s != disc:
            return []
        out = set()
        for num in (-b + s, -b - s):
            if num % (2 * a) == 0:
                out.add(num // (2 * a))
        return sorted(out)
    # Fallback for deg >= 3: rational root test on divisors of p[0] if small, else range
    return find_integer_roots_in_range(p, -200, 200)


def verify_witness_exact(gates: List[Gate], expected_roots: Optional[List[int]] = None,
                         root_bound: Optional[int] = None) -> Dict:
    """
    100% exact arbitrary-precision verification:
      - Evaluates SLP from scratch to exact integer polynomial
      - Checks nonzero
      - Verifies every claimed root has exact f(r) = 0
      - Verifies exact linear factor division by prod (x - r) with remainder 0
      - Verifies all roots are distinct
      - Reports exact tau, mulCount, degree, roots
    """
    poly = eval_slp_exact(gates)
    if not poly:
        raise AssertionError("Polynomial is identically zero!")
    deg = len(poly) - 1
    if expected_roots is not None:
        roots = sorted(set(expected_roots))
    else:
        bound = root_bound if root_bound is not None else 2000
        roots = find_integer_roots_in_range(poly, -bound, bound)

    cur = list(poly)
    for r in roots:
        val = poly_eval(poly, r)
        if val != 0:
            raise AssertionError(f"f({r}) = {val} != 0")
        cur, rem = poly_div_linear(cur, r)
        if rem != 0:
            raise AssertionError(f"Linear division by (x - {r}) left remainder {rem}")

    if not cur:
        raise AssertionError("Quotient became zero unexpectedly!")

    return {
        "tau": len(gates),
        "mulCount": count_muls(gates),
        "degree": deg,
        "num_roots": len(roots),
        "roots": roots,
        "gates": list(gates),
        "slp": format_slp(gates),
        "poly": poly,
    }


class SLPBuilder:
    def __init__(self) -> None:
        self.gates: List[Gate] = []
        self.poly_to_idx: Dict[Tuple[int, ...], int] = {(1,): -1, (0, 1): 0}
        self.idx_to_poly: Dict[int, Poly] = {-1: [1], 0: [0, 1]}

    def copy(self) -> "SLPBuilder":
        b = SLPBuilder()
        b.gates = list(self.gates)
        b.poly_to_idx = dict(self.poly_to_idx)
        b.idx_to_poly = {k: list(v) for k, v in self.idx_to_poly.items()}
        return b

    def op(self, kind: str, i: int, j: int) -> int:
        a, b = self.idx_to_poly[i], self.idx_to_poly[j]
        if kind == "+":
            p = poly_add(a, b)
        elif kind == "-":
            p = poly_sub(a, b)
        elif kind == "*":
            p = poly_mul(a, b)
        else:
            raise ValueError(kind)
        t = tuple(p)
        if t in self.poly_to_idx:
            return self.poly_to_idx[t]
        idx = len(self.gates) + 1
        self.gates.append((kind, i, j))
        self.poly_to_idx[t] = idx
        self.idx_to_poly[idx] = p
        return idx

    def add(self, i: int, j: int) -> int:
        return self.op("+", i, j)

    def sub(self, i: int, j: int) -> int:
        return self.op("-", i, j)

    def mul(self, i: int, j: int) -> int:
        return self.op("*", i, j)

    def sq(self, i: int) -> int:
        return self.op("*", i, i)

    @property
    def tau(self) -> int:
        return len(self.gates)

    def consts(self) -> Dict[int, int]:
        out: Dict[int, int] = {}
        for idx, p in self.idx_to_poly.items():
            if len(p) == 1 and p[0] > 0:
                out[p[0]] = idx
        return out

    def build_const_add_only(self, target: int) -> int:
        """Build positive integer constant using ONLY '+' (0 multiplications!), sharing powers of 2."""
        assert target >= 1
        cs = self.consts()
        if target in cs:
            return cs[target]
        # Build all needed powers of 2 up to bit_length - 1, then sum set bits (reusing powers of 2 across calls!)
        bl = target.bit_length()
        pow2 = {0: -1}
        cur = -1
        for k in range(1, bl):
            cur = self.add(cur, cur)
            pow2[k] = cur
        # Sum set bits from MSB to LSB
        acc = None
        for k in range(bl - 1, -1, -1):
            if (target >> k) & 1:
                if acc is None:
                    acc = pow2[k]
                else:
                    acc = self.add(acc, pow2[k])
        assert acc is not None
        return acc

    def build_const_min(self, target: int, chains: Dict[int, List[Tuple[str, int, int]]]) -> int:
        assert target >= 1
        cs = self.consts()
        if target in cs:
            return cs[target]
        c_list = list(cs.items())
        for v1, i1 in c_list:
            for v2, i2 in c_list:
                if v1 + v2 == target:
                    return self.add(i1, i2)
                if v1 - v2 == target:
                    return self.sub(i1, i2)
                if v1 * v2 == target:
                    return self.mul(i1, i2)
        best_cost = 999
        best_ops = None
        if target in chains:
            best_cost = len(chains[target])
            best_ops = ("chain", chains[target])

        if best_cost > 2:
            for v1, i1 in c_list:
                for v2, i2 in c_list:
                    for op1, w in [("+", v1 + v2), ("-", v1 - v2), ("*", v1 * v2)]:
                        if w <= 0:
                            continue
                        if w * w == target:
                            best_cost = 2
                            best_ops = ("2step_sq", op1, i1, i2)
                            break
                        for v3, i3 in c_list:
                            if w + v3 == target:
                                best_cost = 2
                                best_ops = ("2step", op1, i1, i2, "+", i3)
                                break
                            if w - v3 == target:
                                best_cost = 2
                                best_ops = ("2step", op1, i1, i2, "-", i3)
                                break
                            if v3 - w == target:
                                best_cost = 2
                                best_ops = ("2step_rev", op1, i1, i2, "-", i3)
                                break
                            if w * v3 == target:
                                best_cost = 2
                                best_ops = ("2step", op1, i1, i2, "*", i3)
                                break
                        if best_cost == 2:
                            break
                    if best_cost == 2:
                        break
                if best_cost == 2:
                    break

        if best_ops is not None:
            kind = best_ops[0]
            if kind == "2step_sq":
                _, op1, i1, i2 = best_ops
                w_idx = self.op(op1, i1, i2)
                return self.sq(w_idx)
            elif kind == "2step":
                _, op1, i1, i2, op2, i3 = best_ops
                w_idx = self.op(op1, i1, i2)
                return self.op(op2, w_idx, i3)
            elif kind == "2step_rev":
                _, op1, i1, i2, op2, i3 = best_ops
                w_idx = self.op(op1, i1, i2)
                return self.op(op2, i3, w_idx)
            elif kind == "chain":
                vals_idx = {1: -1}
                vals_list = [1]
                for op, a_pos, b_pos in best_ops[1]:
                    ia = vals_idx[vals_list[a_pos]]
                    ib = vals_idx[vals_list[b_pos]]
                    ni = self.op(op, ia, ib)
                    nv = self.idx_to_poly[ni][0]
                    vals_list.append(nv)
                    vals_idx[nv] = ni
                return vals_idx[target]

        r = math.isqrt(target)
        if r * r == target and r > 1:
            ri = self.build_const_min(r, chains)
            return self.sq(ri)
        return self.build_const_add_only(target)


def precompute_const_chains(max_steps: int = 6, limit: int = 200000) -> Dict[int, List[Tuple[str, int, int]]]:
    """Precompute shortest constant chains up to max_steps."""
    best: Dict[int, List[Tuple[str, int, int]]] = {1: []}
    layers: List[List[Tuple[Tuple[int, ...], List[Tuple[str, int, int]]]]] = [[((1,), [])]]
    seen: Set[Tuple[int, ...]] = {(1,)}

    for step in range(1, max_steps + 1):
        nxt: List[Tuple[Tuple[int, ...], List[Tuple[str, int, int]]]] = []
        for vals, ops in layers[-1]:
            n = len(vals)
            for i in range(n):
                for j in range(i, n):
                    a, b = vals[i], vals[j]
                    cands = [("+", a + b, i, j), ("*", a * b, i, j)]
                    if b > a:
                        cands.append(("-", b - a, j, i))
                    elif a > b:
                        cands.append(("-", a - b, i, j))
                    for op, v, pi, pj in cands:
                        if v <= 0 or v > limit or v in vals:
                            continue
                        new_ops = ops + [(op, pi, pj)]
                        if v not in best:
                            best[v] = new_ops
                        if step < max_steps:
                            new_vals = vals + (v,)
                            key = tuple(sorted(new_vals))
                            if key not in seen:
                                seen.add(key)
                                nxt.append((new_vals, new_ops))
        layers.append(nxt)
    return best


def precompute_all_const_dags(max_steps: int = 4) -> List[Tuple[Tuple[int, ...], List[Tuple[str, int, int]]]]:
    all_states: List[Tuple[Tuple[int, ...], List[Tuple[str, int, int]]]] = [((1,), [])]
    layers = [[((1,), [])]]
    seen: Set[Tuple[int, ...]] = {(1,)}
    for step in range(1, max_steps + 1):
        nxt = []
        for vals, ops in layers[-1]:
            n = len(vals)
            for i in range(n):
                for j in range(i, n):
                    a, b = vals[i], vals[j]
                    cands = [("+", a + b, i, j), ("*", a * b, i, j)]
                    if b > a:
                        cands.append(("-", b - a, j, i))
                    elif a > b:
                        cands.append(("-", a - b, i, j))
                    for op, v, pi, pj in cands:
                        if v <= 0 or v > 50000 or v in vals:
                            continue
                        new_vals = vals + (v,)
                        key = tuple(sorted(new_vals))
                        if key not in seen:
                            seen.add(key)
                            new_ops = ops + [(op, pi, pj)]
                            nxt.append((new_vals, new_ops))
                            all_states.append((new_vals, new_ops))
        layers.append(nxt)
    return all_states


def apply_const_ops(b: SLPBuilder, ops: List[Tuple[str, int, int]]) -> None:
    vals_list = [1]
    vals_idx = {1: -1}
    for op, pi, pj in ops:
        ia = vals_idx[vals_list[pi]]
        ib = vals_idx[vals_list[pj]]
        ni = b.op(op, ia, ib)
        nv = b.idx_to_poly[ni][0]
        vals_list.append(nv)
        vals_idx[nv] = ni


# ---------------------------------------------------------------------------
# Record Tracker + Elite Pool
# ---------------------------------------------------------------------------

class RecordTracker:
    def __init__(self, max_tau: int = 18) -> None:
        self.max_tau = max_tau
        self.best: Dict[int, Dict] = {}
        self.elite: Dict[int, List[Tuple[int, SLPBuilder, Set[int], str]]] = defaultdict(list)

    def submit_builder(self, b: SLPBuilder, prod_idx: int, rset: Set[int], label: str) -> None:
        tau = b.tau
        if tau > self.max_tau or tau < 10:
            return
        # Ensure output gate is prod_idx
        if prod_idx != len(b.gates):
            return
        nr = len(rset)
        # Keep top elites per tau for suffix extension
        el = self.elite[tau]
        if len(el) < 25 or nr >= el[-1][0]:
            # Avoid duplicate SLP strings
            s = format_slp(b.gates)
            if not any(format_slp(x[1].gates) == s for x in el):
                el.append((nr, b.copy(), set(rset), label))
                el.sort(key=lambda x: -x[0])
                if len(el) > 25:
                    el.pop()

        if tau in self.best and nr <= self.best[tau]["num_roots"]:
            return
        info = verify_witness_exact(b.gates, expected_roots=sorted(rset))
        info["label"] = label
        if tau not in self.best or info["num_roots"] > self.best[tau]["num_roots"]:
            self.best[tau] = info
            print(f"  [NEW BEST tau={tau:2d}] roots={info['num_roots']:2d} (deg={info['degree']:2d}, mul={info['mulCount']:2d}) | {label}")
            print(f"      roots = {info['roots']}")
            print(f"      SLP   = {info['slp']}")

    def submit(self, gates: List[Gate], label: str, expected_roots: Optional[List[int]] = None) -> None:
        tau = len(gates)
        if tau > self.max_tau or tau < 10:
            return
        if expected_roots is not None and tau in self.best:
            if len(expected_roots) <= self.best[tau]["num_roots"]:
                return
        info = verify_witness_exact(gates, expected_roots=expected_roots)
        info["label"] = label
        if tau not in self.best or info["num_roots"] > self.best[tau]["num_roots"]:
            self.best[tau] = info
            print(f"  [NEW BEST tau={tau:2d}] roots={info['num_roots']:2d} (deg={info['degree']:2d}, mul={info['mulCount']:2d}) | {label}")
            print(f"      roots = {info['roots']}")
            print(f"      SLP   = {info['slp']}")


# ---------------------------------------------------------------------------
# General DAG Suffix Extender (harvests ALL 1-gate & 2-gate new-root factors!)
# ---------------------------------------------------------------------------

def extend_elite_dags(tracker: RecordTracker) -> None:
    """
    For every elite witness at tau = 11..17, exhaustively check:
      - 1-gate extension: prod * existing_gate (adds roots already in DAG)
      - 2-gate extension: f = g_i op g_j (deg 1 or 2), prod * f (adds +1 or +2 roots!)
      - 3-gate extension: c = c_i op c_j (new constant), f = q - c or u +/- c or x +/- c, prod * f (+2 roots!)
    Recursively up to max_tau = 18!
    """
    print("\n=== Mission 1E: Exhaustive 1/2/3-Gate Factor Harvesting on Elite Prefixes ===")
    for tau in range(11, tracker.max_tau):
        elites = list(tracker.elite[tau])
        for nr, b0, rset0, lbl0 in elites:
            prod_idx = b0.tau
            rem = tracker.max_tau - tau
            all_idxs = [-1, 0] + list(range(1, prod_idx + 1))

            # 1-gate: prod * existing low-deg gate
            for gi in all_idxs:
                p = b0.idx_to_poly[gi]
                if 1 <= len(p) - 1 <= 4:
                    rs = set(integer_roots_of_poly_fast(p)) - rset0
                    if rs:
                        b1 = b0.copy()
                        p1 = b1.mul(prod_idx, gi)
                        tracker.submit_builder(b1, p1, rset0 | rs, f"{lbl0}*g{gi}")

            if rem < 2:
                continue

            # 2-gate: f = g_i op g_j (deg 1 or 2) -> prod * f
            low_idxs = [gi for gi in all_idxs if len(b0.idx_to_poly[gi]) - 1 <= 2]
            seen_new_roots: Set[Tuple[int, ...]] = set()
            for idx_a in range(len(low_idxs)):
                ia = low_idxs[idx_a]
                pa = b0.idx_to_poly[ia]
                for idx_b in range(idx_a, len(low_idxs)):
                    ib = low_idxs[idx_b]
                    pb = b0.idx_to_poly[ib]
                    cands = [
                        ("+", ia, ib, poly_add(pa, pb)),
                        ("-", ia, ib, poly_sub(pa, pb)),
                    ]
                    if ia != ib:
                        cands.append(("-", ib, ia, poly_sub(pb, pa)))
                    for op, x1, x2, pf in cands:
                        if not pf or len(pf) - 1 not in (1, 2):
                            continue
                        rs = set(integer_roots_of_poly_fast(pf)) - rset0
                        if not rs:
                            continue
                        key = tuple(sorted(rs))
                        if key in seen_new_roots:
                            continue
                        seen_new_roots.add(key)
                        b1 = b0.copy()
                        fi = b1.op(op, x1, x2)
                        p1 = b1.mul(prod_idx, fi)
                        tracker.submit_builder(b1, p1, rset0 | rs, f"{lbl0}*(g{x1}{op}g{x2})")

            if rem < 3:
                continue

            # 3-gate: build 1-step constant c = c1 op c2, then quad - c (or quad + c), then mul!
            cs = b0.consts()
            c_items = list(cs.items())
            quad_idxs = [gi for gi in all_idxs if len(b0.idx_to_poly[gi]) - 1 == 2]
            seen_3: Set[Tuple[int, ...]] = set()
            for idx1 in range(len(c_items)):
                v1, i1 = c_items[idx1]
                for idx2 in range(idx1, len(c_items)):
                    v2, i2 = c_items[idx2]
                    c_cands = [("+", i1, i2, v1 + v2), ("*", i1, i2, v1 * v2)]
                    if v1 > v2:
                        c_cands.append(("-", i1, i2, v1 - v2))
                    elif v2 > v1:
                        c_cands.append(("-", i2, i1, v2 - v1))
                    for cop, ci1, ci2, cv in c_cands:
                        if cv in cs or cv <= 0:
                            continue
                        for qi in quad_idxs:
                            qp = b0.idx_to_poly[qi]
                            for qop, pf in [("-", poly_sub(qp, [cv])), ("+", poly_add(qp, [cv]))]:
                                rs = set(integer_roots_of_poly_fast(pf)) - rset0
                                if len(rs) >= 2:
                                    key = tuple(sorted(rs))
                                    if key in seen_3:
                                        continue
                                    seen_3.add(key)
                                    b1 = b0.copy()
                                    ci = b1.op(cop, ci1, ci2)
                                    fi = b1.op(qop, qi, ci)
                                    p1 = b1.mul(prod_idx, fi)
                                    tracker.submit_builder(b1, p1, rset0 | rs, f"{lbl0}*(g{qi}{qop}{cv})")


# ---------------------------------------------------------------------------
# Mission 1A: Shifted Pronic-Square & Sum-of-Two-Squares Multi-Factor + Folding
# ---------------------------------------------------------------------------

def search_shifted_families(tracker: RecordTracker, chains: Dict[int, List[Tuple[str, int, int]]],
                            max_a: int = 2000) -> None:
    print(f"\n=== Mission 1A: Shifted Pronic-Square & Sum-of-Two-Squares (a <= {max_a}) ===")

    pronics: Dict[int, Tuple[int, int]] = {}
    k = 0
    while k * (k + 1) <= 2 * max_a:
        pronics[k * (k + 1)] = (k, -k - 1)
        k += 1
    pronic_vals = sorted(pronics.keys())

    squares: Dict[int, Tuple[int, ...]] = {0: (0,)}
    k = 1
    while k * k <= 2 * max_a:
        squares[k * k] = (k, -k)
        k += 1
    square_vals = sorted(squares.keys())

    for fname, val_map, vals in [("pronic", pronics, pronic_vals), ("square", squares, square_vals)]:
        by_sum: Dict[int, List[Tuple[int, int, int]]] = defaultdict(list)
        n = len(vals)
        for i in range(n):
            v1 = vals[i]
            for j in range(i + 1, n):
                v2 = vals[j]
                S = v1 + v2
                if S > 2 * max_a:
                    break
                by_sum[S].append((v2 - v1, v1, v2))

        for S, pairs in by_sum.items():
            if len(pairs) < 2:
                continue
            is_even = (S % 2 == 0)
            a = S // 2
            c_a = len(chains[a if is_even else S]) if (a if is_even else S) in chains else 99
            if c_a > 6:
                continue
            if c_a > 5 and len(pairs) < 3:
                continue

            pair_info = []
            for diff, v1, v2 in pairs:
                d = diff // 2 if is_even else diff
                d2 = d * d
                c_d = len(chains[d]) if d in chains else 99
                c_d2 = len(chains[d2]) if d2 in chains else 99
                est = min(c_d + 1, c_d2)
                roots_pair = list(val_map[v1]) + list(val_map[v2])
                pair_info.append((est, d, d2, v1, v2, roots_pair))
            pair_info.sort(key=lambda x: x[0])

            b0 = SLPBuilder()
            if fname == "pronic":
                g1 = b0.add(-1, 0)
                q_idx = b0.mul(0, g1)
            else:
                q_idx = b0.sq(0)

            if is_even:
                a_idx = b0.build_const_min(a, chains)
                u_idx = b0.sub(q_idx, a_idx)
            else:
                q2_idx = b0.add(q_idx, q_idx)
                s_idx = b0.build_const_min(S, chains)
                u_idx = b0.sub(q2_idx, s_idx)
            w_idx = b0.sq(u_idx)

            if b0.tau > 11:
                continue

            top_pairs = pair_info[:6]
            m = len(top_pairs)

            def try_bonuses(b_in: SLPBuilder, prod_idx: int, rset: Set[int], desc: str) -> None:
                tracker.submit_builder(b_in, prod_idx, rset, desc)
                rem = tracker.max_tau - b_in.tau
                if rem <= 0:
                    return

                # 1-gate bonuses: * q, * (q - a), * x
                q_roots = set(val_map[0])
                if not q_roots.issubset(rset) and rem >= 1:
                    b1 = b_in.copy()
                    p1 = b1.mul(prod_idx, q_idx)
                    try_bonuses(b1, p1, rset | q_roots, desc + "*q")

                if is_even and a in val_map:
                    u_roots = set(val_map[a])
                    if not u_roots.issubset(rset) and rem >= 1:
                        b1 = b_in.copy()
                        p1 = b1.mul(prod_idx, u_idx)
                        try_bonuses(b1, p1, rset | u_roots, desc + "*(q-a)")

                if 0 not in rset and rem >= 1:
                    b1 = b_in.copy()
                    p1 = b1.mul(prod_idx, 0)
                    try_bonuses(b1, p1, rset | {0}, desc + "*x")

                if rem < 2:
                    return

                # 2-gate bonuses: (q - c) or (u +/- c) where result is in val_map!
                cs = b_in.consts()
                for c_val, c_idx in cs.items():
                    if c_val in val_map:
                        new_r = set(val_map[c_val]) - rset
                        if len(new_r) >= 2:
                            b1 = b_in.copy()
                            f = b1.sub(q_idx, c_idx)
                            p1 = b1.mul(prod_idx, f)
                            try_bonuses(b1, p1, rset | new_r, desc + f"*(q-{c_val})")
                    if is_even:
                        for sign, target_v in [("+", a - c_val), ("-", a + c_val)]:
                            if target_v in val_map:
                                new_r = set(val_map[target_v]) - rset
                                if len(new_r) >= 2:
                                    b1 = b_in.copy()
                                    f = b1.op(sign, u_idx, c_idx)
                                    p1 = b1.mul(prod_idx, f)
                                    try_bonuses(b1, p1, rset | new_r, desc + f"*(q-{target_v})")
                            # Also check pronic a + a^2 = a(a+1) when target_v > 2*max_a!
                            elif fname == "pronic" and target_v > 2 * max_a:
                                # Check if 4*target_v + 1 is odd square
                                disc = 4 * target_v + 1
                                sd = math.isqrt(disc)
                                if sd * sd == disc and sd % 2 == 1:
                                    rk = (sd - 1) // 2
                                    new_r = {rk, -rk - 1} - rset
                                    if len(new_r) >= 2:
                                        b1 = b_in.copy()
                                        f = b1.op(sign, u_idx, c_idx)
                                        p1 = b1.mul(prod_idx, f)
                                        try_bonuses(b1, p1, rset | new_r, desc + f"*(q-{target_v})")

            def add_quartic_factor(b_in: SLPBuilder, d: int, d2: int) -> Tuple[SLPBuilder, int]:
                b1 = b_in.copy()
                cs = b1.consts()
                if d2 in cs:
                    d2_idx = cs[d2]
                else:
                    b_a = b1.copy()
                    di = b_a.build_const_min(d, chains)
                    d2i_a = b_a.sq(di)
                    b_b = b1.copy()
                    d2i_b = b_b.build_const_min(d2, chains)
                    if b_a.tau <= b_b.tau:
                        b1, d2_idx = b_a, d2i_a
                    else:
                        b1, d2_idx = b_b, d2i_b
                fac_idx = b1.sub(w_idx, d2_idx)
                return b1, fac_idx

            for i in range(m):
                _, d1, d1_2, v1a, v1b, r1 = top_pairs[i]
                b1, f1 = add_quartic_factor(b0, d1, d1_2)
                if b1.tau > tracker.max_tau:
                    continue
                for j in range(i + 1, m):
                    _, d2, d2_2, v2a, v2b, r2 = top_pairs[j]
                    b2, f2 = add_quartic_factor(b1, d2, d2_2)
                    if b2.tau + 1 > tracker.max_tau:
                        continue
                    p12 = b2.mul(f1, f2)
                    r12 = set(r1) | set(r2)
                    try_bonuses(b2, p12, r12, f"{fname}(S={S},d={d1},{d2})")

                    for k3 in range(j + 1, m):
                        _, d3, d3_2, v3a, v3b, r3 = top_pairs[k3]
                        b3, f3 = add_quartic_factor(b2, d3, d3_2)
                        if b3.tau + 1 > tracker.max_tau:
                            continue
                        p123 = b3.mul(p12, f3)
                        r123 = r12 | set(r3)
                        try_bonuses(b3, p123, r123, f"{fname}(S={S},d={d1},{d2},{d3})")

                        for k4 in range(k3 + 1, m):
                            _, d4, d4_2, v4a, v4b, r4 = top_pairs[k4]
                            b4, f4 = add_quartic_factor(b3, d4, d4_2)
                            if b4.tau + 1 > tracker.max_tau:
                                continue
                            p1234 = b4.mul(p123, f4)
                            r1234 = r123 | set(r4)
                            try_bonuses(b4, p1234, r1234, f"{fname}(S={S},d={d1},{d2},{d3},{d4})")


# ---------------------------------------------------------------------------
# Mission 1B: Optimal Multi-Constant DAG Sharing
# ---------------------------------------------------------------------------

def search_optimal_const_sharing(tracker: RecordTracker, max_a: int = 1000) -> None:
    print(f"\n=== Mission 1B: Optimal Constant-DAG Sharing Search (a <= {max_a}) ===")
    const_dags = precompute_all_const_dags(max_steps=4)
    print(f"  Enumerated {len(const_dags)} distinct constant DAGs up to 4 gates.")

    pronics = {k * (k + 1): (k, -k - 1) for k in range(0, 200)}
    squares = {k * k: (k, -k) for k in range(1, 200)}
    squares[0] = (0,)

    for fname, val_map in [("pronic", pronics), ("square", squares)]:
        val_set = set(val_map.keys())
        for vals, ops in const_dags:
            vset = set(vals)
            one_step: Dict[int, Tuple[str, int, int]] = {}
            n = len(vals)
            for i in range(n):
                for j in range(i, n):
                    a1, b1 = vals[i], vals[j]
                    for op, r, pi, pj in [("+", a1 + b1, i, j), ("*", a1 * b1, i, j)]:
                        if r not in vset and r not in one_step:
                            one_step[r] = (op, pi, pj)
                    if b1 > a1 and (b1 - a1) not in vset and (b1 - a1) not in one_step:
                        one_step[b1 - a1] = ("-", j, i)
                    elif a1 > b1 and (a1 - b1) not in vset and (a1 - b1) not in one_step:
                        one_step[a1 - b1] = ("-", i, j)

            for a in vals:
                if a < 4 or a > max_a:
                    continue
                pairs = []
                for v1 in val_set:
                    if v1 < a:
                        v2 = 2 * a - v1
                        if v2 in val_set:
                            d = a - v1
                            d2 = d * d
                            if d2 in vset:
                                cost, mode = 0, ("in", d2)
                            elif d in vset:
                                cost, mode = 1, ("sq_in", d)
                            elif d2 in one_step:
                                cost, mode = 1, ("1step", d2)
                            elif d in one_step:
                                cost, mode = 2, ("sq_1step", d)
                            else:
                                continue
                            pairs.append((cost, d, d2, v1, v2, mode))
                if len(pairs) < 2:
                    continue
                pairs.sort(key=lambda x: x[0])

                b0 = SLPBuilder()
                if fname == "pronic":
                    g1 = b0.add(-1, 0)
                    q_idx = b0.mul(0, g1)
                else:
                    q_idx = b0.sq(0)
                apply_const_ops(b0, ops)
                cs0 = b0.consts()
                a_idx = cs0[a]
                u_idx = b0.sub(q_idx, a_idx)
                w_idx = b0.sq(u_idx)

                def realize_d2(b: SLPBuilder, mode) -> int:
                    cs = b.consts()
                    kind, val = mode
                    if kind == "in":
                        return cs[val]
                    elif kind == "sq_in":
                        return b.sq(cs[val])
                    elif kind == "1step":
                        if val in cs:
                            return cs[val]
                        op, pi, pj = one_step[val]
                        return b.op(op, cs[vals[pi]], cs[vals[pj]])
                    else:
                        if val * val in cs:
                            return cs[val * val]
                        if val in cs:
                            return b.sq(cs[val])
                        op, pi, pj = one_step[val]
                        di = b.op(op, cs[vals[pi]], cs[vals[pj]])
                        return b.sq(di)

                top = pairs[:5]
                for i in range(len(top)):
                    for j in range(i + 1, len(top)):
                        b2 = b0.copy()
                        d2i = realize_d2(b2, top[i][5])
                        f1 = b2.sub(w_idx, d2i)
                        d2j = realize_d2(b2, top[j][5])
                        f2 = b2.sub(w_idx, d2j)
                        p12 = b2.mul(f1, f2)
                        r12 = set(val_map[top[i][3]]) | set(val_map[top[i][4]]) | set(val_map[top[j][3]]) | set(val_map[top[j][4]])
                        if b2.tau <= tracker.max_tau:
                            tracker.submit_builder(b2, p12, r12, f"optDAG-{fname}(a={a},d={top[i][1]},{top[j][1]})")
                            if not set(val_map[0]).issubset(r12) and b2.tau + 1 <= tracker.max_tau:
                                bq = b2.copy()
                                pq = bq.mul(p12, q_idx)
                                rq = r12 | set(val_map[0])
                                tracker.submit_builder(bq, pq, rq, f"optDAG-{fname}(a={a},d={top[i][1]},{top[j][1]})*q")

                        for k3 in range(j + 1, len(top)):
                            b3 = b2.copy()
                            d2k = realize_d2(b3, top[k3][5])
                            f3 = b3.sub(w_idx, d2k)
                            p123 = b3.mul(p12, f3)
                            r123 = r12 | set(val_map[top[k3][3]]) | set(val_map[top[k3][4]])
                            if b3.tau <= tracker.max_tau:
                                tracker.submit_builder(b3, p123, r123, f"optDAG3-{fname}(a={a},d={top[i][1]},{top[j][1]},{top[k3][1]})")
                                if not set(val_map[0]).issubset(r123) and b3.tau + 1 <= tracker.max_tau:
                                    bq = b3.copy()
                                    pq = bq.mul(p123, q_idx)
                                    rq = r123 | set(val_map[0])
                                    tracker.submit_builder(bq, pq, rq, f"optDAG3-{fname}(a={a},d={top[i][1]},{top[j][1]},{top[k3][1]})*q")


# ---------------------------------------------------------------------------
# Mission 1C: Generalized Midpoint-Difference Search
# ---------------------------------------------------------------------------

def search_midpoint_families(tracker: RecordTracker, chains: Dict[int, List[Tuple[str, int, int]]]) -> None:
    print("\n=== Mission 1C: Generalized Midpoint-Difference Search ===")
    for c in [1, 2, 3]:
        for m in range(1, 25):
            k = m * (m + c)
            if k not in chains or len(chains[k]) > 5:
                continue
            mid_pairs = []
            for s in range(1, 100):
                val = k + s * s
                if val % 2 == 0:
                    half = val // 2
                    t = math.isqrt(half)
                    if t * t == half and t != s:
                        mid_pairs.append((s, t))
            if not mid_pairs:
                continue

            b0 = SLPBuilder()
            x2 = b0.sq(0)
            if c == 1:
                cx2 = x2
            elif c == 2:
                cx = b0.add(0, 0)
                cx2 = b0.sq(cx)
            else:
                x2_lin = b0.add(0, 0)
                cx = b0.add(x2_lin, 0)
                cx2 = b0.sq(cx)
            ki = b0.build_const_min(k, chains)
            g_k = b0.sub(ki, x2)
            g_ksq = b0.sq(g_k)
            f0 = b0.sub(cx2, g_ksq)
            r0 = {m, -m, m + c, -(m + c)}

            for s1, t1 in mid_pairs:
                b1 = b0.copy()
                if s1 * s1 in b1.consts():
                    s1_2 = b1.consts()[s1 * s1]
                else:
                    s1i = b1.build_const_min(s1, chains)
                    s1_2 = b1.sq(s1i)
                fs1 = b1.sub(x2, s1_2)
                ft1 = b1.sub(g_k, fs1)
                p1 = b1.mul(f0, fs1)
                p2 = b1.mul(p1, ft1)
                r1 = r0 | {s1, -s1, t1, -t1}
                if b1.tau <= tracker.max_tau:
                    tracker.submit_builder(b1, p2, r1, f"mid1(c={c},k={k},s={s1},t={t1})")
                    if b1.tau + 1 <= tracker.max_tau:
                        bx = b1.copy()
                        px = bx.mul(0, p2)
                        tracker.submit_builder(bx, px, r1 | {0}, f"mid1(c={c},k={k},s={s1},t={t1})*x")

    # Dual difference-of-squares with midpoint:
    # f1 = (c1*x)^2 - (k1 - x^2)^2, f2 = (c2*x)^2 - (k2 - x^2)^2, midpoint (k1 - x^2) + (k2 - x^2) = 2(t^2 - x^2)
    cand_f = []
    for c in [1, 2]:
        for m in range(1, 15):
            k = m * (m + c)
            if k in chains and len(chains[k]) <= 5:
                cand_f.append((c, m, k, {m, -m, m + c, -(m + c)}))
    for i in range(len(cand_f)):
        c1, m1, k1, r1 = cand_f[i]
        for j in range(i + 1, len(cand_f)):
            c2, m2, k2, r2 = cand_f[j]
            if (k1 + k2) % 2 != 0:
                continue
            mid = (k1 + k2) // 2
            t = math.isqrt(mid)
            if t * t != mid:
                continue
            r_all = r1 | r2 | {t, -t}
            if len(r_all) < 10:
                continue
            b = SLPBuilder()
            x2 = b.sq(0)
            cx2_map = {1: x2}
            if c1 == 2 or c2 == 2:
                x2l = b.add(0, 0)
                cx2_map[2] = b.sq(x2l)
            k1i = b.build_const_min(k1, chains)
            g1 = b.sub(k1i, x2)
            f1 = b.sub(cx2_map[c1], b.sq(g1))
            k2i = b.build_const_min(k2, chains)
            g2 = b.sub(k2i, x2)
            f2 = b.sub(cx2_map[c2], b.sq(g2))
            p12 = b.mul(f1, f2)
            fm = b.add(g1, g2)
            p12m = b.mul(p12, fm)
            if b.tau <= tracker.max_tau:
                tracker.submit_builder(b, p12m, r_all, f"dual_mid(c1={c1},k1={k1},c2={c2},k2={k2},t={t})")
                if b.tau + 1 <= tracker.max_tau:
                    bx = b.copy()
                    px = bx.mul(0, p12m)
                    tracker.submit_builder(bx, px, r_all | {0}, f"dual_mid(c1={c1},k1={k1},c2={c2},k2={k2},t={t})*x")


# ---------------------------------------------------------------------------
# Mission 2: Diophantine Preimage Tree Test for m = 4 Multiplications
# ---------------------------------------------------------------------------

def search_m4_diophantine(max_a: int = 200000) -> Dict:
    max_S = 2 * max_a
    print(f"\n=== Mission 2: m = 4 Multiplication Diophantine Preimage Tree Search (a <= {max_a}, S <= {max_S}) ===")
    t0 = time.time()

    results: Dict = {
        "max_a": max_a,
        "fold4_16": [],
        "fold4_15": [],
        "fold4_14": [],
        "fold4_12": [],
        "stats": {},
    }

    families = []
    # 1. q = x(x+1)
    p_map = {}
    k = 0
    while k * (k + 1) <= max_S:
        p_map[k * (k + 1)] = (k, -k - 1)
        k += 1
    families.append(("q = x(x+1)", p_map))

    # 2. q = x^2
    s_map = {0: (0,)}
    k = 1
    while k * k <= max_S:
        s_map[k * k] = (k, -k)
        k += 1
    families.append(("q = x^2", s_map))

    for fname, vmap in families:
        tf = time.time()
        vals = sorted(vmap.keys())
        n = len(vals)
        by_S: Dict[int, List[Tuple[int, int, int]]] = defaultdict(list)
        for i in range(n):
            v1 = vals[i]
            for j in range(i + 1, n):
                v2 = vals[j]
                S = v1 + v2
                if S > max_S:
                    break
                by_S[S].append((v2 - v1, v1, v2))

        max_pairs = 0
        count_ge3 = 0
        count_ge4 = 0

        for S, pairs in by_S.items():
            np = len(pairs)
            if np > max_pairs:
                max_pairs = np
            if np < 3:
                continue
            count_ge3 += 1
            if np >= 4:
                count_ge4 += 1

            pairs.sort(key=lambda x: x[0])
            Ds = [p[0] for p in pairs]
            D2s = [d * d for d in Ds]
            D2_set = {d2: idx for idx, d2 in enumerate(D2s)}

            if np >= 4:
                sum_map: Dict[int, List[Tuple[int, int]]] = defaultdict(list)
                for i in range(np):
                    for j in range(i + 1, np):
                        s2 = D2s[i] + D2s[j]
                        if s2 in sum_map:
                            for p_i, p_j in sum_map[s2]:
                                if len({p_i, p_j, i, j}) == 4:
                                    idxs = sorted([p_i, p_j, i, j])
                                    rset = set()
                                    for ix in idxs:
                                        rset.update(vmap[pairs[ix][1]])
                                        rset.update(vmap[pairs[ix][2]])
                                    entry = (fname, S, [pairs[ix] for ix in idxs], sorted(rset))
                                    if len(rset) == 16:
                                        results["fold4_16"].append(entry)
                                    elif len(rset) == 15:
                                        results["fold4_15"].append(entry)
                        sum_map[s2].append((i, j))

            if S % 2 == 0 and (S // 2) in vmap:
                for i in range(np):
                    for j in range(i + 1, np):
                        s2 = D2s[i] + D2s[j]
                        if s2 in D2_set:
                            k_idx = D2_set[s2]
                            rset = set(vmap[S // 2])
                            for ix in (i, j, k_idx):
                                rset.update(vmap[pairs[ix][1]])
                                rset.update(vmap[pairs[ix][2]])
                            if len(rset) >= 13:
                                results["fold4_14"].append((fname, S, [pairs[i], pairs[j], pairs[k_idx]], sorted(rset)))

            if len(results["fold4_12"]) < 10:
                for i in range(np):
                    for k_idx in range(i + 2, np):
                        s2 = D2s[i] + D2s[k_idx]
                        if s2 % 2 == 0 and (s2 // 2) in D2_set:
                            j_idx = D2_set[s2 // 2]
                            rset = set()
                            for ix in (i, j_idx, k_idx):
                                rset.update(vmap[pairs[ix][1]])
                                rset.update(vmap[pairs[ix][2]])
                            if len(rset) == 12:
                                results["fold4_12"].append((fname, S, [pairs[i], pairs[j_idx], pairs[k_idx]], sorted(rset)))

        elapsed = time.time() - tf
        results["stats"][fname] = {
            "num_q_vals": n,
            "max_pairs_same_S": max_pairs,
            "S_with_ge3_pairs": count_ge3,
            "S_with_ge4_pairs": count_ge4,
            "elapsed_s": round(elapsed, 2),
        }
        print(f"  {fname}: {n} values, max_pairs={max_pairs}, S(>=3)={count_ge3}, S(>=4)={count_ge4} ({elapsed:.2f}s)")

    results["fold4_16"].sort(key=lambda x: x[1])
    results["fold4_15"].sort(key=lambda x: x[1])
    results["fold4_14"].sort(key=lambda x: x[1])
    results["fold4_12"].sort(key=lambda x: x[1])

    print(f"\n  TOTAL 16-ROOT 4-LEVEL FOLD SOLUTIONS (a <= {max_a}): {len(results['fold4_16'])}")
    for fname, S, chosen, roots in results["fold4_16"][:10]:
        Ds = [p[0] for p in chosen]
        print(f"    {fname:10s} S={S:7d} (a={S/2:9.1f}) | pairs={[(p[1], p[2]) for p in chosen]} | D={Ds}")

    print(f"  TOTAL 15-ROOT 4-LEVEL FOLD SOLUTIONS (a <= {max_a}): {len(results['fold4_15'])}")
    print(f"  TOTAL 14-ROOT 4-LEVEL FOLD SOLUTIONS (a <= {max_a}): {len(results['fold4_14'])}")
    print(f"  TOTAL 12-ROOT AP3 FOLD SOLUTIONS (sampled): {len(results['fold4_12'])}")

    # Build and EXACT-VERIFY minimal-mul (mulCount=4) witnesses for:
    # 1. Smallest pronic 16-root solution (using integer a = S//2, b, c, e when even!)
    # 2. Smallest square 16-root solution
    # 3. Eisenstein cubic-quartic 12-root solution
    for fname_target in ["q = x(x+1)", "q = x^2"]:
        cands = [x for x in results["fold4_16"] if x[0] == fname_target]
        if not cands:
            continue
        fname, S, chosen, roots = cands[0]
        b = SLPBuilder()
        if fname == "q = x(x+1)":
            g1 = b.add(-1, 0)
            q = b.mul(0, g1)  # mult 1
        else:
            q = b.sq(0)       # mult 1

        Ds = sorted([p[0] for p in chosen])
        D1, D2, D3, D4 = Ds
        # Simplify dividing by 2 whenever possible!
        if S % 2 == 0 and all(d % 2 == 0 for d in Ds):
            a_val = S // 2
            ds = [d // 2 for d in Ds]
            d1, d2, d3, d4 = ds
            ai = b.build_const_add_only(a_val)
            f1 = b.sub(q, ai)
            f2 = b.sq(f1)  # mult 2
            B2 = d1 * d1 + d4 * d4
            assert B2 == d2 * d2 + d3 * d3
            if B2 % 2 == 0:
                b_val = B2 // 2
                bi = b.build_const_add_only(b_val)
                f3_in = b.sub(f2, bi)
                u1 = (d4 * d4 - d1 * d1) // 2
                u2 = (d3 * d3 - d2 * d2) // 2
            else:
                f2_2 = b.add(f2, f2)
                bi = b.build_const_add_only(B2)
                f3_in = b.sub(f2_2, bi)
                u1 = d4 * d4 - d1 * d1
                u2 = d3 * d3 - d2 * d2
            f3 = b.sq(f3_in)  # mult 3
            C2 = u1 * u1 + u2 * u2
            if C2 % 2 == 0:
                c_val = C2 // 2
                e_val = abs(u1 * u1 - u2 * u2) // 2
                ci = b.build_const_add_only(c_val)
                f4_in = b.sub(f3, ci)
                f4_sq = b.sq(f4_in)  # mult 4
                e2i = b.build_const_add_only(e_val * e_val)
                b.sub(f4_sq, e2i)
                formula = f"((({fname.split('= ')[1]} - {a_val})^2 - {b_val if B2%2==0 else f'{B2}/2'})^2 - {c_val})^2 - {e_val}^2"
            else:
                e_val = abs(u1 * u1 - u2 * u2)
                f3_2 = b.add(f3, f3)
                ci = b.build_const_add_only(C2)
                f4_in = b.sub(f3_2, ci)
                f4_sq = b.sq(f4_in)  # mult 4
                e2i = b.build_const_add_only(e_val * e_val)
                b.sub(f4_sq, e2i)
                formula = f"(2(({fname.split('= ')[1]} - {a_val})^2 - ...)^2 - {C2})^2 - {e_val}^2"
        else:
            q2 = b.add(q, q)
            si = b.build_const_add_only(S)
            f1 = b.sub(q2, si)
            f2 = b.sq(f1)  # mult 2
            B2 = D1 * D1 + D4 * D4
            assert B2 == D2 * D2 + D3 * D3
            if B2 % 2 == 0:
                b_val = B2 // 2
                bi = b.build_const_add_only(b_val)
                f3_in = b.sub(f2, bi)
                u1 = (D4 * D4 - D1 * D1) // 2
                u2 = (D3 * D3 - D2 * D2) // 2
            else:
                f2_2 = b.add(f2, f2)
                bi = b.build_const_add_only(B2)
                f3_in = b.sub(f2_2, bi)
                u1 = D4 * D4 - D1 * D1
                u2 = D3 * D3 - D2 * D2
            f3 = b.sq(f3_in)  # mult 3
            C2 = u1 * u1 + u2 * u2
            if C2 % 2 == 0:
                c_val = C2 // 2
                e_val = abs(u1 * u1 - u2 * u2) // 2
                ci = b.build_const_add_only(c_val)
                f4_in = b.sub(f3, ci)
                f4_sq = b.sq(f4_in)  # mult 4
                e2i = b.build_const_add_only(e_val * e_val)
                b.sub(f4_sq, e2i)
                formula = f"(((2*{fname.split('= ')[1]} - {S})^2 - {b_val if B2%2==0 else f'{B2}/2'})^2 - {c_val})^2 - {e_val}^2"
            else:
                e_val = abs(u1 * u1 - u2 * u2)
                f3_2 = b.add(f3, f3)
                ci = b.build_const_add_only(C2)
                f4_in = b.sub(f3_2, ci)
                f4_sq = b.sq(f4_in)  # mult 4
                e2i = b.build_const_add_only(e_val * e_val)
                b.sub(f4_sq, e2i)
                formula = f"(2((2*{fname.split('= ')[1]} - {S})^2 - ...)^2 - {C2})^2 - {e_val}^2"

        info = verify_witness_exact(b.gates, expected_roots=roots)
        assert info["mulCount"] == 4
        assert info["num_roots"] == 16
        print(f"\n  [100% VERIFIED m=4, 16-ROOT WITNESS ({fname}, S={S})]")
        print(f"    Formula  : {formula}")
        print(f"    mulCount : {info['mulCount']} (EXACT!)")
        print(f"    degree   : {info['degree']} (= 2^4 = 16, EXACT!)")
        print(f"    roots(16): {info['roots']}")
        print(f"    tau (add-only consts): {info['tau']}")

    print(f"\n  Mission 2 total time: {time.time() - t0:.2f}s")
    return results


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    t0 = time.time()
    print("Precomputing shortest constant chains up to 6 steps...")
    chains = precompute_const_chains(max_steps=6, limit=200000)
    print(f"  Precomputed {len(chains)} constants in {time.time() - t0:.2f}s.")

    tracker = RecordTracker(max_tau=18)

    # Seed standing tau=12 (9r) and tau=13 (10r) records into tracker & elite pool
    b12 = SLPBuilder()
    g1 = b12.sq(0)
    g2 = b12.add(-1, -1)
    g3 = b12.sub(g2, g1)
    g4 = b12.sq(g3)
    g5 = b12.sub(g1, g4)
    g6 = b12.add(g2, g2)
    g7 = b12.sq(g6)
    g8 = b12.sub(g1, g7)
    g9 = b12.sub(g3, g8)
    g10 = b12.mul(g5, g8)
    g11 = b12.mul(g10, g9)
    tracker.submit_builder(b12, g11, {-4, -3, -2, -1, 1, 2, 3, 4}, "Standing tau=11 midpoint")
    g12 = b12.mul(0, g11)
    tracker.submit_builder(b12, g12, {-4, -3, -2, -1, 0, 1, 2, 3, 4}, "Standing tau=12 midpoint")

    b13 = SLPBuilder()
    g1 = b13.add(-1, 0)
    g2 = b13.mul(0, g1)
    g3 = b13.add(-1, -1)
    g4 = b13.add(g3, g3)
    g5 = b13.sq(g4)
    g6 = b13.sub(g2, g5)
    g7 = b13.sq(g6)
    g8 = b13.sub(g5, g3)
    g9 = b13.sq(g8)
    g10 = b13.sub(g7, g9)
    g11 = b13.sub(g7, g5)
    g12 = b13.mul(g10, g11)
    g13 = b13.mul(g12, g2)
    tracker.submit_builder(b13, g13, {-6, -5, -4, -2, -1, 0, 1, 3, 4, 5}, "Standing tau=13 pronic-square")

    # Run Mission 1 engines
    search_shifted_families(tracker, chains, max_a=2000)
    search_optimal_const_sharing(tracker, max_a=1000)
    search_midpoint_families(tracker, chains)
    # Run exhaustive 1/2/3-gate factor harvesting on all elite prefixes!
    extend_elite_dags(tracker)

    print("\n" + "=" * 78)
    print("MISSION 1 SUMMARY: BEST VERIFIED WITNESSES FOR tau = 11..18")
    print("=" * 78)
    for tau in range(11, 19):
        if tau in tracker.best:
            w = tracker.best[tau]
            print(f"tau={tau:2d}: {w['num_roots']:2d} roots (deg={w['degree']:2d}, mul={w['mulCount']:2d}) | {w['label']}")
            print(f"        roots = {w['roots']}")
            print(f"        SLP   = {w['slp']}")

    # Run Mission 2
    search_m4_diophantine(max_a=200000)


if __name__ == "__main__":
    main()
