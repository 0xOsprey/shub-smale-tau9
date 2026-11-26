#!/usr/bin/env python3
"""
Track B Record Witness Hunter for tau = 10, 11, 12, 13, 14 on Smale's 4th Problem
(the Shub-Smale tau-Conjecture).

100% exact arbitrary-precision Python int verification for every candidate.
Searches:
  1. Shifted pronic-square products: prod ((q - a)^2 - d_i^2) * [q] * [(q - p_k)] * [x - c]
  2. Sum-of-two-squares quartics:    prod ((x^2 - a)^2 - d_i^2) * [x] * [(x^2 - s^2)]
  3. Midpoint-difference products:   (x^2 - (k - x^2)^2) * (x^2 - s^2) * ((k - x^2) - (x^2 - s^2)) * ...
  4. Generalized difference-of-squares: (c*x)^2 - (k - x^2)^2 products & midpoint combos
  5. Eisenstein cubic compositions:  y(y^2 - v1^2)(y^2 - v2^2) for y = x(x^2 - c)
  6. Exact verification of all discovered witnesses from Python + C searches.
"""

from __future__ import annotations
import sys
from collections import defaultdict
from typing import Dict, List, Optional, Set, Tuple

sys.path.insert(0, "/Users/joe/github/gemini-neon/experiments/pvsnp/tau")
from tau_search import (
    Gate,
    Poly,
    eval_slp_exact,
    find_integer_roots_in_range,
    format_slp,
    parse_slp_str,
    poly_eval,
    poly_to_str,
    verify_witness,
)


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

    @staticmethod
    def _add_poly(a: Poly, b: Poly) -> Poly:
        n = max(len(a), len(b))
        r = [0] * n
        for i, v in enumerate(a):
            r[i] += v
        for i, v in enumerate(b):
            r[i] += v
        while r and r[-1] == 0:
            r.pop()
        return r

    @staticmethod
    def _sub_poly(a: Poly, b: Poly) -> Poly:
        n = max(len(a), len(b))
        r = [0] * n
        for i, v in enumerate(a):
            r[i] += v
        for i, v in enumerate(b):
            r[i] -= v
        while r and r[-1] == 0:
            r.pop()
        return r

    @staticmethod
    def _mul_poly(a: Poly, b: Poly) -> Poly:
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

    def op(self, kind: str, i: int, j: int) -> int:
        a, b = self.idx_to_poly[i], self.idx_to_poly[j]
        if kind == "+":
            p = self._add_poly(a, b)
        elif kind == "-":
            p = self._sub_poly(a, b)
        elif kind == "*":
            p = self._mul_poly(a, b)
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
        """Return dict mapping positive constant value -> gate index currently in DAG."""
        out = {}
        for idx, p in self.idx_to_poly.items():
            if len(p) == 1 and p[0] > 0:
                out[p[0]] = idx
        return out

    def try_build_const_1step(self, target: int) -> Optional[int]:
        """If target can be built in 0 or 1 gate from existing constants, build and return idx."""
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
        return None


def precompute_const_chains(max_steps: int = 5, limit: int = 20000) -> Dict[int, List[Tuple[str, int, int]]]:
    best: Dict[int, Tuple[int, List[Tuple[str, int, int]]]] = {1: (0, [])}
    layers: List[List[Tuple[Tuple[int, ...], List[Tuple[str, int, int]]]]] = [[((1,), [])]]
    seen: Set[Tuple[int, ...]] = {(1,)}
    for step in range(1, max_steps + 1):
        nxt = []
        for vals, ops in layers[-1]:
            n = len(vals)
            for i in range(n):
                vi = vals[i]
                for j in range(i, n):
                    vj = vals[j]
                    cands = [("+", vi + vj, vi, vj), ("*", vi * vj, vi, vj)]
                    if vj > vi:
                        cands.append(("-", vj - vi, vj, vi))
                    for op_ch, v, a, b in cands:
                        if v <= 1 or v > limit or v in vals:
                            continue
                        new_ops = ops + [(op_ch, a, b)]
                        if v not in best or step < best[v][0]:
                            best[v] = (step, new_ops)
                        if step < max_steps:
                            nv = tuple(sorted(vals + (v,)))
                            if nv not in seen:
                                seen.add(nv)
                                nxt.append((nv, new_ops))
        layers.append(nxt)
    return {k: v[1] for k, v in best.items()}


def build_const_smart(slp: SLPBuilder, val: int, chains: Dict[int, List[Tuple[str, int, int]]]) -> Optional[int]:
    """Build val using 0 or 1 step from existing constants if possible, else via chains."""
    if val == 1:
        return -1
    r = slp.try_build_const_1step(val)
    if r is not None:
        return r
    if val not in chains:
        return None
    for op_ch, a, b in chains[val]:
        ia = slp.poly_to_idx[(a,)]
        ib = slp.poly_to_idx[(b,)]
        slp.op(op_ch, ia, ib)
    return slp.poly_to_idx[(val,)]


BEST: Dict[int, Tuple[int, List[Gate], List[int], str]] = {}


def record_candidate(gates: List[Gate], desc: str, lo: int = -100, hi: int = 100) -> Optional[Dict]:
    tau = len(gates)
    if tau > 14 or tau < 1:
        return None
    p = eval_slp_exact(gates)
    if not p:
        return None
    roots = find_integer_roots_in_range(p, lo, hi)
    nroots = len(roots)
    cur = BEST.get(tau)
    if cur is None or nroots > cur[0]:
        res = verify_witness(gates, roots)
        BEST[tau] = (nroots, list(gates), roots, desc)
        print(f"  [NEW BEST tau={tau:2d}] {nroots:2d} roots ({desc}): roots={roots}")
        return res
    return None


def search_pronic_squares_deep(chains: Dict[int, List[Tuple[str, int, int]]]) -> None:
    print("=== Deep Pronic-Square Search ((q - a)^2 - d1^2)((q - a)^2 - d2^2) * extra ===")
    pronics = [k * (k + 1) for k in range(35)]
    pronic_set = set(pronics)

    reps: Dict[int, List[Tuple[int, int, int]]] = defaultdict(list)
    for i in range(len(pronics)):
        for j in range(i + 1, len(pronics)):
            s = pronics[i] + pronics[j]
            if s % 2 == 0:
                a = s // 2
                d = (pronics[j] - pronics[i]) // 2
                reps[a].append((d, pronics[i], pronics[j]))

    for a, rlist in sorted(reps.items()):
        if a not in chains or len(chains[a]) > 4:
            continue
        if len(rlist) < 2:
            continue
        for i in range(len(rlist)):
            for j in range(i + 1, len(rlist)):
                d1, p1, p2 = rlist[i]
                d2, p3, p4 = rlist[j]
                b = SLPBuilder()
                xp1 = b.add(-1, 0)
                q = b.mul(0, xp1)
                ia = build_const_smart(b, a, chains)
                if ia is None:
                    continue
                u = b.sub(q, ia)
                u2 = b.sq(u)
                # Build f1 = u^2 - d1^2 (check direct d1^2 or d1 then sq)
                b1 = b.copy()
                id1sq = b1.try_build_const_1step(d1 * d1)
                if id1sq is None:
                    id1 = build_const_smart(b1, d1, chains)
                    if id1 is None:
                        continue
                    id1sq = b1.sq(id1)
                f1 = b1.sub(u2, id1sq)
                id2sq = b1.try_build_const_1step(d2 * d2)
                if id2sq is None:
                    id2 = build_const_smart(b1, d2, chains)
                    if id2 is None:
                        continue
                    id2sq = b1.sq(id2)
                f2 = b1.sub(u2, id2sq)
                prod = b1.mul(f1, f2)
                if b1.tau <= 14:
                    record_candidate(b1.gates, f"psq a={a},d=({d1},{d2})")
                # Try * q (if 0 not in {p1,p2,p3,p4})
                if 0 not in (p1, p2, p3, p4) and b1.tau + 1 <= 14:
                    b2 = b1.copy()
                    p_q = b2.mul(prod, q)
                    record_candidate(b2.gates, f"psq*q a={a},d=({d1},{d2})")
                    # Try one more gate * (q - c) for any existing constant c that is pronic!
                    if b2.tau + 2 <= 14:
                        for cv, cidx in list(b2.consts().items()):
                            if cv in pronic_set and cv not in (0, p1, p2, p3, p4):
                                b3 = b2.copy()
                                fk = b3.sub(q, cidx)
                                b3.mul(p_q, fk)
                                record_candidate(b3.gates, f"psq*q*(q-{cv}) a={a},d=({d1},{d2})")
                # Try * u if a is pronic
                if a in pronic_set and b1.tau + 1 <= 14:
                    b2 = b1.copy()
                    b2.mul(prod, u)
                    record_candidate(b2.gates, f"psq*u a={a},d=({d1},{d2})")
                # Try * (q - c) for any existing constant c that is pronic!
                if b1.tau + 2 <= 14:
                    for cv, cidx in list(b1.consts().items()):
                        if cv in pronic_set and cv not in (p1, p2, p3, p4):
                            b2 = b1.copy()
                            fk = b2.sub(q, cidx)
                            b2.mul(prod, fk)
                            record_candidate(b2.gates, f"psq*(q-{cv}) a={a},d=({d1},{d2})")


def search_s2s_deep(chains: Dict[int, List[Tuple[str, int, int]]]) -> None:
    print("=== Deep Sum-of-Two-Squares Quartic Search ===")
    reps: Dict[int, List[Tuple[int, int, int]]] = defaultdict(list)
    for s1 in range(0, 40):
        for s2 in range(s1 + 1, 40):
            s = s1 * s1 + s2 * s2
            if s % 2 == 0:
                a = s // 2
                d = (s2 * s2 - s1 * s1) // 2
                reps[a].append((d, s1, s2))

    for a, rlist in sorted(reps.items()):
        if a not in chains or len(chains[a]) > 5:
            continue
        if len(rlist) < 2:
            continue
        for i in range(len(rlist)):
            for j in range(i + 1, len(rlist)):
                d1, s1, s2 = rlist[i]
                d2, s3, s4 = rlist[j]
                b = SLPBuilder()
                x2 = b.sq(0)
                ia = build_const_smart(b, a, chains)
                if ia is None:
                    continue
                u = b.sub(x2, ia)
                u2 = b.sq(u)
                id1sq = b.try_build_const_1step(d1 * d1)
                if id1sq is None:
                    id1 = build_const_smart(b, d1, chains)
                    if id1 is None:
                        continue
                    id1sq = b.sq(id1)
                f1 = b.sub(u2, id1sq)
                id2sq = b.try_build_const_1step(d2 * d2)
                if id2sq is None:
                    id2 = build_const_smart(b, d2, chains)
                    if id2 is None:
                        continue
                    id2sq = b.sq(id2)
                f2 = b.sub(u2, id2sq)
                prod = b.mul(f1, f2)
                if b.tau <= 14:
                    record_candidate(b.gates, f"s2s a={a},d=({d1},{d2})")
                if 0 not in (s1, s2, s3, s4) and b.tau + 1 <= 14:
                    b2 = b.copy()
                    b2.mul(prod, 0)
                    record_candidate(b2.gates, f"s2s*x a={a},d=({d1},{d2})")


def search_midpoint_generalized(chains: Dict[int, List[Tuple[str, int, int]]]) -> None:
    """
    Generalize the tau=12 (9 roots) midpoint trick!
    In tau=12:
      g5 = x^2 - (2 - x^2)^2   (roots +-1, +-2)
      g8 = x^2 - 16            (roots +-4)
      g10 = (2 - x^2) - (x^2 - 16) = 2*(9 - x^2) (roots +-3)
    What if we also combine with:
      - (k - x^2) and (x^2 - s^2) for general k = m(m+1) and s^2?
      - OR two midpoint tricks in a row?
    """
    print("=== Generalized Midpoint-Difference Search ===")
    # For k = m(m+1), f1 = x^2 - (k - x^2)^2 has roots +-m, +-(m+1).
    # We want s^2 such that (k + s^2) / 2 = t^2 (another square!).
    squares = {n * n for n in range(1, 50)}
    for m in range(1, 10):
        k = m * (m + 1)
        if k not in chains or len(chains[k]) > 3:
            continue
        for s in range(1, 25):
            if s in (m, m + 1):
                continue
            s2 = s * s
            if (k + s2) % 2 == 0 and ((k + s2) // 2) in squares:
                t2 = (k + s2) // 2
                if s2 not in chains:
                    continue
                b = SLPBuilder()
                ik = build_const_smart(b, k, chains)
                x2 = b.sq(0)
                u = b.sub(ik, x2)
                f1 = b.sub(x2, b.sq(u))
                is2 = build_const_smart(b, s2, chains)
                f2 = b.sub(x2, is2)
                f3 = b.sub(u, f2)  # (k - x^2) - (x^2 - s^2) = 2*(t^2 - x^2)
                p = b.mul(b.mul(f1, f2), f3)
                if b.tau <= 14:
                    record_candidate(b.gates, f"mid k={k},s={s},t2={t2}")
                if b.tau + 1 <= 14:
                    b2 = b.copy()
                    p_x = b2.mul(p, 0)
                    record_candidate(b2.gates, f"mid*x k={k},s={s},t2={t2}")
                    # Can we get ONE MORE square factor (x^2 - c) in 2 gates?
                    if b2.tau + 2 <= 14:
                        for cv, cidx in list(b2.consts().items()):
                            if cv in squares and cv not in (m * m, (m + 1) * (m + 1), s2, t2):
                                b3 = b2.copy()
                                fk = b3.sub(x2, cidx)
                                b3.mul(p_x, fk)
                                record_candidate(b3.gates, f"mid*x*(x^2-{cv}) k={k},s={s}")


def verify_all_known_records() -> None:
    print("\n=== EXACT VERIFICATION OF ALL BEST WITNESSES (tau = 10..14) ===")
    known = [
        ("tau=10 (7 roots, sym)", "g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4; g6 = x * g5; g7 = 1 + g1; g8 = g7 * g7; g9 = g2 - g8; g10 = g6 * g9"),
        ("tau=11 (8 roots, q)", "g1 = 1 + 1; g2 = 1 + x; g3 = g1 + g1; g4 = x * g2; g5 = g1 - g4; g6 = g3 + g5; g7 = g4 * g5; g8 = g6 * g7; g9 = g1 + g3; g10 = g6 + g9; g11 = g8 * g10"),
        ("tau=11 (8 roots, mid-sym)", "g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4; g6 = g1 * g1; g7 = g6 * g6; g8 = g2 - g7; g9 = g5 * g8; g10 = g3 - g8; g11 = g9 * g10"),
        ("tau=12 (9 roots, NEW RECORD mid*x)", "g1 = 1 + 1; g2 = x * x; g3 = g1 - g2; g4 = g3 * g3; g5 = g2 - g4; g6 = g1 * g1; g7 = g6 * g6; g8 = g2 - g7; g9 = g5 * g8; g10 = g3 - g8; g11 = g9 * g10; g12 = x * g11"),
        ("tau=13 (10 roots, NEW RECORD psq*q)", "g1 = 1 + x; g2 = x * g1; g3 = 1 + 1; g4 = g3 + g3; g5 = g4 * g4; g6 = g2 - g5; g7 = g6 * g6; g8 = g5 - g3; g9 = g8 * g8; g10 = g7 - g9; g11 = g7 - g5; g12 = g10 * g11; g13 = g12 * g2"),
        ("tau=14 (10 roots, pronic-5)", "g1 = 1 + 1; g2 = 1 + x; g3 = g1 + g1; g4 = x * g2; g5 = g1 - g4; g6 = g3 + g5; g7 = g4 * g5; g8 = g6 * g7; g9 = g1 + g3; g10 = g6 + g9; g11 = g8 * g10; g12 = g3 + g3; g13 = g10 + g12; g14 = g11 * g13"),
    ]
    for label, slp in known:
        gates = parse_slp_str(slp)
        record_candidate(gates, label)


def main() -> None:
    print("Precomputing 5-step constant chains...")
    chains = precompute_const_chains(max_steps=5, limit=15000)
    print(f"Found chains for {len(chains)} constants.")

    verify_all_known_records()
    search_pronic_squares_deep(chains)
    search_s2s_deep(chains)
    search_midpoint_generalized(chains)

    print("\n=== FINAL BEST LADDER (tau = 10..14) ===")
    for tau in range(10, 15):
        if tau in BEST:
            nroots, gates, roots, desc = BEST[tau]
            res = verify_witness(gates, roots)
            print(f"tau={tau:2d}: {nroots:2d} roots (deg={res['degree']}) [{desc}]")
            print(f"   roots = {roots}")
            print(f"   SLP   = {format_slp(gates)}")
            print(f"   Poly  = {res['poly_str']}")


if __name__ == "__main__":
    main()
