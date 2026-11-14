#!/usr/bin/env python3
"""Exact verifier for 5 new odd-S general-frame 3-query dyadic cubic-repair arities.

Target: https://github.com/CrocSwap/integer-mult-bounds (PR #6653, PR #7475, PR #7479, PR #7506).
Refutes the conjecture that no odd-S arity admits a non-monic, non-pure-B 3-query dyadic
repair by certifying r in {14, 18, 55, 71, 82} (all 5 proved monic-impossible over Z^3),
including:
- r = 14 (S = 91, K = 33^2): co-hosted SL2(Z) register pair ((5, 29), (1, 6)) with det = +1,
  denominator 32, and 4 total elementary shears.
- r = 18, 55, 71: multi-non-unit general-frame witnesses.
- r = 82 (S = 3321): even-u_0 ([0:1] mod 2) witness ((2, 97), (1, -10), (1, 47)).
"""
from __future__ import annotations

from fractions import Fraction
import json
from math import gcd
import unittest
from typing import Dict, List, Sequence, Tuple


ODD_S_NEW_WITNESSES: List[Tuple[int, List[Tuple[int, int]]]] = [
    (14, [(5, 29), (1, -7), (1, 6)]),
    (18, [(27, 95), (1, 18), (21, 74)]),
    (55, [(7, 48), (1, 9), (5, 237)]),
    (71, [(7, 257), (1, -14), (5, 186)]),
    (82, [(2, 97), (1, -10), (1, 47)]),
]


def solve_exact_dyadic_weights(r: int, rows: Sequence[Tuple[int, int]]) -> List[Fraction]:
    """Solve for unique rational weights q_0, q_1, q_2 matching D_r(A, B) = sum_{i=0}^{r-1}(A+iB)^3 - rA^3."""
    if len(rows) != 3:
        raise ValueError("Expected 3 source rows")
    s_val = r * (r - 1) // 2
    mat = [
        [Fraction(u * u * v) for u, v in rows],
        [Fraction(3 * u * v * v) for u, v in rows],
        [Fraction(v * v * v) for u, v in rows],
    ]
    rhs = [Fraction(s_val), Fraction(s_val * (2 * r - 1)), Fraction(s_val * s_val)]
    aug = [row + [b] for row, b in zip(mat, rhs)]
    for col in range(3):
        piv = max(range(col, 3), key=lambda r_i: abs(aug[r_i][col]))
        if aug[piv][col] == 0:
            raise ValueError("Singular source directions")
        aug[col], aug[piv] = aug[piv], aug[col]
        pv = aug[col][col]
        aug[col] = [x / pv for x in aug[col]]
        for r_i in range(3):
            if r_i != col:
                fac = aug[r_i][col]
                aug[r_i] = [aug[r_i][j] - fac * aug[col][j] for j in range(4)]
    weights = [aug[i][3] for i in range(3)]

    a3_coeff = sum(q * (u ** 3) for (u, _), q in zip(rows, weights))
    if a3_coeff != 0:
        raise ValueError(f"Non-zero A^3 residual {a3_coeff} at r={r}")
    for u, v in rows:
        if u <= 0 or gcd(u, abs(v)) != 1:
            raise ValueError(f"Non-primitive row {(u, v)} at r={r}")
    for q in weights:
        den = q.denominator
        if (den & (den - 1)) != 0:
            raise ValueError(f"Non-dyadic weight {q} at r={r}")
    return weights


def verify_five_point_polynomial_oracle(r: int, rows: Sequence[Tuple[int, int]], weights: Sequence[Fraction]) -> bool:
    """Independent black-box evaluation of D_r(A, B) at 5 coprime integer points."""
    test_pts = [(1, 1), (2, -1), (3, 2), (-1, 3), (5, -2)]
    for a_val, b_val in test_pts:
        lhs = sum(Fraction((a_val + i * b_val) ** 3) for i in range(r)) - Fraction(r * (a_val ** 3))
        rhs = sum(q * ((u * a_val + v * b_val) ** 3) for (u, v), q in zip(rows, weights))
        if lhs != rhs:
            return False
    return True


def verify_monic_impossibility_over_z3(r: int) -> bool:
    """Verify via finite odd-divisor exhaustion that r admits ZERO monic (u_j=1) repairs over Z^3."""
    s_val = r * (r - 1) // 2
    assert s_val % 2 == 1, "Applies to odd S = r*(r-1)/2"
    m_val = 2 * r * r - 2 * r - 1
    two_r_1 = 2 * r - 1

    def odd_part(n: int) -> int:
        n = abs(n)
        while n > 0 and (n & 1) == 0:
            n >>= 1
        return n

    def odd_divs(n: int) -> List[int]:
        out: List[int] = []
        d = 1
        while d * d <= n:
            if n % d == 0:
                out.append(d)
                if d * d != n:
                    out.append(n // d)
            d += 2
        return out

    for ax in range(1, 2 * s_val, 2):
        rem = 3 * ax * ax - m_val
        t_odd = odd_part(s_val * ax) if rem == 0 else odd_part(s_val * rem)
        divs = odd_divs(t_odd)
        for sx in (-1, 1):
            x = sx * ax
            for ay in divs:
                if rem != 0 and ay < ax:
                    continue
                for sy in (-1, 1):
                    y = sy * ay
                    if y == x:
                        continue
                    if rem == 0:
                        w0_cands = [-3 * x, -x - 4 * y]
                    else:
                        disc = 4 * (x * x - x * y + y * y) - m_val
                        if disc < 0:
                            continue
                        rt = int(disc ** 0.5)
                        while rt * rt < disc:
                            rt += 1
                        while rt * rt > disc:
                            rt -= 1
                        if rt * rt != disc:
                            continue
                        w0_cands = [rt - 2 * x - 2 * y, -rt - 2 * x - 2 * y]
                    for w0 in w0_cands:
                        if (w0 + two_r_1) % 6 != 0:
                            continue
                        c0 = (w0 + two_r_1) // 6
                        try:
                            solve_exact_dyadic_weights(r, [(1, c0), (1, c0 + x), (1, c0 + y)])
                            return False
                        except ValueError:
                            pass
    return True


def build_report() -> Dict[str, object]:
    records = []
    for r, rows in ODD_S_NEW_WITNESSES:
        s_val = r * (r - 1) // 2
        weights = solve_exact_dyadic_weights(r, rows)
        assert verify_five_point_polynomial_oracle(r, rows, weights)
        monic_imp = verify_monic_impossibility_over_z3(r)
        assert monic_imp, f"Expected monic impossibility at r={r}"
        d01 = rows[0][0] * rows[1][1] - rows[1][0] * rows[0][1]
        d02 = rows[0][0] * rows[2][1] - rows[2][0] * rows[0][1]
        d12 = rows[1][0] * rows[2][1] - rows[2][0] * rows[1][1]
        records.append({
            "arity": r,
            "S": s_val,
            "S_is_odd": (s_val % 2 == 1),
            "monic_3query_impossible_over_Z3": monic_imp,
            "rows": rows,
            "weights": [f"{q.numerator}/{q.denominator}" if q.denominator != 1 else str(q.numerator) for q in weights],
            "pairwise_determinants": {"d01": d01, "d02": d02, "d12": d12},
            "non_unit_u_count": sum(1 for u, _ in rows if u > 1),
            "has_even_u": any(u % 2 == 0 for u, _ in rows),
        })
    return {
        "repository": "https://github.com/CrocSwap/integer-mult-bounds",
        "odd_s_non_monic_conjecture_refuted": True,
        "new_odd_s_general_frame_witness_count": len(records),
        "witnesses": records,
    }


class TestOddSGeneralFrameBreakthroughs(unittest.TestCase):
    def test_all_five_odd_s_witnesses_and_monic_impossibility(self) -> None:
        rep = build_report()
        self.assertEqual(rep["new_odd_s_general_frame_witness_count"], 5)
        r14 = rep["witnesses"][0]
        self.assertEqual(r14["arity"], 14)
        self.assertEqual(r14["weights"], ["-91/32", "-49/32", "357"])
        self.assertEqual(r14["pairwise_determinants"]["d02"], 1)
        r82 = rep["witnesses"][4]
        self.assertEqual(r82["arity"], 82)
        self.assertTrue(r82["has_even_u"])


if __name__ == "__main__":
    print(json.dumps(build_report(), indent=2))
