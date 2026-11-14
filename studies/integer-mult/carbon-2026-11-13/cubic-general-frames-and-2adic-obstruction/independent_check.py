#!/usr/bin/env python3
"""Independent evaluation-grid & 2x2 integer matrix oracle for cubic repair certificates.

Unlike verify.py (which expands symbolic coefficients), this oracle evaluates the
eager vs. deferred stream update y += a^3; a += b directly on 5 independent integer
input pairs (A, B) in {(1,0), (0,1), (1,1), (2,-1), (-3,2)} (spanning Sym^3(Q^2))
and multiplies 2x2 elementary shear matrices over Z.
"""
from fractions import Fraction
import json
from pathlib import Path
import sys

TEST_INPUTS = [(1, 0), (0, 1), (1, 1), (2, -1), (-3, 2)]

def mat_mul_right_row(row, op, k):
    # row * [[1, k], [0, 1]] or row * [[1, 0], [k, 1]]
    if op == "A+=k*B":
        return [row[0], row[1] + k * row[0]]
    if op == "B+=k*A":
        return [row[0] + k * row[1], row[1]]
    raise ValueError(op)

def deferred_defect(r: int, A: int, B: int) -> int:
    return sum((A + i * B) ** 3 for i in range(r)) - r * (A ** 3)

def main() -> int:
    cert = json.loads((Path(__file__).resolve().parent / "CERTIFICATES.json").read_text(encoding="utf-8"))
    for w in cert["new_constructive_witnesses"]:
        r = w["arity"]
        for A, B in TEST_INPUTS:
            lhs = Fraction(0)
            for qrec in w["queries"]:
                row = [1, 0]
                for op, k in qrec["elementary_shears"]:
                    row = mat_mul_right_row(row, op, k)
                val = row[0] * A + row[1] * B
                q = Fraction(qrec["weight_num"], 1 << qrec["weight_pow2_den"])
                lhs += q * (val ** 3)
            rhs = Fraction(deferred_defect(r, A, B))
            assert lhs == rhs, f"Oracle evaluation mismatch at r={r}, (A,B)=({A},{B}): {lhs} != {rhs}"

    # Verify mod-8 congruence impossibility in Theorem 3 directly across all residues mod 8:
    for r_mod in range(8):
        if ((r_mod * (r_mod - 1)) // 2) % 2 == 1:
            K_mod8 = (6 * r_mod * r_mod - 6 * r_mod - 3) % 8
            neg_K_mod8 = (-K_mod8) % 8
            assert neg_K_mod8 == 7, f"Expected -K == 7 (mod 8), got {neg_K_mod8}"
            for w0 in (1, 3, 5, 7):
                for w1 in (1, 3, 5, 7):
                    for w2 in (1, 3, 5, 7):
                        if w0 % 4 == w1 % 4 == w2 % 4:
                            e2_mod8 = (w0 * w1 + w1 * w2 + w2 * w0) % 8
                            assert e2_mod8 == 3 and e2_mod8 != neg_K_mod8

    print("PASS_INDEPENDENT_EVALUATION_AND_MOD8_ORACLE")
    return 0

if __name__ == "__main__":
    sys.exit(main())
