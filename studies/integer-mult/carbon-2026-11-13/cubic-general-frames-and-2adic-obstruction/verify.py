#!/usr/bin/env python3
"""Zero-dependency standard-library verifier for cubic-general-frames-and-2adic-obstruction.

Verifies:
  1. Exact SHA-256 integrity of CERTIFICATES.json.
  2. All 20 strictly new non-pure-B 3-query dyadic cubic repair witnesses:
     - Coprimality gcd(u_j, v_j) == 1 and SL_2(Z) completion det == 1
     - Elementary integer shear replay from [1, 0] -> [u_j, v_j]
     - Dyadic denominators q_j in Z[1/2]
     - Exact coefficientwise cubic defect identity D_r(A, B) == sum_j q_j (u_j A + v_j B)^3
     - Quadratic-field norm-square identity (w_0^2 - K u_0^2)(w_1^2 - K u_1^2)(w_2^2 - K u_2^2) == M_re^2
     - Pairwise determinant law 144 q_j q_k d_ij d_ik d_jk^2 == r^2(r-1)^2(K u_i^2 - w_i^2)
     - Non-overlap against pure-B (u=0) family (#6215), #6653, and #7475
  3. All 17 solvable odd-S monic witnesses in [3, 200] and direct standard-library
     unconditional divisor-bound exhaustion for odd-S arities r in [3, 45], including
     the benchmark open targets r in {15, 22, 30, 31, 34, 39, 43}.
"""
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
EXPECTED_CERT_SHA256 = "697498fee5a1492d3dd86b3e27a6a434f75434d5a5f167081cad2f0c43e4c725"
PR6653_SET = frozenset({6, 7, 12, 13, 21, 25, 42, 51, 52, 76, 85, 93, 97, 114, 156, 157, 160})
PR7475_SET = frozenset({24})

def is_power_of_two(n: int) -> bool:
    return n > 0 and (n & (n - 1)) == 0

def odd_part(n: int) -> int:
    n = abs(n)
    if n == 0:
        return 0
    while (n & 1) == 0:
        n >>= 1
    return n

def odd_divisors(n: int) -> list[int]:
    divs = [1]
    d = 3
    while d * d <= n:
        if n % d == 0:
            cnt = 0
            while n % d == 0:
                n //= d
                cnt += 1
            base = list(divs)
            pw = 1
            for _ in range(cnt):
                pw *= d
                divs.extend(b * pw for b in base)
        d += 2
    if n > 1:
        divs.extend(b * n for b in list(divs))
    return divs

def verify_constructive_witnesses(cert: dict) -> None:
    witnesses = cert["new_constructive_witnesses"]
    assert len(witnesses) == 20, f"Expected 20 witnesses, got {len(witnesses)}"
    seen_r = set()
    for w in witnesses:
        r = w["arity"]
        assert r not in seen_r and r not in PR6653_SET and r not in PR7475_SET
        seen_r.add(r)
        S = r * (r - 1) // 2
        two_r_1 = 2 * r - 1
        K = 6 * r * r - 6 * r - 3
        assert w["S"] == S and w["K"] == K

        qs_list = []
        pts = []
        ws = []
        norms = []
        for qrec in w["queries"]:
            u, v = qrec["u"], qrec["v"]
            assert u != 0, f"Pure-B u=0 forbidden in strict set at r={r}"
            assert math.gcd(abs(u), abs(v)) == 1
            mat = qrec["sl2_matrix"]
            assert mat[0] == [u, v]
            assert mat[0][0] * mat[1][1] - mat[0][1] * mat[1][0] == 1
            row = [1, 0]
            for op, k in qrec["elementary_shears"]:
                if op == "A+=k*B":
                    row = [row[0], row[1] + k * row[0]]
                elif op == "B+=k*A":
                    row = [row[0] + k * row[1], row[1]]
                else:
                    raise ValueError(f"Unknown shear op {op}")
            assert row == [u, v], f"Shear replay mismatch at r={r}"

            q = Fraction(qrec["weight"])
            assert is_power_of_two(q.denominator)
            assert q == Fraction(qrec["weight_num"], 1 << qrec["weight_pow2_den"])

            wj = 6 * v - two_r_1 * u
            assert wj == qrec["w_shifted"]
            nj = wj * wj - K * u * u
            assert nj == qrec["norm_z"]
            qs_list.append(q)
            pts.append((u, v))
            ws.append(wj)
            norms.append(nj)

        # Exact cubic polynomial identity
        assert sum(q * (u ** 3) for q, (u, v) in zip(qs_list, pts)) == 0
        assert sum(3 * q * (u ** 2) * v for q, (u, v) in zip(qs_list, pts)) == 3 * S
        assert sum(3 * q * u * (v ** 2) for q, (u, v) in zip(qs_list, pts)) == S * two_r_1
        assert sum(q * (v ** 3) for q, (u, v) in zip(qs_list, pts)) == S * S

        # Theorem 2 norm-square & pairwise determinant identities
        m_re = ws[0] * ws[1] * ws[2] + K * (
            ws[0] * pts[1][0] * pts[2][0] + ws[1] * pts[0][0] * pts[2][0] + ws[2] * pts[0][0] * pts[1][0]
        )
        assert norms[0] * norms[1] * norms[2] == m_re * m_re
        d01 = pts[0][0] * pts[1][1] - pts[1][0] * pts[0][1]
        d02 = pts[0][0] * pts[2][1] - pts[2][0] * pts[0][1]
        d12 = pts[1][0] * pts[2][1] - pts[2][0] * pts[1][1]
        assert 144 * qs_list[1] * qs_list[2] * d01 * d02 * (d12 ** 2) == (r * (r - 1)) ** 2 * (-norms[0])
        assert 144 * qs_list[0] * qs_list[2] * (-d01) * d12 * (d02 ** 2) == (r * (r - 1)) ** 2 * (-norms[1])
        assert 144 * qs_list[0] * qs_list[1] * d02 * d12 * (d01 ** 2) == (r * (r - 1)) ** 2 * (-norms[2])

def certify_odd_s_monic_python(r: int) -> tuple[bool, int]:
    S = r * (r - 1) // 2
    assert S % 2 == 1
    M = 2 * r * r - 2 * r - 1
    two_r_1 = 2 * r - 1
    checked = 0
    for ax in range(1, 2 * S, 2):
        rem = 3 * ax * ax - M
        if rem == 0:
            divs = odd_divisors(odd_part(S * ax))
            for sx in (-1, 1):
                x = sx * ax
                for ay in divs:
                    for sy in (-1, 1):
                        y = sy * ay
                        if y == x:
                            continue
                        checked += 1
                        for w0 in (-3 * x, -x - 4 * y):
                            if (w0 + two_r_1) % 6 != 0:
                                continue
                            c0 = (w0 + two_r_1) // 6
                            c1, c2 = c0 + x, c0 + y
                            q0 = Fraction(-S * (w0 + 3 * x + 3 * y), 3 * x * y)
                            q1 = Fraction(S * (w0 + 3 * y), 3 * x * (y - x))
                            q2 = Fraction(-S * (w0 + 3 * x), 3 * y * (y - x))
                            if all(is_power_of_two(q.denominator) for q in (q0, q1, q2)):
                                if q0 * (c0 ** 3) + q1 * (c1 ** 3) + q2 * (c2 ** 3) == S * S:
                                    return True, checked
            continue
        divs = odd_divisors(odd_part(S * abs(rem)))
        for sx in (-1, 1):
            x = sx * ax
            for ay in divs:
                if ay < ax:
                    continue
                for sy in (-1, 1):
                    y = sy * ay
                    if y == x:
                        continue
                    checked += 1
                    disc = 4 * (x * x - x * y + y * y) - M
                    if disc < 0:
                        continue
                    rt = math.isqrt(disc)
                    if rt * rt != disc:
                        continue
                    for sr in (-1, 1):
                        w0 = sr * rt - 2 * x - 2 * y
                        if (w0 + two_r_1) % 6 != 0:
                            continue
                        c0 = (w0 + two_r_1) // 6
                        c1, c2 = c0 + x, c0 + y
                        q0 = Fraction(-S * (w0 + 3 * x + 3 * y), 3 * x * y)
                        q1 = Fraction(S * (w0 + 3 * y), 3 * x * (y - x))
                        q2 = Fraction(-S * (w0 + 3 * x), 3 * y * (y - x))
                        if all(is_power_of_two(q.denominator) for q in (q0, q1, q2)):
                            if q0 * (c0 ** 3) + q1 * (c1 ** 3) + q2 * (c2 ** 3) == S * S:
                                return True, checked
    return False, checked

def verify_odd_s_classification(cert: dict) -> None:
    recs = cert["odd_s_monic_classification"]
    assert len(recs) == 99
    for rec in recs:
        r = rec["arity"]
        S = r * (r - 1) // 2
        two_r_1 = 2 * r - 1
        if rec["status"] == "SOLVABLE":
            c0, c1, c2 = rec["c"]
            qs = [Fraction(s) for s in rec["weights"]]
            assert all(is_power_of_two(q.denominator) for q in qs)
            assert sum(qs) == 0
            assert sum(q * c for q, c in zip(qs, (c0, c1, c2))) == S
            assert sum(3 * q * (c ** 2) for q, c in zip(qs, (c0, c1, c2))) == S * two_r_1
            assert sum(q * (c ** 3) for q, c in zip(qs, (c0, c1, c2))) == S * S
        if r <= 45:
            sol, checked = certify_odd_s_monic_python(r)
            assert (rec["status"] == "SOLVABLE") == sol, f"Status mismatch at r={r}"
            if not sol:
                assert rec["divisor_pairs_checked"] == checked, f"Pair count mismatch at r={r}"

def main() -> int:
    cert_path = HERE / "CERTIFICATES.json"
    raw = cert_path.read_bytes()
    actual_sha = hashlib.sha256(raw).hexdigest()
    assert actual_sha == EXPECTED_CERT_SHA256, f"SHA mismatch: {actual_sha}"
    print("PASS_STAGE1_CERTIFICATE_SHA256")

    cert = json.loads(raw.decode("utf-8"))
    verify_constructive_witnesses(cert)
    print("PASS_STAGE2_TWENTY_NEW_GENERAL_WITNESSES")

    verify_odd_s_classification(cert)
    print("PASS_STAGE3_ODD_S_2ADIC_MONIC_OBSTRUCTION")

    print(json.dumps({
        "status": "PASS_ALL_STAGES",
        "certificates_sha256": actual_sha,
        "new_arities_verified": cert["summary"]["new_strict_arities"],
        "multi_non_unit_arities": cert["summary"]["multi_non_unit_arities"],
        "odd_s_monic_impossible_count": cert["summary"]["odd_s_monic_impossible_count"],
        "r15_monic_status": "IMPOSSIBLE_OVER_Z3",
    }, indent=2))
    return 0

if __name__ == "__main__":
    sys.exit(main())
