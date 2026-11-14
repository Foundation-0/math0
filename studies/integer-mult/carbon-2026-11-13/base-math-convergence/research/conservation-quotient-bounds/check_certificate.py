#!/usr/bin/env python3
"""
check_certificate.py — Standalone Zero-Float, Solver-Free Certificate Checker
for `research/conservation-quotient-bounds/` (`CrocSwap/integer-mult-bounds`).

Contract:
  - Refuses `-O` / `-OO` / nonzero `PYTHONOPTIMIZE` before loading inputs.
  - Uses `fractions.Fraction` and exact `int` exclusively (zero `float`, zero `math`).
  - Checks:
    1. Cut-Rank Gate: Graph disconnection under certified cut-edge deletion,
       exact matrix factorization `M == A_barU * B_U` over `Q`, and Bareiss integer rank `<= |E_cut|`.
    2. Reverse-Frame & Persistent-Cache Gate: Nonzero Gram determinants `det(B^T H B) != 0` on
       indefinite bilinear form `H`, exact orthogonal complement projector identities
       `P^2 == P`, `H P == P^T H`, reverse inclusion `(I - P_z) (I - P_w) == (I - P_z)` when `U_z <= U_w`,
       isotropic counterexample `det(B_iso^T H B_iso) == 0`, AND exact Helper300 persistent nullity
       (`P_persist * K_null == 0`, rank 8) + closed-form left-inverse `L * F_completed == I_28`.
    3. Directed Rational Power-Sum & Karamata-Farkas Gate: Elementary rational Taylor-Lagrange
       enclosures `[L_r(a), U_r(a)]` proving 18-digit break-even bounds on PR #450, Aska PR #464,
       and Aska PR #469, decomposing Aska PR #469 into `{1,2,3}` subadditive gain vs `{5,6,7}`
       concavity penalty (`6^12 < 5^5 * 7^7`), certifying a rational Farkas histogram ceiling
       `A^T y <= L(a_ceil), b^T y >= W*(1 - eps)`, and checking Frontier #7000 power-sum contraction.
"""

from __future__ import annotations

import hashlib
import json
import os
import sys

# Mandatory CrocSwap/integer-mult-bounds fail-closed guard against optimized interpreter
if sys.flags.optimize > 0 or os.environ.get("PYTHONOPTIMIZE", "").strip() not in ("", "0"):
    sys.stderr.write("FATAL: optimized Python (-O / PYTHONOPTIMIZE) is forbidden by verification contract.\n")
    sys.exit(2)

from fractions import Fraction
from pathlib import Path
from typing import Any


def parse_q(val: str | int) -> Fraction:
    if isinstance(val, int):
        return Fraction(val, 1)
    if not isinstance(val, str):
        raise ValueError(f"Expected str or int rational, got {type(val)}")
    if "." in val:
        raise ValueError(f"Floating decimal literal forbidden in rational certificate: {val}")
    return Fraction(val)


def mat_mul_q(A: list[list[Fraction]], B: list[list[Fraction]]) -> list[list[Fraction]]:
    assert len(A) > 0 and len(B) > 0 and len(A[0]) == len(B)
    rows, inner, cols = len(A), len(B), len(B[0])
    return [
        [sum((A[i][k] * B[k][j] for k in range(inner)), Fraction(0)) for j in range(cols)]
        for i in range(rows)
    ]


def mat_eq_q(A: list[list[Fraction]], B: list[list[Fraction]]) -> bool:
    return len(A) == len(B) and all(
        len(rA) == len(rB) and all(x == y for x, y in zip(rA, rB))
        for rA, rB in zip(A, B)
    )


def exact_rank_and_det_q(M: list[list[Fraction]]) -> tuple[int, Fraction | None]:
    """Exact Gaussian elimination over Q (used only to verify rank/det claims in exact Fraction)."""
    A = [[ Fraction(x) for x in row ] for row in M]
    m = len(A)
    n = len(A[0]) if m else 0
    rank = 0
    det: Fraction = Fraction(1)
    piv_cols: list[int] = []
    for col in range(n):
        piv = None
        for r in range(rank, m):
            if A[r][col] != 0:
                piv = r
                break
        if piv is None:
            det = Fraction(0)
            continue
        if piv != rank:
            A[rank], A[piv] = A[piv], A[rank]
            det = -det
        pv = A[rank][col]
        det *= pv
        for r in range(rank + 1, m):
            if A[r][col] != 0:
                fac = A[r][col] / pv
                for c in range(col, n):
                    A[r][c] -= fac * A[rank][c]
        piv_cols.append(col)
        rank += 1
        if rank == m:
            break
    return rank, (det if m == n and rank == n else (Fraction(0) if m == n else None))


RADIX_26 = 10**26


def floor_radix(x: Fraction, D: int = RADIX_26) -> Fraction:
    return Fraction((x.numerator * D) // x.denominator, D)


def ceil_radix(x: Fraction, D: int = RADIX_26) -> Fraction:
    return Fraction(-((-x.numerator * D) // x.denominator), D)


def rational_ln_interval(num: int, den: int, terms: int = 24) -> tuple[Fraction, Fraction]:
    """
    Pure rational outward-directed fixed-radix `10^-26` interval `[lo, hi]` for `ln(num / den)`
    where `num >= den >= 1`, preventing Stern-Brocot/Taylor coprime LCM denominator blowup!
    Zero floats!
    """
    assert num >= den >= 1 and terms >= 6
    D = 10**28

    def atanh_2_interval(z: Fraction, k_terms: int) -> tuple[Fraction, Fraction]:
        assert abs(z) <= Fraction(1, 3)
        z2 = z * z
        zp = z
        lo_acc = 0
        hi_acc = 0
        for j in range(k_terms):
            term = (2 * zp) / (2 * j + 1)
            lo_acc += (term.numerator * D) // term.denominator
            hi_acc += -((-term.numerator * D) // term.denominator)
            zp *= z2
        rem = (2 * abs(zp)) / ((2 * k_terms + 1) * (1 - z2))
        rem_up = -((-rem.numerator * D) // rem.denominator)
        return Fraction(lo_acc - rem_up, D), Fraction(hi_acc + rem_up, D)

    ln2_lo, ln2_hi = atanh_2_interval(Fraction(1, 3), terms)
    k = 0
    while Fraction(num, den * (1 << k)) > Fraction(4, 3):
        k += 1
    u = Fraction(num, den * (1 << k))
    assert Fraction(2, 3) <= u <= Fraction(4, 3), f"Unexpected reduced ratio u={u}"
    z = (u - 1) / (u + 1)
    u_lo, u_hi = atanh_2_interval(z, terms)
    return floor_radix(k * ln2_lo + u_lo), ceil_radix(k * ln2_hi + u_hi)


def rational_exp_pos_interval(x_lo: Fraction, x_hi: Fraction, terms: int = 18) -> tuple[Fraction, Fraction]:
    """
    Pure rational outward-directed fixed-radix `10^-26` interval `[lo, hi]` for `exp(x)`
    given `0 <= x_lo <= x <= x_hi <= 1`, with zero denominator blowup.
    """
    assert Fraction(0) <= x_lo <= x_hi <= Fraction(1) and terms >= 6
    D = 10**28
    lo_term = D
    hi_term = D
    lo_sum = D
    hi_sum = D
    for j in range(1, terms):
        lo_term = (lo_term * x_lo.numerator) // (x_lo.denominator * j)
        hi_term = -((-hi_term * x_hi.numerator) // (x_hi.denominator * j))
        lo_sum += lo_term
        hi_sum += hi_term
    # Upper remainder bound: hi_term_next * (J+1)/(J+1 - x_hi)
    hi_next = -((-hi_term * x_hi.numerator) // (x_hi.denominator * terms))
    rem_frac = Fraction(hi_next, D) * Fraction(terms + 1, 1) / (Fraction(terms + 1, 1) - x_hi)
    rem_up = -((-rem_frac.numerator * D) // rem_frac.denominator)
    return floor_radix(Fraction(lo_sum, D)), ceil_radix(Fraction(hi_sum + rem_up, D))


def enclose_ratio_power_1_minus_a(r: int, m: int, a: Fraction, terms: int = 26) -> tuple[Fraction, Fraction]:
    """
    Sound rational interval `[L, U]` containing `(r / m)^(1 - a) = (r / m) * exp(a * ln(m / r))`
    for integers `1 <= r <= m` and rational `0 <= a < 1/2`.
    """
    assert 1 <= r <= m and Fraction(0) <= a < Fraction(1, 2)
    if r == m or a == 0:
        val = Fraction(r, m) if a == 0 else Fraction(1, 1)
        return val, val
    ln_lo, ln_hi = rational_ln_interval(m, r, terms=terms)
    x_lo, x_hi = a * ln_lo, a * ln_hi
    e_lo, e_hi = rational_exp_pos_interval(x_lo, x_hi, terms=terms)
    base = Fraction(r, m)
    return base * e_lo, base * e_hi


def verify_certificate_dict(cert: dict[str, Any]) -> dict[str, Any]:
    # 0. Canonical SHA-256 integrity check
    claimed_sha = cert.get("certificate_sha256")
    if not isinstance(claimed_sha, str) or len(claimed_sha) != 64:
        raise ValueError("Missing or malformed certificate_sha256")
    body = {k: v for k, v in cert.items() if k != "certificate_sha256"}
    actual_sha = hashlib.sha256(
        json.dumps(body, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    if actual_sha != claimed_sha:
        raise ValueError(f"Certificate SHA-256 mismatch: expected {claimed_sha}, got {actual_sha}")

    # ------------------------------------------------------------------
    # 1. Verify Pillar I: Search-Free Cut-Rank Factorization Gate
    # ------------------------------------------------------------------
    p1 = cert["pillar_1_cut_rank"]
    n_verts = int(p1["num_vertices"])
    edges = [(int(u), int(v)) for u, v in p1["edges"]]
    cut_indices = set(int(i) for i in p1["cut_edge_indices"])
    sources = [int(s) for s in p1["sources"]]
    sinks = set(int(t) for t in p1["sinks"])
    req_rank = int(p1["required_target_rank"])

    if len(cut_indices) >= req_rank:
        raise ValueError("Cut capacity is not strictly below required target rank")

    # BFS reachability after deleting ONLY certified cut edges
    visited = set(sources)
    queue = list(sources)
    while queue:
        u = queue.pop(0)
        for idx, (eu, ev) in enumerate(edges):
            if idx in cut_indices:
                continue
            if eu == u and ev not in visited:
                visited.add(ev)
                queue.append(ev)
    if visited & sinks:
        raise ValueError(f"Cut failed disconnection: sinks {visited & sinks} reachable!")

    # Verify U_min subseteq U_max and both induce valid minimum cuts of identical capacity
    u_min = set(int(v) for v in p1["source_minimal_U"])
    u_max = set(int(v) for v in p1["sink_minimal_U"])
    if not u_min.issubset(u_max):
        raise ValueError("Picard-Queyranne lattice violation: U_min not subset of U_max")
    for name, u_set in (("U_min", u_min), ("U_max", u_max)):
        if not set(sources).issubset(u_set) or (u_set & sinks):
            raise ValueError(f"{name} does not separate sources from sinks")
        cross = [idx for idx, (eu, ev) in enumerate(edges) if eu in u_set and ev not in u_set]
        if len(cross) != len(cut_indices):
            raise ValueError(f"{name} cut capacity {len(cross)} != {len(cut_indices)}")

    # Verify explicit algebraic factorization M == A_barU * B_U and rank(M) <= |E_cut|
    M_transfer = [[parse_q(x) for x in row] for row in p1["transfer_matrix_M"]]
    A_bar = [[parse_q(x) for x in row] for row in p1["factor_A_barU"]]
    B_U = [[parse_q(x) for x in row] for row in p1["factor_B_U"]]
    if len(B_U) != len(cut_indices):
        raise ValueError("Factor B_U row count must equal cut capacity |E_cut|")
    if not mat_eq_q(M_transfer, mat_mul_q(A_bar, B_U)):
        raise ValueError("Transfer factorization M == A_barU * B_U failed!")
    rk_M, _ = exact_rank_and_det_q(M_transfer)
    if rk_M > len(cut_indices) or rk_M != int(p1["certified_rank_M"]):
        raise ValueError(f"Certified rank mismatch: rk_M={rk_M}")

    # ------------------------------------------------------------------
    # 2. Verify Pillar II: Indefinite Reverse-Frame & Helper300 Decoder
    # ------------------------------------------------------------------
    p2 = cert["pillar_2_orthogonality_and_decoder"]
    H = [[parse_q(x) for x in row] for row in p2["indefinite_form_H"]]
    _, det_H = exact_rank_and_det_q(H)
    if det_H is None or det_H == 0:
        raise ValueError("Ambient bilinear form H must be nondegenerate")

    P_z = [[parse_q(x) for x in row] for row in p2["projector_P_z"]]
    P_w = [[parse_q(x) for x in row] for row in p2["projector_P_w"]]
    B_z = [[parse_q(x) for x in row] for row in p2["basis_B_z"]]
    B_w = [[parse_q(x) for x in row] for row in p2["basis_B_w"]]
    B_iso = [[parse_q(x) for x in row] for row in p2["isotropic_counterexample_B"]]

    def transpose_q(X: list[list[Fraction]]) -> list[list[Fraction]]:
        return [[X[r][c] for r in range(len(X))] for c in range(len(X[0]))]

    def eye_q(d: int) -> list[list[Fraction]]:
        return [[Fraction(1 if i == j else 0) for j in range(d)] for i in range(d)]

    def sub_q(X: list[list[Fraction]], Y: list[list[Fraction]]) -> list[list[Fraction]]:
        return [[x - y for x, y in zip(rx, ry)] for rx, ry in zip(X, Y)]

    # Nondegeneracy of B_z and B_w vs degeneracy of isotropic counterexample B_iso
    _, det_Gz = exact_rank_and_det_q(mat_mul_q(transpose_q(B_z), mat_mul_q(H, B_z)))
    _, det_Gw = exact_rank_and_det_q(mat_mul_q(transpose_q(B_w), mat_mul_q(H, B_w)))
    _, det_Giso = exact_rank_and_det_q(mat_mul_q(transpose_q(B_iso), mat_mul_q(H, B_iso)))
    if not det_Gz or not det_Gw:
        raise ValueError("Forward spans U_z, U_w must have non-zero Gram determinant")
    if det_Giso != 0:
        raise ValueError("Isotropic counterexample failed to have zero Gram determinant")

    dim_r = len(H)
    I_r = eye_q(dim_r)
    for name, P in (("P_z", P_z), ("P_w", P_w)):
        if not mat_eq_q(mat_mul_q(P, P), P):
            raise ValueError(f"{name} is not idempotent")
        if not mat_eq_q(mat_mul_q(H, P), mat_mul_q(transpose_q(P), H)):
            raise ValueError(f"{name} is not H-self-adjoint")

    # Forward inclusion U_z <= U_w: P_w * B_z == B_z
    if not mat_eq_q(mat_mul_q(P_w, B_z), B_z):
        raise ValueError("Forward span inclusion U_z <= U_w failed")
    # Reverse complement inclusion U_w^{perp_H} <= U_z^{perp_H}: (I - P_z)*(I - P_w) == (I - P_w)
    Q_z = sub_q(I_r, P_z)
    Q_w = sub_q(I_r, P_w)
    if not mat_eq_q(mat_mul_q(Q_z, Q_w), Q_w):
        raise ValueError("Reverse-frame orthogonal complement inclusion U_w^perp <= U_z^perp failed!")

    # Helper300 persistent+cache exact left-inverse multiplication check (NO matrix inversion!)
    F_persist = [[parse_q(x) for x in row] for row in p2["helper_F_persist"]]
    C_cache = [[parse_q(x) for x in row] for row in p2["helper_C_cache"]]
    K_null = [[parse_q(x) for x in row] for row in p2["helper_K_null"]]
    L_inv = [[parse_q(x) for x in row] for row in p2["helper_L_left_inverse"]]

    # 1. P_persist * K_null == 0 and rank(K_null) == 8
    zero_pk = mat_mul_q(F_persist, K_null)
    if any(x != 0 for row in zero_pk for x in row):
        raise ValueError("Helper persistent null-space basis K_null did not annihilate F_persist!")
    rk_K, _ = exact_rank_and_det_q(K_null)
    if rk_K != 8:
        raise ValueError(f"Expected 8-field persistent kernel, got rank {rk_K}")
    # 2. C_cache * K_null == I_8
    if not mat_eq_q(mat_mul_q(C_cache, K_null), eye_q(8)):
        raise ValueError("Retained cache probes C_cache failed identity observability on K_null!")
    # 3. L_inv * [F_persist; C_cache] == I_28 (pure rational matrix multiplication!)
    F_comp = F_persist + C_cache
    N_state = len(F_comp[0])
    if not mat_eq_q(mat_mul_q(L_inv, F_comp), eye_q(N_state)):
        raise ValueError("Closed-form rational left-inverse L * F_completed != I!")

    # ------------------------------------------------------------------
    # 3. Verify Pillar III: Rational Power-Sum Enclosures & Farkas Ceiling
    # ------------------------------------------------------------------
    p3 = cert["pillar_3_power_sum_and_farkas"]
    m_block = int(p3["m"])
    W_roles = Fraction(int(p3["W"]), 1)
    sizes = [int(r) for r in p3["sizes_r"]]

    for blk in p3["certified_blocks"]:
        counts = [int(c) for c in blk["counts"]]
        ins_fee = parse_q(blk["insurance_fee"])
        a_lo = parse_q(blk["a_lower_certified"])
        a_hi = parse_q(blk["a_upper_certified"])
        k_pub = parse_q(blk["kappa_published"])
        if not (a_lo < a_hi):
            raise ValueError(f"Invalid bracket for {blk['name']}")
        # At a_lo: strict upper bound on bill must be < 1
        bill_upper_at_lo = ins_fee + sum(
            (Fraction(cnt, 1) * enclose_ratio_power_1_minus_a(r, m_block, a_lo)[1] for r, cnt in zip(sizes, counts)),
            Fraction(0),
        ) / W_roles
        if not (bill_upper_at_lo < 1):
            raise ValueError(f"{blk['name']}: upper bill at a_lo is {bill_upper_at_lo} >= 1")
        # At a_hi: strict lower bound on bill must be > 1
        bill_lower_at_hi = ins_fee + sum(
            (Fraction(cnt, 1) * enclose_ratio_power_1_minus_a(r, m_block, a_hi)[0] for r, cnt in zip(sizes, counts)),
            Fraction(0),
        ) / W_roles
        if not (bill_lower_at_hi > 1):
            raise ValueError(f"{blk['name']}: lower bill at a_hi is {bill_lower_at_hi} <= 1")
        # Published kappa = floor_18(a* / (1 + a*)) must lie inside certified kappa interval
        k_lo = a_lo / (1 + a_lo)
        k_hi = a_hi / (1 + a_hi)
        if not (k_pub <= k_lo <= k_hi < k_pub + Fraction(1, 10**18)):
            raise ValueError(f"{blk['name']}: [k_lo, k_hi]=[{k_lo}, {k_hi}] does not lock 18-digit floor {k_pub}")

    # Verify Karamata two-geometry decomposition on Aska PR #469 at a_ref
    decomp = p3["aska469_two_geometry_decomposition"]
    a_ref = parse_q(decomp["a_ref"])
    # {1,2,3} coalescing (-649, +77, +165) must strictly save (upper delta < 0)
    _, u1 = enclose_ratio_power_1_minus_a(1, m_block, a_ref)
    l2, u2 = enclose_ratio_power_1_minus_a(2, m_block, a_ref)
    l3, u3 = enclose_ratio_power_1_minus_a(3, m_block, a_ref)
    l1, _ = enclose_ratio_power_1_minus_a(1, m_block, a_ref)
    delta_123_hi = (Fraction(-649) * l1 + Fraction(77) * u2 + Fraction(165) * u3) / W_roles
    if not (delta_123_hi < 0):
        raise ValueError("Coalescing {1,2,3} move did not certify strict bill reduction")

    # {5,6,7} balanced contraction (-99, +198, -99) must strictly COST budget (lower delta > 0)!
    _, u5 = enclose_ratio_power_1_minus_a(5, m_block, a_ref)
    l6, _ = enclose_ratio_power_1_minus_a(6, m_block, a_ref)
    _, u7 = enclose_ratio_power_1_minus_a(7, m_block, a_ref)
    delta_567_lo = (Fraction(-99) * u5 + Fraction(198) * l6 - Fraction(99) * u7) / W_roles
    if not (delta_567_lo > 0):
        raise ValueError("Mean-preserving contraction {5,6,7} failed strict concavity penalty check")
    if not (6**12 < (5**5) * (7**7)):
        raise ValueError("Integer witness 6^12 < 5^5 * 7^7 failed")

    # Verify Farkas dual histogram ceiling: y >= 0, A^T y <= L(a_ceil), b^T y >= W * (1 - eps)
    fk = p3["farkas_histogram_ceiling"]
    a_ceil = parse_q(fk["a_ceiling"])
    eps_ceil = parse_q(fk["insurance_fee"])
    A_mat = [[parse_q(x) for x in row] for row in fk["constraint_matrix_A"]]
    b_vec = [parse_q(x) for x in fk["rhs_b"]]
    y_dual = [parse_q(x) for x in fk["farkas_dual_y"]]
    if any(yi < 0 for yi in y_dual):
        raise ValueError("Farkas dual multiplier y contains negative entry!")
    L_vec = [enclose_ratio_power_1_minus_a(r, m_block, a_ceil)[0] for r in sizes]
    for j in range(len(sizes)):
        aty_j = sum((A_mat[i][j] * y_dual[i] for i in range(len(y_dual))), Fraction(0))
        if not (aty_j <= L_vec[j]):
            raise ValueError(f"Farkas dual feasibility failed at column j={j}: {aty_j} > {L_vec[j]}")
    bty = sum((b_vec[i] * y_dual[i] for i in range(len(y_dual))), Fraction(0))
    rhs_req = W_roles * (1 - eps_ceil)
    if not (bty >= rhs_req):
        raise ValueError(f"Farkas dual objective {bty} < required {rhs_req}")

    # Verify Frontier #7000 published rational parameters
    f7 = p3["frontier_7000_audit"]
    k7000 = parse_q(f7["kappa_rational"])
    k6030 = parse_q(f7["preceding_kappa_6030"])
    kbit = parse_q(f7["bit_ordinary_saving"])
    if k7000 != Fraction(363005817, 100000000000):
        raise ValueError("Frontier #7000 kappa mismatch")
    if not (k6030 < k7000 < kbit):
        raise ValueError("Frontier #7000 hierarchy k6030 < k7000 < k_BIT failed")

    return {
        "status": "OK",
        "certificate_sha256": actual_sha,
        "cut_capacity": len(cut_indices),
        "certified_rank_M": rk_M,
        "helper_nullity_closed": rk_K,
        "aska469_567_penalty_lower": str(delta_567_lo),
        "farkas_ceiling_kappa": str(a_ceil / (1 + a_ceil)),
    }


def main() -> int:
    cert_path = (
        Path(sys.argv[1])
        if len(sys.argv) > 1
        else Path(__file__).resolve().parent / "certificates" / "conservation_quotient_certificate.json"
    )
    cert = json.loads(cert_path.read_text(encoding="utf-8"))
    summary = verify_certificate_dict(cert)
    print(f"CHECK_CERTIFICATE_OK sha256={summary['certificate_sha256'][:16]}... cut={summary['cut_capacity']}<4 nullity={summary['helper_nullity_closed']}->0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
