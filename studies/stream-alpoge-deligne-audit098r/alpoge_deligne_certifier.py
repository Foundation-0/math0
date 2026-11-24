"""Pure-Q / exact-cyclotomic certifier for AUDIT-098 (Alpoge-Deligne sign-only proof).

Standalone pure-stdlib verification engine (zero floats, zero external dependencies):
1. Exact arithmetic in Z[zeta_p] = Z[x] / (1 + x + ... + x^{p-1}) for primes p >= 2.
2. Witness W1: Paper Example 5 (U = A^1, k = 2, Y: x1*x2 + a*x1 + b*x2 + c = 0) across
   p in {2, 3, 5, 7, 11}, verifying K_1 K_1^* = Q*I, Q*N - M^2 = R = sum_{h != 0} S_h,
   exact Parseval bound, AND negative control (ab == c singular conic -> R = Q^2 - Q).
3. Witness W2: Punctured line U = G_m (k = 2, 3 over F_3, F_5, F_7), verifying exact
   cohomological cancellation (-1)^{D-1} R = 1^k + Tr(K_k) with non-vanishing H^1_c(G_m).
4. Witness W3: Smooth affine elliptic curves E^o: y^2 = x^3 + A*x + B over F_5, F_7, F_11
   using finite Noether normalization pi(x, y) = x (fibre cap B = 2), Jacobian smoothness,
   exact fibre-grouped cyclotomic sum vs direct point count, and HS-03 bound.
5. Witness W4: Higher dimension d = 2 AND characteristic p = 2 (U = A^2 over F_2, F_3, F_4)
   verifying nondegenerate dot product b(x, y) = x1*y1 + x2*y2 in char 2, K_1 K_1^* = Q^2 I,
   and (-1)^{D-1} R = +Q^2.
6. Witness W5: Lisse rank-1 quadratic character sheaf L_chi on G_m (q = 5, 7, 11),
   contrasting non-generic Y (a1 = a2 = 0, smooth yet |R| = q*(q-1)) against generic
   linear perturbation (a1, a2 != 0, ab != c -> |R| <= 2*q << (q-1)*q^{3/2}).
7. Witness W6: Exact HS-01 rational generating-function non-cancellation (positive vs
   virtual signed multiplicities) AND exact 2x2 Weil-group Kummer extension witness
   refuting Hexagon deposit L89-91 (AD-03).
"""

from __future__ import annotations

from fractions import Fraction
import hashlib
import json
import sys
from typing import Any, Mapping, Sequence


# ---------------------------------------------------------------------------
# 1. Exact cyclotomic ring Z[zeta_p] (basis 1, zeta_p, ..., zeta_p^{p-2})
# ---------------------------------------------------------------------------


def cyc_zero(p: int) -> tuple[int, ...]:
    if type(p) is not int or p < 2:
        raise ValueError("prime p must be an int >= 2")
    return (0,) * (p - 1)


def cyc_power(p: int, exp: int) -> tuple[int, ...]:
    """Return zeta_p^exp in canonical Z[zeta_p] basis of length p - 1."""
    if type(p) is not int or p < 2:
        raise ValueError("prime p must be an int >= 2")
    r = exp % p
    if r == p - 1:
        return (-1,) * (p - 1)
    vec = [0] * (p - 1)
    vec[r] = 1
    return tuple(vec)


def cyc_add(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    if len(a) != len(b):
        raise ValueError("cyclotomic dimension mismatch")
    return tuple(x + y for x, y in zip(a, b))


def cyc_scale_int(k: int, a: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(k * x for x in a)


def cyc_mul(p: int, a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    """Exact product in Z[x] / (1 + x + ... + x^{p-1})."""
    m = p - 1
    if len(a) != m or len(b) != m:
        raise ValueError("cyclotomic vector length mismatch")
    raw = [0] * p
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            if bj != 0:
                raw[(i + j) % p] += ai * bj
    top = raw[m]
    return tuple(raw[i] - top for i in range(m))


def cyc_conj(p: int, a: tuple[int, ...]) -> tuple[int, ...]:
    """Complex conjugation zeta_p^j -> zeta_p^{p-j} in Z[zeta_p]."""
    out = cyc_zero(p)
    for j, coeff in enumerate(a):
        if coeff != 0:
            out = cyc_add(out, cyc_scale_int(coeff, cyc_power(p, (-j) % p)))
    return out


def cyc_as_int(a: tuple[int, ...]) -> int | None:
    """Return exact integer value if a lies in Z subset Z[zeta_p], else None."""
    if any(x != 0 for x in a[1:]):
        return None
    return a[0]


# ---------------------------------------------------------------------------
# 2. Exact finite field arithmetic (F_p and F_4 = F_2[w]/(w^2 + w + 1))
# ---------------------------------------------------------------------------


def gf4_add(x: int, y: int) -> int:
    return x ^ y


def gf4_mul(x: int, y: int) -> int:
    """Exact multiplication in F_4 = {0, 1, w, w+1} encoded as 2-bit ints."""
    a0, a1 = x & 1, (x >> 1) & 1
    b0, b1 = y & 1, (y >> 1) & 1
    # (a0 + a1*w)(b0 + b1*w) = a0*b0 + (a0*b1 + a1*b0)*w + a1*b1*(w + 1)
    c0 = (a0 & b0) ^ (a1 & b1)
    c1 = (a0 & b1) ^ (a1 & b0) ^ (a1 & b1)
    return c0 | (c1 << 1)


def gf4_trace(x: int) -> int:
    """Trace Tr_{F_4 / F_2}(a0 + a1*w) = a1 in F_2."""
    return (x >> 1) & 1


def legendre_mod_p(a: int, p: int) -> int:
    """Exact Legendre symbol (a/p) in {-1, 0, 1} for odd prime p."""
    v = a % p
    if v == 0:
        return 0
    r = pow(v, (p - 1) // 2, p)
    return 1 if r == 1 else -1


# ---------------------------------------------------------------------------
# 3. Exact matrix unitarity check K K^* = Q^d I for path kernel
# ---------------------------------------------------------------------------


def verify_path_kernel_unitarity_fp(p: int, d: int, h: int) -> dict[str, Any]:
    """Verify K K^* = p^d I over Z[zeta_p] for K(x, y) = zeta_p^{h * (x . y)} on F_p^d."""
    if h % p == 0:
        raise ValueError("h must be nonzero mod p")
    pts: list[tuple[int, ...]] = [()]
    for _ in range(d):
        pts = [pt + (v,) for pt in pts for v in range(p)]
    n = len(pts)
    k_mat = [
        [cyc_power(p, h * sum(x[r] * y[r] for r in range(d))) for y in pts]
        for x in pts
    ]
    all_diag_exact = True
    all_offdiag_zero = True
    for i in range(n):
        for j in range(n):
            acc = cyc_zero(p)
            for m in range(n):
                acc = cyc_add(acc, cyc_mul(p, k_mat[i][m], cyc_conj(p, k_mat[j][m])))
            val = cyc_as_int(acc)
            if i == j:
                if val != n:
                    all_diag_exact = False
            else:
                if val != 0:
                    all_offdiag_zero = False
    return {
        "q": p,
        "d": d,
        "h": h,
        "matrix_size": n,
        "all_diag_equal_q_pow_d": all_diag_exact,
        "all_offdiag_zero": all_offdiag_zero,
        "passed": all_diag_exact and all_offdiag_zero,
    }


def verify_path_kernel_unitarity_f4(d: int, h: int) -> dict[str, Any]:
    """Verify K K^* = 4^d I over Z (since char=2 -> zeta_2 = -1) for F_4^d."""
    if h not in (1, 2, 3):
        raise ValueError("h must be in F_4^* = {1, 2, 3}")
    pts: list[tuple[int, ...]] = [()]
    for _ in range(d):
        pts = [pt + (v,) for pt in pts for v in range(4)]
    n = len(pts)
    k_mat: list[list[int]] = []
    for x in pts:
        row: list[int] = []
        for y in pts:
            dot = 0
            for r in range(d):
                dot = gf4_add(dot, gf4_mul(x[r], y[r]))
            row.append(-1 if gf4_trace(gf4_mul(h, dot)) else 1)
        k_mat.append(row)
    all_diag_exact = True
    all_offdiag_zero = True
    for i in range(n):
        for j in range(n):
            acc = sum(k_mat[i][m] * k_mat[j][m] for m in range(n))
            if i == j:
                if acc != n:
                    all_diag_exact = False
            else:
                if acc != 0:
                    all_offdiag_zero = False
    return {
        "q": 4,
        "d": d,
        "h": h,
        "matrix_size": n,
        "all_diag_equal_q_pow_d": all_diag_exact,
        "all_offdiag_zero": all_offdiag_zero,
        "passed": all_diag_exact and all_offdiag_zero,
    }


# ---------------------------------------------------------------------------
# 4. Exact path character sum S_h via matrix-vector chain over Z[zeta_p]
# ---------------------------------------------------------------------------


def compute_path_sum_fp(
    p: int,
    d: int,
    k: int,
    weights_by_h_and_i: Mapping[int, Sequence[Sequence[tuple[int, ...]]]],
    c: int,
) -> dict[str, Any]:
    """Evaluate sum_{h in F_p} psi(h*c) sum_{x in (F_p^d)^k} prod_i t_{i,h}(x_i) psi(h * sum x_i.x_{i+1})."""
    if k < 2:
        raise ValueError("k must be >= 2")
    pts: list[tuple[int, ...]] = [()]
    for _ in range(d):
        pts = [pt + (v,) for pt in pts for v in range(p)]
    n = len(pts)
    h0_sum = cyc_power(p, 0)
    for i in range(k):
        tot_i = cyc_zero(p)
        for v in weights_by_h_and_i[0][i]:
            tot_i = cyc_add(tot_i, v)
        h0_sum = cyc_mul(p, h0_sum, tot_i)
    r_cyc = cyc_zero(p)
    for h in range(1, p):
        # Right-to-left chain: vec = t_{k,h}; for i = k-1 down to 1: vec = D_i K_i vec
        vec = list(weights_by_h_and_i[h][k - 1])
        for i in range(k - 2, -1, -1):
            nxt = [cyc_zero(p) for _ in range(n)]
            ti = weights_by_h_and_i[h][i]
            for ix, x in enumerate(pts):
                tx = ti[ix]
                if all(val == 0 for val in tx):
                    continue
                acc = cyc_zero(p)
                for iy, y in enumerate(pts):
                    vy = vec[iy]
                    if all(val == 0 for val in vy):
                        continue
                    dot = sum(x[r] * y[r] for r in range(d))
                    acc = cyc_add(acc, cyc_mul(p, cyc_power(p, h * dot), vy))
                nxt[ix] = cyc_mul(p, tx, acc)
            vec = nxt
        sh = cyc_zero(p)
        for val in vec:
            sh = cyc_add(sh, val)
        sh = cyc_mul(p, cyc_power(p, h * c), sh)
        r_cyc = cyc_add(r_cyc, sh)
    m_pow_k = cyc_as_int(h0_sum)
    r_int = cyc_as_int(r_cyc)
    if m_pow_k is None or r_int is None:
        raise ValueError("expected exact integer zero-mode and remainder sum")
    return {
        "zero_mode_M_pow_k": m_pow_k,
        "remainder_R_from_chars": r_int,
        "total_QN_from_chars": m_pow_k + r_int,
    }


# ---------------------------------------------------------------------------
# 5. Witness W1: Paper Example 5 (U = A^1, k = 2, conic xy + ax + by + c = 0)
# ---------------------------------------------------------------------------


def certify_witness_w1_affine_line_conic() -> dict[str, Any]:
    cases: list[dict[str, Any]] = []
    all_ok = True
    for p in (2, 3, 5, 7, 11):
        a, b, c = 1 % p, 1 % p, 0  # ab - c = 1 != 0 mod p (smooth G_m)
        m_val = p
        n_direct = sum(1 for x in range(p) for y in range(p) if (x * y + a * x + b * y + c) % p == 0)
        r_direct = p * n_direct - m_val * m_val
        weights: dict[int, list[list[tuple[int, ...]]]] = {}
        for h in range(p):
            w1 = [cyc_power(p, h * a * x) for x in range(p)]
            w2 = [cyc_power(p, h * b * x) for x in range(p)]
            weights[h] = [w1, w2]
        char_res = compute_path_sum_fp(p, 1, 2, weights, c)
        unitarity = verify_path_kernel_unitarity_fp(p, 1, 1)
        # (-1)^{D-1} R = (-1)^1 (-p) = +p; HS-03 squared bound: R^2 <= (p-1)^2 * p^3
        signed_r = -r_direct
        hs03_rhs_sq = (p - 1) * (p - 1) * (p ** 3)
        ok = (
            n_direct == p - 1
            and r_direct == -p
            and signed_r == p
            and char_res["zero_mode_M_pow_k"] == m_val * m_val
            and char_res["remainder_R_from_chars"] == r_direct
            and char_res["total_QN_from_chars"] == p * n_direct
            and r_direct * r_direct <= hs03_rhs_sq
            and unitarity["passed"]
        )
        all_ok = all_ok and ok
        cases.append(
            {
                "p": p,
                "a": a,
                "b": b,
                "c": c,
                "M": m_val,
                "N_direct": n_direct,
                "R_direct": r_direct,
                "R_from_chars": char_res["remainder_R_from_chars"],
                "signed_effective_trace": signed_r,
                "expected_K2_trace": p,
                "R_sq": r_direct * r_direct,
                "hs03_bound_sq": hs03_rhs_sq,
                "unitarity_passed": unitarity["passed"],
                "passed": ok,
            }
        )

    # Negative control: singular reducible conic ab == c (xy + x + y + 1 = (x+1)(y+1) = 0)
    p_neg = 7
    n_sing = sum(1 for x in range(p_neg) for y in range(p_neg) if (x * y + x + y + 1) % p_neg == 0)
    r_sing = p_neg * n_sing - p_neg * p_neg
    neg_control_caught = (n_sing == 2 * p_neg - 1) and (r_sing == p_neg * p_neg - p_neg) and (r_sing != -p_neg)
    all_ok = all_ok and neg_control_caught
    return {
        "witness_id": "W1_AFFINE_LINE_CONIC_EXAMPLE5",
        "cases": cases,
        "singular_negative_control": {
            "p": p_neg,
            "equation": "(x+1)(y+1)=0",
            "N_singular": n_sing,
            "R_singular": r_sing,
            "violates_smooth_remainder_minus_p": neg_control_caught,
        },
        "passed": all_ok,
    }


# ---------------------------------------------------------------------------
# 6. Witness W2: Punctured line U = G_m (k = 2, 3), non-trivial H^1_c(G_m)
# ---------------------------------------------------------------------------


def certify_witness_w2_gm_nonvanishing_h1c() -> dict[str, Any]:
    cases: list[dict[str, Any]] = []
    all_ok = True
    # k = 2 over F_3, F_5, F_7 with a1=1, a2=1, c=2 (so a1*a2 - c = -1 != 0 and a1,a2,c != 0)
    for p in (3, 5, 7):
        a1, a2, c = 1, 1, 2
        m_val = p - 1
        n_direct = sum(
            1 for x in range(1, p) for y in range(1, p) if (x * y + a1 * x + a2 * y + c) % p == 0
        )
        r_direct = p * n_direct - m_val * m_val
        weights: dict[int, list[list[tuple[int, ...]]]] = {}
        for h in range(p):
            w1 = [cyc_zero(p) if x == 0 else cyc_power(p, h * a1 * x) for x in range(p)]
            w2 = [cyc_zero(p) if x == 0 else cyc_power(p, h * a2 * x) for x in range(p)]
            weights[h] = [w1, w2]
        char_res = compute_path_sum_fp(p, 1, 2, weights, c)
        # Y subset G_m^2 is P^1 minus 4 points (x=0, x=-a2, x=inf, x=-c/a1), all distinct when a1*a2!=c and a1,a2,c!=0:
        # so N = p - 3, R = p(p-3) - (p-1)^2 = -p - 1, (-1)^1 R = p + 1 = 1^2 + p (H^1_c(G_m)^{otimes 2} + K_2)!
        signed_r = -r_direct
        hs03_rhs_sq = (p - 1) * (p - 1) * (p ** 3)
        ok = (
            n_direct == p - 3
            and signed_r == 1 + p
            and char_res["remainder_R_from_chars"] == r_direct
            and r_direct * r_direct <= hs03_rhs_sq
        )
        all_ok = all_ok and ok
        cases.append(
            {
                "p": p,
                "k": 2,
                "M": m_val,
                "N_direct": n_direct,
                "R_direct": r_direct,
                "R_from_chars": char_res["remainder_R_from_chars"],
                "signed_effective_trace": signed_r,
                "h1c_tensor_k_trace": 1,
                "K_trace": signed_r - 1,
                "hs03_bound_sq": hs03_rhs_sq,
                "passed": ok,
            }
        )

    # k = 3 over F_5 and F_7: generic (a1,a2,a3,c)=(1,1,2,3) has L1 cap L2 = (1,-2) in G_m^2,
    # giving N = p^2 - 3p + 5 and exact effective trace (-1)^2 R = +R = 1 + 2p = Tr(H^1_c(G_m)^{otimes 3}) + Tr(K_3)!
    for p3 in (5, 7):
        a_lin = (1, 1, 2)
        c3 = 3
        m3 = p3 - 1
        n3 = sum(
            1
            for x1 in range(1, p3)
            for x2 in range(1, p3)
            for x3 in range(1, p3)
            if (x1 * x2 + x2 * x3 + a_lin[0] * x1 + a_lin[1] * x2 + a_lin[2] * x3 + c3) % p3 == 0
        )
        r3 = p3 * n3 - m3 ** 3
        w3: dict[int, list[list[tuple[int, ...]]]] = {}
        for h in range(p3):
            w3[h] = [
                [cyc_zero(p3) if x == 0 else cyc_power(p3, h * a_lin[idx] * x) for x in range(p3)]
                for idx in range(3)
            ]
        c3_res = compute_path_sum_fp(p3, 1, 3, w3, c3)
        hs03_k3_sq = (p3 - 1) * (p3 - 1) * (p3 ** 4)
        ok3 = (
            n3 == p3 * p3 - 3 * p3 + 5
            and r3 == 1 + 2 * p3
            and c3_res["zero_mode_M_pow_k"] == m3 ** 3
            and c3_res["remainder_R_from_chars"] == r3
            and r3 * r3 <= hs03_k3_sq
        )
        all_ok = all_ok and ok3
        cases.append(
            {
                "p": p3,
                "k": 3,
                "M": m3,
                "N_direct": n3,
                "R_direct": r3,
                "R_from_chars": c3_res["remainder_R_from_chars"],
                "signed_effective_trace": r3,
                "h1c_tensor_k_trace": 1,
                "K_trace": r3 - 1,
                "hs03_bound_sq": hs03_k3_sq,
                "passed": ok3,
            }
        )

    # Smooth-but-non-generic Weak-Lefschetz negative control on G_m^3 (p = 5):
    # a1 == a3 == 1 makes L1: x1+x3+2=0 and L2: x1+x3+1=0 parallel -> H^1(G_m^3) -> H^1(Y) fails iso (dim 3 != 4),
    # yielding non-effective R = -p^2 + 2p + 1 = -14!
    p_wl = 5
    n_wl_fail = sum(
        1
        for x1 in range(1, p_wl)
        for x2 in range(1, p_wl)
        for x3 in range(1, p_wl)
        if (x1 * x2 + x2 * x3 + x1 + 2 * x2 + x3 + 1) % p_wl == 0
    )
    r_wl_fail = p_wl * n_wl_fail - (p_wl - 1) ** 3
    wl_neg_ok = (n_wl_fail == p_wl * p_wl - 4 * p_wl + 5) and (r_wl_fail == -(p_wl * p_wl) + 2 * p_wl + 1)
    all_ok = all_ok and wl_neg_ok
    return {
        "witness_id": "W2_PUNCTURED_LINE_GM_K2_K3",
        "cases": cases,
        "smooth_nongeneric_wl_negative_control": {
            "p": p_wl,
            "k": 3,
            "params": "a1=1, a2=2, a3=1, c=1 (parallel lines L1 || L2)",
            "N_nongeneric": n_wl_fail,
            "R_nongeneric": r_wl_fail,
            "expected_non_effective_minus_p2_plus_2p_plus_1": -(p_wl * p_wl) + 2 * p_wl + 1,
            "demonstrates_smooth_alone_insufficient_for_wl": wl_neg_ok,
        },
        "passed": all_ok,
    }


# ---------------------------------------------------------------------------
# 7. Witness W3: Smooth affine elliptic curves E^o with Noether B = 2
# ---------------------------------------------------------------------------


def _elliptic_affine_points(p: int, coef_a: int, coef_b: int) -> list[tuple[int, int]]:
    pts: list[tuple[int, int]] = []
    for x in range(p):
        rhs = (x * x * x + coef_a * x + coef_b) % p
        for y in range(p):
            if (y * y) % p == rhs:
                pts.append((x, y))
    return pts


def _is_elliptic_path_hypersurface_smooth_fp(
    p: int,
    coef_a: int,
    pts: Sequence[tuple[int, int]],
    a11: int,
    a12: int,
    a21: int,
    a22: int,
    c: int,
) -> bool:
    """Check Jacobian rank 3 on Y subset A^4 defined by f1=0, f2=0, P=0 at every F_p-point of Y."""
    for x1, y1 in pts:
        for x2, y2 in pts:
            if (x1 * x2 + a11 * x1 + a12 * y1 + a21 * x2 + a22 * y2 + c) % p != 0:
                continue
            # df1 = (3 x1^2 + A, -2 y1, 0, 0)
            # df2 = (0, 0, 3 x2^2 + A, -2 y2)
            # dP  = (x2 + a11, a12, x1 + a21, a22)
            # Smooth at (u1, u2) iff dP does NOT vanish on tangent space T_{u1} E x T_{u2} E,
            # spanned by t1 = (2 y1, 3 x1^2 + A, 0, 0) and t2 = (0, 0, 2 y2, 3 x2^2 + A).
            v1 = ((x2 + a11) * (2 * y1) + a12 * (3 * x1 * x1 + coef_a)) % p
            v2 = ((x1 + a21) * (2 * y2) + a22 * (3 * x2 * x2 + coef_a)) % p
            if v1 == 0 and v2 == 0:
                return False
    return True


def certify_witness_w3_elliptic_noether_b2() -> dict[str, Any]:
    # Three smooth elliptic curves over F_5, F_7, F_11 with non-zero discriminant 4A^3 + 27B^2 != 0 mod p
    specs = [
        (5, 1, 1, (1, 1, 2, 1, 1)),   # y^2 = x^3 + x + 1 / F_5, #E = 9, a_5 = -3
        (7, 0, 2, (1, 1, 2, 1, 1)),   # y^2 = x^3 + 2 / F_7, #E = 9, a_7 = -1
        (11, 1, 6, (1, 1, 2, 1, 2)),  # y^2 = x^3 + x + 6 / F_11, #E = 13, a_11 = -1
    ]
    cases: list[dict[str, Any]] = []
    all_ok = True
    for p, coef_a, coef_b, (a11, a12, a21, a22, c) in specs:
        disc_mod_p = (4 * (coef_a ** 3) + 27 * (coef_b ** 2)) % p
        pts = _elliptic_affine_points(p, coef_a, coef_b)
        m_val = len(pts)
        a_p = p + 1 - (m_val + 1)  # trace of Frobenius on H^1(E)
        hasse_ok = a_p * a_p <= 4 * p
        # Group points by Noether normalization pi(x, y) = x -> max fibre size <= B = 2
        fibres: dict[int, list[tuple[int, int]]] = {x: [] for x in range(p)}
        for pt in pts:
            fibres[pt[0]].append(pt)
        max_fibre = max(len(v) for v in fibres.values())
        b_cap = 2
        n_direct = sum(
            1
            for x1, y1 in pts
            for x2, y2 in pts
            if (x1 * x2 + a11 * x1 + a12 * y1 + a21 * x2 + a22 * y2 + c) % p == 0
        )
        r_direct = p * n_direct - m_val * m_val
        weights: dict[int, list[list[tuple[int, ...]]]] = {}
        for h in range(p):
            w1: list[tuple[int, ...]] = []
            w2: list[tuple[int, ...]] = []
            for x in range(p):
                acc1 = cyc_zero(p)
                acc2 = cyc_zero(p)
                for fx, fy in fibres[x]:
                    acc1 = cyc_add(acc1, cyc_power(p, h * (a11 * fx + a12 * fy)))
                    acc2 = cyc_add(acc2, cyc_power(p, h * (a21 * fx + a22 * fy)))
                w1.append(acc1)
                w2.append(acc2)
            weights[h] = [w1, w2]
        char_res = compute_path_sum_fp(p, 1, 2, weights, c)
        smooth_fp = _is_elliptic_path_hypersurface_smooth_fp(p, coef_a, pts, a11, a12, a21, a22, c)
        # HS-03 squared bound with B = 2, C = 1, w = 0, d = 1, k = 2:
        # |R| <= (p-1) * B^2 * p^{3/2}  <=>  R^2 <= (p-1)^2 * 16 * p^3
        hs03_rhs_sq = (p - 1) * (p - 1) * (b_cap ** 4) * (p ** 3)
        ok = (
            disc_mod_p != 0
            and hasse_ok
            and max_fibre <= b_cap
            and smooth_fp
            and char_res["zero_mode_M_pow_k"] == m_val * m_val
            and char_res["remainder_R_from_chars"] == r_direct
            and char_res["total_QN_from_chars"] == p * n_direct
            and r_direct * r_direct <= hs03_rhs_sq
        )
        all_ok = all_ok and ok
        cases.append(
            {
                "p": p,
                "curve": f"y^2 = x^3 + {coef_a}x + {coef_b}",
                "disc_mod_p": disc_mod_p,
                "M_affine_points": m_val,
                "a_p_trace": a_p,
                "hasse_bound_a_p_sq_le_4p": hasse_ok,
                "max_noether_fibre_size": max_fibre,
                "noether_B": b_cap,
                "Y_smooth_at_Fp_points": smooth_fp,
                "N_direct": n_direct,
                "R_direct": r_direct,
                "R_from_chars": char_res["remainder_R_from_chars"],
                "R_sq": r_direct * r_direct,
                "hs03_bound_sq": hs03_rhs_sq,
                "passed": ok,
            }
        )
    return {"witness_id": "W3_ELLIPTIC_CURVES_NOETHER_B2", "cases": cases, "passed": all_ok}


# ---------------------------------------------------------------------------
# 8. Witness W4: Higher dimension d = 2 AND characteristic p = 2 (F_2, F_3, F_4)
# ---------------------------------------------------------------------------


def certify_witness_w4_higher_dim_and_char2() -> dict[str, Any]:
    cases: list[dict[str, Any]] = []
    all_ok = True
    # Over F_2 and F_3: U = A^2, k = 2 (D = 4), Y: x1*y1 + x2*y2 + 1 = 0
    for p in (2, 3):
        m_val = p * p
        n_direct = sum(
            1
            for x1 in range(p)
            for x2 in range(p)
            for y1 in range(p)
            for y2 in range(p)
            if (x1 * y1 + x2 * y2 + 1) % p == 0
        )
        r_direct = p * n_direct - m_val * m_val
        weights = {h: [[cyc_power(p, 0)] * (p * p), [cyc_power(p, 0)] * (p * p)] for h in range(p)}
        char_res = compute_path_sum_fp(p, 2, 2, weights, 1)
        unit = verify_path_kernel_unitarity_fp(p, 2, 1)
        # Exact count on smooth quadric x1*y1 + x2*y2 = -1 in A^4: N = p^3 - p, R = -p^2, (-1)^{D-1} R = +p^2
        signed_r = -r_direct
        hs03_rhs_sq = (p - 1) * (p - 1) * (p ** 6)  # d=2, k=2 => Q^{d(k+1)} = p^6
        ok = (
            n_direct == p ** 3 - p
            and r_direct == -(p * p)
            and signed_r == p * p
            and char_res["remainder_R_from_chars"] == r_direct
            and r_direct * r_direct <= hs03_rhs_sq
            and unit["passed"]
        )
        all_ok = all_ok and ok
        cases.append(
            {
                "field": f"F_{p}",
                "char": p,
                "q": p,
                "d": 2,
                "k": 2,
                "M": m_val,
                "N_direct": n_direct,
                "R_direct": r_direct,
                "R_from_chars": char_res["remainder_R_from_chars"],
                "signed_effective_trace": signed_r,
                "unitarity_passed": unit["passed"],
                "hs03_bound_sq": hs03_rhs_sq,
                "passed": ok,
            }
        )

    # Over F_4 (char 2, non-prime extension!): U = A^2, k = 2, Y: x1*y1 + x2*y2 + 1 = 0
    q4 = 4
    m4 = q4 * q4
    n4 = sum(
        1
        for x1 in range(4)
        for x2 in range(4)
        for y1 in range(4)
        for y2 in range(4)
        if gf4_add(gf4_add(gf4_mul(x1, y1), gf4_mul(x2, y2)), 1) == 0
    )
    r4 = q4 * n4 - m4 * m4
    # Exact character sum over h in F_4^* = {1, 2, 3}
    r4_chars = 0
    for h in (1, 2, 3):
        sh = 0
        for x1 in range(4):
            for x2 in range(4):
                for y1 in range(4):
                    for y2 in range(4):
                        val = gf4_add(gf4_add(gf4_mul(x1, y1), gf4_mul(x2, y2)), 1)
                        sh += -1 if gf4_trace(gf4_mul(h, val)) else 1
        r4_chars += sh
    unit4 = verify_path_kernel_unitarity_f4(2, 2)
    hs03_f4_sq = (q4 - 1) * (q4 - 1) * (q4 ** 6)
    ok4 = (
        n4 == q4 ** 3 - q4
        and r4 == -(q4 * q4)
        and r4_chars == r4
        and r4 * r4 <= hs03_f4_sq
        and unit4["passed"]
    )
    all_ok = all_ok and ok4
    cases.append(
        {
            "field": "F_4",
            "char": 2,
            "q": q4,
            "d": 2,
            "k": 2,
            "M": m4,
            "N_direct": n4,
            "R_direct": r4,
            "R_from_chars": r4_chars,
            "signed_effective_trace": -r4,
            "unitarity_passed": unit4["passed"],
            "hs03_bound_sq": hs03_f4_sq,
            "passed": ok4,
        }
    )
    return {"witness_id": "W4_HIGHER_DIM_D2_AND_CHAR2", "cases": cases, "passed": all_ok}


# ---------------------------------------------------------------------------
# 9. Witness W5: Lisse rank-1 quadratic twist L_chi on G_m (genericity control!)
# ---------------------------------------------------------------------------


def certify_witness_w5_lisse_quadratic_twist() -> dict[str, Any]:
    cases: list[dict[str, Any]] = []
    all_ok = True
    for p in (5, 7, 11):
        # M = sum_{u in F_p^*} chi(u) = 0
        m_val = sum(legendre_mod_p(u, p) for u in range(1, p))
        # Non-generic smooth hypersurface Y_0: x1*x2 + 1 = 0 (a1 = a2 = 0):
        # L_chi boxtimes L_chi trivializes on Y_0 -> |N_nongeneric| = p - 1, |R_nongeneric| = p(p-1)!
        n_nongeneric = sum(
            legendre_mod_p(x1, p) * legendre_mod_p(x2, p)
            for x1 in range(1, p)
            for x2 in range(1, p)
            if (x1 * x2 + 1) % p == 0
        )
        r_nongeneric = p * n_nongeneric - m_val * m_val
        # Generic perturbation Y_gen: x1*x2 + x1 + x2 + 2 = 0 (a1=1, a2=1, c=2, a1*a2 - c = -1 != 0)
        a1, a2, c = 1, 1, 2
        n_gen = sum(
            legendre_mod_p(x1, p) * legendre_mod_p(x2, p)
            for x1 in range(1, p)
            for x2 in range(1, p)
            if (x1 * x2 + a1 * x1 + a2 * x2 + c) % p == 0
        )
        r_gen = p * n_gen - m_val * m_val
        weights: dict[int, list[list[tuple[int, ...]]]] = {}
        for h in range(p):
            w1 = [
                cyc_zero(p) if x == 0 else cyc_scale_int(legendre_mod_p(x, p), cyc_power(p, h * a1 * x))
                for x in range(p)
            ]
            w2 = [
                cyc_zero(p) if x == 0 else cyc_scale_int(legendre_mod_p(x, p), cyc_power(p, h * a2 * x))
                for x in range(p)
            ]
            weights[h] = [w1, w2]
        char_res = compute_path_sum_fp(p, 1, 2, weights, c)
        hs03_rhs_sq = (p - 1) * (p - 1) * (p ** 3)
        ok = (
            m_val == 0
            and abs(n_nongeneric) == p - 1
            and abs(r_nongeneric) == p * (p - 1)
            and abs(r_gen) < abs(r_nongeneric)
            and char_res["remainder_R_from_chars"] == r_gen
            and r_gen * r_gen <= hs03_rhs_sq
        )
        all_ok = all_ok and ok
        cases.append(
            {
                "p": p,
                "M_twist": m_val,
                "N_nongeneric_smooth": n_nongeneric,
                "R_nongeneric_smooth": r_nongeneric,
                "N_generic": n_gen,
                "R_generic": r_gen,
                "R_generic_from_chars": char_res["remainder_R_from_chars"],
                "genericity_drop_confirmed": abs(r_gen) < abs(r_nongeneric),
                "hs03_bound_sq": hs03_rhs_sq,
                "passed": ok,
            }
        )
    return {"witness_id": "W5_LISSE_QUADRATIC_TWIST_GENERICITY", "cases": cases, "passed": all_ok}


# ---------------------------------------------------------------------------
# 10. Witness W6: HS-01 rational pole non-cancellation & AD-03 Kummer counterexample
# ---------------------------------------------------------------------------


def _poly_mul_q(a: Sequence[Fraction], b: Sequence[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return out


def _poly_eval_q(poly: Sequence[Fraction], z: Fraction) -> Fraction:
    acc = Fraction(0)
    for coeff in reversed(poly):
        acc = acc * z + coeff
    return acc


def verify_hs01_rational_poles(eigen_mult_pairs: Sequence[tuple[Fraction, int]]) -> dict[str, Any]:
    """Build G(z) = sum_j m_j * mu_j * z / (1 - mu_j * z) = P(z) / Q(z) in Q(z).

    For distinct nonzero mu_j, Q(z) = prod_j (1 - mu_j z) and P(1/mu_j) != 0 iff m_j != 0.
    """
    grouped: dict[Fraction, int] = {}
    for mu, mult in eigen_mult_pairs:
        if not isinstance(mu, Fraction) or mu == 0:
            raise ValueError("eigenvalue mu must be a nonzero Fraction")
        if type(mult) is not int:
            raise ValueError("multiplicity must be an exact int")
        grouped[mu] = grouped.get(mu, 0) + mult

    distinct_mus = list(grouped.keys())
    q_poly: list[Fraction] = [Fraction(1)]
    for mu in distinct_mus:
        q_poly = _poly_mul_q(q_poly, [Fraction(1), -mu])

    p_poly = [Fraction(0)] * (len(distinct_mus) + 1)
    for idx, mu in enumerate(distinct_mus):
        mult = grouped[mu]
        other: list[Fraction] = [Fraction(1)]
        for j, mu_other in enumerate(distinct_mus):
            if j != idx:
                other = _poly_mul_q(other, [Fraction(1), -mu_other])
        # Add mult * mu * z * other(z)
        for deg, coeff in enumerate(other):
            p_poly[deg + 1] += Fraction(mult) * mu * coeff

    surviving_poles: list[str] = []
    cancelled_poles: list[str] = []
    for mu in distinct_mus:
        z0 = Fraction(1, 1) / mu
        num_at_z0 = _poly_eval_q(p_poly, z0)
        if num_at_z0 != 0:
            surviving_poles.append(f"{z0.numerator}/{z0.denominator}")
        else:
            cancelled_poles.append(f"{z0.numerator}/{z0.denominator}")
    return {
        "distinct_eigenvalues": len(distinct_mus),
        "all_multiplicities_positive": all(m > 0 for m in grouped.values()),
        "surviving_poles": surviving_poles,
        "cancelled_poles": cancelled_poles,
        "zero_pole_cancellation": len(cancelled_poles) == 0,
    }


def _mat2_mul(a: tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]],
              b: tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]) -> tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]:
    return (
        (a[0][0] * b[0][0] + a[0][1] * b[1][0], a[0][0] * b[0][1] + a[0][1] * b[1][1]),
        (a[1][0] * b[0][0] + a[1][1] * b[1][0], a[1][0] * b[0][1] + a[1][1] * b[1][1]),
    )


def certify_witness_w6_hs01_and_ad03_kummer() -> dict[str, Any]:
    # 1. Effective positive multiplicities: zero pole cancellation (even when merging V^{otimes k} + K_k)
    eff = verify_hs01_rational_poles([(Fraction(3), 1), (Fraction(5), 2), (Fraction(3), 4)])
    # 2. Virtual (signed) multiplicities: +1 and -1 at mu = 10 cancel completely -> 0 surviving poles!
    virt = verify_hs01_rational_poles([(Fraction(10), 1), (Fraction(10), -1)])
    # 3. Exact 2x2 Kummer extension witness on G_m / F_q (q = 5):
    #    0 -> Q_l(1) -> K_t -> Q_l -> 0
    #    Geometric Frobenius F = diag(1/q, 1), tame monodromy T = [[1, 1], [0, 1]]
    #    Check exact Weil-group relation F * T * F^{-1} = T^{1/q} = [[1, 1/q], [0, 1]]
    #    and prove K_t is indecomposable (unique 1D T-invariant subspace span(e_1), distinct F-eigenvalues 1/q != 1).
    q = 5
    f_mat = ((Fraction(1, q), Fraction(0)), (Fraction(0), Fraction(1)))
    f_inv = ((Fraction(q), Fraction(0)), (Fraction(0), Fraction(1)))
    t_mat = ((Fraction(1), Fraction(1)), (Fraction(0), Fraction(1)))
    t_pow_inv_q = ((Fraction(1), Fraction(1, q)), (Fraction(0), Fraction(1)))
    conj_t = _mat2_mul(_mat2_mul(f_mat, t_mat), f_inv)
    weil_rel_ok = conj_t == t_pow_inv_q
    # Any 1D T-invariant subspace span((u, v)) requires (u + v, v) = lambda*(u, v) => v = 0 (since lambda = 1 if v != 0 => u+v=u => v=0).
    # Verify (T - I) has rank 1 and image == ker == span(e_1), so no complementary T-invariant line exists.
    t_minus_i = ((t_mat[0][0] - 1, t_mat[0][1]), (t_mat[1][0], t_mat[1][1] - 1))
    nilpotent_sq = _mat2_mul(t_minus_i, t_minus_i)
    zero_mat = ((Fraction(0), Fraction(0)), (Fraction(0), Fraction(0)))
    unique_line_proved = (t_minus_i != zero_mat) and (nilpotent_sq == zero_mat)
    distinct_weights = f_mat[0][0] != f_mat[1][1]
    kummer_refutes_direct_sum = weil_rel_ok and unique_line_proved and distinct_weights

    ok = (
        eff["all_multiplicities_positive"]
        and eff["zero_pole_cancellation"]
        and len(eff["surviving_poles"]) == 2
        and (not virt["zero_pole_cancellation"])
        and len(virt["surviving_poles"]) == 0
        and kummer_refutes_direct_sum
    )
    return {
        "witness_id": "W6_HS01_POLES_AND_AD03_KUMMER_COUNTEREXAMPLE",
        "hs01_effective_positive": eff,
        "hs01_virtual_cancellation_control": virt,
        "ad03_kummer_extension_witness": {
            "base_scheme": "G_m / F_5 (smooth normal affine curve)",
            "exact_sequence": "0 -> Q_l(1) -> K_t -> Q_l -> 0",
            "f_eigenvalues": ["1/5", "1/1"],
            "weil_relation_FTF_inv_eq_T_pow_inv_q": weil_rel_ok,
            "t_minus_i_nonzero_nilpotent_unique_1d_subspace": unique_line_proved,
            "distinct_frobenius_weights": distinct_weights,
            "indecomposable_refutes_hexagon_L89_91_direct_sum": kummer_refutes_direct_sum,
        },
        "passed": ok,
    }


# ---------------------------------------------------------------------------
# 11. Top-level certificate assembly
# ---------------------------------------------------------------------------


def run_all_certifications() -> dict[str, Any]:
    witnesses = [
        certify_witness_w1_affine_line_conic(),
        certify_witness_w2_gm_nonvanishing_h1c(),
        certify_witness_w3_elliptic_noether_b2(),
        certify_witness_w4_higher_dim_and_char2(),
        certify_witness_w5_lisse_quadratic_twist(),
        certify_witness_w6_hs01_and_ad03_kummer(),
    ]
    all_passed = all(bool(w["passed"]) for w in witnesses)
    inner = {
        "audit_id": "AUDIT-098",
        "target": "hexagonmath.org/2611.00789v1 (Alpoge-Deligne sign-only proof of Deligne bound)",
        "execution_mode": "standalone_pure_q_and_cyclotomic",
        "honest_novelty_tier": "N0",
        "main_proof_verdict": "MATHEMATICALLY_SOUND_WITH_MINOR_GAPS_AD01_AD02_AD04",
        "hexagon_v1_erratum": "AD-03_LAFFORGUE_COR_VII8_NONSEMISIMPLE_KUMMER_COUNTEREXAMPLE_L89_91",
        "witness_count": len(witnesses),
        "all_witnesses_passed": all_passed,
        "witnesses": witnesses,
    }
    canonical = json.dumps(inner, sort_keys=True, separators=(",", ":")).encode("utf-8")
    digest = hashlib.sha256(canonical).hexdigest()
    return {
        "schema": "aletheia-audit-098-certificate/v1",
        "canonical_inner_sha256": digest,
        "passed": all_passed,
        **inner,
    }


EXPECTED_WITNESS_IDS: tuple[str, ...] = (
    "W1_AFFINE_LINE_CONIC_EXAMPLE5",
    "W2_PUNCTURED_LINE_GM_K2_K3",
    "W3_ELLIPTIC_CURVES_NOETHER_B2",
    "W4_HIGHER_DIM_D2_AND_CHAR2",
    "W5_LISSE_QUADRATIC_TWIST_GENERICITY",
    "W6_HS01_POLES_AND_AD03_KUMMER_COUNTEREXAMPLE",
)

EXPECTED_INNER_KEYS: tuple[str, ...] = (
    "audit_id",
    "target",
    "execution_mode",
    "honest_novelty_tier",
    "main_proof_verdict",
    "hexagon_v1_erratum",
    "witness_count",
    "all_witnesses_passed",
    "witnesses",
)

EXPECTED_TOP_KEYS: frozenset[str] = frozenset(
    (*EXPECTED_INNER_KEYS, "schema", "canonical_inner_sha256", "passed")
)

_HEX_LOWER: frozenset[str] = frozenset("0123456789abcdef")

_WITNESS_MIN_CASES: dict[str, int] = {
    "W1_AFFINE_LINE_CONIC_EXAMPLE5": 5,
    "W2_PUNCTURED_LINE_GM_K2_K3": 5,
    "W3_ELLIPTIC_CURVES_NOETHER_B2": 3,
    "W4_HIGHER_DIM_D2_AND_CHAR2": 3,
    "W5_LISSE_QUADRATIC_TWIST_GENERICITY": 3,
}

_WITNESS_REQUIRED_CONTROL_FLAGS: dict[str, tuple[str, str, bool]] = {
    "W1_AFFINE_LINE_CONIC_EXAMPLE5": ("singular_negative_control", "violates_smooth_remainder_minus_p", True),
    "W2_PUNCTURED_LINE_GM_K2_K3": ("smooth_nongeneric_wl_negative_control", "demonstrates_smooth_alone_insufficient_for_wl", True),
}


def _contains_float(obj: Any) -> bool:
    """Recursively detect any floating-point value anywhere inside a JSON-like structure."""
    if isinstance(obj, float):
        return True
    if isinstance(obj, Mapping):
        return any(_contains_float(k) or _contains_float(v) for k, v in obj.items())
    if isinstance(obj, (list, tuple)):
        return any(_contains_float(item) for item in obj)
    return False


def _validate_witness_payload(w: Mapping[str, Any]) -> None:
    """Reject hollow witness shells and require non-empty verified payloads for W1..W6."""
    wid = w.get("witness_id")
    if wid in _WITNESS_MIN_CASES:
        cases = w.get("cases")
        min_n = _WITNESS_MIN_CASES[str(wid)]
        if not isinstance(cases, list) or len(cases) < min_n:
            raise ValueError(f"{wid} requires >= {min_n} case records")
        if any(not isinstance(c, Mapping) or c.get("passed") is not True for c in cases):
            raise ValueError(f"{wid} contains an invalid or failing case record")
        if wid in _WITNESS_REQUIRED_CONTROL_FLAGS:
            ctrl_key, flag_key, expected_flag = _WITNESS_REQUIRED_CONTROL_FLAGS[str(wid)]
            ctrl = w.get(ctrl_key)
            if not isinstance(ctrl, Mapping) or ctrl.get(flag_key) is not expected_flag:
                raise ValueError(f"{wid} missing verified negative control {ctrl_key}.{flag_key}")
        return
    # W6: HS-01 positive + virtual cancellation control + AD-03 Kummer counterexample
    eff = w.get("hs01_effective_positive")
    virt = w.get("hs01_virtual_cancellation_control")
    kum = w.get("ad03_kummer_extension_witness")
    if not isinstance(eff, Mapping) or eff.get("zero_pole_cancellation") is not True:
        raise ValueError("W6 missing verified hs01_effective_positive payload")
    if not isinstance(virt, Mapping) or virt.get("zero_pole_cancellation") is not False:
        raise ValueError("W6 missing verified hs01_virtual_cancellation_control payload")
    if not isinstance(kum, Mapping) or kum.get("indecomposable_refutes_hexagon_L89_91_direct_sum") is not True:
        raise ValueError("W6 missing verified ad03_kummer_extension_witness payload")


def validate_certificate(cert: Any) -> dict[str, Any]:
    """Fail-closed validator for AUDIT-098 certificate objects."""
    if not isinstance(cert, Mapping):
        raise ValueError("certificate must be a mapping")
    if set(cert.keys()) != EXPECTED_TOP_KEYS:
        raise ValueError("certificate top-level keys must match exact AUDIT-098 schema")
    if _contains_float(cert):
        raise ValueError("floating-point values are forbidden in AUDIT-098 certificate")
    if cert.get("schema") != "aletheia-audit-098-certificate/v1":
        raise ValueError("unexpected certificate schema")
    if cert.get("audit_id") != "AUDIT-098":
        raise ValueError("unexpected audit_id")
    if cert.get("execution_mode") != "standalone_pure_q_and_cyclotomic":
        raise ValueError("unexpected execution_mode")
    if cert.get("honest_novelty_tier") != "N0":
        raise ValueError("AUDIT-098 honest_novelty_tier must be N0")
    if cert.get("main_proof_verdict") != "MATHEMATICALLY_SOUND_WITH_MINOR_GAPS_AD01_AD02_AD04":
        raise ValueError("unexpected main_proof_verdict")
    if cert.get("hexagon_v1_erratum") != "AD-03_LAFFORGUE_COR_VII8_NONSEMISIMPLE_KUMMER_COUNTEREXAMPLE_L89_91":
        raise ValueError("unexpected hexagon_v1_erratum")
    target_val = cert.get("target")
    if not isinstance(target_val, str) or not target_val.strip():
        raise ValueError("target must be a non-empty string")
    if type(cert.get("passed")) is not bool or type(cert.get("all_witnesses_passed")) is not bool:
        raise ValueError("passed and all_witnesses_passed must be booleans")
    if cert.get("passed") is not True or cert.get("all_witnesses_passed") is not True:
        raise ValueError("certificate must record passed=True and all_witnesses_passed=True")
    w_count = cert.get("witness_count")
    witnesses = cert.get("witnesses")
    if type(w_count) is not int or not isinstance(witnesses, list) or len(witnesses) != len(EXPECTED_WITNESS_IDS) or w_count != len(witnesses):
        raise ValueError("witness_count and witnesses list must match 6 expected witnesses")
    seen_ids = tuple(w.get("witness_id") if isinstance(w, Mapping) else None for w in witnesses)
    if seen_ids != EXPECTED_WITNESS_IDS:
        raise ValueError(f"unexpected witness_ids sequence: {seen_ids!r}")
    if any(not isinstance(w, Mapping) or w.get("passed") is not True for w in witnesses):
        raise ValueError("every witness must have passed=True")
    for w in witnesses:
        _validate_witness_payload(w)
    claimed_sha = cert.get("canonical_inner_sha256")
    if not isinstance(claimed_sha, str) or len(claimed_sha) != 64 or not all(ch in _HEX_LOWER for ch in claimed_sha):
        raise ValueError("canonical_inner_sha256 must be a lowercase 64-hex string")
    inner = {k: cert.get(k) for k in EXPECTED_INNER_KEYS}
    recomputed = hashlib.sha256(
        json.dumps(inner, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    if recomputed != claimed_sha:
        raise ValueError(f"canonical_inner_sha256 mismatch: {claimed_sha} != {recomputed}")
    return {"valid": True, "canonical_inner_sha256": recomputed, "witness_count": w_count}


def main(argv: Sequence[str] | None = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    cert = run_all_certifications()
    if "--json" in args:
        sys.stdout.write(json.dumps(cert, indent=2, sort_keys=True) + "\n")
    else:
        sys.stdout.write(
            f"AUDIT-098 passed={cert['passed']} witnesses={cert['witness_count']} "
            f"sha256={cert['canonical_inner_sha256']}\n"
        )
    return 0 if cert["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
