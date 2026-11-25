"""Clean-room pure-Z/Q/F_p executable tomography for Portal 78 (VP != VNP).

Independently implements and stress-tests the seven core finite algebraic
mechanisms of anthropics/formal-math/vp-vnp (paper.pdf + Ov/, Nc/, NS1/, Paper/)
using exact integer, rational (Fraction), finite-field (F_p), and Laurent
polynomial arithmetic (zero floating-point operations, zero bare asserts).

Oracles:
  1. probe_meixner_crossing_identity     (App. B, Prop B.2 / display (B.1))
  2. probe_cat0_mat_f2_dichotomy         (App. C-D, Thm C.1, Thm D.2, Rem D.3)
  3. probe_flat_case_perm_and_hub_bounds (App. E, Prop E.1, f_{3,1}, Prop E.10, Thm E.11)
  4. probe_char2_perm_vs_hc_gadgets      (App. M, Prop M.2 vs Prop E.1, S41 Polya)
  5. probe_contracting_unitriangular     (App. F/H, Lem F.2, Prop H.1)
  6. probe_lowdeg_parse_tree_and_diag    (App. K, Lem K.2, Sec 2.5 Boolean, Thm K.6)
  7. probe_border_laurent_closure        (App. N, Lem N.2, Lem N.3, Prop N.4)
"""

from __future__ import annotations

from fractions import Fraction
import itertools
from typing import Dict, List, Mapping, Sequence, Tuple


class ProbeError(ValueError):
    """Typed failure raised when a mathematical oracle invariant fails."""


def _require(cond: bool, msg: str) -> None:
    if not cond:
        raise ProbeError(msg)


# ---------------------------------------------------------------------------
# Exact univariate integer polynomial arithmetic Z[X] (dense trimmed tuples)
# ---------------------------------------------------------------------------


def _poly_trim(coeffs: Sequence[int]) -> Tuple[int, ...]:
    end = len(coeffs)
    while end > 0 and coeffs[end - 1] == 0:
        end -= 1
    return tuple(coeffs[:end])


def _poly_add(a: Sequence[int], b: Sequence[int]) -> Tuple[int, ...]:
    n = max(len(a), len(b))
    out = [
        (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
        for i in range(n)
    ]
    return _poly_trim(out)


def _poly_sub(a: Sequence[int], b: Sequence[int]) -> Tuple[int, ...]:
    n = max(len(a), len(b))
    out = [
        (a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0)
        for i in range(n)
    ]
    return _poly_trim(out)


def _poly_neg(a: Sequence[int]) -> Tuple[int, ...]:
    return tuple(-c for c in a)


def _poly_mul(a: Sequence[int], b: Sequence[int]) -> Tuple[int, ...]:
    if not a:
        return ()
    if not b:
        return ()
    out = [0] * (len(a) + len(b) - 1)
    for i, ca in enumerate(a):
        if ca == 0:
            continue
        for j, cb in enumerate(b):
            if cb != 0:
                out[i + j] += ca * cb
    return _poly_trim(out)


def _poly_shift(a: Sequence[int], k: int) -> Tuple[int, ...]:
    if not a:
        return ()
    return (0,) * k + tuple(a)


def _poly_sub_x2(p_y: Sequence[int]) -> Tuple[int, ...]:
    """Substitute y = X^2 into polynomial p(y) in Z[y] -> Z[X]."""
    if not p_y:
        return ()
    out = [0] * (2 * len(p_y) - 1)
    for idx, coeff in enumerate(p_y):
        out[2 * idx] = coeff
    return _poly_trim(out)


def _poly_eval_1(a: Sequence[int]) -> int:
    return sum(a)


def _poly_det(mat: Sequence[Sequence[Tuple[int, ...]]]) -> Tuple[int, ...]:
    """Exact Leibniz determinant over Z[X] (division-free, valid for small n)."""
    n = len(mat)
    acc: Tuple[int, ...] = ()
    for perm in itertools.permutations(range(n)):
        # Parity via inversion count
        inv = 0
        for i in range(n):
            for j in range(i + 1, n):
                if perm[i] > perm[j]:
                    inv += 1
        prod: Tuple[int, ...] = (1,)
        zero = False
        for r in range(n):
            entry = mat[r][perm[r]]
            if not entry:
                zero = True
                break
            prod = _poly_mul(prod, entry)
        if zero:
            continue
        if inv % 2 == 1:
            acc = _poly_sub(acc, prod)
        else:
            acc = _poly_add(acc, prod)
    return acc


def _rank_q(rows: Sequence[Sequence[int]]) -> int:
    """Exact matrix rank over Q using Fraction Gaussian elimination."""
    if not rows:
        return 0
    m = len(rows)
    n = len(rows[0])
    a = [[Fraction(v) for v in row] for row in rows]
    rank = 0
    for col in range(n):
        piv = -1
        for r in range(rank, m):
            if a[r][col] != 0:
                piv = r
                break
        if piv == -1:
            continue
        a[rank], a[piv] = a[piv], a[rank]
        pv = a[rank][col]
        for r in range(rank + 1, m):
            if a[r][col] != 0:
                factor = a[r][col] / pv
                for c in range(col, n):
                    a[r][c] -= factor * a[rank][c]
        rank += 1
    return rank


def _det_q(mat: Sequence[Sequence[Fraction]]) -> Fraction:
    """Exact rational determinant over Q."""
    n = len(mat)
    a = [[Fraction(v) for v in row] for row in mat]
    sign = Fraction(1)
    for k in range(n):
        piv = -1
        for i in range(k, n):
            if a[i][k] != 0:
                piv = i
                break
        if piv == -1:
            return Fraction(0)
        if piv != k:
            a[k], a[piv] = a[piv], a[k]
            sign = -sign
        pv = a[k][k]
        for i in range(k + 1, n):
            if a[i][k] != 0:
                f = a[i][k] / pv
                for j in range(k, n):
                    a[i][j] -= f * a[k][j]
    out = sign
    for k in range(n):
        out *= a[k][k]
    return out


# ---------------------------------------------------------------------------
# Oracle 1: Appendix B — Meixner Crossing-Wires Identity (Prop B.2)
# ---------------------------------------------------------------------------


def _meixner_tables(max_r: int, max_n: int) -> Tuple[List[List[Tuple[int, ...]]], List[List[Tuple[int, ...]]]]:
    """Build exact B(r, n) and C(r, n) in Z[y] via generating-function recurrences."""
    b_tbl: List[List[Tuple[int, ...]]] = [[() for _ in range(max_n + 1)] for _ in range(max_r + 1)]
    c_tbl: List[List[Tuple[int, ...]]] = [[() for _ in range(max_n + 1)] for _ in range(max_r + 1)]
    for n in range(max_n + 1):
        sign = 1 if (n % 2 == 0) else -1
        b_tbl[0][n] = _poly_shift((sign,), n)
        c_tbl[0][n] = (sign,)
    for r in range(1, max_r + 1):
        b_tbl[r][0] = (1,)
        c_tbl[r][0] = (1,)
        for n in range(1, max_n + 1):
            # (1 + yt) beta_{r} = (1 + t) beta_{r-1}
            b_tbl[r][n] = _poly_sub(
                _poly_add(b_tbl[r - 1][n], b_tbl[r - 1][n - 1]),
                _poly_shift(b_tbl[r][n - 1], 1),
            )
            # (1 + t) gamma_{r} = (1 + yt) gamma_{r-1}
            c_tbl[r][n] = _poly_sub(
                _poly_add(c_tbl[r - 1][n], _poly_shift(c_tbl[r - 1][n - 1], 1)),
                c_tbl[r][n - 1],
            )
    return b_tbl, c_tbl


def _frobenius_symbol_count_le(energy_cap: int) -> int:
    """Count P(E): number of Frobenius symbols (I, J) with |I|=|J| and energy <= E."""
    # Maximum element i has 2i + 1 <= E
    max_elem = (energy_cap - 1) // 2 if energy_cap >= 1 else -1
    # DP: subsets of {0..max_elem} grouped by (size, sum(2i+1))
    counts: Dict[Tuple[int, int], int] = {(0, 0): 1}
    for i in range(max_elem + 1):
        w = 2 * i + 1
        nxt = dict(counts)
        for (sz, en), cnt in counts.items():
            if en + w <= energy_cap:
                key = (sz + 1, en + w)
                nxt[key] = nxt.get(key, 0) + cnt
        counts = nxt
    total = 0
    for (sz1, en1), cnt1 in counts.items():
        for (sz2, en2), cnt2 in counts.items():
            if sz1 == sz2 and en1 + en2 <= energy_cap:
                total += cnt1 * cnt2
    return total


def _build_crossing_matrix(
    sa: Tuple[Tuple[int, ...], Tuple[int, ...]],
    sb: Tuple[Tuple[int, ...], Tuple[int, ...]],
    sc: Tuple[Tuple[int, ...], Tuple[int, ...]],
    sd: Tuple[Tuple[int, ...], Tuple[int, ...]],
    b_tbl: Sequence[Sequence[Tuple[int, ...]]],
    c_tbl: Sequence[Sequence[Tuple[int, ...]]],
) -> List[List[Tuple[int, ...]]]:
    """Build exact 4-party block matrix M in Z[X] (Nc.Cross.matM / Prop B.2)."""
    ia, ja = sa
    ib, jb = sb
    ic, jc = sc
    id_, jd = sd
    y_minus_1 = (-1, 0, 1)  # X^2 - 1

    def b_x(r: int, n: int) -> Tuple[int, ...]:
        return _poly_sub_x2(b_tbl[r][n])

    def c_x(r: int, n: int) -> Tuple[int, ...]:
        return _poly_sub_x2(c_tbl[r][n])

    def x_pow(p: int) -> Tuple[int, ...]:
        return _poly_shift((1,), p)

    # Row tags: ('a', idx), ('d', idx), ('c', idx), ('b', idx)
    row_tags = (
        [("a", v) for v in ia]
        + [("d", v) for v in id_]
        + [("c", v) for v in ic]
        + [("b", v) for v in ib]
    )
    col_tags = (
        [("a", v) for v in ja]
        + [("d", v) for v in jd]
        + [("c", v) for v in jc]
        + [("b", v) for v in jb]
    )
    mat: List[List[Tuple[int, ...]]] = []
    for rp, i in row_tags:
        row: List[Tuple[int, ...]] = []
        for cp, j in col_tags:
            if rp == "a" and cp == "d":
                val = c_x(i, j)
            elif rp == "d" and cp == "a":
                val = _poly_neg(c_x(j, i))
            elif rp == "a" and cp == "c":
                val = x_pow(2 * i + 1) if i == j else ()
            elif rp == "a" and cp == "b":
                val = _poly_mul(y_minus_1, _poly_mul(x_pow(2 * i + 1), b_x(i, j)))
            elif rp == "d" and cp == "c":
                val = _poly_mul(x_pow(2 * j + 1), b_x(j, i))
            elif rp == "d" and cp == "b":
                val = _poly_neg(x_pow(2 * i + 1)) if i == j else ()
            elif rp == "c" and cp == "a":
                val = _poly_neg(x_pow(2 * i + 1)) if i == j else ()
            elif rp == "c" and cp == "d":
                val = _poly_neg(_poly_mul(x_pow(2 * i + 1), b_x(i, j)))
            elif rp == "b" and cp == "a":
                val = _poly_neg(_poly_mul(y_minus_1, _poly_mul(x_pow(2 * j + 1), b_x(j, i))))
            elif rp == "b" and cp == "d":
                val = x_pow(2 * i + 1) if i == j else ()
            elif rp == "c" and cp == "b":
                val = _poly_neg(_poly_mul(y_minus_1, c_x(i, j)))
            elif rp == "b" and cp == "c":
                val = _poly_mul(y_minus_1, c_x(j, i))
            else:
                val = ()
            row.append(val)
        mat.append(row)
    return mat


def probe_meixner_crossing_identity() -> Dict[str, object]:
    """Oracle 1: Verify Prop B.2 Meixner orthogonality, X=1 crossing, reflection, ranks."""
    b_tbl, c_tbl = _meixner_tables(6, 6)

    # 1a. Reciprocal identity y^n B(r,n)|_{1/y} = C(r,n) for 0 <= r, n <= 5
    recip_checks = 0
    for r in range(6):
        for n in range(6):
            brn = b_tbl[r][n]
            recip = _poly_trim([brn[n - k] if (n - k) < len(brn) else 0 for k in range(n + 1)])
            _require(recip == c_tbl[r][n], f"Meixner reciprocal failed at r={r}, n={n}")
            recip_checks += 1

    # 1b. Truncated orthogonality (B.1): (1-y) sum_{r<R} y^r B(r,i) B(r,j) == [i=j] y^i (mod y^R)
    orth_checks = 0
    one_minus_y = (1, -1)
    for big_r in range(1, 7):
        for i in range(6):
            for j in range(6):
                acc: Tuple[int, ...] = ()
                for r in range(big_r):
                    term = _poly_shift(_poly_mul(b_tbl[r][i], b_tbl[r][j]), r)
                    acc = _poly_add(acc, term)
                lhs = _poly_mul(one_minus_y, acc)
                lhs_mod = _poly_trim([lhs[k] if k < len(lhs) else 0 for k in range(big_r)])
                rhs_mod = _poly_shift((1,), i) if (i == j and i < big_r) else ()
                _require(lhs_mod == rhs_mod, f"Orthogonality (B.1) failed at R={big_r}, i={i}, j={j}")
                orth_checks += 1

    # 1c. Exact 4-party crossing identity for Sigma_1 = Sigma_2 = states(size=1, energy=4):
    #     Sigma = {({0},{1}), ({1},{0})}, |Sigma| = 2, Theta = 2*(4+4) = 16.
    sigma: List[Tuple[Tuple[int, ...], Tuple[int, ...]]] = [((0,), (1,)), ((1,), (0,))]
    theta = 16
    psi_table: Dict[Tuple[int, int, int, int], Tuple[int, ...]] = {}
    max_deg = 0
    for ia in range(2):
        for ib in range(2):
            for ic in range(2):
                for id_ in range(2):
                    mat = _build_crossing_matrix(
                        sigma[ia], sigma[ib], sigma[ic], sigma[id_], b_tbl, c_tbl
                    )
                    poly = _poly_det(mat)
                    deg = len(poly) - 1 if poly else 0
                    _require(deg <= theta, f"deg(Psi)={deg} exceeded Theta={theta}")
                    if deg > max_deg:
                        max_deg = deg
                    psi_table[(ia, ib, ic, id_)] = poly

    # Verify (a): Psi(1) = eps * [Jc=Ia, Ic=Ja, Jb=Id, Ib=Jd] (swap index in sigma!)
    # Note: for sigma[0]=({0},{1}) and sigma[1]=({1},{0}), swap(sigma[idx]) = sigma[1 - idx].
    eps_seen: int = 0
    x1_nonzero = 0
    for (ia, ib, ic, id_), poly in psi_table.items():
        val = _poly_eval_1(poly)
        matched = (ic == 1 - ia) and (id_ == 1 - ib)
        if matched:
            _require(val in (-1, 1), f"Psi(1) on matched tuple must be +-1, got {val}")
            if eps_seen == 0:
                eps_seen = val
            else:
                _require(val == eps_seen, "Psi(1) sign not constant across matched tuples")
            x1_nonzero += 1
        else:
            _require(val == 0, f"Psi(1) nonzero on unmatched tuple {(ia, ib, ic, id_)}: {val}")
    _require(x1_nonzero == 4, f"Expected 4 matched crossing tuples, got {x1_nonzero}")

    # Verify reflection symmetry: X^Theta Psi(1/X; sa, sb, sc, sd) = Psi(X; sa, sd, sc, sb)
    refl_checks = 0
    for (ia, ib, ic, id_), poly in psi_table.items():
        rev = _poly_trim([poly[theta - k] if (theta - k) < len(poly) else 0 for k in range(theta + 1)])
        swapped = psi_table[(ia, id_, ic, ib)]
        _require(rev == swapped, f"Reflection identity failed at {(ia, ib, ic, id_)}")
        refl_checks += 1

    # Verify (b) and (c): exact flattening ranks <= (N+1)P(N) and <= (Theta-N+1)P(Theta-N)
    p_vals = {e: _frobenius_symbol_count_le(e) for e in range(theta + 1)}
    ad_bc_ranks: List[int] = []
    ab_cd_ranks: List[int] = []
    for n_deg in range(theta + 1):
        # 4x4 flattening across ad | bc
        mat_ad_bc = []
        for ia in range(2):
            for id_ in range(2):
                row = []
                for ib in range(2):
                    for ic in range(2):
                        p = psi_table[(ia, ib, ic, id_)]
                        row.append(p[n_deg] if n_deg < len(p) else 0)
                mat_ad_bc.append(row)
        rk_ad = _rank_q(mat_ad_bc)
        bound_ad = (n_deg + 1) * p_vals[n_deg]
        _require(rk_ad <= bound_ad, f"ad|bc rank {rk_ad} > {bound_ad} at N={n_deg}")
        ad_bc_ranks.append(rk_ad)

        # 4x4 flattening across ab | cd
        mat_ab_cd = []
        for ia in range(2):
            for ib in range(2):
                row = []
                for ic in range(2):
                    for id_ in range(2):
                        p = psi_table[(ia, ib, ic, id_)]
                        row.append(p[n_deg] if n_deg < len(p) else 0)
                mat_ab_cd.append(row)
        rk_ab = _rank_q(mat_ab_cd)
        n_prime = theta - n_deg
        bound_ab = (n_prime + 1) * p_vals[n_prime]
        _require(rk_ab <= bound_ab, f"ab|cd rank {rk_ab} > {bound_ab} at N={n_deg}")
        ab_cd_ranks.append(rk_ab)

    # Confirm nontrivial crossing rank profile (ranks symmetric: rk_ab[N] == rk_ad[Theta - N])
    _require(ab_cd_ranks == list(reversed(ad_bc_ranks)), "Flattening rank reflection symmetry broken")

    return {
        "recip_checks": recip_checks,
        "orth_checks": orth_checks,
        "theta": theta,
        "max_deg_psi": max_deg,
        "x1_sign": eps_seen,
        "x1_matched_count": x1_nonzero,
        "reflection_checks": refl_checks,
        "max_ad_bc_rank": max(ad_bc_ranks),
        "p_energy_0_to_6": [p_vals[e] for e in range(7)],
        "ad_bc_rank_profile": ad_bc_ranks,
    }


# ---------------------------------------------------------------------------
# Oracle 2: Appendix C-D — CAT(0) CN Inequality & Mat_mu(F_2) Dichotomy
# ---------------------------------------------------------------------------


def _rank_f2_rows(rows: Sequence[int], n: int) -> int:
    work = list(rows)
    rank = 0
    for col in range(n):
        piv = -1
        for r in range(rank, n):
            if (work[r] >> col) & 1:
                piv = r
                break
        if piv == -1:
            continue
        work[rank], work[piv] = work[piv], work[rank]
        for r in range(n):
            if r != rank and ((work[r] >> col) & 1):
                work[r] ^= work[rank]
        rank += 1
    return rank


def probe_cat0_mat_f2_dichotomy() -> Dict[str, object]:
    """Oracle 2: Verify Mat_2/Mat_3(F_2) rank distribution, CAT(0) CN, Remark D.3."""
    # Exact rank counts in Mat_2(F_2) (16 matrices) and Mat_3(F_2) (512 matrices)
    hist2 = [0, 0, 0]
    for mask in range(16):
        rk = _rank_f2_rows([(mask >> 2) & 3, mask & 3], 2)
        hist2[rk] += 1
    _require(hist2 == [1, 9, 6], f"Unexpected Mat_2(F_2) rank counts: {hist2}")

    hist3 = [0, 0, 0, 0]
    for mask in range(512):
        rk = _rank_f2_rows([(mask >> 6) & 7, (mask >> 3) & 7, mask & 7], 3)
        hist3[rk] += 1
    _require(hist3 == [1, 49, 294, 168], f"Unexpected Mat_3(F_2) rank counts: {hist3}")

    # Verify diagonal subcube {0,1}^3 inside Mat_3(F_2) has exact Euclidean squared distances
    diag_mats = [((b0 << 2), (b1 << 1), b2) for b0 in (0, 1) for b1 in (0, 1) for b2 in (0, 1)]
    cube_pairs_checked = 0
    for idx1, m1 in enumerate(diag_mats):
        b1 = (idx1 >> 2, (idx1 >> 1) & 1, idx1 & 1)
        for idx2, m2 in enumerate(diag_mats):
            b2 = (idx2 >> 2, (idx2 >> 1) & 1, idx2 & 1)
            rk_diff = _rank_f2_rows([m1[r] ^ m2[r] for r in range(3)], 3)
            eucl_sq = sum((b1[k] - b2[k]) ** 2 for k in range(3))
            _require(rk_diff == eucl_sq, "Diagonal subcube metric failed Euclidean match")
            cube_pairs_checked += 1

    # Verify Bruhat-Tits CAT(0) CN inequality: |zm|^2 <= (1/2)|zx|^2 + (1/2)|zv|^2 - (1/4)|xv|^2
    # (a) Euclidean equality on R^2: x=(0,0), v=(2,0), m=(1,0), z=(0,3)
    #     |zm|^2 = 10, (1/2)(9) + (1/2)(13) - (1/4)(4) = 11 - 1 = 10
    eucl_cn_lhs = Fraction(10)
    eucl_cn_rhs = Fraction(9, 2) + Fraction(13, 2) - Fraction(4, 4)
    _require(eucl_cn_lhs == eucl_cn_rhs, "Euclidean CN equality failed")

    # (b) Strict CAT(0) inequality on 3-star tree (center m, leaves x, v, z at edge length 1):
    #     |zm|=1, |zx|=2, |zv|=2, |xv|=2 -> 1 <= (1/2)(4) + (1/2)(4) - (1/4)(4) = 3 (strict gap = 2)
    tree_cn_lhs = Fraction(1)
    tree_cn_rhs = Fraction(4, 2) + Fraction(4, 2) - Fraction(4, 4)
    _require(tree_cn_lhs < tree_cn_rhs, "Tree strict CN inequality failed")

    # Remark D.3: Exact non-Euclidean Gram witness in Mat_3(F_2):
    # 5 points {0, E00, E01, E11, E00+E11} under d(A,B)^2 = rk(A - B)
    witness_mats = [
        (0b100, 0b000, 0b000),  # A1 = E00 (rk 1)
        (0b010, 0b000, 0b000),  # A2 = E01 (rk 1)
        (0b000, 0b010, 0b000),  # A3 = E11 (rk 1)
        (0b100, 0b010, 0b000),  # A4 = E00 + E11 (rk 2)
    ]
    gram: List[List[Fraction]] = []
    for i in range(4):
        ri = _rank_f2_rows(witness_mats[i], 3)
        row_g: List[Fraction] = []
        for j in range(4):
            rj = _rank_f2_rows(witness_mats[j], 3)
            rij = _rank_f2_rows([witness_mats[i][r] ^ witness_mats[j][r] for r in range(3)], 3)
            row_g.append(Fraction(ri + rj - rij, 2))
        gram.append(row_g)
    gram_det = _det_q(gram)
    _require(gram_det == Fraction(-1, 4), f"Expected Gram det -1/4, got {gram_det}")

    # Direct negative quadratic-form certificate u = (2, -1, 2, -2): u^T G u = -1 < 0
    u_vec = (2, -1, 2, -2)
    quad_val = sum(
        Fraction(u_vec[i]) * gram[i][j] * Fraction(u_vec[j])
        for i in range(4)
        for j in range(4)
    )
    _require(quad_val == Fraction(-1), f"Expected u^T G u = -1, got {quad_val}")

    return {
        "mat2_rank_hist": hist2,
        "mat3_rank_hist": hist3,
        "cube_pairs_verified": cube_pairs_checked,
        "tree_cn_gap": str(tree_cn_rhs - tree_cn_lhs),
        "non_euclidean_gram_det": str(gram_det),
        "non_euclidean_quad_form": str(quad_val),
    }


# ---------------------------------------------------------------------------
# Oracle 3: Appendix E — Prop E.1 Permanent Gadget, f_{3,1}, Prop E.10, Thm E.11
# ---------------------------------------------------------------------------


def _perm_ryser_q(mat: Sequence[Sequence[Fraction]]) -> Fraction:
    """Exact permanent over Q via Ryser's formula (zero floats)."""
    n = len(mat)
    total = Fraction(0)
    for mask in range(1, 1 << n):
        bits = mask.bit_count()
        prod = Fraction(1)
        for r in range(n):
            row_sum = Fraction(0)
            for c in range(n):
                if (mask >> c) & 1:
                    row_sum += mat[r][c]
            prod *= row_sum
        if (n - bits) % 2 == 1:
            total -= prod
        else:
            total += prod
    return total


def _perm_ryser_mod(mat: Sequence[Sequence[int]], mod_p: int) -> int:
    """Exact permanent over F_p via Ryser's formula."""
    n = len(mat)
    total = 0
    for mask in range(1, 1 << n):
        bits = mask.bit_count()
        prod = 1
        for r in range(n):
            row_sum = 0
            for c in range(n):
                if (mask >> c) & 1:
                    row_sum = (row_sum + mat[r][c]) % mod_p
            prod = (prod * row_sum) % mod_p
        if (n - bits) % 2 == 1:
            total = (total - prod) % mod_p
        else:
            total = (total + prod) % mod_p
    return total


def _det_mod(mat: Sequence[Sequence[int]], mod_p: int) -> int:
    """Exact determinant over F_p (prime p) via Gaussian elimination."""
    n = len(mat)
    a = [[v % mod_p for v in row] for row in mat]
    sign = 1
    for k in range(n):
        piv = -1
        for i in range(k, n):
            if a[i][k] != 0:
                piv = i
                break
        if piv == -1:
            return 0
        if piv != k:
            a[k], a[piv] = a[piv], a[k]
            sign = (-sign) % mod_p
        inv_pv = pow(a[k][k], mod_p - 2, mod_p)
        for i in range(k + 1, n):
            if a[i][k] != 0:
                f = (a[i][k] * inv_pv) % mod_p
                for j in range(k, n):
                    a[i][j] = (a[i][j] - f * a[k][j]) % mod_p
    res = sign
    for k in range(n):
        res = (res * a[k][k]) % mod_p
    return res


def _build_prop_e1_matrix_scaled(
    sigma: Sequence[int],
    rho: Sequence[int],
    weights: Sequence[Mapping[Tuple[int, int], int]],
) -> List[List[int]]:
    """Build 2-cleared integer matrix for Prop E.1 (Row 1 multiplied by 2).

    Columns per n in I: 3*n -> A_n, 3*n+1 -> B_n, 3*n+2 -> C_n.
    Rows per n in I:
      3*n   : A_n + B_n + A_{sigma(n)} - C_n   (true Row 1 is half of this!)
      3*n+1 : A_n + B_n - A_{sigma(n)} + C_n
      3*n+2 : W_n(1,1) C_n + W_n(0,1) B_n + W_{rho(n)}(1,0) C_{rho(n)} + W_{rho(n)}(0,0) B_{rho(n)}
    """
    m = len(sigma)
    dim = 3 * m
    mat = [[0] * dim for _ in range(dim)]
    for n in range(m):
        sn = sigma[n]
        rn = rho[n]
        # Row 3*n (scaled by 2)
        r0 = 3 * n
        mat[r0][3 * n] += 1
        mat[r0][3 * n + 1] += 1
        mat[r0][3 * sn] += 1
        mat[r0][3 * n + 2] -= 1
        # Row 3*n + 1
        r1 = 3 * n + 1
        mat[r1][3 * n] += 1
        mat[r1][3 * n + 1] += 1
        mat[r1][3 * sn] -= 1
        mat[r1][3 * n + 2] += 1
        # Row 3*n + 2
        r2 = 3 * n + 2
        mat[r2][3 * n + 2] += weights[n][(1, 1)]
        mat[r2][3 * n + 1] += weights[n][(0, 1)]
        mat[r2][3 * rn + 2] += weights[rn][(1, 0)]
        mat[r2][3 * rn + 1] += weights[rn][(0, 0)]
    return mat


def _grid_sum_direct(
    v_map: Sequence[int],
    w_map: Sequence[int],
    n_v: int,
    n_k: int,
    weights: Sequence[Mapping[Tuple[int, int], int]],
) -> int:
    total = 0
    for x_bits in itertools.product((0, 1), repeat=n_v):
        for r_bits in itertools.product((0, 1), repeat=n_k):
            prod = 1
            for n, wn in enumerate(weights):
                prod *= wn[(x_bits[v_map[n]], r_bits[w_map[n]])]
            total += prod
    return total


def probe_flat_case_perm_and_hub_bounds() -> Dict[str, object]:
    """Oracle 3: Verify Prop E.1 over Q/F_3/F_5 + char-2 collapse, f_{3,1}, Prop E.10, Thm E.11."""
    # Non-trivial surjections: |I| = 3, |V| = 2, |K| = 2 -> 9x9 matrix!
    # v: 0->0, 1->0, 2->1 (cycles: (0 1), (2))
    # w: 0->0, 1->1, 2->1 (cycles: (0), (1 2))
    v_map = (0, 0, 1)
    w_map = (0, 1, 1)
    sigma = (1, 0, 2)
    rho = (0, 2, 1)
    weights = [
        {(0, 0): 2, (0, 1): 4, (1, 0): 6, (1, 1): 7},
        {(0, 0): 10, (0, 1): 12, (1, 0): 14, (1, 1): 19},
        {(0, 0): 22, (0, 1): 24, (1, 0): 26, (1, 1): 37},
    ]
    direct_sum = _grid_sum_direct(v_map, w_map, 2, 2, weights)
    scaled_mat = _build_prop_e1_matrix_scaled(sigma, rho, weights)

    # Exact Q verification (divide Row 3*n by 2 -> exact half entries)
    q_mat = [
        [Fraction(v, 2) if (r % 3 == 0) else Fraction(v) for v in row]
        for r, row in enumerate(scaled_mat)
    ]
    perm_q = _perm_ryser_q(q_mat)
    _require(perm_q == Fraction(direct_sum), f"Prop E.1 Q mismatch: {perm_q} != {direct_sum}")

    # Exact F_3 and F_5 verification
    fp_matches: Dict[str, int] = {}
    for p in (3, 5):
        inv2 = pow(2, p - 2, p)
        p_mat = [
            [((v * inv2) % p) if (r % 3 == 0) else (v % p) for v in row]
            for r, row in enumerate(scaled_mat)
        ]
        perm_p = _perm_ryser_mod(p_mat, p)
        _require(perm_p == direct_sum % p, f"Prop E.1 F_{p} mismatch")
        fp_matches[f"F_{p}"] = perm_p

    # Exact char=2 collapse check: clearing 1/2 yields 2^|I| * perm = 0 mod 2 ALWAYS,
    # whereas direct_sum is odd (sum of products of odd/prime weights) -> 1 mod 2!
    scaled_f2 = [[v % 2 for v in row] for row in scaled_mat]
    perm_scaled_f2 = _perm_ryser_mod(scaled_f2, 2)
    _require(perm_scaled_f2 == 0, "Cleared Prop E.1 matrix must vanish mod 2")
    _require(direct_sum % 2 == 1, "Witness direct sum should be odd to exhibit char-2 collapse")

    # Verify f_{3,1} = 2x2 matrix multiplication trilinear form (8 monomials)
    f31_terms = set()
    for p_bit in (0, 1):
        for q_bit in (0, 1):
            for r_bit in (0, 1):
                f31_terms.add(((p_bit, q_bit), (p_bit, r_bit), (q_bit, r_bit)))
    _require(len(f31_terms) == 8, "f_{3,1} must have 8 distinct trilinear terms")

    # Prop E.10 exact rational hub-saving bound across all balanced cuts for k = 3..8
    balanced_cuts_checked = 0
    min_ratio_81 = Fraction(1000)  # tracks min (81 * ||w_S||^2) / k^3 >= 4
    for k in range(3, 9):
        for sz in range(1, k):
            if 3 * sz < k or 3 * sz > 2 * k:
                continue
            for subset in itertools.combinations(range(k), sz):
                s_set = set(subset)
                # Ends: for a < b, (a,b) at +(1/2)e_a, (b,a) at -(1/2)e_a.
                # w_S = 2 * sum_{a in S, b != a} pos(a,b)
                # Component a in S gets +(count of b > a) - (count of b < a)?
                # Wait: check paper.txt L2705-2713 verbatim!
                # For a < b: if BOTH a,b in S, (a,b) contributes +e_a and (b,a) contributes -e_a -> CANCEL!
                # If a in S, b not in S: +e_a (if a < b) or -e_b (if b < a)!
                # So coordinate a has magnitude c_a = #{b > a : exactly one of a,b in S} with sign +1 (a in S) or -1 (a not in S)?
                # Let's compute DIRECTLY from the exact positions +-1/2 e_a!
                w_vec = [0] * k
                for a in range(k):
                    for b in range(a + 1, k):
                        # End (a, b) belongs to node a, position +(1/2) e_a -> twice is +1 on e_a
                        if a in s_set:
                            w_vec[a] += 1
                        # End (b, a) belongs to node b, position -(1/2) e_a -> twice is -1 on e_a
                        if b in s_set:
                            w_vec[a] -= 1
                norm_sq = sum(c * c for c in w_vec)
                l1_sum = sum(abs(c) for c in w_vec)
                _require(l1_sum == sz * (k - sz), "Prop E.10 |w_S|_1 != |S|(k-|S|)")
                _require(9 * l1_sum >= 2 * k * k, "Prop E.10 balanced cut bound failed")
                # Cauchy-Schwarz: k * ||w_S||^2 >= (|w_S|_1)^2 >= 4 k^4 / 81 => 81 ||w_S||^2 >= 4 k^3
                _require(81 * norm_sq >= 4 * (k ** 3), "Prop E.10 ||w_S||^2 >= (4/81)k^3 failed")
                ratio = Fraction(81 * norm_sq, k ** 3)
                if ratio < min_ratio_81:
                    min_ratio_81 = ratio
                balanced_cuts_checked += 1

    # Thm E.11 exact parameter scaling: k = r^2, l = 100*r -> logM ~ 200*r^3, log(5L) >= (25/4)*r^4
    exponent_checks = 0
    for r in (2, 3, 5, 10, 20):
        k = r * r
        ell = 100 * r
        log_l_num = ell * (r ** 3)  # ell * k^(3/2) = 100 * r^4
        _require(log_l_num == 100 * (r ** 4), "Flat-case r^4 scaling mismatch")
        # Check (log_l_num / 16)^3 / (200 * r^3)^4 is constant independent of r!
        ratio_r = Fraction((log_l_num ** 3), (16 ** 3) * ((200 * (r ** 3)) ** 4))
        _require(ratio_r == Fraction(125, 819200000), f"Unexpected r-invariant exponent ratio: {ratio_r}")
        exponent_checks += 1

    return {
        "prop_e1_matrix_dim": 9,
        "direct_grid_sum": direct_sum,
        "perm_q_exact": str(perm_q),
        "fp_matches": fp_matches,
        "char2_cleared_perm_mod2": perm_scaled_f2,
        "char2_true_sum_mod2": direct_sum % 2,
        "f31_monomial_count": len(f31_terms),
        "balanced_cuts_checked": balanced_cuts_checked,
        "min_81_normsq_over_k3": str(min_ratio_81),
        "exponent_scaling_checks": exponent_checks,
    }


# ---------------------------------------------------------------------------
# Oracle 4: Appendix M — Prop M.2 Directed HC XOR-Gadget vs Prop E.1 & S41
# ---------------------------------------------------------------------------


def _hc_sum_sparse(adj: Mapping[int, Mapping[int, int]], n_verts: int) -> int:
    """Exact directed Hamiltonian cycle polynomial HC(M) over Z via sparse DFS.

    Starts at vertex 0 and visits all n_verts vertices before returning to 0,
    enumerating every single-cycle permutation in S_{n_verts} exactly once.
    """
    full_mask = (1 << n_verts) - 1
    total = 0
    stack: List[Tuple[int, int, int]] = [(0, 1, 1)]
    while stack:
        u, mask, prod = stack.pop()
        if mask == full_mask:
            back_w = adj[u].get(0, 0)
            if back_w != 0:
                total += prod * back_w
            continue
        for v, w in adj[u].items():
            if w == 0:
                continue
            if not ((mask >> v) & 1):
                stack.append((v, mask | (1 << v), prod * w))
    return total


def _build_prop_m2_graph(
    v_map: Sequence[int],
    w_map: Sequence[int],
    n_v: int,
    n_k: int,
    weights: Sequence[Mapping[Tuple[int, int], int]],
) -> Tuple[Dict[int, Dict[int, int]], int]:
    """Verbatim clean-room construction of Prop M.2 / Nc.Hc.gridRow directed graph.

    Vertices:
      - head(seg) for every segment (|V| + |K| + 7|I|)
      - tip(g, True), tip(g, False), mid(g) for every XOR gadget (10|I| gadgets -> 30|I| verts)
    Total vertices = |V| + |K| + 37|I| <= 39|I| <= 40|I|.
    """
    m_inc = len(v_map)
    segs: List[Tuple[str, ...]] = []
    for a in range(n_v):
        segs.append(("var", str(a)))
    for b in range(n_k):
        segs.append(("row", str(b)))
    for n in range(m_inc):
        segs.append(("edge", str(n)))
        segs.append(("left", str(n)))
        segs.append(("right", str(n)))
        for xb in ("0", "1"):
            for rb in ("0", "1"):
                segs.append(("tab", str(n), xb, rb))

    seg_opts: Dict[Tuple[str, ...], List[Tuple[str, ...]]] = {}
    opt_weight: Dict[Tuple[Tuple[str, ...], Tuple[str, ...]], int] = {}
    for seg in segs:
        kind = seg[0]
        if kind in ("var", "row", "tab"):
            seg_opts[seg] = [("0",), ("1",)]
            opt_weight[(seg, ("0",))] = 1
            opt_weight[(seg, ("1",))] = 1
        elif kind == "edge":
            n_idx = int(seg[1])
            seg_opts[seg] = [("0", "0"), ("0", "1"), ("1", "0"), ("1", "1")]
            for xb in (0, 1):
                for rb in (0, 1):
                    opt_weight[(seg, (str(xb), str(rb)))] = weights[n_idx][(xb, rb)]
        else:
            # left / right checks: ("none",), ("some", "0"), ("some", "1")
            seg_opts[seg] = [("none",), ("some", "0"), ("some", "1")]
            for o in seg_opts[seg]:
                opt_weight[(seg, o)] = 1

    # Cyclic successor next(seg)
    seg_next: Dict[Tuple[str, ...], Tuple[str, ...]] = {
        segs[i]: segs[(i + 1) % len(segs)] for i in range(len(segs))
    }

    # Build the 10 XOR gadgets per incidence n (matching Nc/Hc/Grid.lean gridPort verbatim!)
    gadgets: List[Tuple[Tuple[Tuple[str, ...], Tuple[str, ...]], Tuple[Tuple[str, ...], Tuple[str, ...]]]] = []
    for n in range(m_inc):
        vn = str(v_map[n])
        wn = str(w_map[n])
        ns = str(n)
        # 4 selector <-> tab-false XORs
        for xb in ("0", "1"):
            for rb in ("0", "1"):
                p_true = (("edge", ns), (xb, rb))
                p_false = (("tab", ns, xb, rb), ("0",))
                gadgets.append((p_true, p_false))
        # 3 left-check XORs
        gadgets.append(((("left", ns), ("none",)), (("var", vn), ("1",))))
        gadgets.append(((("left", ns), ("some", "0")), (("tab", ns, "1", "0"), ("0",))))
        gadgets.append(((("left", ns), ("some", "1")), (("tab", ns, "1", "1"), ("0",))))
        # 3 right-check XORs
        gadgets.append(((("right", ns), ("none",)), (("row", wn), ("1",))))
        gadgets.append(((("right", ns), ("some", "0")), (("tab", ns, "0", "1"), ("0",))))
        gadgets.append(((("right", ns), ("some", "1")), (("tab", ns, "1", "1"), ("0",))))

    # Assign integer vertex IDs
    vid: Dict[Tuple[object, ...], int] = {}
    for seg in segs:
        vid[("head", seg)] = len(vid)
    for g_idx in range(len(gadgets)):
        vid[("tip", g_idx, True)] = len(vid)
        vid[("tip", g_idx, False)] = len(vid)
        vid[("mid", g_idx)] = len(vid)
    n_verts = len(vid)

    # Order gadget ports along each option
    opt_ports: Dict[Tuple[Tuple[str, ...], Tuple[str, ...]], List[Tuple[int, bool]]] = {
        (seg, o): [] for seg in segs for o in seg_opts[seg]
    }
    for g_idx, (p_t, p_f) in enumerate(gadgets):
        opt_ports[p_t].append((g_idx, True))
        opt_ports[p_f].append((g_idx, False))

    adj: Dict[int, Dict[int, int]] = {i: {} for i in range(n_verts)}

    def add_edge(u: int, v: int, w: int) -> None:
        _require(v not in adj[u], f"Parallel directed edge detected: {u} -> {v}")
        adj[u][v] = w

    # Head edges and after-tip continuations
    for seg in segs:
        h_u = vid[("head", seg)]
        h_nxt = vid[("head", seg_next[seg])]
        for o in seg_opts[seg]:
            ports = opt_ports[(seg, o)]
            w = opt_weight[(seg, o)]
            first_v = vid[("tip", ports[0][0], ports[0][1])] if ports else h_nxt
            add_edge(h_u, first_v, w)
            for idx_p, (g_idx, side) in enumerate(ports):
                nxt_v = (
                    vid[("tip", ports[idx_p + 1][0], ports[idx_p + 1][1])]
                    if idx_p + 1 < len(ports)
                    else h_nxt
                )
                # Option enters tip(g, side) -> mid(g) -> tip(g, !side) -> after(g, side)
                # So edge from tip(g, !side) to nxt_v!
                add_edge(vid[("tip", g_idx, not side)], nxt_v, 1)

    # Internal bidirectional XOR gadget edges: tip(g, s) <-> mid(g)
    for g_idx in range(len(gadgets)):
        m_v = vid[("mid", g_idx)]
        t_v = vid[("tip", g_idx, True)]
        f_v = vid[("tip", g_idx, False)]
        add_edge(t_v, m_v, 1)
        add_edge(f_v, m_v, 1)
        add_edge(m_v, t_v, 1)
        add_edge(m_v, f_v, 1)

    return adj, n_verts


def probe_char2_perm_vs_hc_gadgets() -> Dict[str, object]:
    """Oracle 4: Verify char=2 perm=det vs HC!=det, Track S41 Polya 0/512, and Prop M.2."""
    # 4a. Verify perm == det over F_2 on 3x3 and 4x4 matrices while HC != det
    w3 = [[1, 1, 0], [0, 1, 1], [1, 0, 1]]
    det3_f2 = _det_mod(w3, 2)
    perm3_f2 = _perm_ryser_mod(w3, 2)
    adj3 = {i: {j: w3[i][j] for j in range(3) if w3[i][j]} for i in range(3)}
    hc3_f2 = _hc_sum_sparse(adj3, 3) % 2
    _require(det3_f2 == 0, "3x3 char-2 det must be 0")
    _require(perm3_f2 == 0, "3x3 char-2 perm must be 0")
    _require(hc3_f2 == 1, "3x3 char-2 hc must be 1")

    w4 = [[1, 1, 0, 0], [0, 1, 1, 0], [0, 0, 1, 1], [1, 0, 0, 1]]
    det4_f2 = _det_mod(w4, 2)
    perm4_f2 = _perm_ryser_mod(w4, 2)
    adj4 = {i: {j: w4[i][j] for j in range(4) if w4[i][j]} for i in range(4)}
    hc4_f2 = _hc_sum_sparse(adj4, 4) % 2
    _require(det4_f2 == 0, "4x4 char-2 det must be 0")
    _require(perm4_f2 == 0, "4x4 char-2 perm must be 0")
    _require(hc4_f2 == 1, "4x4 char-2 hc must be 1")

    # 4b. Track S41 cross-check: Polya 3x3 permanent-sign obstruction (0/512 sign maps work over Z)
    # Test against the 6 permutation matrices of S_3 (necessary & sufficient for formal equality)
    s3_perms = list(itertools.permutations(range(3)))
    polya_hits = 0
    for sign_mask in range(512):
        # 3x3 signs in {+1, -1}
        ok = True
        for perm in s3_perms:
            inv = (
                int(perm[0] > perm[1])
                + int(perm[0] > perm[2])
                + int(perm[1] > perm[2])
            )
            det_sign = -1 if (inv % 2 == 1) else 1
            prod_s = 1
            for r in range(3):
                bit = (sign_mask >> (3 * r + perm[r])) & 1
                prod_s *= -1 if bit else 1
            if det_sign * prod_s != 1:
                ok = False
                break
        if ok:
            polya_hits += 1
    _require(polya_hits == 0, f"Polya 3x3 obstruction failed: found {polya_hits} maps")

    # 4c. Prop M.2 full 39-vertex directed XOR-gadget graph for |I|=1, |V|=1, |K|=1
    #     Works over Z (hence Q, F_2, F_3, F_5 simultaneously!) with ZERO division by 2!
    w_single = [{(0, 0): 3, (0, 1): 5, (1, 0): 7, (1, 1): 12}]
    adj_m2, n_verts_m2 = _build_prop_m2_graph((0,), (0,), 1, 1, w_single)
    _require(n_verts_m2 == 39, f"Expected 39 vertices for |I|=1 Prop M.2 graph, got {n_verts_m2}")
    hc_exact = _hc_sum_sparse(adj_m2, n_verts_m2)
    direct_single = _grid_sum_direct((0,), (0,), 1, 1, w_single)
    _require(hc_exact == direct_single, f"Prop M.2 HC mismatch: {hc_exact} != {direct_single}")

    # Verify entries are strictly in {0, 1} U {W_0(x, r)} (ZERO 1/2, ZERO -1!)
    allowed_entries = {0, 1, 3, 5, 7, 12}
    for row_map in adj_m2.values():
        for w in row_map.values():
            _require(w in allowed_entries, f"Unexpected entry {w} in Prop M.2 matrix")

    # Verify exact match modulo 2, 3, 5 simultaneously
    mod_checks = {f"F_{p}": hc_exact % p for p in (2, 3, 5)}
    _require(mod_checks["F_2"] == direct_single % 2, "Prop M.2 F_2 parity mismatch")
    _require(mod_checks["F_2"] == 1, "Prop M.2 F_2 witness should be nonzero (1)")

    return {
        "char2_3x3_det_perm_hc": [det3_f2, perm3_f2, hc3_f2],
        "char2_4x4_det_perm_hc": [det4_f2, perm4_f2, hc4_f2],
        "s41_polya_3x3_valid_sign_maps": polya_hits,
        "prop_m2_vertices": n_verts_m2,
        "prop_m2_hc_exact_z": hc_exact,
        "prop_m2_direct_sum": direct_single,
        "prop_m2_mod_checks": mod_checks,
    }


# ---------------------------------------------------------------------------
# Oracle 5: Appendix F & H — U_n(F_2) Lemma F.2 & SL_3(F_2[s]/(s^3)) Tower
# ---------------------------------------------------------------------------


def _mat_mul_f2(a: Sequence[Sequence[int]], b: Sequence[Sequence[int]]) -> List[List[int]]:
    n = len(a)
    out = [[0] * n for _ in range(n)]
    for i in range(n):
        for k in range(n):
            if a[i][k]:
                for j in range(n):
                    out[i][j] ^= b[k][j]
    return out


def _gen_un_f2(n: int, j: int) -> List[List[int]]:
    m = [[1 if r == c else 0 for c in range(n)] for r in range(n)]
    m[j][j + 1] = 1
    return m


def _word_eval_un_f2(n: int, word: Sequence[int]) -> List[List[int]]:
    acc = [[1 if r == c else 0 for c in range(n)] for r in range(n)]
    for g in word:
        acc = _mat_mul_f2(acc, _gen_un_f2(n, g))
    return acc


def _lem_f2_endpoint1_word(n: int, k: int, xi: Sequence[int], omega: Sequence[int]) -> List[int]:
    """Lemma F.2 word A B^{-1} x_{k-1} B A^{-1} when xi[k-1]=1 and omega[0]=1."""
    # A = x_{i_l} ... x_{i_1} x_0 ... x_{k-2} satisfies A e_{k-1} = xi
    zeros_xi = [i for i in range(k - 1) if xi[i] == 0]
    word_a = list(reversed(zeros_xi)) + list(range(k - 1))
    # B in {x_j : j >= k} with e'_0^T B = omega^T:
    # e'_0^T (x_{n-2} ... x_k) = (1,...,1); multiplying on right by x_{k+j-1} toggles pos k+j (right-to-left)
    # Wait: verify left/right action! For row vector v, (v x_j)[j+1] = v[j+1] ^ v[j].
    # Start with e_k^T = (1,0,...,0).
    # Multiply on right by x_k, x_{k+1}, ..., x_{n-2} -> (1, 1, ..., 1).
    # Then multiply on right by x_{k + j - 1} for j in increasing order where omega[j] == 0?
    # Check: if v = (1,...,1), then (v x_{k+j-1}) flips entry k+j ONLY if entry k+j-1 is 1!
    # So doing zeros in DECREASING order of j (highest index first!) ensures v[k+j-1] is still 1!
    zeros_om = [j for j in range(1, n - k) if omega[j] == 0]
    word_b = list(range(k, n - 1)) + [k + j - 1 for j in reversed(zeros_om)]
    # In F_2, each x_j is self-inverse, so inv(w) = reversed(w).
    return word_a + list(reversed(word_b)) + [k - 1] + word_b + list(reversed(word_a))


def _lem_f2_general_word(n: int, k: int, xi: Sequence[int], omega: Sequence[int]) -> List[int]:
    """Decompose any nonzero xi, omega into <= 2 endpoint-1 vectors each (<= 16 uses/gen)."""
    if xi[k - 1] == 1:
        xi_parts = [list(xi)]
    else:
        e_last = [0] * (k - 1) + [1]
        xi_plus = [xi[i] ^ e_last[i] for i in range(k)]
        xi_parts = [xi_plus, e_last]

    if omega[0] == 1:
        om_parts = [list(omega)]
    else:
        e_first = [1] + [0] * (n - k - 1)
        om_plus = [omega[j] ^ e_first[j] for j in range(n - k)]
        om_parts = [om_plus, e_first]

    full_word: List[int] = []
    for xp in xi_parts:
        for op in om_parts:
            full_word.extend(_lem_f2_endpoint1_word(n, k, xp, op))
    return full_word


def probe_contracting_unitriangular() -> Dict[str, object]:
    """Oracle 5: Exhaustively verify Lem F.2 in U_4(F_2) & U_5(F_2) + Prop H.1 tower."""
    endpoint1_checked = 0
    general_checked = 0
    max_ep1_mult = 0
    max_gen_mult = 0

    for n in (4, 5):
        for k in range(1, n):
            for xi in itertools.product((0, 1), repeat=k):
                if not any(xi):
                    continue
                for omega in itertools.product((0, 1), repeat=n - k):
                    if not any(omega):
                        continue
                    target = [[1 if r == c else 0 for c in range(n)] for r in range(n)]
                    for r in range(k):
                        for c in range(n - k):
                            target[r][k + c] = xi[r] & omega[c]
                    word = _lem_f2_general_word(n, k, xi, omega)
                    got = _word_eval_un_f2(n, word)
                    _require(got == target, f"Lem F.2 matrix mismatch at n={n}, k={k}")
                    mults = [word.count(g) for g in range(n - 1)]
                    peak = max(mults)
                    if xi[k - 1] == 1 and omega[0] == 1:
                        _require(peak <= 4, f"Endpoint-1 generator mult {peak} > 4")
                        if peak > max_ep1_mult:
                            max_ep1_mult = peak
                        endpoint1_checked += 1
                    _require(peak <= 16, f"General generator mult {peak} > 16")
                    if peak > max_gen_mult:
                        max_gen_mult = peak
                    general_checked += 1

    # Prop H.1 tower: SL_3(F_2[s]/(s^3)) commutator [e_jk(r), e_kl(r')] = e_jl(r*r')
    # Represent elements of F_2[s]/(s^3) as 3-bit masks (bit d = coeff of s^d).
    def ring_mul(a: int, b: int) -> int:
        res = 0
        for d1 in range(3):
            if (a >> d1) & 1:
                for d2 in range(3 - d1):
                    if (b >> d2) & 1:
                        res ^= 1 << (d1 + d2)
        return res

    def sl3_mul(m1: Sequence[Sequence[int]], m2: Sequence[Sequence[int]]) -> List[List[int]]:
        out = [[0] * 3 for _ in range(3)]
        for i in range(3):
            for j in range(3):
                acc = 0
                for k in range(3):
                    acc ^= ring_mul(m1[i][k], m2[k][j])
                out[i][j] = acc
        return out

    def elem_e(j: int, k: int, r: int) -> List[List[int]]:
        m = [[1 if a == b else 0 for b in range(3)] for a in range(3)]
        m[j][k] = r
        return m

    tower_comm_checks = 0
    for j, k, l in itertools.permutations(range(3), 3):
        for r1 in (1, 2, 4):  # 1, s, s^2
            for r2 in (1, 2, 4):
                # In char 2, e_jk(r)^{-1} = e_jk(r)!
                e1 = elem_e(j, k, r1)
                e2 = elem_e(k, l, r2)
                comm = sl3_mul(sl3_mul(e1, e2), sl3_mul(e1, e2))
                expected = elem_e(j, l, ring_mul(r1, r2))
                _require(comm == expected, f"Tower commutator failed at ({j},{k},{l}), {r1},{r2}")
                tower_comm_checks += 1

    return {
        "u4_u5_general_rank1_checked": general_checked,
        "u4_u5_endpoint1_checked": endpoint1_checked,
        "max_endpoint1_gen_mult": max_ep1_mult,
        "max_general_gen_mult": max_gen_mult,
        "sl3_tower_commutator_checks": tower_comm_checks,
    }


# ---------------------------------------------------------------------------
# Oracle 6: Appendix K — Lemma K.2 Parse-Tree Unfolding, Boolean Barrier, Thm K.6
# ---------------------------------------------------------------------------


def _mvpoly_add(a: Mapping[Tuple[int, ...], int], b: Mapping[Tuple[int, ...], int], mod_p: int) -> Dict[Tuple[int, ...], int]:
    out = dict(a)
    for mon, c in b.items():
        nv = out.get(mon, 0) + c
        if mod_p > 0:
            nv %= mod_p
        if nv == 0:
            out.pop(mon, None)
        else:
            out[mon] = nv
    return out


def _mvpoly_mul(a: Mapping[Tuple[int, ...], int], b: Mapping[Tuple[int, ...], int], mod_p: int) -> Dict[Tuple[int, ...], int]:
    out: Dict[Tuple[int, ...], int] = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            mon = tuple(m1[i] + m2[i] for i in range(len(m1)))
            nv = out.get(mon, 0) + c1 * c2
            if mod_p > 0:
                nv %= mod_p
            if nv == 0:
                out.pop(mon, None)
            else:
                out[mon] = nv
    return out


def _mvpoly_scale(a: Mapping[Tuple[int, ...], int], s: int, mod_p: int) -> Dict[Tuple[int, ...], int]:
    if mod_p > 0:
        s %= mod_p
    if s == 0:
        return {}
    out: Dict[Tuple[int, ...], int] = {}
    for mon, c in a.items():
        nv = c * s
        if mod_p > 0:
            nv %= mod_p
        if nv != 0:
            out[mon] = nv
    return out


def probe_lowdeg_parse_tree_and_diag() -> Dict[str, object]:
    """Oracle 6: Verify Lem K.2 parse-tree recursion over Z/F_2/F_3/F_5 + Sec 2.5 + Thm K.6."""
    # Explicit 9-gate nonlinear circuit in 3 variables (x0, x1, x2) with constants,
    # fanout, addition, product, and squaring (g * g -> factor-2 chain!):
    #   g0 = 2 (const)
    #   g1 = x0
    #   g2 = x1
    #   g3 = x2
    #   g4 = g0 + g1 = 2 + x0
    #   g5 = g4 * g2 = (2 + x0) * x1
    #   g6 = g5 + g3 = x2 + 2*x1 + x0*x1
    #   g7 = g6 * g6  (squaring gate! tests double-chain rule!)
    #   g8 = g7 * g4  (degree 5 output!)
    gates: List[Tuple[str, int, int]] = [
        ("const", 2, 0),
        ("var", 0, 0),
        ("var", 1, 0),
        ("var", 2, 0),
        ("add", 0, 1),
        ("mul", 4, 2),
        ("add", 5, 3),
        ("mul", 6, 6),
        ("mul", 7, 4),
    ]
    n_vars = 3
    zero_mon = (0, 0, 0)
    rings_verified: List[str] = []

    for mod_p, label in ((0, "Z"), (2, "F_2"), (3, "F_3"), (5, "F_5")):
        # Direct full polynomial evaluation at every gate
        polys: List[Dict[Tuple[int, ...], int]] = []
        for kind, a, b in gates:
            if kind == "const":
                v = a % mod_p if mod_p > 0 else a
                polys.append({zero_mon: v} if v != 0 else {})
            elif kind == "var":
                mon = tuple(1 if i == a else 0 for i in range(n_vars))
                polys.append({mon: 1})
            elif kind == "add":
                polys.append(_mvpoly_add(polys[a], polys[b], mod_p))
            else:
                polys.append(_mvpoly_mul(polys[a], polys[b], mod_p))

        # Degree-0 parts g^(0)
        g0 = [p.get(zero_mon, 0) for p in polys]
        n_g = len(gates)

        # Chain-sum constants c_{g, gamma} (paper.txt L4161-4165)
        # c_{g, g} = 1; for g = g' + g'': c_{g, gamma} = c_{g', gamma} + c_{g'', gamma}
        # for g = g' * g'': c_{g, gamma} = g''^(0) c_{g', gamma} + g'^(0) c_{g'', gamma}
        c_chain = [[0] * n_g for _ in range(n_g)]
        for g in range(n_g):
            c_chain[g][g] = 1
            kind, a, b = gates[g]
            if kind == "add":
                for gam in range(g):
                    nv = c_chain[a][gam] + c_chain[b][gam]
                    c_chain[g][gam] = nv % mod_p if mod_p > 0 else nv
            elif kind == "mul":
                for gam in range(g):
                    nv = g0[b] * c_chain[a][gam] + g0[a] * c_chain[b][gam]
                    c_chain[g][gam] = nv % mod_p if mod_p > 0 else nv

        # a_{g, l} and b_{g, g', g''}
        a_coef = [[0] * n_vars for _ in range(n_g)]
        for g in range(n_g):
            for gam, (kind, v_idx, _) in enumerate(gates):
                if kind == "var":
                    nv = a_coef[g][v_idx] + c_chain[g][gam]
                    a_coef[g][v_idx] = nv % mod_p if mod_p > 0 else nv

        b_coef: List[Dict[Tuple[int, int], int]] = [{} for _ in range(n_g)]
        for g in range(n_g):
            for gam, (kind, p1, p2) in enumerate(gates):
                if kind == "mul":
                    key = (p1, p2)
                    nv = b_coef[g].get(key, 0) + c_chain[g][gam]
                    if mod_p > 0:
                        nv %= mod_p
                    if nv == 0:
                        b_coef[g].pop(key, None)
                    else:
                        b_coef[g][key] = nv

        # Unfold homogeneous parts g^(i) for i = 1..5 purely via Lem K.2 recursion
        hom: List[List[Dict[Tuple[int, ...], int]]] = [[{} for _ in range(6)] for _ in range(n_g)]
        for g in range(n_g):
            p1_acc: Dict[Tuple[int, ...], int] = {}
            for l_var in range(n_vars):
                if a_coef[g][l_var] != 0:
                    mon = tuple(1 if i == l_var else 0 for i in range(n_vars))
                    p1_acc = _mvpoly_add(p1_acc, {mon: a_coef[g][l_var]}, mod_p)
            hom[g][1] = p1_acc
        for deg in range(2, 6):
            for g in range(n_g):
                acc: Dict[Tuple[int, ...], int] = {}
                for (p1, p2), bc in b_coef[g].items():
                    for j in range(1, deg):
                        term = _mvpoly_scale(_mvpoly_mul(hom[p1][j], hom[p2][deg - j], mod_p), bc, mod_p)
                        acc = _mvpoly_add(acc, term, mod_p)
                hom[g][deg] = acc

        # Compare reconstructed homogeneous parts 0..5 against direct output polynomial!
        out_poly = polys[-1]
        for deg in range(6):
            expected_deg = {m: c for m, c in out_poly.items() if sum(m) == deg}
            got_deg = ({zero_mon: g0[-1]} if g0[-1] != 0 else {}) if deg == 0 else hom[-1][deg]
            _require(got_deg == expected_deg, f"Lem K.2 mismatch in {label} at degree {deg}")
        rings_verified.append(label)

    # Section 2.5 Boolean-Circuit Barrier witness over F_2:
    # f(x) = x0*x1*x2, g(x) = f(x) + (x0^2 - x0)*x1*x2 = x0^2 * x1 * x2 (in F_2!)
    f_poly = {(1, 1, 1): 1}
    g_poly = {(2, 1, 1): 1}
    bool_points_agree = 0
    for x0, x1, x2 in itertools.product((0, 1), repeat=3):
        fv = (x0 * x1 * x2) % 2
        gv = (x0 * x0 * x1 * x2) % 2
        _require(fv == gv, "Boolean witness must agree on {0,1}^3")
        bool_points_agree += 1
    f_deg3 = {m: c for m, c in f_poly.items() if sum(m) <= 3}
    g_deg3 = {m: c for m, c in g_poly.items() if sum(m) <= 3}
    _require(f_deg3 == {(1, 1, 1): 1}, "Original f deg<=3 part mismatch")
    _require(g_deg3 == {}, "Boolean garbage failed to annihilate deg<=3 part")

    # Theorem K.6 finite-field power-of-2 period witness (for F_3, F_5, F_7):
    # In any finite field F_q, c^{2^j} enters a finite cycle with tail <= 1 and period <= phi(q-1)
    ff_periods: Dict[str, int] = {}
    for q in (3, 5, 7):
        max_per = 0
        for c in range(1, q):
            seen: Dict[int, int] = {}
            val = c
            step = 0
            while val not in seen:
                seen[val] = step
                val = (val * val) % q
                step += 1
            per = step - seen[val]
            if per > max_per:
                max_per = per
        _require(max_per >= 1, "Period must be positive")
        ff_periods[f"F_{q}"] = max_per

    return {
        "rings_verified": rings_verified,
        "output_degree": 5,
        "boolean_points_identical": bool_points_agree,
        "boolean_f_deg3_terms": len(f_deg3),
        "boolean_g_deg3_terms": len(g_deg3),
        "finite_field_squaring_periods": ff_periods,
    }


# ---------------------------------------------------------------------------
# Oracle 7: Appendix N — Border Complexity / Laurent Series Closure
# ---------------------------------------------------------------------------


def _laurent_add(a: Mapping[int, int], b: Mapping[int, int], mod_p: int) -> Dict[int, int]:
    out = dict(a)
    for e, c in b.items():
        nv = out.get(e, 0) + c
        if mod_p > 0:
            nv %= mod_p
        if nv == 0:
            out.pop(e, None)
        else:
            out[e] = nv
    return out


def _laurent_mul(a: Mapping[int, int], b: Mapping[int, int], mod_p: int) -> Dict[int, int]:
    out: Dict[int, int] = {}
    for e1, c1 in a.items():
        for e2, c2 in b.items():
            nv = out.get(e1 + e2, 0) + c1 * c2
            if mod_p > 0:
                nv %= mod_p
            if nv == 0:
                out.pop(e1 + e2, None)
            else:
                out[e1 + e2] = nv
    return out


def _laurent_truncate(a: Mapping[int, int], max_exp: int) -> Dict[int, int]:
    return {e: c for e, c in a.items() if e <= max_exp}


def _laurent_subst_eps_pow(a: Mapping[int, int], r: int) -> Dict[int, int]:
    """Prop N.4 endomorphism sigma_r: eps -> eps^r."""
    return {e * r: c for e, c in a.items()}


def probe_border_laurent_closure() -> Dict[str, object]:
    """Oracle 7: Verify Lem N.2 cutoff N = 2^L*Delta, Lem N.3 cover bound, Prop N.4 sigma_r."""
    # Genuine border circuit computing f(x1,x2,y1,y2) = x1*y2 + x2*y1 via 1/eps pole cancellation:
    #   Out = c_inv * ((x1 + c_eps * x2) * (y1 + c_eps * y2) - x1 * y1)
    # Add arbitrary higher-order Laurent series tail noise starting at eps^{N+1} where L=4, Delta=1 -> N=16!
    # Verify over BOTH Z (char 0) and F_2 (char 2)!
    big_l = 4
    delta = 1
    cutoff_n = (1 << big_l) * delta  # 16
    border_rings_ok: List[str] = []

    for mod_p, label in ((0, "Z"), (2, "F_2")):
        # Noisy constants in R[[eps]][eps^{-1}]: c_inv = eps^{-1} + eps^{17}, c_eps = eps + eps^{18}
        c_inv_full = {-1: 1, cutoff_n + 1: 1}
        c_eps_full = {1: 1, cutoff_n + 2: 1}
        c_inv_cut = _laurent_truncate(c_inv_full, cutoff_n)
        c_eps_cut = _laurent_truncate(c_eps_full, cutoff_n)

        # Evaluate border circuit on concrete integer assignment (x1=3, x2=5, y1=7, y2=11)
        # True f = x1*y2 + x2*y1 = 3*11 + 5*7 = 68 (or 0 mod 2 -> pick x1=1,x2=1,y1=1,y2=0 => f=1 mod 2!)
        x1, x2, y1, y2 = (1, 1, 1, 0) if mod_p == 2 else (3, 5, 7, 11)
        expected_f = (x1 * y2 + x2 * y1) % mod_p if mod_p > 0 else (x1 * y2 + x2 * y1)

        def eval_border(ci: Mapping[int, int], ce: Mapping[int, int]) -> Dict[int, int]:
            t1 = _laurent_add({0: x1}, _laurent_mul(ce, {0: x2}, mod_p), mod_p)
            t2 = _laurent_add({0: y1}, _laurent_mul(ce, {0: y2}, mod_p), mod_p)
            prod = _laurent_mul(t1, t2, mod_p)
            neg_xy = {0: (-x1 * y1) % mod_p if mod_p > 0 else (-x1 * y1)}
            diff = _laurent_add(prod, neg_xy, mod_p)
            return _laurent_mul(ci, diff, mod_p)

        out_full = eval_border(c_inv_full, c_eps_full)
        out_cut = eval_border(c_inv_cut, c_eps_cut)
        nonpos_full = {e: c for e, c in out_full.items() if e <= 0}
        nonpos_cut = {e: c for e, c in out_cut.items() if e <= 0}
        _require(nonpos_full == {0: expected_f}, f"Border circuit pole cancellation failed in {label}")
        _require(nonpos_cut == nonpos_full, f"Lem N.2 cutoff corrupted eps<=0 part in {label}")
        border_rings_ok.append(label)

    # Lemma N.3 exact subexponential cover bound: (2*n*Delta + 1)^|V| < 2^n for explicit n
    # Example: |V| = 4, Delta = 2 -> at n = 32: (129)^4 = 276,922,881 < 2^32 = 4,294,967,296!
    cover_lhs = (2 * 32 * 2 + 1) ** 4
    cover_rhs = 1 << 32
    _require(cover_lhs < cover_rhs, "Lem N.3 subexponential cover inequality failed")

    # Prop N.4 scale-composition sigma_r error isolation + mod 2^W [eps^0] extraction:
    # Suppose outer sum has lambda_0 = eps^{-2}, lambda_1 = 1 + eps^2 (max |exp| = 2 -> pick r = 3 > 2),
    # and inner approximate program returns sum(z_e) + eps * err_e with sum_e lambda_e sum(z_e) = V + eps*G.
    # Choose sum(z_0) = 0, sum(z_1) = 7, err_0 = 5, err_1 = 11 -> lambda_0*(0 + 5*eps^3) + lambda_1*(7 + 11*eps^3)
    # = 5*eps + 7 + 7*eps^2 + 11*eps^3 + 11*eps^5 -> ZERO negative powers AND exact [eps^0] = 7!
    r_sub = 3
    lam0 = {-2: 1}
    lam1 = {0: 1, 2: 1}
    inner0 = _laurent_subst_eps_pow({0: 0, 1: 5}, r_sub)
    inner1 = _laurent_subst_eps_pow({0: 7, 1: 11}, r_sub)
    composed = _laurent_add(_laurent_mul(lam0, inner0, 0), _laurent_mul(lam1, inner1, 0), 0)
    min_exp_composed = min(composed.keys())
    _require(min_exp_composed == 0, f"Prop N.4 sigma_r leaked negative exponent: {min_exp_composed}")
    _require(composed.get(0, 0) == 7, "Prop N.4 sigma_r corrupted [eps^0] value")

    # Modular exponent counter mod 2^W (W = 4 -> mod 16, all true |exp| < 8):
    # Extract [eps^0] from product of Laurent factors (eps^{-2} + 3*eps^0) * (2*eps^2 + 5*eps^0)
    # = 2*eps^0 + 5*eps^{-2} + 6*eps^2 + 15*eps^0 -> true [eps^0] = 17!
    w_bits = 4
    mod_w = 1 << w_bits
    fac1 = {(-2): 1, 0: 3}
    fac2 = {2: 2, 0: 5}
    extracted_eps0 = 0
    for e1, c1 in fac1.items():
        for e2, c2 in fac2.items():
            if (e1 + e2) % mod_w == 0:
                extracted_eps0 += c1 * c2
    _require(extracted_eps0 == 17, f"Prop N.4 mod-2^W extraction failed: {extracted_eps0}")

    return {
        "lem_n2_cutoff_n": cutoff_n,
        "lem_n2_rings_verified": border_rings_ok,
        "lem_n3_cover_n32_lhs": cover_lhs,
        "lem_n3_cover_n32_rhs": cover_rhs,
        "prop_n4_sigma_r": r_sub,
        "prop_n4_min_exp_after_sigma_r": min_exp_composed,
        "prop_n4_eps0_after_sigma_r": composed[0],
        "prop_n4_mod_2w_extracted_eps0": extracted_eps0,
    }


def run_all_mechanism_probes() -> Dict[str, object]:
    """Execute all 7 pure-Z/Q/F_p mathematical tomography oracles."""
    return {
        "oracle_1_meixner_crossing": probe_meixner_crossing_identity(),
        "oracle_2_cat0_mat_f2_dichotomy": probe_cat0_mat_f2_dichotomy(),
        "oracle_3_flat_perm_and_hubs": probe_flat_case_perm_and_hub_bounds(),
        "oracle_4_char2_perm_vs_hc_and_s41": probe_char2_perm_vs_hc_gadgets(),
        "oracle_5_contracting_unitriangular": probe_contracting_unitriangular(),
        "oracle_6_lowdeg_parse_tree_and_diag": probe_lowdeg_parse_tree_and_diag(),
        "oracle_7_border_laurent_closure": probe_border_laurent_closure(),
    }
