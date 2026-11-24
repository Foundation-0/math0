#!/usr/bin/env python3
"""Track S29 (AUDIT-129 / Portal 25): Terence Tao Live 2025-2026 Exact-Operator
Quintet in Pure Exact Z/Q.

100% pure Python 3 stdlib (int, fractions.Fraction, itertools, math, hashlib).
ZERO IEEE-754 floats, ZERO bare assert statements, ZERO RNG calls, ZERO
third-party imports, ZERO personal-path or private-repo references.

Honest Law-4 Novelty: N1 (clean-room unified pure-Z/Q verification engine across
Tao's 2025-2026 five-pillar oeuvre, exact ring-closure HNF separation of Z vs.
Z[1/2] on Katz-Tao 11/6 & 7/4 certificates, live open-seam stacked-page probes,
exact rational Taylor-enclosure Odd Banks-Martin checks, exact 3-adic Syracuse
stationary measures, Singer/Gowers/dyadic-NS/DPTZ/ETP exact certificates, and
Uniform Zone-B atomic dir_fd certification; all published theorems & records
strictly quarantined as N0).
"""
from __future__ import annotations

from fractions import Fraction
import itertools
import math
from typing import Any

TRACK_ID = "TRACK-S29-AUDIT-129"
SCHEMA_VERSION = "1.0.0"
MAX_RATIONAL_BITS = 4_000
MAX_JSON_INT_BITS = 4_000

TAO_SLOPES: tuple[Fraction, ...] = (
    Fraction(-1, 1),
    Fraction(2, 1),
    Fraction(3, 1),
    Fraction(-2, 1),
    Fraction(3, 2),
    Fraction(5, 3),
    Fraction(7, 4),
    Fraction(13, 8),
)

# Exact rational log approximants matching Pillar 2's 180 (Omega=2) witness
RATIONAL_LOG_APPROX: dict[int, Fraction] = {
    2: Fraction(693, 1000),
    3: Fraction(1099, 1000),
    5: Fraction(1609, 1000),
    7: Fraction(1946, 1000),
}

_VALID_RINGS = frozenset({"Z", "Z[1/2]", "Q"})


class TaoOperatorsError(ValueError):
    """Typed fail-closed error for Track S29 domain, algebraic, and Zone-B checks."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"[{code}] {message}")
        self.code = code
        self.detail = message


# ============================================================================
# 1. Strict Type, Domain, Rational, and Linear-Algebra Primitives
# ============================================================================

def require_ok(cond: bool, code: str, message: str) -> None:
    if type(cond) is not bool:
        raise TaoOperatorsError("INVALID_CONDITION_TYPE", f"{code}: condition must be exact bool")
    if not cond:
        raise TaoOperatorsError(code, message)


def require_exact_int(
    val: Any,
    name: str,
    lo: int | None = None,
    hi: int | None = None,
) -> int:
    if type(val) is not int:
        raise TaoOperatorsError("INVALID_INT_TYPE", f"{name} must be exact int")
    if val.bit_length() > MAX_RATIONAL_BITS:
        raise TaoOperatorsError("INT_BIT_LIMIT", f"{name} exceeds {MAX_RATIONAL_BITS}-bit cap")
    if lo is not None and val < lo:
        raise TaoOperatorsError("INT_OUT_OF_RANGE", f"{name} must be >= {lo}")
    if hi is not None and val > hi:
        raise TaoOperatorsError("INT_OUT_OF_RANGE", f"{name} must be <= {hi}")
    return val


def require_exact_bool(val: Any, name: str) -> bool:
    if type(val) is not bool:
        raise TaoOperatorsError("INVALID_BOOL_TYPE", f"{name} must be exact bool")
    return val


def require_exact_fraction(val: Any, name: str) -> Fraction:
    if type(val) is not Fraction:
        raise TaoOperatorsError("INVALID_FRACTION_TYPE", f"{name} must be exact Fraction")
    if val.numerator.bit_length() > MAX_RATIONAL_BITS or val.denominator.bit_length() > MAX_RATIONAL_BITS:
        raise TaoOperatorsError("RATIONAL_BIT_LIMIT", f"{name} exceeds {MAX_RATIONAL_BITS}-bit cap")
    return val


def format_fraction(q: Fraction) -> str:
    q = require_exact_fraction(q, "q")
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"


def is_prime_small(n: int) -> bool:
    """Exact trial-division primality check for 0 <= n <= 10^8."""
    n = require_exact_int(n, "n", lo=0, hi=10**8)
    if n < 2:
        return False
    if n in (2, 3):
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    lim = math.isqrt(n)
    d = 5
    while d <= lim:
        if n % d == 0 or n % (d + 2) == 0:
            return False
        d += 6
    return True


def factorize_small(n: int) -> dict[int, int]:
    """Exact trial-division factorization for 1 <= n <= 10^8."""
    n = require_exact_int(n, "n", lo=1, hi=10**8)
    fac: dict[int, int] = {}
    rem = n
    d = 2
    while d * d <= rem:
        if rem % d == 0:
            e = 0
            while rem % d == 0:
                rem //= d
                e += 1
            fac[d] = e
        d = 3 if d == 2 else d + 2
    if rem > 1:
        fac[rem] = 1
    return fac


def solve_linear_fraction(matrix: list[list[Fraction]], rhs: list[Fraction]) -> list[Fraction]:
    """Exact Gauss-Jordan linear solver A x = b over Fraction (fail-closed on singularity)."""
    if type(matrix) is not list or type(rhs) is not list:
        raise TaoOperatorsError("INVALID_MATRIX_TYPE", "matrix and rhs must be exact lists")
    n = len(matrix)
    require_ok(n >= 1 and len(rhs) == n, "INVALID_MATRIX_DIM", "matrix must be non-empty square matching rhs")
    aug: list[list[Fraction]] = []
    for i in range(n):
        row = matrix[i]
        require_ok(type(row) is list and len(row) == n, "INVALID_MATRIX_ROW", "row must be exact list of length n")
        aug_row = [require_exact_fraction(v, f"A[{i}][{j}]") for j, v in enumerate(row)]
        aug_row.append(require_exact_fraction(rhs[i], f"b[{i}]"))
        aug.append(aug_row)
    for col in range(n):
        piv = -1
        for r in range(col, n):
            if aug[r][col] != 0:
                piv = r
                break
        require_ok(piv != -1, "SINGULAR_MATRIX", f"zero pivot at column {col}")
        if piv != col:
            aug[col], aug[piv] = aug[piv], aug[col]
        pv = aug[col][col]
        aug[col] = [val / pv for val in aug[col]]
        for r in range(n):
            if r != col:
                factor = aug[r][col]
                aug[r] = [aug[r][c] - factor * aug[col][c] for c in range(n + 1)]
    return [aug[i][n] for i in range(n)]


def det_fraction(matrix: list[list[Fraction]]) -> Fraction:
    """Exact determinant of a non-empty square matrix over Fraction."""
    if type(matrix) is not list:
        raise TaoOperatorsError("INVALID_MATRIX_TYPE", "matrix must be exact list")
    n = len(matrix)
    require_ok(n >= 1, "INVALID_MATRIX_DIM", "matrix must be non-empty")
    a: list[list[Fraction]] = []
    for i in range(n):
        row = matrix[i]
        require_ok(type(row) is list and len(row) == n, "INVALID_MATRIX_ROW", "matrix must be square")
        a.append([require_exact_fraction(v, f"M[{i}][{j}]") for j, v in enumerate(row)])
    det = Fraction(1, 1)
    for col in range(n):
        piv = -1
        for r in range(col, n):
            if a[r][col] != 0:
                piv = r
                break
        if piv == -1:
            return Fraction(0, 1)
        if piv != col:
            a[col], a[piv] = a[piv], a[col]
            det = -det
        pv = a[col][col]
        det *= pv
        for r in range(col + 1, n):
            factor = a[r][col] / pv
            a[r] = [a[r][j] - factor * a[col][j] for j in range(n)]
    return det


def _bmask(indices: list[int] | tuple[int, ...]) -> int:
    m = 0
    for i in indices:
        m |= 1 << i
    return m


# ============================================================================
# 2. Pillar 1 — Katz-Tao Conditional-Copy Shannon Certificates & Complexity
# ============================================================================

def row_hnf_exact(int_rows: list[list[int]], dim: int) -> list[list[int]]:
    """Exact integer Row Hermite Normal Form over Z (pure int)."""
    dim = require_exact_int(dim, "dim", lo=1, hi=16)
    require_ok(type(int_rows) is list, "INVALID_ROWS_TYPE", "int_rows must be exact list")
    mat: list[list[int]] = []
    for row in int_rows:
        require_ok(type(row) is list and len(row) == dim, "INVALID_ROW_LEN", "each row must have length dim")
        mat.append([require_exact_int(v, "hnf_entry") for v in row])
    r = 0
    for c in range(dim):
        while True:
            nz = [i for i in range(r, len(mat)) if mat[i][c] != 0]
            if not nz:
                break
            piv = min(nz, key=lambda i: abs(mat[i][c]))
            mat[r], mat[piv] = mat[piv], mat[r]
            if mat[r][c] < 0:
                mat[r] = [-x for x in mat[r]]
            changed = False
            for i in range(r + 1, len(mat)):
                if mat[i][c] != 0:
                    q = mat[i][c] // mat[r][c]
                    mat[i] = [mat[i][j] - q * mat[r][j] for j in range(dim)]
                    changed = True
            if not changed:
                break
        if r < len(mat) and mat[r][c] != 0:
            for i in range(r):
                q = mat[i][c] // mat[r][c]
                if q != 0:
                    mat[i] = [mat[i][j] - q * mat[r][j] for j in range(dim)]
            r += 1
    return mat[:r]


def _in_hnf_span(hnf: list[list[int]], target: list[int], dim: int, ring: str) -> bool:
    v = [Fraction(x, 1) for x in target]
    for row in hnf:
        piv_c = next(c for c in range(dim) if row[c] != 0)
        if v[piv_c] != 0:
            coeff = v[piv_c] / Fraction(row[piv_c], 1)
            if ring == "Z" and coeff.denominator != 1:
                return False
            if ring == "Z[1/2]" and (coeff.denominator & (coeff.denominator - 1)) != 0:
                return False
            v = [v[j] - coeff * row[j] for j in range(dim)]
    return all(x == 0 for x in v)


def in_ring_span(int_rows: list[list[int]], target: list[int], dim: int, ring: str) -> bool:
    """Exact membership of integer vector target in ring-span(int_rows) for ring in {'Z','Z[1/2]','Q'}."""
    require_ok(type(ring) is str and ring in _VALID_RINGS, "INVALID_RING", "ring must be 'Z', 'Z[1/2]', or 'Q'")
    dim = require_exact_int(dim, "dim", lo=1, hi=16)
    require_ok(type(target) is list and len(target) == dim, "INVALID_TARGET_VEC", "target must be exact list of len dim")
    hnf = row_hnf_exact(int_rows, dim)
    clean_target = [require_exact_int(x, "target_entry") for x in target]
    return _in_hnf_span(hnf, clean_target, dim, ring)


def _find_copy_isos(
    vecs: list[list[int]],
    dvecs: list[tuple[list[int], int, int]],
    dim: int,
    cl_u_mask: int,
    cl_g_mask: int,
    cl_up_mask: int,
) -> list[dict[int, int]]:
    """Find all exact linear + diff-pair bijections phi: cl(U) -> cl(U') fixing cl(G) pointwise."""
    m = len(vecs)
    cl_u = [i for i in range(m) if (cl_u_mask >> i) & 1]
    cl_g = [i for i in range(m) if (cl_g_mask >> i) & 1]
    cl_up = [i for i in range(m) if (cl_up_mask >> i) & 1]
    if len(cl_u) != len(cl_up):
        return []
    vec_to_idx = {tuple(Fraction(c, 1) for c in vecs[i]): i for i in range(m)}
    cl_g_set = set(cl_g)
    cl_u_set = set(cl_u)
    cl_up_set = set(cl_up)

    # Basis of cl(U) extending a basis of cl(G)
    basis_idx: list[int] = []
    cur_rows: list[list[int]] = []
    for i in cl_g + [x for x in cl_u if x not in cl_g_set]:
        cand = row_hnf_exact(cur_rows + [vecs[i]], dim)
        if len(cand) > len(cur_rows):
            basis_idx.append(i)
            cur_rows = cand
    r = len(basis_idx)
    g_rank = len(row_hnf_exact([vecs[i] for i in cl_g], dim)) if cl_g else 0
    if r == 0:
        return [{}]

    # Select r linearly independent columns of the basis matrix
    piv_cols: list[int] = []
    for c in range(dim):
        sub = [[vecs[b][cc] for cc in piv_cols + [c]] for b in basis_idx]
        if len(row_hnf_exact(sub, len(piv_cols) + 1)) > len(piv_cols):
            piv_cols.append(c)
            if len(piv_cols) == r:
                break
    bt = [[Fraction(vecs[basis_idx[k]][c], 1) for k in range(r)] for c in piv_cols]
    coords = {i: solve_linear_fraction(bt, [Fraction(vecs[i][c], 1) for c in piv_cols]) for i in cl_u}

    dp_u = [(dv, xi, yi) for dv, xi, yi in dvecs if xi in cl_u_set and yi in cl_u_set]
    dp_up_pairs: dict[frozenset[int], tuple[tuple[Fraction, ...], tuple[Fraction, ...]]] = {}
    for dv, xi, yi in dvecs:
        if xi in cl_up_set and yi in cl_up_set:
            pos_v = tuple(Fraction(c, 1) for c in dv)
            neg_v = tuple(Fraction(-c, 1) for c in dv)
            dp_up_pairs[frozenset((xi, yi))] = (pos_v, neg_v)
    if len(dp_u) != len(dp_up_pairs):
        return []
    dp_u_coords = [
        (solve_linear_fraction(bt, [Fraction(dv[c], 1) for c in piv_cols]), xi, yi)
        for dv, xi, yi in dp_u
    ]

    free_cands = [i for i in cl_up if i not in cl_g_set]
    free_k = r - g_rank
    isos: list[dict[int, int]] = []
    for choice in itertools.permutations(free_cands, free_k):
        img_basis = list(basis_idx[:g_rank]) + list(choice)
        if len(row_hnf_exact([vecs[b] for b in img_basis], dim)) != r:
            continue
        phi: dict[int, int] = {}
        ok = True
        for i in cl_u:
            cs = coords[i]
            img_v = tuple(sum((cs[k] * vecs[img_basis[k]][c] for k in range(r)), Fraction(0, 1)) for c in range(dim))
            tgt = vec_to_idx.get(img_v)
            if tgt not in cl_up_set:
                ok = False
                break
            phi[i] = tgt
        if not ok:
            continue
        for cs, xi, yi in dp_u_coords:
            img_dv = tuple(sum((cs[k] * vecs[img_basis[k]][c] for k in range(r)), Fraction(0, 1)) for c in range(dim))
            pair = frozenset((phi[xi], phi[yi]))
            allowed = dp_up_pairs.get(pair, ())
            if img_dv not in allowed:
                ok = False
                break
        if ok:
            isos.append(phi)
    return isos


def verify_shannon_certificate(
    atoms: list[tuple[str, tuple[int, ...]]],
    diff_pairs: list[tuple[tuple[int, ...], int, int]],
    copy_steps: list[tuple[int, int, int, int]],
    eq_groups: list[list[int]],
    target_mask: int,
    rhs_terms: list[tuple[int, Fraction]],
    dual_rows: list[tuple[str, Fraction, Any]],
    ring: str,
) -> dict[str, Any]:
    """Zero-float pure-Q conditional-copy Shannon entropy certificate verifier.

    Checks exact container/mask bounds, non-negative submodularity/monotonicity
    multipliers, exact ring closure cl_R(T) == cl_Q(T), exact linear modularity
    and unique linear+diff-pair copy isomorphism on every copy step, copy-derived
    equal-law verification on every eq_group, and exact zero coefficient residual.
    """
    require_ok(type(ring) is str and ring in _VALID_RINGS, "INVALID_RING", "ring must be 'Z', 'Z[1/2]', or 'Q'")
    require_ok(type(atoms) is list and len(atoms) >= 1, "INVALID_ATOMS", "atoms must be non-empty list")
    m = len(atoms)
    full_mask = (1 << m) - 1
    vecs: list[list[int]] = []
    seen_vecs: set[tuple[int, ...]] = set()
    dim = -1
    for entry in atoms:
        require_ok(type(entry) is tuple and len(entry) == 2, "INVALID_ATOMS", "atom must be (name, vec) 2-tuple")
        a_name, a_vec = entry
        require_ok(type(a_name) is str, "INVALID_ATOMS", "atom name must be exact str")
        require_ok(type(a_vec) is tuple and len(a_vec) >= 1, "INVALID_ATOMS", "atom vec must be non-empty tuple")
        if dim == -1:
            dim = len(a_vec)
        else:
            require_ok(len(a_vec) == dim, "INVALID_ATOMS", "all atom vectors must have equal dimension")
        clean_v = [require_exact_int(c, "atom_coord") for c in a_vec]
        require_ok(any(clean_v), "ZERO_VECTOR_FORBIDDEN", "atom coordinate vector must be nonzero")
        vt = tuple(clean_v)
        require_ok(vt not in seen_vecs, "INVALID_ATOMS", "duplicate atom coordinate vector")
        seen_vecs.add(vt)
        vecs.append(clean_v)

    require_ok(type(diff_pairs) is list, "INVALID_DIFF_PAIRS", "diff_pairs must be exact list")
    dvecs: list[tuple[list[int], int, int]] = []
    for dp_entry in diff_pairs:
        require_ok(type(dp_entry) is tuple and len(dp_entry) == 3, "INVALID_DIFF_PAIRS", "diff_pair must be 3-tuple")
        dv, xi, yi = dp_entry
        require_ok(type(dv) is tuple and len(dv) == dim, "INVALID_DIFF_PAIRS", "diff vector must have length dim")
        clean_dv = [require_exact_int(c, "diff_coord") for c in dv]
        require_ok(any(clean_dv), "ZERO_VECTOR_FORBIDDEN", "diff_pair vector must be nonzero")
        c_xi = require_exact_int(xi, "diff_xi", lo=0, hi=m - 1)
        c_yi = require_exact_int(yi, "diff_yi", lo=0, hi=m - 1)
        require_ok(
            clean_dv == [vecs[c_xi][c] - vecs[c_yi][c] for c in range(dim)],
            "INVALID_DIFF_PAIR_VECTOR",
            "diff_pair vector must equal vecs[xi] - vecs[yi]",
        )
        dvecs.append((clean_dv, c_xi, c_yi))

    require_ok(type(copy_steps) is list, "INVALID_COPY_STEPS", "copy_steps must be exact list")
    clean_copies: list[tuple[int, int, int, int]] = []
    for c_entry in copy_steps:
        require_ok(type(c_entry) is tuple and len(c_entry) == 4, "INVALID_COPY_STEPS", "copy_step must be 4-tuple")
        o_m, u_m, g_m, up_m = (
            require_exact_int(c_entry[0], "copy_o", lo=0, hi=full_mask),
            require_exact_int(c_entry[1], "copy_u", lo=0, hi=full_mask),
            require_exact_int(c_entry[2], "copy_g", lo=0, hi=full_mask),
            require_exact_int(c_entry[3], "copy_up", lo=0, hi=full_mask),
        )
        clean_copies.append((o_m, u_m, g_m, up_m))

    require_ok(type(eq_groups) is list, "INVALID_EQ_GROUP", "eq_groups must be exact list")
    clean_eq_groups: list[list[int]] = []
    for grp in eq_groups:
        require_ok(type(grp) is list and len(grp) >= 1, "INVALID_EQ_GROUP", "eq_group must be non-empty list")
        clean_eq_groups.append([require_exact_int(mk, "eq_mask", lo=0, hi=full_mask) for mk in grp])

    require_ok(type(rhs_terms) is list, "INVALID_RHS_TERMS", "rhs_terms must be exact list")
    require_ok(type(dual_rows) is list, "INVALID_DUAL_ROWS", "dual_rows must be exact list")

    close_cache: dict[tuple[int, str], int] = {}

    def close_ring(mask: int, r_name: str) -> int:
        key = (mask, r_name)
        if key in close_cache:
            return close_cache[key]
        cur = mask
        while True:
            hnf = row_hnf_exact([vecs[i] for i in range(m) if (cur >> i) & 1], dim)
            nxt = cur
            for i in range(m):
                if not ((nxt >> i) & 1):
                    if _in_hnf_span(hnf, vecs[i], dim, r_name):
                        nxt |= 1 << i
            for dv, xi, yi in dvecs:
                pm = (1 << xi) | (1 << yi)
                if (nxt & pm) != pm:
                    if _in_hnf_span(hnf, dv, dim, r_name):
                        nxt |= pm
            if nxt == cur:
                close_cache[key] = cur
                close_cache[(cur, r_name)] = cur
                return cur
            cur = nxt

    clean_target = require_exact_int(target_mask, "target_mask", lo=1, hi=full_mask)
    touched: set[int] = {0, clean_target}
    base_mask = clean_target
    clean_rhs: list[tuple[int, Fraction]] = []
    for r_entry in rhs_terms:
        require_ok(type(r_entry) is tuple and len(r_entry) == 2, "INVALID_RHS_TERMS", "rhs_term must be 2-tuple")
        rm = require_exact_int(r_entry[0], "rhs_mask", lo=1, hi=full_mask)
        coeff = require_exact_fraction(r_entry[1], "rhs_coeff")
        require_ok(coeff >= 0, "NEGATIVE_RHS_COEFF", "RHS coeff must be >= 0")
        clean_rhs.append((rm, coeff))
        touched.add(rm)
        base_mask |= rm
    touched.add(base_mask)
    for o_m, u_m, g_m, up_m in clean_copies:
        touched |= {o_m | up_m, g_m, o_m, u_m, up_m}
    clean_duals: list[tuple[str, Fraction, Any]] = []
    for d_entry in dual_rows:
        require_ok(type(d_entry) is tuple and len(d_entry) == 3, "INVALID_DUAL_ROWS", "dual_row must be 3-tuple")
        kind, mult, data = d_entry
        mult = require_exact_fraction(mult, "dual_mult")
        if kind == "submod":
            require_ok(mult >= 0, "NEGATIVE_SHANNON_MULTIPLIER", "submod multiplier must be >= 0")
            require_ok(type(data) is tuple and len(data) == 3, "INVALID_DUAL_ROWS", "submod data must be 3-tuple")
            k_m = require_exact_int(data[0], "submod_k", lo=0, hi=full_mask)
            i_idx = require_exact_int(data[1], "submod_i", lo=0, hi=m - 1)
            j_idx = require_exact_int(data[2], "submod_j", lo=0, hi=m - 1)
            clean_duals.append((kind, mult, (k_m, i_idx, j_idx)))
            touched |= {k_m | (1 << i_idx), k_m | (1 << j_idx), k_m | (1 << i_idx) | (1 << j_idx), k_m}
        elif kind == "mono":
            require_ok(mult >= 0, "NEGATIVE_SHANNON_MULTIPLIER", "mono multiplier must be >= 0")
            require_ok(type(data) is tuple and len(data) == 2, "INVALID_DUAL_ROWS", "mono data must be 2-tuple")
            k_m = require_exact_int(data[0], "mono_k", lo=0, hi=full_mask)
            i_idx = require_exact_int(data[1], "mono_i", lo=0, hi=m - 1)
            clean_duals.append((kind, mult, (k_m, i_idx)))
            touched |= {k_m | (1 << i_idx), k_m}
        elif kind == "copy":
            c_idx = require_exact_int(data, "copy_idx", lo=0, hi=len(clean_copies) - 1)
            clean_duals.append((kind, mult, c_idx))
        else:
            raise TaoOperatorsError("INVALID_DUAL_KIND", f"unknown dual row kind: {kind!r}")
    for grp in clean_eq_groups:
        for mk in grp:
            touched.add(mk)

    # Ring closure check cl_R(T) == cl_Q(T) on every touched subset
    cl_map: dict[int, int] = {}
    for mk in touched:
        cr = close_ring(mk, ring)
        cq = close_ring(mk, "Q")
        require_ok(cr == cq, "RING_CLOSURE_MISMATCH", f"cl_{ring}({mk}) != cl_Q({mk})")
        cl_map[mk] = cr

    def rk_closed(cm: int) -> int:
        return len(row_hnf_exact([vecs[i] for i in range(m) if (cm >> i) & 1], dim)) if cm else 0

    # Verify sequential copy-chain freshness, closure containment, intersection, linear modularity, & unique copy iso
    cl_base = cl_map[base_mask]
    cum_cl = 0
    step_maps: list[tuple[int, dict[int, int]]] = []
    for step_idx, (o_m, u_m, g_m, up_m) in enumerate(clean_copies):
        cl_o, cl_u, cl_g, cl_up = cl_map[o_m], cl_map[u_m], cl_map[g_m], cl_map[up_m]
        cl_ou = cl_map[o_m | up_m]
        if step_idx == 0:
            require_ok((cl_o & cl_base) == cl_base, "BROKEN_COPY_IDENTITY", "initial copy space O_0 must contain base atoms")
        else:
            require_ok(cl_o == cum_cl, "BROKEN_COPY_IDENTITY", "sequential copy space O_k must equal prior closure O_{k-1} U U'_{k-1}")
        require_ok((cl_o & cl_u) == cl_u, "BROKEN_COPY_IDENTITY", "U not determined by O")
        require_ok((cl_u & cl_g) == cl_g, "COPY_GLUE_NOT_IN_SOURCE", "G not determined by U")
        require_ok((cl_o & cl_up) == cl_g, "BROKEN_COPY_IDENTITY", "cl(O) intersect cl(U') != cl(G)")
        require_ok(
            rk_closed(cl_ou) + rk_closed(cl_g) == rk_closed(cl_o) + rk_closed(cl_up),
            "BROKEN_COPY_IDENTITY",
            "copy step violates exact Q-rank modularity",
        )
        isos = _find_copy_isos(vecs, dvecs, dim, cl_u, cl_g, cl_up)
        require_ok(len(isos) == 1, "BROKEN_COPY_IDENTITY", f"expected unique copy isomorphism, found {len(isos)}")
        phi = isos[0]
        inv_phi = {v: u for u, v in phi.items()}
        sigma: dict[int, int] = {}
        for u, v in phi.items():
            sigma[u] = v
            sigma[v] = u
        step_maps.append((cl_u, phi))
        step_maps.append((cl_up, inv_phi))
        step_maps.append((cl_u | cl_up, sigma))
        cum_cl = cl_ou

    # Derive exact copy-induced equal-law relation via BFS over verified copy maps
    law_parent: dict[int, int] = {cm: cm for cm in set(cl_map.values())}

    def find_law(x: int) -> int:
        law_parent.setdefault(x, x)
        while law_parent[x] != x:
            law_parent[x] = law_parent[law_parent[x]]
            x = law_parent[x]
        return x

    def union_law(a: int, b: int) -> None:
        ra, rb = find_law(a), find_law(b)
        if ra != rb:
            if ra < rb:
                law_parent[rb] = ra
            else:
                law_parent[ra] = rb

    if step_maps:
        queue = sorted(law_parent.keys())
        seen_cl = set(queue)
        while queue:
            cur = queue.pop()
            for dom_mask, mp in step_maps:
                if (cur & dom_mask) == cur:
                    img = 0
                    for i in range(m):
                        if (cur >> i) & 1:
                            img |= 1 << mp[i]
                    cimg = close_ring(img, ring)
                    union_law(cur, cimg)
                    if cimg not in seen_cl:
                        seen_cl.add(cimg)
                        queue.append(cimg)

    # Validate EVERY caller-supplied eq_group against the proved copy-induced law equivalence
    parent = {cm: cm for cm in set(cl_map.values())}

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for grp in clean_eq_groups:
        c0 = cl_map[grp[0]]
        law0 = find_law(c0)
        b0 = find(c0)
        for g in grp[1:]:
            cg = cl_map[g]
            require_ok(find_law(cg) == law0, "INVALID_EQ_GROUP", "eq_group equates subsets not proved equal in law")
            rg = find(cg)
            if rg != b0:
                if b0 < rg:
                    parent[rg] = b0
                else:
                    parent[b0] = rg
                    b0 = rg

    empty_rep = find(cl_map[0])
    acc: dict[int, Fraction] = {}

    def add_term(mk: int, c_val: Fraction) -> None:
        r = find(cl_map[mk])
        if r != empty_rep:
            acc[r] = acc.get(r, Fraction(0, 1)) + c_val

    add_term(target_mask, Fraction(-1, 1))
    for rm, coeff in clean_rhs:
        add_term(rm, coeff)

    for kind, mult, data in clean_duals:
        if kind == "copy":
            o_m, _u_m, g_m, up_m = clean_copies[data]
            for mk, sgn in ((o_m | up_m, 1), (g_m, 1), (o_m, -1), (up_m, -1)):
                add_term(mk, -mult * sgn)
        elif kind == "submod":
            k_m, i_idx, j_idx = data
            for mk, sgn in ((k_m | (1 << i_idx), 1), (k_m | (1 << j_idx), 1), (k_m | (1 << i_idx) | (1 << j_idx), -1), (k_m, -1)):
                add_term(mk, -mult * sgn)
        else:
            k_m, i_idx = data
            for mk, sgn in ((k_m | (1 << i_idx), 1), (k_m, -1)):
                add_term(mk, -mult * sgn)

    nonzero = {k: v for k, v in acc.items() if v != 0}
    require_ok(len(nonzero) == 0, "NONZERO_CERT_RESIDUAL", f"certificate residual non-zero ({len(nonzero)} terms)")
    exponent = sum((c for _, c in clean_rhs), Fraction(0, 1))
    return {
        "ring": ring,
        "cl_ring_equals_cl_Q": True,
        "dual_row_count": len(clean_duals),
        "copy_step_count": len(clean_copies),
        "exponent": format_fraction(exponent),
        "rhs_weights": [format_fraction(c) for _, c in clean_rhs],
        "residual_count": 0,
    }


def _require_proj_point(pt: Any, name: str) -> tuple[int, int]:
    require_ok(type(pt) is tuple and len(pt) == 2, "INVALID_PROJ_POINT", f"{name} must be 2-tuple of exact ints")
    p = require_exact_int(pt[0], f"{name}[0]")
    q = require_exact_int(pt[1], f"{name}[1]")
    require_ok(p != 0 or q != 0, "ZERO_PROJ_POINT", f"{name} cannot be (0, 0)")
    return (p, q)


def _proj_apply_mobius(mat: tuple[int, int, int, int], pt: tuple[int, int]) -> tuple[int, int]:
    """Apply PGL_2(Q) matrix (a,b,c,d) to projective point [p:q] (inf = [1:0])."""
    require_ok(type(mat) is tuple and len(mat) == 4, "INVALID_MOBIUS_MAT", "mat must be 4-tuple of exact ints")
    a = require_exact_int(mat[0], "mat[0]")
    b = require_exact_int(mat[1], "mat[1]")
    c = require_exact_int(mat[2], "mat[2]")
    d = require_exact_int(mat[3], "mat[3]")
    require_ok(a * d - b * c != 0, "SINGULAR_MOBIUS", "Mobius determinant must be nonzero")
    p, q = _require_proj_point(pt, "pt")
    num = a * p + b * q
    den = c * p + d * q
    g = math.gcd(abs(num), abs(den))
    return (num // g, den // g)


def projective_cross_ratio(
    z1: tuple[int, int],
    z2: tuple[int, int],
    z3: tuple[int, int],
    z4: tuple[int, int],
) -> Fraction:
    """Exact projective cross-ratio (z1, z2; z3, z4) on P^1(Q) via homogeneous determinants."""
    p1 = _require_proj_point(z1, "z1")
    p2 = _require_proj_point(z2, "z2")
    p3 = _require_proj_point(z3, "z3")
    p4 = _require_proj_point(z4, "z4")
    det13 = p1[0] * p3[1] - p3[0] * p1[1]
    det24 = p2[0] * p4[1] - p4[0] * p2[1]
    det14 = p1[0] * p4[1] - p4[0] * p1[1]
    det23 = p2[0] * p3[1] - p3[0] * p2[1]
    den = det14 * det23
    require_ok(den != 0, "DEGENERATE_CROSS_RATIO", "cross-ratio denominator is zero")
    return Fraction(det13 * det24, den)


def tao_rational_complexity_base(slope: Fraction) -> int:
    """Exact Tao (arXiv:2511.15135 Def 1.1) D({0,1,inf}; a/b) = min{D>=0 : max(|a|,|b|) <= 2^D}."""
    slope = require_exact_fraction(slope, "slope")
    m_val = max(abs(slope.numerator), slope.denominator)
    d = 0
    while (1 << d) < m_val:
        d += 1
    return d


def _build_katz_tao_11_6_spec() -> tuple[Any, ...]:
    atoms = [
        ("a", (1, 0, 0, 0, 0)),
        ("b", (0, 1, 0, 0, 0)),
        ("c", (0, 0, 1, 0, 0)),
        ("d", (0, 0, 0, 1, 0)),
        ("e", (0, 0, 0, 0, 1)),
        ("y4", (1, 1, 0, 0, -1)),
        ("s0", (1, 1, 0, 0, 0)),
        ("s1", (1, 0, 1, 0, 0)),
        ("s2", (0, 1, 0, 1, 0)),
        ("s3", (0, 0, 1, 1, 0)),
        ("s5", (0, 0, 1, 0, 1)),
    ]
    diff_pairs = [
        ((1, -1, 0, 0, 0), 0, 1),
        ((1, 0, -1, 0, 0), 0, 2),
        ((0, -1, 0, 1, 0), 3, 1),
        ((0, 0, -1, 1, 0), 3, 2),
        ((-1, -1, 0, 0, 2), 4, 5),
        ((0, 0, -1, 0, 1), 4, 2),
    ]
    z0, z1 = _bmask([0, 1]), _bmask([0, 2])
    z2, z3 = _bmask([3, 1]), _bmask([3, 2])
    z4, z5 = _bmask([4, 5]), _bmask([4, 2])
    copies = [
        (z0, z0, 1 << 0, z1),
        (z0 | z1, z0 | z1, _bmask([1, 2]), z2 | z3),
        (z0 | z1 | z2 | z3, z0 | z1, _bmask([6, 2]), z4 | z5),
    ]
    vs = [(0, 1, 6), (0, 2, 7), (3, 1, 8), (3, 2, 9), (4, 5, 6), (4, 2, 10)]
    eq_groups = [[_bmask([v[b] for b in range(3) if (sub >> b) & 1]) for v in vs] for sub in range(1, 8)]
    pats = ([0, 1, 6, 0, 2, 7], [0, 2, 7, 0, 1, 6], [3, 1, 8, 3, 2, 9], [3, 2, 9, 3, 1, 8], [4, 5, 6, 4, 2, 10], [4, 2, 10, 4, 5, 6])
    for sub in range(1, 64):
        eq_groups.append([_bmask([pat[b] for b in range(6) if (sub >> b) & 1]) for pat in pats])
    rhs = [(1 << 0, Fraction(2, 3)), (1 << 1, Fraction(2, 3)), (1 << 6, Fraction(1, 2))]
    duals = [
        ("copy", Fraction(1, 2), 0),
        ("copy", Fraction(1, 6), 1),
        ("copy", Fraction(1, 6), 2),
        ("submod", Fraction(1, 6), (768, 0, 5)),
        ("submod", Fraction(1, 6), (0, 0, 8)),
        ("submod", Fraction(1, 6), (0, 0, 9)),
        ("submod", Fraction(1, 6), (0, 1, 2)),
        ("submod", Fraction(1, 6), (0, 1, 7)),
        ("submod", Fraction(1, 6), (0, 5, 8)),
        ("submod", Fraction(1, 6), (256, 5, 9)),
        ("submod", Fraction(1, 6), (1, 8, 9)),
    ]
    return atoms, diff_pairs, copies, eq_groups, z0, rhs, duals


def _build_katz_tao_7_4_spec() -> tuple[Any, ...]:
    atoms = [
        ("x0", (1, 0, 0, 0)),
        ("y0", (0, 1, 0, 0)),
        ("s0", (1, 1, 0, 0)),
        ("t0", (1, 2, 0, 0)),
        ("y1", (0, 0, 1, 0)),
        ("s1", (1, 0, 1, 0)),
        ("t1", (1, 0, 2, 0)),
        ("x2", (0, 0, 0, 1)),
        ("y2", (1, 1, 0, -1)),
        ("t2", (2, 2, 0, -1)),
        ("s3", (0, 0, 1, 1)),
        ("t3", (0, 0, 2, 1)),
    ]
    diff_pairs = [
        ((1, -1, 0, 0), 0, 1),
        ((1, 0, -1, 0), 0, 4),
        ((-1, -1, 0, 2), 7, 8),
        ((0, 0, -1, 1), 7, 4),
    ]
    z0, z1 = _bmask([0, 1]), _bmask([0, 4])
    z2, z3 = _bmask([7, 8]), _bmask([7, 4])
    copies = [(z0, z0, 1 << 0, z1), (z0 | z1, z0 | z1, _bmask([2, 4]), z2 | z3)]
    vs = [(0, 1, 2, 3), (0, 4, 5, 6), (7, 8, 2, 9), (7, 4, 10, 11)]
    eq_groups = [[_bmask([v[b] for b in range(4) if (sub >> b) & 1]) for v in vs] for sub in range(1, 16)]
    pats = ([0, 1, 2, 3, 0, 4, 5, 6], [0, 4, 5, 6, 0, 1, 2, 3], [7, 8, 2, 9, 7, 4, 10, 11], [7, 4, 10, 11, 7, 8, 2, 9])
    for sub in range(1, 256):
        eq_groups.append([_bmask([pat[b] for b in range(8) if (sub >> b) & 1]) for pat in pats])
    rhs = [(1 << 0, Fraction(1, 2)), (1 << 1, Fraction(1, 2)), (1 << 2, Fraction(1, 2)), (1 << 3, Fraction(1, 4))]
    duals = [
        ("copy", Fraction(1, 2), 0),
        ("copy", Fraction(1, 4), 1),
        ("submod", Fraction(1, 4), (0, 1, 5)),
        ("submod", Fraction(1, 4), (0, 1, 6)),
        ("submod", Fraction(1, 4), (0, 5, 8)),
        ("submod", Fraction(1, 4), (256, 5, 11)),
    ]
    return atoms, diff_pairs, copies, eq_groups, z0, rhs, duals


def _int_basis_add(basis: list[tuple[int, list[int]]], vec: list[int], dim: int) -> tuple[list[tuple[int, list[int]]], bool]:
    v = list(vec)
    for pc, brow in basis:
        vc = v[pc]
        if vc != 0:
            pv = brow[pc]
            g = math.gcd(pv, abs(vc))
            a, b = pv // g, vc // g
            v = [a * v[j] - b * brow[j] for j in range(dim)]
    for j in range(dim):
        if v[j] != 0:
            g = 0
            for x in v:
                if x != 0:
                    g = math.gcd(g, abs(x))
            if g > 1:
                v = [x // g for x in v]
            if v[j] < 0:
                v = [-x for x in v]
            return basis + [(j, v)], True
    return basis, False


def _in_int_basis(basis: list[tuple[int, list[int]]], vec: list[int], dim: int) -> bool:
    v = list(vec)
    for pc, brow in basis:
        vc = v[pc]
        if vc != 0:
            pv = brow[pc]
            for j in range(dim):
                v[j] = pv * v[j] - vc * brow[j]
    return not any(v)


def _close_int_basis(
    mask: int,
    basis: list[tuple[int, list[int]]],
    vecs: list[list[int]],
    dvecs: list[tuple[list[int], int, int]],
    dim: int,
    memo_m: dict[int, tuple[int, int]],
    memo_b: dict[int, list[tuple[int, list[int]]]],
) -> tuple[int, int]:
    if mask in memo_m:
        return memo_m[mask]
    m = len(vecs)
    if len(basis) == dim:
        full_m = (1 << m) - 1
        res = (full_m, dim)
        memo_m[mask] = res
        memo_m[full_m] = res
        memo_b[full_m] = basis
        return res
    cur = mask
    b = basis
    while True:
        nxt = cur
        for i in range(m):
            if not ((nxt >> i) & 1):
                if _in_int_basis(b, vecs[i], dim):
                    nxt |= 1 << i
        grew = False
        for dv, xi, yi in dvecs:
            pm = (1 << xi) | (1 << yi)
            if (nxt & pm) != pm:
                if _in_int_basis(b, dv, dim):
                    for idx_e in (xi, yi):
                        if not ((nxt >> idx_e) & 1):
                            nxt |= 1 << idx_e
                            b, _ = _int_basis_add(b, vecs[idx_e], dim)
                            grew = True
        if not grew:
            res = (nxt, len(b))
            memo_m[mask] = res
            memo_m[nxt] = res
            memo_b[nxt] = b
            return res
        cur = nxt


def verify_primal_7_4_polymatroid(
    vecs: list[list[int]],
    dvecs: list[tuple[list[int], int, int]],
    dim: int,
    cap: int,
    copy_triples: list[tuple[int, int, int]],
) -> dict[str, Any]:
    """Live pure-Z verification of the primal Shannon polymatroid h(A) = min(cap, 4*rk(cl(A)) - n_dp(cl(A)))."""
    dim = require_exact_int(dim, "dim", lo=1, hi=16)
    cap = require_exact_int(cap, "cap", lo=1, hi=1_000)
    require_ok(type(vecs) is list and len(vecs) >= 4, "INVALID_POLYMATROID_INPUT", "vecs must be list of >= 4 vectors")
    clean_vecs: list[list[int]] = []
    for row in vecs:
        require_ok(type(row) is list and len(row) == dim, "INVALID_POLYMATROID_INPUT", "each vector must be list of len dim")
        cv = [require_exact_int(x, "poly_coord") for x in row]
        require_ok(any(cv), "ZERO_VECTOR_FORBIDDEN", "polymatroid atom vector must be nonzero")
        clean_vecs.append(cv)
    m = len(clean_vecs)
    full_m = (1 << m) - 1
    require_ok(type(dvecs) is list, "INVALID_POLYMATROID_INPUT", "dvecs must be exact list")
    clean_dvecs: list[tuple[list[int], int, int]] = []
    for dp_entry in dvecs:
        require_ok(type(dp_entry) is tuple and len(dp_entry) == 3, "INVALID_POLYMATROID_INPUT", "dvec entry must be 3-tuple")
        dv, xi, yi = dp_entry
        require_ok(type(dv) is list and len(dv) == dim, "INVALID_POLYMATROID_INPUT", "dvec must be list of len dim")
        cdv = [require_exact_int(x, "poly_dv_coord") for x in dv]
        require_ok(any(cdv), "ZERO_VECTOR_FORBIDDEN", "polymatroid diff vector must be nonzero")
        clean_dvecs.append((cdv, require_exact_int(xi, "poly_xi", lo=0, hi=m - 1), require_exact_int(yi, "poly_yi", lo=0, hi=m - 1)))
    require_ok(type(copy_triples) is list, "INVALID_POLYMATROID_INPUT", "copy_triples must be exact list")
    clean_triples: list[tuple[int, int, int]] = []
    for tr in copy_triples:
        require_ok(type(tr) is tuple and len(tr) == 3, "INVALID_POLYMATROID_INPUT", "copy_triple must be 3-tuple")
        clean_triples.append(
            (
                require_exact_int(tr[0], "poly_o", lo=0, hi=full_m),
                require_exact_int(tr[1], "poly_g", lo=0, hi=full_m),
                require_exact_int(tr[2], "poly_up", lo=0, hi=full_m),
            )
        )
    vecs = clean_vecs
    dvecs = clean_dvecs
    copy_triples = clean_triples
    pm_list = [_bmask([xi, yi]) for _, xi, yi in dvecs]
    memo_m: dict[int, tuple[int, int]] = {0: (0, 0)}
    memo_b: dict[int, list[tuple[int, list[int]]]] = {0: []}
    csets: dict[int, int] = {0: 0}
    exts: dict[int, list[int]] = {}
    front = [0]
    while front:
        nf: list[int] = []
        for c in front:
            if c == full_m:
                exts[c] = []
                continue
            rk_c = csets[c]
            if rk_c == dim - 1:
                if full_m not in csets:
                    csets[full_m] = dim
                    memo_m[full_m] = (full_m, dim)
                    nf.append(full_m)
                exts[c] = [full_m]
                continue
            b_c = memo_b[c]
            ex: set[int] = set()
            seen_ext = c
            for i in range(m):
                if not ((seen_ext >> i) & 1):
                    mk = c | (1 << i)
                    if mk in memo_m:
                        nc, nrk = memo_m[mk]
                    else:
                        b2, _ = _int_basis_add(b_c, vecs[i], dim)
                        nc, nrk = _close_int_basis(mk, b2, vecs, dvecs, dim, memo_m, memo_b)
                    ex.add(nc)
                    if nrk == rk_c + 1:
                        seen_ext |= nc
                    if nc not in csets:
                        csets[nc] = nrk
                        nf.append(nc)
            exts[c] = sorted(ex)
        front = nf

    h = {c: min(cap, 4 * rk - sum(1 for pm in pm_list if (c & pm) == pm)) for c, rk in csets.items()}
    mono_violations = 0
    submod_violations = 0
    for c, elist in exts.items():
        hc = h[c]
        for ca in elist:
            if h[ca] < hc:
                mono_violations += 1
        for ia, ca in enumerate(elist):
            hca = h[ca]
            rka = csets[ca]
            for cb in elist[ia + 1 :]:
                if (ca & cb) != c:
                    continue
                if hca + h[cb] >= cap + hc:
                    continue
                u_raw = ca | cb
                if u_raw in memo_m:
                    cab, _ = memo_m[u_raw]
                elif rka == dim - 1:
                    cab = full_m
                elif csets[cb] == dim - 1:
                    cab = full_m
                else:
                    b_u = memo_b[ca]
                    diff_bits = cb & ~ca
                    for j in range(m):
                        if (diff_bits >> j) & 1:
                            b_u, _ = _int_basis_add(b_u, vecs[j], dim)
                    cab, _ = _close_int_basis(u_raw, b_u, vecs, dvecs, dim, memo_m, memo_b)
                if hca + h[cb] < h[cab] + hc:
                    submod_violations += 1

    def cl_mask(mk: int) -> int:
        if mk in memo_m:
            return memo_m[mk][0]
        b_u: list[tuple[int, list[int]]] = []
        for j in range(m):
            if (mk >> j) & 1:
                b_u, _ = _int_basis_add(b_u, vecs[j], dim)
        return _close_int_basis(mk, b_u, vecs, dvecs, dim, memo_m, memo_b)[0]

    copies_exact = all(
        h[cl_mask(o_m | up_m)] + h[cl_mask(g_m)] == h[cl_mask(o_m)] + h[cl_mask(up_m)]
        for o_m, g_m, up_m in copy_triples
    )
    rhs_vals = [h[cl_mask(1 << idx)] for idx in range(4)]
    z0_val = h[cl_mask(_bmask([0, 1]))]
    require_ok(rhs_vals[0] > 0, "DEGENERATE_POLYMATROID", "singleton entropy h(X) must be > 0")
    ratio = Fraction(z0_val, rhs_vals[0])
    valid_7_4 = all(
        (
            mono_violations == 0,
            submod_violations == 0,
            copies_exact,
            rhs_vals == [4, 4, 4, 4],
            z0_val == 7,
        )
    )
    return {
        "closed_set_count": len(csets),
        "cap": cap,
        "mono_violations": mono_violations,
        "submod_violations": submod_violations,
        "copies_exact": copies_exact,
        "primal_lower_bound": format_fraction(ratio),
        "valid_7_4_polymatroid": valid_7_4,
        "h_map": h,
    }


def _probe_open_seam_4slope_2page() -> dict[str, Any]:
    """Live pure-Z/Q 2-page rank-3 stacking probe on the 4-slope 7/4 page P0 across 8 canonical glues."""
    atoms0, dp0, copies0, _eq0, _z0, _rhs0, _duals0 = _build_katz_tao_7_4_spec()
    vecs0 = [list(v) for _, v in atoms0]
    dvecs0 = [(list(dv), xi, yi) for dv, xi, yi in dp0]
    m0 = len(atoms0)

    p0_res = verify_primal_7_4_polymatroid(vecs0, dvecs0, 4, 12, [(o_m, g_m, up_m) for o_m, _, g_m, up_m in copies0])
    h0_map = p0_res["h_map"]
    p0_full = (1 << m0) - 1

    canonical_glues = (
        ("G1_2pair_z0z1", 127),
        ("G2_2pair_z0z2", 911),
        ("G3_1pair_z1_y2", 369),
        ("G4_1pair_z1_t2", 625),
        ("G5_syz4_y0s1y2s3", 1314),
        ("G6_syz4_t0t1y2s3", 1352),
        ("G7_syz4_t0s1t2s3", 1576),
        ("G8_ind3_s0s1s3", 1060),
    )

    def remap(mk: int, ids: list[int]) -> int:
        out = 0
        for i in range(m0):
            if (mk >> i) & 1:
                out |= 1 << ids[i]
        return out

    glue_receipts: list[dict[str, Any]] = []
    glue_ratios: list[Fraction] = []
    for name, gm in canonical_glues:
        basis_g: list[int] = []
        b_cur: list[tuple[int, list[int]]] = []
        for i in range(m0):
            if (gm >> i) & 1:
                b_new, added = _int_basis_add(b_cur, vecs0[i], 4)
                if added:
                    basis_g.append(i)
                    b_cur = b_new
        comp = next(i for i in range(m0) if _int_basis_add(b_cur, vecs0[i], 4)[1])
        bt = [[Fraction(vecs0[b][r], 1) for b in basis_g + [comp]] for r in range(4)]
        c_coords = {i: solve_linear_fraction(bt, [Fraction(x, 1) for x in vecs0[i]]) for i in range(m0)}
        den_lcm = 1
        for cs in c_coords.values():
            for x in cs:
                den_lcm = math.lcm(den_lcm, x.denominator)
        p0_vecs = [tuple(x * den_lcm for x in vecs0[i]) + (0,) for i in range(m0)]
        p1_vecs: list[tuple[int, ...]] = []
        for i in range(m0):
            cs = c_coords[i]
            gp = [sum((cs[k] * vecs0[basis_g[k]][r] for k in range(3)), Fraction(0, 1)) * den_lcm for r in range(4)]
            p1_vecs.append(tuple(int(x.numerator) for x in gp) + (int((cs[3] * den_lcm).numerator),))
        v_to_id: dict[tuple[int, ...], int] = {}
        vecs2: list[list[int]] = []
        p0_ids: list[int] = []
        p1_ids: list[int] = []
        for v in p0_vecs:
            v_to_id[v] = len(vecs2)
            p0_ids.append(len(vecs2))
            vecs2.append(list(v))
        for v in p1_vecs:
            if v in v_to_id:
                p1_ids.append(v_to_id[v])
            else:
                v_to_id[v] = len(vecs2)
                p1_ids.append(len(vecs2))
                vecs2.append(list(v))
        dvecs2: list[tuple[list[int], int, int]] = []
        seen_dp: set[tuple[tuple[int, ...], int, int]] = set()
        for dv, xi, yi in dp0:
            dv0 = tuple(x * den_lcm for x in dv) + (0,)
            k0 = (dv0, p0_ids[xi], p0_ids[yi])
            if k0 not in seen_dp:
                seen_dp.add(k0)
                dvecs2.append((list(dv0), p0_ids[xi], p0_ids[yi]))
            cs = solve_linear_fraction(bt, [Fraction(x, 1) for x in dv])
            gp = [sum((cs[k] * vecs0[basis_g[k]][r] for k in range(3)), Fraction(0, 1)) * den_lcm for r in range(4)]
            dv1 = tuple(int(x.numerator) for x in gp) + (int((cs[3] * den_lcm).numerator),)
            k1 = (dv1, p1_ids[xi], p1_ids[yi])
            if k1 not in seen_dp:
                seen_dp.add(k1)
                dvecs2.append((list(dv1), p1_ids[xi], p1_ids[yi]))

        def rk5(idxs: list[int]) -> int:
            b_tmp: list[tuple[int, list[int]]] = []
            for idx_v in idxs:
                b_tmp, _ = _int_basis_add(b_tmp, vecs2[idx_v], 5)
            return len(b_tmp)

        rk_p0 = rk5(p0_ids)
        rk_p1 = rk5(p1_ids)
        rk_g = rk5([i for i in range(m0) if (gm >> i) & 1])
        rk_u = rk5(list(range(len(vecs2))))
        mod_ok = (rk_u + rk_g == rk_p0 + rk_p1)
        n_dp_g = sum(1 for _, xi, yi in dvecs2 if (gm & _bmask([xi, yi])) == _bmask([xi, yi]))
        cap = 12 + n_dp_g

        if n_dp_g == 0:
            # Exact linear projection polymatroid h(A) = h0(pi(A)):
            # Verify h0(G) == 12 == h0(P0) and pi(v) = v[:4] + (v[4]/den_lcm)*comp maps P1 -> P0 exactly.
            comp_v = vecs0[comp]
            proj_ok = all(
                tuple(p1_vecs[i][r] + p1_vecs[i][4] * comp_v[r] for r in range(4)) == p0_vecs[i][:4]
                for i in range(m0)
            )
            proj_ratio = Fraction(p0_res["primal_lower_bound"])
            glue_ratios.append(proj_ratio)
            tight_ok = all((mod_ok, p0_res["valid_7_4_polymatroid"], h0_map[gm] == 12, h0_map[p0_full] == 12, proj_ok))
            glue_receipts.append(
                {
                    "glue_name": name,
                    "glue_mask": gm,
                    "atoms_2page": len(vecs2),
                    "rank_modular_5d": mod_ok,
                    "proof_method": "linear_projection_h0",
                    "cap": cap,
                    "primal_lower_bound": format_fraction(proj_ratio),
                    "tight_at_7_4": tight_ok,
                }
            )
        else:
            p0_m = _bmask(p0_ids)
            p1_m = _bmask(p1_ids)
            c_triples = [(remap(om, p0_ids), remap(g, p0_ids), remap(up, p0_ids)) for om, _, g, up in copies0]
            c_triples += [(remap(om, p1_ids), remap(g, p1_ids), remap(up, p1_ids)) for om, _, g, up in copies0]
            c_triples.append((p0_m, gm, p1_m))
            res2 = verify_primal_7_4_polymatroid(vecs2, dvecs2, 5, cap, c_triples)
            glue_ratios.append(Fraction(res2["primal_lower_bound"]))
            tight_ok = all((mod_ok, res2["valid_7_4_polymatroid"]))
            glue_receipts.append(
                {
                    "glue_name": name,
                    "glue_mask": gm,
                    "atoms_2page": len(vecs2),
                    "closed_sets_verified": res2["closed_set_count"],
                    "rank_modular_5d": mod_ok,
                    "proof_method": "full_5d_polymatroid",
                    "cap": cap,
                    "primal_lower_bound": res2["primal_lower_bound"],
                    "tight_at_7_4": tight_ok,
                }
            )

    all_tight = all(r["tight_at_7_4"] for r in glue_receipts)
    best_achieved = format_fraction(min(glue_ratios))
    return {
        "three_slope_published_records_N0": {"farnamfar_5page_std": "152/83", "farnamfar_18page_std": "2762/1509"},
        "p0_primal_closed_sets_verified": p0_res["closed_set_count"],
        "p0_primal_lower_bound": p0_res["primal_lower_bound"],
        "four_slope_2page_rank3_glues_probed": len(glue_receipts),
        "four_slope_2page_best_achieved": best_achieved,
        "all_glues_tight_at_7_4": all_tight,
        "beats_7_4_in_2page_rank3_cone": not all_tight,
        "per_glue_receipts": glue_receipts,
        "honest_novelty_grade": "N1",
    }


def verify_pillar1_katz_tao_entropy() -> dict[str, Any]:
    """Certify Pillar 1: 11/6 (over Z), 7/4 (over Z[1/2]), trivial 2 (with mono),
    ring-closure separation, PGL_2(Q) cross-ratio invariance, Tao rational complexity,
    and live pure-Z/Q 2-page rank-3 primal-polymatroid tightness proof across 8 glues."""
    # 1a. Classical Katz-Tao 11/6 over Z & 7/4 over Z[1/2]
    cert_11_6 = verify_shannon_certificate(*_build_katz_tao_11_6_spec(), ring="Z")
    cert_7_4 = verify_shannon_certificate(*_build_katz_tao_7_4_spec(), ring="Z[1/2]")

    # 1b. Trivial SD({0, inf}; -1) <= 2 using monotonicity + submodularity
    triv_atoms = [("X", (1, 0)), ("Y", (0, 1)), ("D", (1, -1))]
    cert_triv2 = verify_shannon_certificate(
        triv_atoms,
        [],
        [],
        [],
        1 << 2,
        [(1 << 0, Fraction(1, 1)), (1 << 1, Fraction(1, 1))],
        [("submod", Fraction(1, 1), (0, 0, 1)), ("mono", Fraction(1, 1), (1 << 2, 0))],
        ring="Z",
    )

    # 1c. Exact ring-closure separation witnesses: Z vs Z[1/2] vs Q
    sep_2y_z = in_ring_span([[1, 0], [1, 2]], [0, 1], 2, "Z")
    sep_2y_z2 = in_ring_span([[1, 0], [1, 2]], [0, 1], 2, "Z[1/2]")
    sep_3y_z2 = in_ring_span([[1, 0], [1, 3]], [0, 1], 2, "Z[1/2]")
    sep_3y_q = in_ring_span([[1, 0], [1, 3]], [0, 1], 2, "Q")

    # 1d. Exact PGL_2(Q) projective invariance of cross-ratios (0,1;inf,-1)=2 & (0,inf;1,-1)=-1
    pt0, pt1, ptinf, ptm1 = (0, 1), (1, 1), (1, 0), (-1, 1)
    cr_2 = projective_cross_ratio(pt0, pt1, ptinf, ptm1)
    cr_m1 = projective_cross_ratio(pt0, ptinf, pt1, ptm1)
    mobius_maps = ((2, 3, 5, 7), (1, -1, 1, 1), (3, -2, 1, 4), (0, 1, 1, 0))
    mobius_ok = True
    for mat in mobius_maps:
        q0, q1, qinf, qm1 = (_proj_apply_mobius(mat, p) for p in (pt0, pt1, ptinf, ptm1))
        if projective_cross_ratio(q0, q1, qinf, qm1) != cr_2:
            mobius_ok = False
        if projective_cross_ratio(q0, qinf, q1, qm1) != cr_m1:
            mobius_ok = False

    # 1e. Tao rational complexity D({0,1,inf}; a/b)
    complexity_table = [
        {"slope": format_fraction(s), "D_rational_complexity": tao_rational_complexity_base(s)}
        for s in TAO_SLOPES
    ]

    # 1f. Live pure-Z/Q open-seam 4-slope 2-page rank-3 stacking tightness probe
    probe_2page = _probe_open_seam_4slope_2page()

    all_verified = all(
        (
            cert_11_6["exponent"] == "11/6",
            cert_7_4["exponent"] == "7/4",
            cert_triv2["exponent"] == "2",
            not sep_2y_z,
            sep_2y_z2,
            not sep_3y_z2,
            sep_3y_q,
            cr_2 == Fraction(2, 1),
            cr_m1 == Fraction(-1, 1),
            mobius_ok,
            [r["D_rational_complexity"] for r in complexity_table] == [0, 1, 2, 1, 2, 3, 3, 4],
            probe_2page["p0_primal_closed_sets_verified"] == 100,
            probe_2page["all_glues_tight_at_7_4"],
            probe_2page["four_slope_2page_rank3_glues_probed"] == 8,
        )
    )

    return {
        "all_verified": all_verified,
        "katz_tao_11_6_certificate": cert_11_6,
        "katz_tao_7_4_certificate": cert_7_4,
        "trivial_2_mono_certificate": cert_triv2,
        "ring_closure_separation": {
            "y_in_Z_span_x_xplus2y": sep_2y_z,
            "y_in_Zhalf_span_x_xplus2y": sep_2y_z2,
            "y_in_Zhalf_span_x_xplus3y": sep_3y_z2,
            "y_in_Q_span_x_xplus3y": sep_3y_q,
        },
        "cross_ratio_invariance": {
            "cr_0_1_inf_m1": format_fraction(cr_2),
            "cr_0_inf_1_m1": format_fraction(cr_m1),
            "mobius_maps_verified": len(mobius_maps),
            "all_invariant": mobius_ok,
        },
        "tao_rational_complexity": complexity_table,
        "open_seam_probe_honest_status": probe_2page,
    }


# ============================================================================
# 3. Pillar 2 — von Mangoldt Downward Markov Chains & Odd Banks-Martin
# ============================================================================

def ln_interval_exact(n: int, terms: int = 10) -> tuple[Fraction, Fraction]:
    """Pure-Q rational enclosure ln_lo(n) < ln(n) < ln_hi(n) via artanh series."""
    n = require_exact_int(n, "n", lo=2, hi=10_000)
    terms = require_exact_int(terms, "terms", lo=1, hi=30)
    u = Fraction(n - 1, n + 1)
    u2 = u * u
    lo = Fraction(0, 1)
    p_u = u
    for j in range(terms):
        lo += Fraction(2, 2 * j + 1) * p_u
        p_u *= u2
    rem = Fraction(2, 2 * terms + 1) * p_u / (Fraction(1, 1) - u2)
    return lo, lo + rem


def von_mangoldt_hit_prob(start: int, target_set: set[int], l_weights: dict[int, Fraction]) -> Fraction:
    """Exact pure-Q hitting probability of antichain target_set from start under P_L(n -> n/p^k)."""
    start = require_exact_int(start, "start", lo=1, hi=10**8)
    require_ok(type(target_set) is set, "INVALID_TARGET_SET", "target_set must be exact set")
    require_ok(type(l_weights) is dict and len(l_weights) >= 1, "INVALID_L_WEIGHTS", "l_weights must be non-empty dict")
    for p, w in l_weights.items():
        require_ok(is_prime_small(p), "NON_PRIME_WEIGHT_KEY", f"key {p} must be prime")
        require_ok(require_exact_fraction(w, f"L[{p}]") > 0, "NONPOSITIVE_WEIGHT", f"L[{p}] must be > 0")
    memo: dict[int, Fraction] = {}

    def _prob(n: int) -> Fraction:
        if n in target_set:
            return Fraction(1, 1)
        if n == 1:
            return Fraction(0, 1)
        if n in memo:
            return memo[n]
        fac = factorize_small(n)
        for p in fac:
            require_ok(p in l_weights, "MISSING_PRIME_WEIGHT", f"missing weight for prime {p}")
        tot = sum((Fraction(e, 1) * l_weights[p] for p, e in fac.items()), Fraction(0, 1))
        res = Fraction(0, 1)
        for p, e in fac.items():
            step_p = l_weights[p] / tot
            pk = p
            for _ in range(e):
                res += step_p * _prob(n // pk)
                pk *= p
        memo[n] = res
        return res

    return _prob(start)


def is_primitive_antichain(nums: list[int]) -> bool:
    """True iff nums is a non-empty list of distinct integers >= 2 with no pairwise divisibility."""
    require_ok(type(nums) is list and len(nums) >= 1, "INVALID_ANTICHAIN", "nums must be non-empty list")
    cleaned = [require_exact_int(x, "antichain_elem", lo=2) for x in nums]
    for i, a in enumerate(cleaned):
        for j, b in enumerate(cleaned):
            if i != j and b % a == 0:
                return False
    return True


def verify_pillar2_von_mangoldt_chains() -> dict[str, Any]:
    """Certify Pillar 2 (arXiv:2605.00301v1): generalized von Mangoldt kernel identity,
    210 saturation vs. 180 leap slack, perfect & primitive-abundant antichains,
    pure-Q Taylor log enclosures, Odd Banks-Martin monotonicity & (6.2) sub-invariance,
    and the 2 in Q obstruction."""
    l_unif = {p: Fraction(1, 1) for p in (2, 3, 5, 7)}
    l_dec = RATIONAL_LOG_APPROX

    # 2a. Verify sum_{q | n} Lambda_L(q) == L(n) across ALL {2,3,5,7}-smooth 2 <= n <= 120
    smooth_nums: list[int] = []
    kernel_id_ok = True
    for n in range(2, 121):
        fac = factorize_small(n)
        if all(p in (2, 3, 5, 7) for p in fac):
            smooth_nums.append(n)
            for l_map in (l_unif, l_dec):
                l_n = sum((Fraction(e, 1) * l_map[p] for p, e in fac.items()), Fraction(0, 1))
                lam_sum = Fraction(0, 1)
                for d in range(2, n + 1):
                    if n % d == 0:
                        df = factorize_small(d)
                        if len(df) == 1:
                            p_only = next(iter(df))
                            lam_sum += l_map[p_only]
                if lam_sum != l_n:
                    kernel_id_ok = False

    # 2b. Squarefree 210 saturation == 1 vs. 180 prime-power leap slack < 1 (Omega = 2)
    divs_210 = [d for d in range(2, 211) if 210 % d == 0]
    a210_om2 = {d for d in divs_210 if sum(factorize_small(d).values()) == 2}
    divs_180 = [d for d in range(2, 181) if 180 % d == 0]
    a180_om2 = {d for d in divs_180 if sum(factorize_small(d).values()) == 2}
    h210_unif = von_mangoldt_hit_prob(210, a210_om2, l_unif)
    h210_dec = von_mangoldt_hit_prob(210, a210_om2, l_dec)
    h180_unif = von_mangoldt_hit_prob(180, a180_om2, l_unif)
    h180_dec = von_mangoldt_hit_prob(180, a180_om2, l_dec)

    # 2c. Explicit perfect-number & primitive-abundant antichains linking to S22a/S22b/S25
    perf_antichain = [6, 28, 496]
    prim_ab_antichain = [12, 18, 20, 30, 42, 70, 945]
    perf_is_prim = is_primitive_antichain(perf_antichain)
    prim_ab_is_prim = is_primitive_antichain(prim_ab_antichain)
    l_perf = {2: Fraction(1, 1), 3: Fraction(1, 1), 7: Fraction(1, 1), 31: Fraction(1, 1)}
    hit_perf_from_lcm = von_mangoldt_hit_prob(10_416, set(perf_antichain), l_perf)
    hit_prim_ab_from_lcm = von_mangoldt_hit_prob(3_780, set(prim_ab_antichain), l_unif)

    # 2d. Pure-Q Taylor log enclosures: Odd Banks-Martin Q={3,5,7} vs 2 in Q obstruction
    ln_map = {p: ln_interval_exact(p, 10) for p in (2, 3, 5, 7)}

    def f_enclosure(nums: list[int]) -> tuple[Fraction, Fraction]:
        f_lo = Fraction(0, 1)
        f_hi = Fraction(0, 1)
        for num in nums:
            fac = factorize_small(num)
            l_lo = sum((e * ln_map[p][0] for p, e in fac.items()), Fraction(0, 1))
            l_hi = sum((e * ln_map[p][1] for p, e in fac.items()), Fraction(0, 1))
            f_lo += Fraction(1, num) / l_hi
            f_hi += Fraction(1, num) / l_lo
        return f_lo, f_hi

    q_odd = (3, 5, 7)
    n1_odd = list(q_odd)
    n2_odd = sorted({p * q for p in q_odd for q in q_odd})
    n3_odd = sorted({p * q * r for p in q_odd for q in q_odd for r in q_odd})
    f1_lo, f1_hi = f_enclosure(n1_odd)
    f2_lo, f2_hi = f_enclosure(n2_odd)
    f3_lo, f3_hi = f_enclosure(n3_odd)

    # Exact Section 6 (6.2) Odd Banks-Martin local sub-invariance upper bound <= 1 on N_2 U N_3 ({3,5,7})
    beta_odd = {p: Fraction(p, p - 2) for p in q_odd}
    max_subinv_hi = Fraction(0, 1)
    for m in n2_odd + n3_odd:
        fac = factorize_small(m)
        l_hi = sum((fac.get(p, 0) * ln_map[p][1] for p in q_odd), Fraction(0, 1))
        lam_lo = sum((fac.get(p, 0) * beta_odd[p] * ln_map[p][0] for p in q_odd), Fraction(0, 1))
        lhs_hi = Fraction(0, 1)
        for p in q_odd:
            lhs_hi += (
                l_hi
                * (fac.get(p, 0) + 1)
                * beta_odd[p]
                * ln_map[p][1]
                / (p * (l_hi + ln_map[p][0]) * (lam_lo + beta_odd[p] * ln_map[p][0]))
            )
        if lhs_hi > max_subinv_hi:
            max_subinv_hi = lhs_hi

    # 2 in Q obstruction: beta_2 = 2/(2-2) pole + 2*nu_0(2) > 1 vs p*nu_0(p) < 1 for odd p >= 3
    two_nu0_lo = Fraction(1, 1) / ln_map[2][1]
    three_nu0_hi = Fraction(1, 1) / ln_map[3][0]
    q_with_2_n1 = f_enclosure([2, 3])
    q_with_2_n2 = f_enclosure([4, 6, 9])

    all_verified = all(
        (
            len(smooth_nums) == 49,
            kernel_id_ok,
            len(a210_om2) == 6,
            len(a180_om2) == 5,
            h210_unif == Fraction(1, 1),
            h210_dec == Fraction(1, 1),
            h180_unif == Fraction(23, 30),
            h180_dec == Fraction(7925799930620659238, 9872377837458467625),
            perf_is_prim,
            prim_ab_is_prim,
            hit_perf_from_lcm <= 1,
            hit_prim_ab_from_lcm <= 1,
            f1_lo > f2_hi,
            f2_lo > f3_hi,
            max_subinv_hi <= 1,
            two_nu0_lo > 1,
            three_nu0_hi < 1,
            q_with_2_n1[0] > q_with_2_n2[1],
        )
    )

    return {
        "all_verified": all_verified,
        "smooth_2_to_120_count": len(smooth_nums),
        "von_mangoldt_kernel_identity_ok": kernel_id_ok,
        "hit_210_omega2_uniform": format_fraction(h210_unif),
        "hit_210_omega2_log_approx": format_fraction(h210_dec),
        "hit_180_omega2_uniform": format_fraction(h180_unif),
        "hit_180_omega2_log_approx": format_fraction(h180_dec),
        "perfect_antichain_hit_from_10416": format_fraction(hit_perf_from_lcm),
        "primitive_abundant_antichain_hit_from_3780": format_fraction(hit_prim_ab_from_lcm),
        "odd_banks_martin_Q357": {
            "f_N1_gt_f_N2_certified": f1_lo > f2_hi,
            "f_N2_gt_f_N3_certified": f2_lo > f3_hi,
            "subinvariance_eq62_max_upper_bound_le_1": max_subinv_hi <= 1,
            "beta_weights": {str(p): format_fraction(beta_odd[p]) for p in q_odd},
        },
        "two_in_Q_obstruction": {
            "beta_2_denominator_p_minus_2": 2 - 2,
            "two_nu0_lower_gt_1": two_nu0_lo > 1,
            "three_nu0_upper_lt_1": three_nu0_hi < 1,
            "remark63_k1_erdos_strong_Q23_holds": q_with_2_n1[0] > q_with_2_n2[1],
            "full_monotonicity_failure_note": "N0: Lichtman (1909.00804) proved f(N_k) fails monotonicity at k=6 on all primes; 2605.00301 Lemma 6.1 beta_p=p/(p-2) hits an exact pole at p=2.",
        },
    }


# ============================================================================
# 4. Pillar 3 — Collatz 3-Adic Syracuse Transfer & Gilbreath Obstructions
# ============================================================================

def gilbreath_left_diagonal(seq: list[int]) -> list[int]:
    """Compute exact integer left diagonal of the Gilbreath absolute-difference triangle."""
    require_ok(type(seq) is list and len(seq) >= 2, "INVALID_SEQ", "seq must be list of len >= 2")
    row = [require_exact_int(x, "seq_elem", lo=0) for x in seq]
    diag = [row[0]]
    while len(row) > 1:
        row = [abs(row[i + 1] - row[i]) for i in range(len(row) - 1)]
        diag.append(row[0])
    return diag


def syracuse_3adic_markov(m: int) -> dict[str, Any]:
    """Exact pure-Q fine-scale 3-adic Syracuse Markov chain on (Z/3^m Z)^x (m in {2, 3})."""
    m = require_exact_int(m, "m", lo=2, hi=3)
    mod = 3**m
    states = [x for x in range(1, mod) if x % 3 != 0]
    idx = {s: i for i, s in enumerate(states)}
    k_states = len(states)
    ord2 = 2 * (3 ** (m - 1))
    inv2 = pow(2, -1, mod)
    denom = (1 << ord2) - 1
    t_mat = [[Fraction(0, 1)] * k_states for _ in range(k_states)]
    for i, x in enumerate(states):
        cur = (3 * x + 1) % mod
        for j in range(1, ord2 + 1):
            cur = (cur * inv2) % mod
            t_mat[i][idx[cur]] += Fraction(1 << (ord2 - j), denom)
    row_sums_ok = all(sum(row, Fraction(0, 1)) == Fraction(1, 1) for row in t_mat)
    sys_a = [
        [t_mat[j][i] - (Fraction(1, 1) if i == j else Fraction(0, 1)) for j in range(k_states)]
        for i in range(k_states)
    ]
    sys_b = [Fraction(0, 1)] * k_states
    sys_a[k_states - 1] = [Fraction(1, 1)] * k_states
    sys_b[k_states - 1] = Fraction(1, 1)
    pi_star = solve_linear_fraction(sys_a, sys_b)
    residuals_zero = all(
        sum((pi_star[j] * t_mat[j][i] for j in range(k_states)), Fraction(0, 1)) == pi_star[i]
        for i in range(k_states)
    )
    unif = Fraction(1, k_states)
    tv_dist = sum((abs(p - unif) for p in pi_star), Fraction(0, 1)) / 2
    return {
        "m": m,
        "modulus": mod,
        "state_count": k_states,
        "ord_2_mod_3m": ord2,
        "row_stochastic_exact": row_sums_ok,
        "stationary_residual_zero": residuals_zero,
        "stationary_min": format_fraction(min(pi_star)),
        "stationary_max": format_fraction(max(pi_star)),
        "max_to_min_ratio": format_fraction(max(pi_star) / min(pi_star)),
        "tv_distance_from_uniform": format_fraction(tv_dist),
        "stationary_pi_mod9": {str(states[i]): format_fraction(pi_star[i]) for i in range(k_states)} if m == 2 else {},
    }


def verify_pillar3_syracuse_and_gilbreath() -> dict[str, Any]:
    """Certify Pillar 3 (arXiv:1909.03562 + arXiv:2607.08712v1): 2-adic parity bijection,
    exact Syracuse cycle equation (short circuits + negative {-1,-5,-17}), 3-adic Markov
    chains mod 9 & 27, Gilbreath 500 primes, and Chase-Hunter-Tao failure witnesses."""
    # 3a. 2-adic parity-vector bijection on Z/2^k Z for k in 1..8
    bijection_ok = True
    for k in range(1, 9):
        mod = 1 << k
        vecs: set[tuple[int, ...]] = set()
        for r in range(mod):
            x = r
            pv: list[int] = []
            for _ in range(k):
                bit = x & 1
                pv.append(bit)
                x = (3 * x + 1) // 2 if bit else x // 2
            vecs.add(tuple(pv))
        if len(vecs) != mod:
            bijection_ok = False

    # 3b. Exact Syracuse cycle equation n = C(a) / (2^S - 3^k) for 1 <= k <= 5, k <= S <= 2k
    pos_cycles: set[tuple[int, int]] = set()
    neg_cycles: set[tuple[int, int]] = set()
    compositions_checked = 0
    for k in range(1, 6):
        for s_sum in range(k, 2 * k + 1):
            denom = (1 << s_sum) - (3**k)
            if denom == 0:
                continue
            for cuts in itertools.combinations(range(1, s_sum), k - 1):
                compositions_checked += 1
                parts: list[int] = []
                prev = 0
                for c in cuts + (s_sum,):
                    parts.append(c - prev)
                    prev = c
                c_num = 0
                acc = 0
                for j, aj in enumerate(parts):
                    c_num += (3 ** (k - 1 - j)) * (1 << acc)
                    acc += aj
                if c_num % denom == 0:
                    n_val = c_num // denom
                    if n_val % 2 != 0:
                        cur = n_val
                        orb: list[int] = []
                        for _ in range(k):
                            orb.append(cur)
                            u = 3 * cur + 1
                            v2 = (u & -u).bit_length() - 1
                            cur = u >> v2
                        if cur == n_val:
                            canon = min(orb) if n_val > 0 else max(orb)
                            if n_val > 0:
                                pos_cycles.add((canon, len(set(orb))))
                            else:
                                neg_cycles.add((canon, len(set(orb))))

    # Direct certification of the 7-step negative Syracuse cycle starting at -17 (k=7, S=11)
    cur17 = -17
    orb17: list[int] = []
    a17: list[int] = []
    for _ in range(7):
        orb17.append(cur17)
        u = 3 * cur17 + 1
        v2 = (u & -u).bit_length() - 1
        a17.append(v2)
        cur17 = u >> v2
    c17 = 0
    acc17 = 0
    for j, aj in enumerate(a17):
        c17 += (3 ** (6 - j)) * (1 << acc17)
        acc17 += aj
    neg17_exact = all((cur17 == -17, len(set(orb17)) == 7, Fraction(c17, (1 << sum(a17)) - 3**7) == Fraction(-17, 1)))

    # 3c. Fine-scale 3-adic Syracuse Markov matrices mod 9 & mod 27 + live 2-adic Haar drift
    mk9 = syracuse_3adic_markov(2)
    mk27 = syracuse_3adic_markov(3)
    # Live exact pure-Q 2-adic Haar valuation expectation over odd residues mod 2^8
    m_haar = 8
    odd_count = 1 << (m_haar - 1)
    ev2_trunc = sum(
        (Fraction(min(((3 * x + 1) & -(3 * x + 1)).bit_length() - 1, m_haar), 1) for x in range(1, 1 << m_haar, 2)),
        Fraction(0, 1),
    ) / odd_count
    ev2_trunc_formula = Fraction(2, 1) - Fraction(1, 1 << (m_haar - 1))
    half = Fraction(1, 2)
    s_telescoping = sum((Fraction(k, 1 << k) for k in range(1, m_haar + 1)), Fraction(0, 1))
    telescoping_ok = ((Fraction(1, 1) - half) ** 2) * s_telescoping == half - Fraction(m_haar + 2, 1 << (m_haar + 2))
    ev2_haar = half / ((Fraction(1, 1) - half) ** 2)
    geom_step_ratio = Fraction(3, 1) / (Fraction(2, 1) ** ev2_haar.numerator)

    # 3d. Gilbreath on first 500 primes + Chase-Hunter-Tao failure witnesses
    primes_500: list[int] = []
    cand = 2
    while len(primes_500) < 500:
        if is_prime_small(cand):
            primes_500.append(cand)
        cand += 1
    g_diag = gilbreath_left_diagonal(primes_500)
    gilbreath_500_all_ones = all(x == 1 for x in g_diag[1:])

    cht_zero_diag = gilbreath_left_diagonal([2, 3, 5, 7, 9, 11, 13, 15, 25])
    cht_d2_diag = gilbreath_left_diagonal([2, 3, 7, 9, 13, 15, 19])
    cht_d3_diag = gilbreath_left_diagonal([2, 3, 9, 12, 18, 21, 27])

    all_verified = all(
        (
            bijection_ok,
            sorted(pos_cycles) == [(1, 1)],
            sorted(neg_cycles) == [(-5, 2), (-1, 1)],
            neg17_exact,
            mk9["row_stochastic_exact"],
            mk9["stationary_residual_zero"],
            mk27["row_stochastic_exact"],
            mk27["stationary_residual_zero"],
            ev2_trunc == ev2_trunc_formula,
            telescoping_ok,
            ev2_haar == Fraction(2, 1),
            geom_step_ratio == Fraction(3, 4),
            geom_step_ratio < 1,
            primes_500[-1] == 3571,
            gilbreath_500_all_ones,
            any(x != 1 for x in cht_zero_diag[1:]),
            any(x != 1 for x in cht_d2_diag[1:]),
            any(x != 1 for x in cht_d3_diag[1:]),
        )
    )

    return {
        "all_verified": all_verified,
        "two_adic_parity_bijection_k1_to_8": bijection_ok,
        "short_circuit_compositions_checked": compositions_checked,
        "positive_short_cycles": [list(x) for x in sorted(pos_cycles)],
        "negative_short_cycles": [list(x) for x in sorted(neg_cycles)],
        "negative_17_cycle": {"orbit": orb17, "valuations": a17, "rational_formula_exact": neg17_exact},
        "syracuse_3adic_mod9": mk9,
        "syracuse_3adic_mod27": mk27,
        "syracuse_2adic_haar_drift": {
            "precision_bits_m": m_haar,
            "odd_residues_checked": odd_count,
            "truncated_ev2_mod256": format_fraction(ev2_trunc),
            "truncated_formula_matches": ev2_trunc == ev2_trunc_formula,
            "telescoping_identity_exact": telescoping_ok,
            "asymptotic_haar_ev2": format_fraction(ev2_haar),
            "asymptotic_haar_geometric_drift": format_fraction(geom_step_ratio),
            "strictly_contractive": geom_step_ratio < 1,
        },
        "geometric_contraction_ratio": format_fraction(geom_step_ratio),
        "logarithmic_density_note": "N0: Tao (1909.03562) proves almost all orbits attain bounded values in logarithmic density; full Collatz remains open.",
        "gilbreath_first_500_primes": {
            "p_500": primes_500[-1],
            "left_diagonal_all_ones": gilbreath_500_all_ones,
        },
        "chase_hunter_tao_witnesses": {
            "long_zero_block_left_diag": cht_zero_diag,
            "shallow_0_2_block_left_diag": cht_d2_diag,
            "shallow_0_3_block_left_diag": cht_d3_diag,
        },
    }


# ============================================================================
# 5. Pillar 4 — Singer Sidon Sets, 2-Golomb, Gowers U^2/U^3/U^4 & Ruzsa
# ============================================================================

def satisfies_cot_diameter_bound(k_len: int, diameter: int) -> bool:
    """Exact integer-square elimination of Carter-O'Bryant-Tao diam >= k^2 - (189/100) k^{3/2}."""
    k_len = require_exact_int(k_len, "k_len", lo=1)
    diameter = require_exact_int(diameter, "diameter", lo=0)
    gap = k_len * k_len - diameter
    return gap <= 0 or (10_000 * gap * gap <= 189 * 189 * (k_len**3))


def construct_singer_sidon(q: int) -> dict[str, Any]:
    """Construct exact Singer difference set in Z/(q^2+q+1)Z for q in {2, 3, 4, 5, 7}."""
    q = require_exact_int(q, "q", lo=2, hi=7)
    require_ok(q in (2, 3, 4, 5, 7), "INVALID_SINGER_ORDER", "q must be a prime power in {2, 3, 4, 5, 7}")
    modulus = q * q + q + 1
    if q == 4:
        f4_mul = ((0, 0, 0, 0), (0, 1, 2, 3), (0, 2, 3, 1), (0, 3, 1, 2))
        f4_inv = (0, 1, 3, 2)
        c2, c1, c0 = 1, 1, 2
        v = (1, 0, 0)
        s_set: list[int] = []
        seen_p: set[tuple[int, int, int]] = set()
        for k in range(modulus):
            lead = next(c for c in v if c != 0)
            iv = f4_inv[lead]
            seen_p.add((f4_mul[v[0]][iv], f4_mul[v[1]][iv], f4_mul[v[2]][iv]))
            if v[2] == 0:
                s_set.append(k)
            v = (f4_mul[v[2]][c0], v[0] ^ f4_mul[v[2]][c1], v[1] ^ f4_mul[v[2]][c2])
    else:
        poly_map = {2: (1, 0, 1), 3: (2, 0, 1), 5: (1, 0, 1), 7: (1, 1, 2)}
        c2, c1, c0 = poly_map[q]
        v = (1, 0, 0)
        s_set = []
        seen_p = set()
        for k in range(modulus):
            lead = next(c for c in v if c != 0)
            iv = pow(lead, -1, q)
            seen_p.add(((v[0] * iv) % q, (v[1] * iv) % q, (v[2] * iv) % q))
            if v[2] == 0:
                s_set.append(k)
            v = ((-v[2] * c0) % q, (v[0] - v[2] * c1) % q, (v[1] - v[2] * c2) % q)

    diffs = [(a - b) % modulus for a in s_set for b in s_set if a != b]
    k_len = len(s_set)
    diam = max(s_set) - min(s_set)
    cot_bound_ok = satisfies_cot_diameter_bound(k_len, diam)
    return {
        "q": q,
        "modulus": modulus,
        "k": k_len,
        "sidon_set": s_set,
        "projective_points_covered": len(seen_p),
        "duplicate_nonzero_differences": len(diffs) - len(set(diffs)),
        "diameter": diam,
        "carter_obryant_tao_bound_ok": cot_bound_ok,
    }


def _validate_f2_4_vals(vals: Any) -> list[int]:
    require_ok(type(vals) is list and len(vals) == 16, "INVALID_WHT_LEN", "vals must be list of length 16")
    return [require_exact_int(x, "wht_entry", lo=-1, hi=1) for x in vals]


def wht_f2_4(vals: list[int]) -> list[int]:
    """Exact integer Walsh-Hadamard transform on F_2^4 (length 16)."""
    a = _validate_f2_4_vals(vals)
    h = 1
    while h < 16:
        for i in range(0, 16, h * 2):
            for j in range(i, i + h):
                u, v = a[j], a[j + h]
                a[j] = u + v
                a[j + h] = u - v
        h <<= 1
    return a


def gowers_u2_pow4_f2_4(vals: list[int]) -> Fraction:
    w = wht_f2_4(vals)
    return Fraction(sum(c**4 for c in w), 16**4)


def gowers_u3_pow8_f2_4(vals: list[int]) -> Fraction:
    clean = _validate_f2_4_vals(vals)
    tot = Fraction(0, 1)
    for h1 in range(16):
        df = [clean[x] * clean[x ^ h1] for x in range(16)]
        tot += gowers_u2_pow4_f2_4(df)
    return tot / 16


def gowers_u4_pow16_f2_4(vals: list[int]) -> Fraction:
    clean = _validate_f2_4_vals(vals)
    tot = Fraction(0, 1)
    for h1 in range(16):
        df1 = [clean[x] * clean[x ^ h1] for x in range(16)]
        for h2 in range(16):
            df2 = [df1[x] * df1[x ^ h2] for x in range(16)]
            tot += gowers_u2_pow4_f2_4(df2)
    return tot / 256


def verify_pillar4_sidon_gowers_ruzsa() -> dict[str, Any]:
    """Certify Pillar 4 (2610.36207v1 + 2311.05762 + 2601.00961v1): Singer Sidon sets
    q in {2,3,4,5,7}, 2-Golomb ruler witness, Gowers U^2/U^3/U^4 on F_2^4, and Ruzsa."""
    singers = [construct_singer_sidon(q) for q in (2, 3, 4, 5, 7)]

    # Exact 2-Golomb ruler witness (max nonzero difference multiplicity == 2)
    golomb2 = [0, 1, 2, 5, 7]
    diff_mults: dict[int, int] = {}
    for a in golomb2:
        for b in golomb2:
            if a > b:
                diff_mults[a - b] = diff_mults.get(a - b, 0) + 1
    max_mult_g2 = max(diff_mults.values())

    # Exact Gowers norms on F_2^4
    f_lin = [1 if ((x & 1) == 0) else -1 for x in range(16)]
    f_bent = [1 if ((((x & 1) * ((x >> 1) & 1)) ^ (((x >> 2) & 1) * ((x >> 3) & 1))) == 0) else -1 for x in range(16)]
    f_cub = [1 if (((x & 1) * ((x >> 1) & 1) * ((x >> 2) & 1)) == 0) else -1 for x in range(16)]
    bent_wht_flat = all(abs(c) == 4 for c in wht_f2_4(f_bent))

    lin_norms = (gowers_u2_pow4_f2_4(f_lin), gowers_u3_pow8_f2_4(f_lin), gowers_u4_pow16_f2_4(f_lin))
    bent_norms = (gowers_u2_pow4_f2_4(f_bent), gowers_u3_pow8_f2_4(f_bent), gowers_u4_pow16_f2_4(f_bent))
    cub_norms = (gowers_u2_pow4_f2_4(f_cub), gowers_u3_pow8_f2_4(f_cub), gowers_u4_pow16_f2_4(f_cub))

    # Exact Ruzsa triangle inequality |A - C| * |B| <= |A - B| * |B - C| & Plunnecke-Ruzsa doubling
    set_a = {0, 1, 2, 10, 11, 12}
    set_b = {0, 1, 2, 3, 4}
    set_c = {0, 3, 6, 9, 12}

    def diffset(s1: set[int], s2: set[int]) -> set[int]:
        return {x - y for x in s1 for y in s2}

    def sumset(s1: set[int], s2: set[int]) -> set[int]:
        return {x + y for x in s1 for y in s2}

    ruzsa_lhs = len(diffset(set_a, set_c)) * len(set_b)
    ruzsa_rhs = len(diffset(set_a, set_b)) * len(diffset(set_b, set_c))
    k_doub = Fraction(len(sumset(set_a, set_a)), len(set_a))
    pr_2a_minus_a = len(diffset(sumset(set_a, set_a), set_a))
    pr_bound = (k_doub**3) * len(set_a)

    all_verified = all(
        (
            all(s["duplicate_nonzero_differences"] == 0 for s in singers),
            all(s["carter_obryant_tao_bound_ok"] for s in singers),
            max_mult_g2 == 2,
            bent_wht_flat,
            lin_norms == (Fraction(1, 1), Fraction(1, 1), Fraction(1, 1)),
            bent_norms == (Fraction(1, 16), Fraction(1, 1), Fraction(1, 1)),
            cub_norms == (Fraction(11, 32), Fraction(11, 32), Fraction(1, 1)),
            ruzsa_lhs <= ruzsa_rhs,
            Fraction(pr_2a_minus_a, 1) <= pr_bound,
        )
    )

    return {
        "all_verified": all_verified,
        "singer_sidon_sets": singers,
        "two_golomb_ruler_witness": {"set": golomb2, "max_difference_multiplicity": max_mult_g2},
        "gowers_f2_4": {
            "bent_wht_all_abs_4": bent_wht_flat,
            "linear_x0": {"U2_4": format_fraction(lin_norms[0]), "U3_8": format_fraction(lin_norms[1]), "U4_16": format_fraction(lin_norms[2])},
            "bent_x0x1_plus_x2x3": {"U2_4": format_fraction(bent_norms[0]), "U3_8": format_fraction(bent_norms[1]), "U4_16": format_fraction(bent_norms[2])},
            "cubic_x0x1x2": {"U2_4": format_fraction(cub_norms[0]), "U3_8": format_fraction(cub_norms[1]), "U4_16": format_fraction(cub_norms[2])},
        },
        "ruzsa_and_plunnecke": {
            "ruzsa_triangle_lhs": ruzsa_lhs,
            "ruzsa_triangle_rhs": ruzsa_rhs,
            "doubling_constant_K": format_fraction(k_doub),
            "size_2A_minus_A": pr_2a_minus_a,
            "plunnecke_ruzsa_K3_A_bound": format_fraction(pr_bound),
        },
    }


# ============================================================================
# 6. Pillar 5 — Dyadic NS Blowup Barrier, DPTZ Identity & ETP Magmas
# ============================================================================

def dyadic_ns_bilinear(x_shells: list[Fraction], lam: Fraction) -> list[Fraction]:
    """Exact Katz-Pavlovic / Tao dyadic bilinear shell operator B_n = lam^{n-1} X_{n-1}^2 - lam^n X_n X_{n+1}."""
    require_ok(type(x_shells) is list and len(x_shells) >= 2, "INVALID_SHELLS", "x_shells must have length >= 2")
    lam = require_exact_fraction(lam, "lam")
    require_ok(lam > 1, "INVALID_LAMBDA", "dyadic scaling lam must be > 1")
    xs = [require_exact_fraction(v, f"X[{i}]") for i, v in enumerate(x_shells)]
    n_len = len(xs)
    out: list[Fraction] = []
    for n in range(n_len):
        inflow = (lam ** (n - 1)) * xs[n - 1] * xs[n - 1] if n > 0 else Fraction(0, 1)
        outflow = (lam**n) * xs[n] * xs[n + 1] if n + 1 < n_len else Fraction(0, 1)
        out.append(inflow - outflow)
    return out


def verify_dptz_rational_matrix(u_vec: tuple[int, ...], eigenvalues: tuple[int, ...]) -> dict[str, Any]:
    """Verify exact Denton-Parke-Tao-Zhang & adjugate/Schur identities on Q D Q^T (Householder Q)."""
    n = len(u_vec)
    require_ok(n >= 2 and len(eigenvalues) == n, "INVALID_DPTZ_INPUT", "u_vec and eigenvalues must match length >= 2")
    u_clean = tuple(require_exact_int(x, "u_i") for x in u_vec)
    eigs_clean = tuple(require_exact_int(x, "eig_i") for x in eigenvalues)
    require_ok(len(set(eigs_clean)) == n, "REPEATED_EIGENVALUES", "eigenvalues must be distinct")
    uu = sum(x * x for x in u_clean)
    require_ok(uu > 0, "ZERO_HOUSEHOLDER_VEC", "Householder vector must be nonzero")
    q_mat = [
        [(Fraction(1, 1) if i == j else Fraction(0, 1)) - Fraction(2 * u_clean[i] * u_clean[j], uu) for j in range(n)]
        for i in range(n)
    ]
    a_mat = [
        [sum((q_mat[i][k] * Fraction(eigs_clean[k], 1) * q_mat[j][k] for k in range(n)), Fraction(0, 1)) for j in range(n)]
        for i in range(n)
    ]

    # Check DPTZ across ALL n*n eigenpair-minor pairs
    pairs_checked = 0
    dptz_ok = True
    for i in range(n):
        lam = Fraction(eigs_clean[i], 1)
        prod_diff = Fraction(1, 1)
        for k in range(n):
            if k != i:
                prod_diff *= lam - eigs_clean[k]
        for j in range(n):
            v_ij = q_mat[j][i]
            lhs = v_ij * v_ij * prod_diff
            minor_m = [[(lam if r == c else Fraction(0, 1)) - a_mat[r][c] for c in range(n) if c != j] for r in range(n) if r != j]
            if lhs != det_fraction(minor_m):
                dptz_ok = False
            pairs_checked += 1

    # Cross-check exact adjugate / Schur-complement formula det(lam I - M_j) == det(lam I - A) * [(lam I - A)^{-1}]_{jj}
    lam_probe = Fraction(max(eigs_clean) + 5, 1)
    shifted = [[(lam_probe if r == c else Fraction(0, 1)) - a_mat[r][c] for c in range(n)] for r in range(n)]
    det_shifted = det_fraction(shifted)
    schur_ok = True
    for j in range(n):
        ej = [Fraction(1, 1) if r == j else Fraction(0, 1) for r in range(n)]
        inv_col = solve_linear_fraction(shifted, ej)
        minor_m = [[shifted[r][c] for c in range(n) if c != j] for r in range(n) if r != j]
        if det_shifted * inv_col[j] != det_fraction(minor_m):
            schur_ok = False

    return {
        "n": n,
        "eigenvalues": list(eigs_clean),
        "eigenpair_minor_pairs_checked": pairs_checked,
        "dptz_all_exact": dptz_ok,
        "adjugate_schur_crosscheck_exact": schur_ok,
    }


def verify_magma_laws(table: list[list[int]]) -> dict[str, Any]:
    """Exhaustively evaluate canonical ETP magma laws on a finite Cayley table."""
    require_ok(type(table) is list and len(table) >= 1, "INVALID_CAYLEY", "table must be non-empty list")
    m = len(table)
    for row in table:
        require_ok(type(row) is list and len(row) == m, "INVALID_CAYLEY_ROW", "table must be m x m")
        for v in row:
            require_exact_int(v, "cayley_entry", lo=0, hi=m - 1)

    def _find_witness_law1689() -> list[int] | None:
        for x in range(m):
            for y in range(m):
                for z in range(m):
                    if x != table[table[y][x]][table[x][z]]:
                        return [x, y, z]
        return None

    def _find_witness_assoc() -> list[int] | None:
        for x in range(m):
            for y in range(m):
                for z in range(m):
                    if table[table[x][y]][z] != table[x][table[y][z]]:
                        return [x, y, z]
        return None

    def _find_witness_comm() -> list[int] | None:
        for x in range(m):
            for y in range(m):
                if table[x][y] != table[y][x]:
                    return [x, y]
        return None

    def _find_witness_idem() -> list[int] | None:
        for x in range(m):
            if table[x][x] != x:
                return [x]
        return None

    def _find_witness_medial() -> list[int] | None:
        for x in range(m):
            for y in range(m):
                for z in range(m):
                    for w in range(m):
                        if table[table[x][y]][table[z][w]] != table[table[x][z]][table[y][w]]:
                            return [x, y, z, w]
        return None

    w1689 = _find_witness_law1689()
    w_assoc = _find_witness_assoc()
    w_comm = _find_witness_comm()
    w_idem = _find_witness_idem()
    w_med = _find_witness_medial()
    return {
        "order": m,
        "law1689_central_groupoid": w1689 is None,
        "law1689_refutation": w1689,
        "associative": w_assoc is None,
        "associative_refutation": w_assoc,
        "commutative": w_comm is None,
        "commutative_refutation": w_comm,
        "idempotent": w_idem is None,
        "idempotent_refutation": w_idem,
        "medial": w_med is None,
        "medial_refutation": w_med,
    }


def verify_pillar5_dyadic_ns_dptz_etp() -> dict[str, Any]:
    """Certify Pillar 5 (1402.0290 + 1908.03795 + 2512.07087v1): Katz-Pavlovic / Tao
    dyadic NS energy conservation & weighted Lyapunov blowup identity, Denton-Parke-Tao-Zhang
    3x3 & 4x4 rational-spectrum + Schur identities, and ETP finite magma separations."""
    # 5a. Dyadic NS bilinear shell operator
    lam = Fraction(2, 1)
    mu = Fraction(3, 2)
    test_shells = [
        [Fraction(1, 1), Fraction(1, 2), Fraction(1, 3), Fraction(1, 5), Fraction(1, 7), Fraction(1, 11)],
        [Fraction(3, 2), Fraction(5, 4), Fraction(2, 3), Fraction(7, 8), Fraction(4, 5), Fraction(1, 2)],
    ]
    energy_ok = True
    lyapunov_id_ok = True
    lyapunov_pos_ok = True
    lyap_rates: list[str] = []
    for xs in test_shells:
        bs = dyadic_ns_bilinear(xs, lam)
        if sum((xs[n] * bs[n] for n in range(len(xs))), Fraction(0, 1)) != 0:
            energy_ok = False
        lhs_lyap = Fraction(2, 1) * sum(((mu**n) * xs[n] * bs[n] for n in range(len(xs))), Fraction(0, 1))
        rhs_lyap = Fraction(2, 1) * sum(
            (((lam**n) * (mu**n) * (mu - 1) * xs[n] * xs[n] * xs[n + 1]) for n in range(len(xs) - 1)),
            Fraction(0, 1),
        )
        if lhs_lyap != rhs_lyap:
            lyapunov_id_ok = False
        if lhs_lyap <= 0:
            lyapunov_pos_ok = False
        lyap_rates.append(format_fraction(lhs_lyap))
    lyapunov_ok = all((lyapunov_id_ok, lyapunov_pos_ok))

    # Positive-cone boundary inwardness check (X_2 == 0 => B_2 >= 0)
    cone_xs = [Fraction(1, 1), Fraction(3, 2), Fraction(0, 1), Fraction(2, 1)]
    cone_inward_ok = dyadic_ns_bilinear(cone_xs, lam)[2] >= 0

    # 5b. Denton-Parke-Tao-Zhang 3x3 & 4x4 exact rational spectrum + Schur cross-check
    dptz_3 = verify_dptz_rational_matrix((1, 2, 2), (1, 4, 9))
    dptz_4 = verify_dptz_rational_matrix((1, 1, 2, 2), (1, 3, 7, 13))

    # 5c. Equational Theories Project (2512.07087v1) finite magma countermodels
    cg_table = [[2 * (x & 1) + ((y >> 1) & 1) for y in range(4)] for x in range(4)]
    left_proj_table = [[x for _ in range(3)] for x in range(3)]
    affine_medial_table = [[(2 * x + 2 * y) % 3 for y in range(3)] for x in range(3)]
    cyclic_group_table = [[(x + y) % 3 for y in range(3)] for x in range(3)]

    etp_cg = verify_magma_laws(cg_table)
    etp_lp = verify_magma_laws(left_proj_table)
    etp_am = verify_magma_laws(affine_medial_table)
    etp_z3 = verify_magma_laws(cyclic_group_table)

    all_verified = all(
        (
            energy_ok,
            lyapunov_ok,
            cone_inward_ok,
            dptz_3["dptz_all_exact"],
            dptz_3["adjugate_schur_crosscheck_exact"],
            dptz_4["dptz_all_exact"],
            dptz_4["adjugate_schur_crosscheck_exact"],
            etp_cg["law1689_central_groupoid"],
            not etp_cg["associative"],
            etp_lp["associative"],
            etp_lp["idempotent"],
            not etp_lp["commutative"],
            etp_am["commutative"],
            etp_am["medial"],
            not etp_am["associative"],
            etp_z3["associative"],
            etp_z3["commutative"],
            not etp_z3["idempotent"],
        )
    )

    return {
        "all_verified": all_verified,
        "dyadic_ns_barrier": {
            "lambda": format_fraction(lam),
            "mu": format_fraction(mu),
            "energy_conservation_exact": energy_ok,
            "weighted_lyapunov_identity_exact": lyapunov_ok,
            "positive_cone_inward_exact": cone_inward_ok,
            "lyapunov_growth_rates": lyap_rates,
        },
        "dptz_eigenvector_eigenvalue": {
            "matrix_3x3": dptz_3,
            "matrix_4x4": dptz_4,
        },
        "etp_magma_countermodels": {
            "central_groupoid_order4": etp_cg,
            "left_projection_order3": etp_lp,
            "affine_medial_order3": etp_am,
            "cyclic_group_Z3": etp_z3,
        },
    }


def compute_s29_payload() -> dict[str, Any]:
    """Build the complete deterministic zero-float Track S29 (Portal 25) payload."""
    return {
        "track_id": TRACK_ID,
        "novelty_class": "N1",
        "oracle_class": "exact",
        "pillar1_katz_tao_entropy": verify_pillar1_katz_tao_entropy(),
        "pillar2_von_mangoldt_chains": verify_pillar2_von_mangoldt_chains(),
        "pillar3_syracuse_and_gilbreath": verify_pillar3_syracuse_and_gilbreath(),
        "pillar4_sidon_gowers_ruzsa": verify_pillar4_sidon_gowers_ruzsa(),
        "pillar5_dyadic_ns_dptz_etp": verify_pillar5_dyadic_ns_dptz_etp(),
    }
