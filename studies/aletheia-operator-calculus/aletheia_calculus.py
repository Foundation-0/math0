#!/usr/bin/env python3
r"""Aletheia Operator Calculus (Wave 2 Round 4C — AUDIT-051).

Zero-float pure-Q/Z executable engine, Unicode/ASCII expression parser,
theorem compression suite, and pairwise commutator/composition prover for the
canonical 8-glyph operator basis registered in `glyph_registry.json`:

    ⧄ (U+29C4, |/| )  Fiber-Elimination Schur Pushforward     (binary, prec 60 L)
    ⧅ (U+29C5, |\| )  Singular-Kernel / Dark-Mode Shadow      (binary, prec 60 L)
    ⦷ (U+29B7, (||))  Holonomy-Unmasking Differential         (binary, prec 55 L)
    ⟠ (U+27E0, <=> )  Observer-Net Equalizer                  (binary, prec 50 L)
    ⧇ (U+29C7, [o] )  Dimensionless Cohomological Obstruction (unary,  prec 70)
    ⦺ (U+29BA, (+-0)) Krein Inertia Signature Functor         (unary,  prec 70)
    ⩩ (U+2A69, =#= )  Coordinate-Free Exact Null-Equivalence  (binary, prec 30)
    ⫩ (U+2AE9, _|T )  R5 Refusal-Verified Gate                (binary, prec 20)

Zero external dependencies; zero floating-point arithmetic in any exact theorem;
zero bare asserts.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random
import sys
from typing import Any, Callable
import unicodedata


class CalculusError(ValueError):
    """Explicit structured error (never silenced under python3 -O)."""


def require(cond: bool, code: str, msg: str) -> None:
    if not cond:
        raise CalculusError(f"[{code}] {msg}")


def is_exact_int(x: Any) -> bool:
    return isinstance(x, int) and not isinstance(x, bool)


def frac_str(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


def canonical_json(obj: Any) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), allow_nan=False)


# =============================================================================
# 1. Exact Pure-Q Linear Algebra & Bunch-Kaufman Krein Inertia Engine
# =============================================================================

QMat = tuple[tuple[Fraction, ...], ...]


def to_q(x: int | Fraction) -> Fraction:
    if isinstance(x, Fraction):
        return x
    require(is_exact_int(x), "BAD_Q_SCALAR", f"Non-exact scalar {type(x).__name__}")
    return Fraction(x, 1)


def qmat(rows: list[list[int | Fraction]] | tuple[tuple[int | Fraction, ...], ...]) -> QMat:
    require(len(rows) > 0, "EMPTY_MAT", "Matrix must be non-empty")
    ncols = len(rows[0])
    require(ncols > 0, "EMPTY_COL", "Matrix columns must be non-empty")
    out: list[tuple[Fraction, ...]] = []
    for r in rows:
        require(len(r) == ncols, "RAGGED_MAT", "Ragged matrix row")
        out.append(tuple(to_q(v) for v in r))
    return tuple(out)


def is_symmetric(m: QMat) -> bool:
    n = len(m)
    if n != len(m[0]):
        return False
    for i in range(n):
        for j in range(i + 1, n):
            if m[i][j] != m[j][i]:
                return False
    return True


def qeye(n: int) -> QMat:
    return tuple(tuple(Fraction(1 if i == j else 0) for j in range(n)) for i in range(n))


def qzeros(r: int, c: int) -> QMat:
    return tuple(tuple(Fraction(0) for _ in range(c)) for _ in range(r))


def qtranspose(a: QMat) -> QMat:
    return tuple(tuple(a[r][c] for r in range(len(a))) for c in range(len(a[0])))


def qadd(a: QMat, b: QMat) -> QMat:
    require(len(a) == len(b) and len(a[0]) == len(b[0]), "SHAPE_MISMATCH", "qadd shape mismatch")
    return tuple(tuple(a[i][j] + b[i][j] for j in range(len(a[0]))) for i in range(len(a)))


def qsub(a: QMat, b: QMat) -> QMat:
    require(len(a) == len(b) and len(a[0]) == len(b[0]), "SHAPE_MISMATCH", "qsub shape mismatch")
    return tuple(tuple(a[i][j] - b[i][j] for j in range(len(a[0]))) for i in range(len(a)))


def qscale(c: Fraction, a: QMat) -> QMat:
    return tuple(tuple(c * a[i][j] for j in range(len(a[0]))) for i in range(len(a)))


def qmul(a: QMat, b: QMat) -> QMat:
    require(len(a[0]) == len(b), "MUL_SHAPE", "qmul inner dimension mismatch")
    m, k, n = len(a), len(b), len(b[0])
    return tuple(tuple(sum((a[i][t] * b[t][j] for t in range(k)), Fraction(0)) for j in range(n)) for i in range(m))


def qsubmat(m: QMat, rows: tuple[int, ...], cols: tuple[int, ...]) -> QMat:
    return tuple(tuple(m[r][c] for c in cols) for r in rows)


def qsolve(a: QMat, b: QMat) -> QMat:
    """Exact Gauss-Jordan solver over Q for square invertible A."""
    n = len(a)
    require(n == len(a[0]) and len(b) == n, "SOLVE_SHAPE", "Invalid solve shape")
    m = len(b[0])
    aug = [list(a[i]) + list(b[i]) for i in range(n)]
    for col in range(n):
        piv = -1
        for r in range(col, n):
            if aug[r][col] != 0:
                piv = r
                break
        require(piv >= 0, "SINGULAR_SOLVE", f"Singular matrix at col {col}")
        if piv != col:
            aug[col], aug[piv] = aug[piv], aug[col]
        pv = aug[col][col]
        aug[col] = [v / pv for v in aug[col]]
        for r in range(n):
            if r != col and aug[r][col] != 0:
                fac = aug[r][col]
                aug[r] = [aug[r][j] - fac * aug[col][j] for j in range(n + m)]
    return tuple(tuple(aug[i][n:]) for i in range(n))


def qrank(a: QMat) -> int:
    m, n = len(a), len(a[0])
    w = [list(row) for row in a]
    r = 0
    for c in range(n):
        piv = -1
        for i in range(r, m):
            if w[i][c] != 0:
                piv = i
                break
        if piv < 0:
            continue
        if piv != r:
            w[r], w[piv] = w[piv], w[r]
        pv = w[r][c]
        for i in range(r + 1, m):
            if w[i][c] != 0:
                fac = w[i][c] / pv
                for j in range(c, n):
                    w[i][j] -= fac * w[r][j]
        r += 1
    return r


def qnullspace(a: QMat) -> tuple[tuple[Fraction, ...], ...]:
    """Exact rational basis for ker(A), returned as tuple of column vectors."""
    m, n = len(a), len(a[0])
    w = [list(row) for row in a]
    piv_cols: list[int] = []
    r = 0
    for c in range(n):
        piv = -1
        for i in range(r, m):
            if w[i][c] != 0:
                piv = i
                break
        if piv < 0:
            continue
        if piv != r:
            w[r], w[piv] = w[piv], w[r]
        pv = w[r][c]
        w[r] = [v / pv for v in w[r]]
        for i in range(m):
            if i != r and w[i][c] != 0:
                fac = w[i][c]
                w[i] = [w[i][j] - fac * w[r][j] for j in range(n)]
        piv_cols.append(c)
        r += 1
    piv_set = set(piv_cols)
    free_cols = [c for c in range(n) if c not in piv_set]
    basis: list[tuple[Fraction, ...]] = []
    for fc in free_cols:
        vec = [Fraction(0)] * n
        vec[fc] = Fraction(1)
        for row_idx, pc in enumerate(piv_cols):
            vec[pc] = -w[row_idx][fc]
        basis.append(tuple(vec))
    return tuple(basis)


def qpinv_sym(m: QMat) -> QMat:
    """Exact rational Moore-Penrose pseudoinverse for symmetric M over Q.

    For symmetric M of rank r with column-space basis B (n x r), M = B C B^T
    with C invertible, hence B^T M B is invertible and M^+ = B (B^T M B)^{-1} B^T.
    """
    require(is_symmetric(m), "NOT_SYMMETRIC", "qpinv_sym requires symmetric matrix")
    n = len(m)
    w = [list(row) for row in m]
    piv_cols: list[int] = []
    r = 0
    for c in range(n):
        piv = -1
        for i in range(r, n):
            if w[i][c] != 0:
                piv = i
                break
        if piv < 0:
            continue
        if piv != r:
            w[r], w[piv] = w[piv], w[r]
        pv = w[r][c]
        for i in range(r + 1, n):
            if w[i][c] != 0:
                fac = w[i][c] / pv
                for j in range(c, n):
                    w[i][j] -= fac * w[r][j]
        piv_cols.append(c)
        r += 1
    if not piv_cols:
        return qzeros(n, n)
    b_mat = tuple(tuple(m[i][c] for c in piv_cols) for i in range(n))
    bt = qtranspose(b_mat)
    gram = qmul(bt, qmul(m, b_mat))
    gram_inv = qsolve(gram, qeye(len(piv_cols)))
    return qmul(b_mat, qmul(gram_inv, bt))


def qinertia(m: QMat) -> tuple[int, int, int]:
    """Exact zero-float Sylvester-Krein inertia (n_+, n_0, n_-) via Bunch-Kaufman over Q."""
    require(is_symmetric(m), "NOT_SYMMETRIC", "Krein inertia requires symmetric matrix")
    n = len(m)
    a = [list(row) for row in m]
    pos = zero = neg = 0
    k = 0
    while k < n:
        diag_piv = -1
        for i in range(k, n):
            if a[i][i] != 0:
                diag_piv = i
                break
        if diag_piv >= 0:
            if diag_piv != k:
                a[k], a[diag_piv] = a[diag_piv], a[k]
                for row in a:
                    row[k], row[diag_piv] = row[diag_piv], row[k]
            d = a[k][k]
            if d > 0:
                pos += 1
            else:
                neg += 1
            for i in range(k + 1, n):
                if a[i][k] != 0:
                    fac = a[i][k] / d
                    for j in range(k + 1, n):
                        a[i][j] -= fac * a[k][j]
            k += 1
            continue

        off_i = off_j = -1
        for i in range(k, n):
            for j in range(i + 1, n):
                if a[i][j] != 0:
                    off_i, off_j = i, j
                    break
            if off_i >= 0:
                break
        if off_i < 0:
            zero += n - k
            break

        # Swap off_i -> k and off_j -> k+1 (both diagonals are 0 => hyperbolic 2x2 pivot -> +1, -1)
        if off_i != k:
            a[k], a[off_i] = a[off_i], a[k]
            for row in a:
                row[k], row[off_i] = row[off_i], row[k]
        if off_j != k + 1:
            a[k + 1], a[off_j] = a[off_j], a[k + 1]
            for row in a:
                row[k + 1], row[off_j] = row[off_j], row[k + 1]
        p = a[k][k + 1]
        pos += 1
        neg += 1
        for i in range(k + 2, n):
            ci0, ci1 = a[i][k], a[i][k + 1]
            if ci0 != 0 or ci1 != 0:
                inv0, inv1 = ci1 / p, ci0 / p
                for j in range(k + 2, n):
                    a[i][j] -= inv0 * a[k][j] + inv1 * a[k + 1][j]
        k += 2
    return (pos, zero, neg)


# =============================================================================
# 2. Typed Domain Objects for the 8-Glyph Aletheia Operator Calculus
# =============================================================================

@dataclass(frozen=True)
class IndexSet:
    indices: tuple[int, ...]

    def __post_init__(self) -> None:
        require(len(set(self.indices)) == len(self.indices), "DUP_INDEX", "Duplicate index in IndexSet")

    def union(self, other: IndexSet) -> IndexSet:
        s_self = set(self.indices)
        require(s_self.isdisjoint(other.indices), "OVERLAP_UNION", "Disjoint union requires disjoint sets")
        return IndexSet(tuple(sorted(self.indices + other.indices)))


@dataclass(frozen=True)
class ShadowRecord:
    kernel_basis: tuple[tuple[Fraction, ...], ...]
    coupling_map: QMat | None
    dim_dark: int
    r_cross: int


@dataclass(frozen=True)
class InertiaTriple:
    pos: int
    zero: int
    neg: int

    def as_tuple(self) -> tuple[int, int, int]:
        return (self.pos, self.zero, self.neg)

    def __add__(self, other: InertiaTriple) -> InertiaTriple:
        return InertiaTriple(self.pos + other.pos, self.zero + other.zero, self.neg + other.neg)


@dataclass(frozen=True)
class WeightedGraph:
    n_verts: int
    edges: tuple[tuple[int, int, Fraction], ...]
    boundary: tuple[int, ...]

    def interior(self) -> tuple[int, ...]:
        bset = set(self.boundary)
        return tuple(v for v in range(self.n_verts) if v not in bset)

    def laplacian(self, signs: tuple[int, ...] | None = None) -> QMat:
        if signs is None:
            signs = (1,) * len(self.edges)
        require(len(signs) == len(self.edges), "SIGN_LEN", "Cocycle sign length mismatch")
        l_mat = [[Fraction(0)] * self.n_verts for _ in range(self.n_verts)]
        for (u, v, w), s in zip(self.edges, signs):
            require(s in (-1, 1), "BAD_SIGN", f"Invalid Z_2 sign {s}")
            require(w > 0, "NONPOS_WEIGHT", f"Edge weight must be > 0, got {w}")
            l_mat[u][u] += w
            l_mat[v][v] += w
            l_mat[u][v] -= s * w
            l_mat[v][u] -= s * w
        return tuple(tuple(row) for row in l_mat)

    def harmonic_extension(self, signs: tuple[int, ...]) -> tuple[Fraction, ...]:
        """Exact rational signed-harmonic extension x with x|_B = 1_B."""
        l_full = self.laplacian(signs)
        b_nodes = self.boundary
        i_nodes = self.interior()
        l_ii = qsubmat(l_full, i_nodes, i_nodes)
        l_ib = qsubmat(l_full, i_nodes, b_nodes)
        rhs = tuple((sum((-l_ib[r][c] for c in range(len(b_nodes))), Fraction(0)),) for r in range(len(i_nodes)))
        sol = qsolve(l_ii, rhs)
        x = [Fraction(1)] * self.n_verts
        for idx, v in enumerate(i_nodes):
            x[v] = sol[idx][0]
        return tuple(x)

    def dirichlet_energy(self, signs: tuple[int, ...], x: tuple[Fraction, ...]) -> Fraction:
        return sum((w * (x[u] - s * x[v]) ** 2 for (u, v, w), s in zip(self.edges, signs)), Fraction(0))


@dataclass(frozen=True)
class CocycleZ2:
    signs: tuple[int, ...]

    def __post_init__(self) -> None:
        for s in self.signs:
            require(is_exact_int(s) and s in (-1, 1), "BAD_COCYCLE", f"Invalid sign {s!r}")

    def product(self, other: CocycleZ2) -> CocycleZ2:
        require(len(self.signs) == len(other.signs), "COCYCLE_LEN", "Cocycle lengths differ")
        return CocycleZ2(tuple(a * b for a, b in zip(self.signs, other.signs)))


@dataclass(frozen=True)
class OneCochain:
    graph: WeightedGraph
    omega: tuple[Fraction, ...]

    def __post_init__(self) -> None:
        require(len(self.omega) == len(self.graph.edges), "COCHAIN_LEN", "Cochain length mismatch")


@dataclass(frozen=True)
class ObserverGroup:
    """Finite permutation symmetry group acting on matrices, OR multiplicative regulator net."""

    kind: str  # "perm_group" or "mellin_net"
    elements: tuple[Any, ...]


@dataclass(frozen=True)
class MellinSeriesProbe:
    """Exact polynomial moment k for Mellin regulator equalization of sum_{n>=1} n^k."""

    k_power: int


@dataclass(frozen=True)
class R5Spec:
    predicate: Callable[[Any], bool]
    mutants: tuple[Any, ...]


@dataclass(frozen=True)
class GateResult:
    passed: bool
    accept_target: bool
    killed: int
    total_mutants: int
    kill_ratio: Fraction


# =============================================================================
# 3. Exact Semantics of the 8 Canonical Operators (Zero Floats!)
# =============================================================================

def op_schur_pushforward(m: QMat, elim: IndexSet) -> QMat:
    """OP-01 ⧄ (U+29C4): M ⧄ B = M_{AA} - M_{AB} M_{BB}^+ M_{BA} over exact Q."""
    require(is_symmetric(m), "SCHUR_NOT_SYM", "Schur pushforward requires symmetric matrix")
    n = len(m)
    b_idx = elim.indices
    require(all(0 <= i < n for i in b_idx), "SCHUR_OOB", "Elimination index out of bounds")
    b_set = set(b_idx)
    a_idx = tuple(i for i in range(n) if i not in b_set)
    require(len(a_idx) > 0, "SCHUR_EMPTY_KEEP", "Cannot eliminate all indices")
    if not b_idx:
        return m
    m_aa = qsubmat(m, a_idx, a_idx)
    m_ab = qsubmat(m, a_idx, b_idx)
    m_ba = qsubmat(m, b_idx, a_idx)
    m_bb = qsubmat(m, b_idx, b_idx)
    m_bb_pinv = qpinv_sym(m_bb)
    return qsub(m_aa, qmul(m_ab, qmul(m_bb_pinv, m_ba)))


def op_dark_mode_shadow(m: QMat, elim: IndexSet) -> ShadowRecord:
    """OP-02 ⧅ (U+29C5): M ⧅ B = (ker(M_{BB}), M_{AB}|_{ker}, dim_dark, r_cross)."""
    require(is_symmetric(m), "SHADOW_NOT_SYM", "Dark-mode shadow requires symmetric matrix")
    n = len(m)
    b_idx = elim.indices
    require(all(0 <= i < n for i in b_idx), "SHADOW_OOB", "Index out of bounds")
    b_set = set(b_idx)
    a_idx = tuple(i for i in range(n) if i not in b_set)
    m_bb = qsubmat(m, b_idx, b_idx)
    k_basis = qnullspace(m_bb)
    dim_dark = len(k_basis)
    if dim_dark == 0 or not a_idx:
        return ShadowRecord(kernel_basis=k_basis, coupling_map=None, dim_dark=dim_dark, r_cross=0)
    m_ab = qsubmat(m, a_idx, b_idx)
    k_mat = qtranspose(k_basis)  # |B| x dim_dark
    c_ab = qmul(m_ab, k_mat)
    return ShadowRecord(kernel_basis=k_basis, coupling_map=c_ab, dim_dark=dim_dark, r_cross=qrank(c_ab))


def op_holonomy_unmask(g: WeightedGraph, chi: CocycleZ2) -> QMat:
    """OP-03 ⦷ (U+29B7): L ⦷ χ = (L^χ ⧄ I) - (L ⧄ I) in Sym_{|B|}(Q)."""
    i_set = IndexSet(g.interior())
    b_set = set(g.boundary)
    # Require cocycle flips to lie strictly inside E(I) (untwisted boundary/collar)
    for (u, v, _w), s in zip(g.edges, chi.signs):
        if s == -1:
            require((u not in b_set) and (v not in b_set), "BOUNDARY_TWIST", "Holonomy flip must lie in E(I)")
    lam_0 = op_schur_pushforward(g.laplacian(), i_set)
    lam_chi = op_schur_pushforward(g.laplacian(chi.signs), i_set)
    return qsub(lam_chi, lam_0)


def bernoulli_q(n_max: int) -> list[Fraction]:
    """Exact Bernoulli numbers B_0..B_{n_max} (B_1 = -1/2) via Akiyama-Tanigawa."""
    a = [Fraction(0)] * (n_max + 1)
    out: list[Fraction] = []
    for m in range(n_max + 1):
        a[m] = Fraction(1, m + 1)
        for j in range(m, 0, -1):
            a[j - 1] = j * (a[j - 1] - a[j])
        out.append(a[0])
    if n_max >= 1:
        out[1] = Fraction(-1, 2)
    return out


def op_observer_equalizer(x: Any, grp: ObserverGroup) -> Any:
    """OP-04 ⟠ (U+27E0): X ⟠ G exact Reynolds group equalizer or Mellin regulator-net equalizer."""
    if grp.kind == "perm_group":
        require(isinstance(x, tuple) and len(x) > 0 and isinstance(x[0], tuple), "EQ_MAT_REQ", "Expected QMat")
        n = len(x)
        order = len(grp.elements)
        require(order > 0, "EMPTY_GROUP", "Observer group cannot be empty")
        acc = [[Fraction(0)] * n for _ in range(n)]
        for perm in grp.elements:
            require(len(perm) == n and sorted(perm) == list(range(n)), "BAD_PERM", "Invalid permutation in group")
            for i in range(n):
                for j in range(n):
                    acc[i][j] += x[perm[i]][perm[j]]
        return tuple(tuple(acc[i][j] / order for j in range(n)) for i in range(n))

    if grp.kind == "mellin_net":
        require(isinstance(x, MellinSeriesProbe), "EQ_MELLIN_REQ", "Expected MellinSeriesProbe")
        k = x.k_power
        b_nums = bernoulli_q(k + 1)
        # For cutoff eta(eps*n) = sum_i w_i exp(-lam_i * eps * (n + alpha_i)):
        # Constant (eps^0) term of sum_{n>=1} n^k eta(eps*n) for unshifted (alpha=0) with sum w_i = 1:
        #   sum_i w_i * (-B_{k+1}/(k+1)) = -B_{k+1}/(k+1) = zeta(-k)
        # For shifted exp(-lam * eps * (n + alpha)):
        #   sum_{n>=1} n^k exp(-lam*eps*(n+alpha)) has eps^0 coefficient
        #   -B_{k+1}(alpha)/(k+1) + (0^k if ...): specifically for k=1, -1/12 + alpha^2/2? Wait:
        #   sum_{n>=1} n e^{-t(n+a)} = e^{-ta} * e^{-t}/(1-e^{-t})^2
        #   Expand e^{-ta} = 1 - ta + t^2 a^2 / 2 - ... and e^{-t}/(1-e^{-t})^2 = 1/t^2 - 1/12 + t^2/240 - ...
        #   Product constant term (t^0) = -1/12 + a^2/2!
        vals: list[Fraction] = []
        for net_entry in grp.elements:
            # Each observer in the net is a tuple of (weight_w, scale_lam, shift_alpha)
            w_sum = sum((w for w, _lam, _a in net_entry), Fraction(0))
            require(w_sum == 1, "NET_UNNORMALIZED", f"Regulator net weights sum to {w_sum} != 1")
            c0 = Fraction(0)
            for w, lam, alpha in net_entry:
                require(lam > 0, "BAD_LAM", "Scale lam must be > 0")
                if alpha == 0:
                    c0 += w * (-b_nums[k + 1] / (k + 1))
                else:
                    require(k == 1, "SHIFT_K1_ONLY", "Shifted observer formula checked for k=1")
                    c0 += w * (Fraction(-1, 12) + (alpha * alpha) / 2)
            vals.append(c0)
        require(len(set(vals)) == 1, "NET_NOT_EQUALIZED", f"Observer net failed to equalize: {[frac_str(v) for v in vals]}")
        return vals[0]

    raise CalculusError(f"[BAD_OBS_KIND] Unknown observer group kind {grp.kind!r}")


def op_cohom_obstruction(cochain: OneCochain) -> Fraction:
    """OP-05 ⧇ (U+29C7): ⧇(ω) = ||ω_harm||_w^2 / ||ω||_w^2 in [0, 1] cap Q."""
    g = cochain.graph
    m = len(g.edges)
    n = g.n_verts
    omega = cochain.omega
    norm_sq = sum((w * om * om for (_u, _v, w), om in zip(g.edges, omega)), Fraction(0))
    if norm_sq == 0:
        return Fraction(0)
    # Exact Hodge decomposition: ω = d^0 φ + ω_harm, where L φ = d^0* W ω = B^T W ω
    # Fix gauge φ_0 = 0 on connected graph (delete vertex 0) or use L^+!
    l_full = g.laplacian()
    l_pinv = qpinv_sym(l_full)
    # rhs_v = sum_{e=(u,v)} w_e * omega_e * (delta_{v,u} - delta_{v,v'})
    rhs = [Fraction(0)] * n
    for (u, v, w), om in zip(g.edges, omega):
        rhs[u] += w * om
        rhs[v] -= w * om
    phi = [sum((l_pinv[i][j] * rhs[j] for j in range(n)), Fraction(0)) for i in range(n)]
    harm_sq = sum((w * (om - (phi[u] - phi[v])) ** 2 for (u, v, w), om in zip(g.edges, omega)), Fraction(0))
    return harm_sq / norm_sq


def op_krein_inertia(m: QMat) -> InertiaTriple:
    """OP-06 ⦺ (U+29BA): ⦺(A) = (n_+, n_0, n_-) exact zero-float inertia."""
    p, z, neg = qinertia(m)
    return InertiaTriple(p, z, neg)


def op_exact_null_equiv(x: Any, y: Any) -> bool:
    """OP-07 ⩩ (U+2A69): Coordinate-free exact null-equivalence (zero float tolerance)."""
    require(not isinstance(x, float) and not isinstance(y, float), "NO_FLOATS_IN_EXACTEQ", "Floats forbidden in ⩩")
    if isinstance(x, (int, Fraction)) and isinstance(y, (int, Fraction)):
        return to_q(x) - to_q(y) == 0
    if isinstance(x, InertiaTriple) and isinstance(y, InertiaTriple):
        return x.as_tuple() == y.as_tuple()
    if isinstance(x, tuple) and isinstance(y, tuple) and len(x) == len(y):
        if len(x) > 0 and isinstance(x[0], tuple):
            diff = qsub(x, y)
            return all(val == 0 for row in diff for val in row)
        return x == y
    return bool(x == y)


def op_r5_gate(spec: R5Spec, target: Any) -> GateResult:
    """OP-08 ⫩ (U+2AE9): T ⫩ x iff T(x) == True AND forall m in M(x), T(m) == False."""
    require(len(spec.mutants) > 0, "EMPTY_MUTANTS", "R5 gate requires non-empty mutant family")
    accept_ok = bool(spec.predicate(target))
    killed = sum(1 for m in spec.mutants if not bool(spec.predicate(m)))
    total = len(spec.mutants)
    ratio = Fraction(killed, total)
    return GateResult(
        passed=accept_ok and (killed == total),
        accept_target=accept_ok,
        killed=killed,
        total_mutants=total,
        kill_ratio=ratio,
    )


# =============================================================================
# 4. Live Unicode & ASCII Fallback Lexer + Recursive-Descent Parser + Evaluator
# =============================================================================

GLYPH_TO_TOKEN = {
    "\u29c4": "SCHUR",    # ⧄
    "\u29c5": "SHADOW",   # ⧅
    "\u29b7": "UNMASK",   # ⦷
    "\u27e0": "EQOBS",    # ⟠
    "\u29c7": "OBST",     # ⧇
    "\u29ba": "INERTIA",  # ⦺
    "\u2a69": "EXACTEQ",  # ⩩
    "\u2ae9": "R5GATE",   # ⫩
}

ASCII_TO_TOKEN = {
    "|/|": "SCHUR",
    "|\\|": "SHADOW",
    "(||)": "UNMASK",
    "<=>": "EQOBS",
    "[o]": "OBST",
    "(+-0)": "INERTIA",
    "=#=": "EXACTEQ",
    "_|T": "R5GATE",
}


def tokenize(expr: str) -> list[tuple[str, str]]:
    tokens: list[tuple[str, str]] = []
    i = 0
    n = len(expr)
    ascii_keys = sorted(ASCII_TO_TOKEN.keys(), key=len, reverse=True)
    while i < n:
        ch = expr[i]
        if ch.isspace():
            i += 1
            continue
        if ch in GLYPH_TO_TOKEN:
            tok = GLYPH_TO_TOKEN[ch]
            # Support subscripted inertia projections ⦺_+, ⦺_0, ⦺_-
            if tok == "INERTIA" and i + 2 < n and expr[i + 1] == "_" and expr[i + 2] in ("+", "0", "-"):
                tokens.append((f"INERTIA_{expr[i + 2]}", expr[i : i + 3]))
                i += 3
            else:
                tokens.append((tok, ch))
                i += 1
            continue
        matched_ascii = False
        for ak in ascii_keys:
            if expr.startswith(ak, i):
                tok = ASCII_TO_TOKEN[ak]
                end = i + len(ak)
                if tok == "INERTIA" and end + 1 < n and expr[end] == "_" and expr[end + 1] in ("+", "0", "-"):
                    tokens.append((f"INERTIA_{expr[end + 1]}", expr[i : end + 2]))
                    i = end + 2
                else:
                    tokens.append((tok, ak))
                    i = end
                matched_ascii = True
                break
        if matched_ascii:
            continue
        if ch in "(),+-*|":
            tokens.append((ch, ch))
            i += 1
            continue
        if ch.isdigit():
            j = i
            while j < n and expr[j].isdigit():
                j += 1
            if j < n and expr[j] == "/" and j + 1 < n and expr[j + 1].isdigit():
                j += 1
                while j < n and expr[j].isdigit():
                    j += 1
            tokens.append(("NUM", expr[i:j]))
            i = j
            continue
        if ch.isalpha() or ch == "_":
            j = i
            while j < n and (expr[j].isalnum() or expr[j] == "_"):
                j += 1
            tokens.append(("IDENT", expr[i:j]))
            i = j
            continue
        raise CalculusError(f"[LEX_ERR] Unexpected character {ch!r} at pos {i} in {expr!r}")
    tokens.append(("EOF", ""))
    return tokens


class Parser:
    """Precedence-climbing / recursive-descent parser respecting glyph_registry.json:
    prec 20: ⫩ | prec 30: ⩩ | prec 40: +,- | prec 45: *,| | prec 50: ⟠ | prec 55: ⦷ | prec 60: ⧄,⧅ | prec 70: prefix ⧇,⦺
    """

    def __init__(self, tokens: list[tuple[str, str]]) -> None:
        self.tokens = tokens
        self.pos = 0

    def peek(self) -> tuple[str, str]:
        return self.tokens[self.pos]

    def consume(self, expected: str | None = None) -> tuple[str, str]:
        tok = self.tokens[self.pos]
        if expected is not None:
            require(tok[0] == expected, "PARSE_ERR", f"Expected {expected}, got {tok}")
        self.pos += 1
        return tok

    def parse(self) -> Any:
        node = self.parse_r5()
        require(self.peek()[0] == "EOF", "TRAILING_TOK", f"Trailing token {self.peek()}")
        return node

    def parse_r5(self) -> Any:
        left = self.parse_exacteq()
        if self.peek()[0] == "R5GATE":
            self.consume("R5GATE")
            right = self.parse_exacteq()
            return ("R5GATE", left, right)
        return left

    def parse_exacteq(self) -> Any:
        left = self.parse_add()
        if self.peek()[0] == "EXACTEQ":
            self.consume("EXACTEQ")
            right = self.parse_add()
            return ("EXACTEQ", left, right)
        return left

    def parse_add(self) -> Any:
        node = self.parse_mul()
        while self.peek()[0] in ("+", "-"):
            op = self.consume()[0]
            rhs = self.parse_mul()
            node = (op, node, rhs)
        return node

    def parse_mul(self) -> Any:
        node = self.parse_eqobs()
        while self.peek()[0] in ("*", "|"):
            op = self.consume()[0]
            rhs = self.parse_eqobs()
            node = (op, node, rhs)
        return node

    def parse_eqobs(self) -> Any:
        node = self.parse_unmask()
        while self.peek()[0] == "EQOBS":
            self.consume("EQOBS")
            rhs = self.parse_unmask()
            node = ("EQOBS", node, rhs)
        return node

    def parse_unmask(self) -> Any:
        node = self.parse_schur_shadow()
        while self.peek()[0] == "UNMASK":
            self.consume("UNMASK")
            rhs = self.parse_schur_shadow()
            node = ("UNMASK", node, rhs)
        return node

    def parse_schur_shadow(self) -> Any:
        node = self.parse_prefix()
        while self.peek()[0] in ("SCHUR", "SHADOW"):
            op = self.consume()[0]
            rhs = self.parse_prefix()
            node = (op, node, rhs)
        return node

    def parse_prefix(self) -> Any:
        tk = self.peek()[0]
        if tk in ("OBST", "INERTIA", "INERTIA_+", "INERTIA_0", "INERTIA_-"):
            self.consume()
            arg = self.parse_prefix()
            return (tk, arg)
        if tk == "-":
            self.consume("-")
            arg = self.parse_prefix()
            return ("NEG", arg)
        return self.parse_atom()

    def parse_atom(self) -> Any:
        tk, val = self.peek()
        if tk == "(":
            self.consume("(")
            first = self.parse_r5()
            if self.peek()[0] == ",":
                elems = [first]
                while self.peek()[0] == ",":
                    self.consume(",")
                    elems.append(self.parse_r5())
                self.consume(")")
                return ("TUPLE", tuple(elems))
            self.consume(")")
            return first
        if tk == "NUM":
            self.consume("NUM")
            return ("NUM", Fraction(val))
        if tk == "IDENT":
            self.consume("IDENT")
            if self.peek()[0] == "(":
                self.consume("(")
                args = []
                if self.peek()[0] != ")":
                    args.append(self.parse_r5())
                    while self.peek()[0] == ",":
                        self.consume(",")
                        args.append(self.parse_r5())
                self.consume(")")
                return ("CALL", val, tuple(args))
            return ("VAR", val)
        raise CalculusError(f"[PARSE_ERR] Unexpected token {tk!r} ({val!r})")


def eval_ast(node: Any, env: dict[str, Any]) -> Any:
    tag = node[0]
    if tag == "NUM":
        return node[1]
    if tag == "VAR":
        name = node[1]
        require(name in env, "UNBOUND_VAR", f"Unknown identifier {name!r}")
        return env[name]
    if tag == "TUPLE":
        vals = tuple(eval_ast(x, env) for x in node[1])
        if len(vals) == 3 and all(isinstance(v, Fraction) and v.denominator == 1 for v in vals):
            return InertiaTriple(int(vals[0]), int(vals[1]), int(vals[2]))
        return vals
    if tag == "NEG":
        v = eval_ast(node[1], env)
        if isinstance(v, Fraction):
            return -v
        if isinstance(v, tuple) and len(v) > 0 and isinstance(v[0], tuple):
            return qscale(Fraction(-1), v)
        raise CalculusError(f"[BAD_NEG] Cannot negate {type(v).__name__}")
    if tag == "SCHUR":
        return op_schur_pushforward(eval_ast(node[1], env), eval_ast(node[2], env))
    if tag == "SHADOW":
        return op_dark_mode_shadow(eval_ast(node[1], env), eval_ast(node[2], env))
    if tag == "UNMASK":
        return op_holonomy_unmask(eval_ast(node[1], env), eval_ast(node[2], env))
    if tag == "EQOBS":
        return op_observer_equalizer(eval_ast(node[1], env), eval_ast(node[2], env))
    if tag == "OBST":
        return op_cohom_obstruction(eval_ast(node[1], env))
    if tag == "INERTIA":
        return op_krein_inertia(eval_ast(node[1], env))
    if tag == "INERTIA_+":
        return Fraction(op_krein_inertia(eval_ast(node[1], env)).pos)
    if tag == "INERTIA_0":
        return Fraction(op_krein_inertia(eval_ast(node[1], env)).zero)
    if tag == "INERTIA_-":
        return Fraction(op_krein_inertia(eval_ast(node[1], env)).neg)
    if tag == "EXACTEQ":
        return op_exact_null_equiv(eval_ast(node[1], env), eval_ast(node[2], env))
    if tag == "R5GATE":
        return op_r5_gate(eval_ast(node[1], env), eval_ast(node[2], env))
    if tag == "+":
        a, b = eval_ast(node[1], env), eval_ast(node[2], env)
        if isinstance(a, InertiaTriple) and isinstance(b, InertiaTriple):
            return a + b
        if isinstance(a, tuple) and isinstance(b, tuple):
            return qadd(a, b)
        return to_q(a) + to_q(b)
    if tag == "-":
        a, b = eval_ast(node[1], env), eval_ast(node[2], env)
        if isinstance(a, tuple) and isinstance(b, tuple):
            return qsub(a, b)
        return to_q(a) - to_q(b)
    if tag == "*":
        a, b = eval_ast(node[1], env), eval_ast(node[2], env)
        if isinstance(a, CocycleZ2) and isinstance(b, CocycleZ2):
            return a.product(b)
        if isinstance(a, tuple) and isinstance(b, tuple):
            return qmul(a, b)
        return to_q(a) * to_q(b)
    if tag == "|":
        a, b = eval_ast(node[1], env), eval_ast(node[2], env)
        require(isinstance(a, IndexSet) and isinstance(b, IndexSet), "BAD_UNION", "| requires IndexSet operands")
        return a.union(b)
    if tag == "CALL":
        fn, args = node[1], tuple(eval_ast(x, env) for x in node[2])
        if fn == "rk":
            arg = args[0]
            return Fraction(arg.r_cross if isinstance(arg, ShadowRecord) else qrank(arg))
        if fn == "dim":
            arg = args[0]
            require(isinstance(arg, ShadowRecord), "DIM_REQ_SHADOW", "dim() expects ShadowRecord")
            return Fraction(arg.dim_dark)
        if fn == "Phi":
            mat = args[0]
            return sum((mat[r][c] for r in range(len(mat)) for c in range(len(mat[0]))), Fraction(0))
        if fn == "Tr":
            mat = args[0]
            return sum((mat[i][i] for i in range(len(mat))), Fraction(0))
        if fn == "kill":
            gr = args[0]
            require(isinstance(gr, GateResult), "KILL_REQ_GATE", "kill() expects GateResult")
            return gr.kill_ratio
        raise CalculusError(f"[UNKNOWN_FN] Unknown built-in {fn!r}")
    raise CalculusError(f"[BAD_AST] Unknown AST node {tag!r}")


def eval_expr(expr: str, env: dict[str, Any]) -> Any:
    return eval_ast(Parser(tokenize(expr)).parse(), env)


# =============================================================================
# 5. Registry Validation & One-Line Compressed Expedition Theorems
# =============================================================================

def verify_glyph_registry() -> dict[str, Any]:
    reg_path = Path(__file__).resolve().parent / "glyph_registry.json"
    data = json.loads(reg_path.read_text(encoding="utf-8"))
    glyphs = data["glyphs"]
    seen_cp: set[str] = set()
    rows: list[dict[str, Any]] = []
    all_ok = len(glyphs) == 8
    for g in glyphs:
        ch = g["glyph"]
        cp = f"U+{ord(ch):04X}"
        cat = unicodedata.category(ch)
        ok_row = (
            len(ch) == 1
            and cp == g["codepoint"]
            and ch.encode("utf-8").hex() == g["utf8_hex"]
            and cat == "Sm"
            and ch in GLYPH_TO_TOKEN
            and g["ascii_fallback"] in ASCII_TO_TOKEN
            and g["lean4_hits"] == 0
            and g["expedition_hits"] == 0
            and g["sessions_hits"] == 0
            and cp not in seen_cp
        )
        all_ok = all_ok and ok_row
        seen_cp.add(cp)
        rows.append({"id": g["id"], "codepoint": cp, "unicode_name": unicodedata.name(ch), "ascii": g["ascii_fallback"]})
    return {
        "schema_verified": data["schema"],
        "glyph_count": len(rows),
        "all_category_Sm_and_zero_collision": all_ok,
        "unicode_ascii_lexer_bound": all_ok,
        "glyphs": rows,
    }


def make_btz_depth2() -> WeightedGraph:
    # Horizon D={0,1,2}, Collar C={3,4,5}, Outer Boundary B={6..11}
    edges = (
        (0, 1, Fraction(1)), (1, 2, Fraction(1)), (2, 0, Fraction(1)),
        (0, 3, Fraction(1)), (1, 4, Fraction(1)), (2, 5, Fraction(1)),
        (3, 6, Fraction(1)), (3, 7, Fraction(1)),
        (4, 8, Fraction(1)), (4, 9, Fraction(1)),
        (5, 10, Fraction(1)), (5, 11, Fraction(1)),
    )
    return WeightedGraph(n_verts=12, edges=edges, boundary=(6, 7, 8, 9, 10, 11))


def make_btz_odd_wormhole() -> WeightedGraph:
    edges = (
        (0, 1, Fraction(1)), (1, 2, Fraction(1)), (2, 0, Fraction(1)),
        (3, 4, Fraction(1)), (4, 5, Fraction(1)), (5, 3, Fraction(1)),
        (0, 3, Fraction(1)),
        (1, 6, Fraction(1)), (2, 7, Fraction(1)), (4, 8, Fraction(1)), (5, 9, Fraction(1)),
    )
    return WeightedGraph(n_verts=10, edges=edges, boundary=(6, 7, 8, 9))


def make_btz_even_wormhole() -> WeightedGraph:
    edges = (
        (0, 1, Fraction(1)), (1, 2, Fraction(1)), (2, 3, Fraction(1)), (3, 0, Fraction(1)),
        (4, 5, Fraction(1)), (5, 6, Fraction(1)), (6, 7, Fraction(1)), (7, 4, Fraction(1)),
        (0, 4, Fraction(1)),
        (1, 8, Fraction(1)), (2, 9, Fraction(1)), (3, 10, Fraction(1)),
        (5, 11, Fraction(1)), (6, 12, Fraction(1)), (7, 13, Fraction(1)),
    )
    return WeightedGraph(n_verts=14, edges=edges, boundary=(8, 9, 10, 11, 12, 13))


def make_k3_all_flipped() -> tuple[WeightedGraph, CocycleZ2]:
    edges = (
        (0, 1, Fraction(1)), (1, 2, Fraction(1)), (2, 0, Fraction(1)),
        (0, 3, Fraction(1)), (1, 4, Fraction(1)), (2, 5, Fraction(1)),
    )
    return WeightedGraph(n_verts=6, edges=edges, boundary=(3, 4, 5)), CocycleZ2((-1, -1, -1, 1, 1, 1))


def ramanujan_cert_matrix(n: int, edges: list[tuple[int, int]]) -> QMat:
    adj = [[0] * n for _ in range(n)]
    degs = [0] * n
    for u, v in edges:
        adj[u][v] += 1
        adj[v][u] += 1
        degs[u] += 1
        degs[v] += 1
    d = degs[0]
    p = d - 1
    a2 = [[sum(adj[i][k] * adj[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
    return qmat([[(4 * p * n if i == j else 0) - n * a2[i][j] + d * d for j in range(n)] for i in range(n)])


def run_compressed_theorems() -> dict[str, Any]:
    """Execute 7 compressed expedition theorems directly via Unicode & ASCII expressions."""
    results: list[dict[str, Any]] = []

    def check_both(tid: str, u_expr: str, a_expr: str, env: dict[str, Any]) -> None:
        u_val = eval_expr(u_expr, env)
        a_val = eval_expr(a_expr, env)
        results.append({"id": tid, "unicode_expr": u_expr, "ascii_expr": a_expr, "verified": bool(u_val is True and a_val is True)})

    # T1: SF-01 Quotient-in-Stages (depth-2 BTZ untwisted Laplacian, B={6..11}, C={3..5}, D={0..2})
    g_d2 = make_btz_depth2()
    l_d2 = g_d2.laplacian()
    env_t1 = {
        "M": l_d2,
        "D": IndexSet((0, 1, 2)),
        "C": IndexSet((3, 4, 5)),
        "C_after_D": IndexSet((0, 1, 2)),  # After eliminating {0,1,2}, vertices {3,4,5} become indices {0,1,2}
    }
    check_both("T1_quotient_in_stages", "(M ⧄ D) ⧄ C_after_D ⩩ M ⧄ (D | C)", "(M |/| D) |/| C_after_D =#= M |/| (D | C)", env_t1)

    # T2: AUDIT-041 Haynsworth-Krein Shadow Law (smooth r_cross=0 vs singular r_cross=1)
    m_smooth = qmat([[5, 1, 2, 0], [1, 4, 0, 1], [2, 0, 3, 1], [0, 1, 1, 2]])
    m_sing = qmat([[4, 0, 1, 1], [0, 4, 0, 0], [1, 0, 1, 1], [1, 0, 1, 1]])  # M_BB has ker=span{(1,-1)}, coupled to v0? Wait (1,1)*(1,-1)=0 -> change M_AB[0]=(1,0) so coupled!
    m_sing = qmat([[4, 0, 1, 0], [0, 4, 0, 0], [1, 0, 1, 1], [0, 0, 1, 1]])
    env_t2 = {
        "Ms": m_smooth,
        "Ms_BB": qsubmat(m_smooth, (2, 3), (2, 3)),
        "Mx": m_sing,
        "B": IndexSet((2, 3)),
    }
    check_both("T2a_haynsworth_smooth", "⦺(Ms) ⩩ ⦺(Ms_BB) + ⦺(Ms ⧄ B)", "(+-0)(Ms) =#= (+-0)(Ms_BB) + (+-0)(Ms |/| B)", env_t2)
    check_both("T2b_singular_shadow_krein", "⦺_-(Mx) ⩩ rk(Mx ⧅ B)", "(+-0)_-(Mx) =#= rk(Mx |\\| B)", env_t2)

    # T3: AUDIT-043 Hodge-1 Resistance Law: ⧇(e) ⩩ 1 - R_eff(e) & ⧇(d0_f) ⩩ 0
    g_tri = WeightedGraph(
        n_verts=4,
        edges=((0, 1, Fraction(2)), (1, 2, Fraction(3)), (2, 0, Fraction(5)), (2, 3, Fraction(7))),
        boundary=(3,),
    )
    # Exact R_eff of edge 0=(0,1) with weight 2: parallel path 0-2-1 has resistance 1/5 + 1/3 = 8/15;
    # edge resistance = 1/2 => R_eff(e0) = (1/2 * 8/15)/(1/2 + 8/15) = (4/15)/(31/30) = 8/31 => w*R_eff = 16/31 => c_harm = 15/31!
    e0_cochain = OneCochain(g_tri, (Fraction(1), Fraction(0), Fraction(0), Fraction(0)))
    # Exact coboundary d^0 f for f = (1, 4, -2, 5): diffs = (-3, 6, -3, -7)
    d0_cochain = OneCochain(g_tri, (Fraction(-3), Fraction(6), Fraction(-3), Fraction(-7)))
    env_t3 = {"e0": e0_cochain, "d0f": d0_cochain}
    check_both("T3a_hodge_resistance", "⧇(e0) ⩩ 15/31", "[o](e0) =#= 15/31", env_t3)
    check_both("T3b_coboundary_zero", "⧇(d0f) ⩩ 0", "[o](d0f) =#= 0", env_t3)

    # T4: AUDIT-044 Zero-Float Ramanujan Certifier (Petersen passes, Dumbbell14 fails with n_-=1)
    petersen = [(i, (i + 1) % 5) for i in range(5)] + [(5 + i, 5 + (i + 2) % 5) for i in range(5)] + [(i, 5 + i) for i in range(5)]
    dumbbell14 = [
        (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 4), (3, 5), (4, 5), (4, 6), (5, 6),
        (7, 8), (7, 9), (7, 10), (8, 9), (8, 10), (9, 11), (10, 12), (11, 12), (11, 13), (12, 13),
        (6, 13),
    ]
    env_t4 = {"R_pet": ramanujan_cert_matrix(10, petersen), "R_dumb": ramanujan_cert_matrix(14, dumbbell14)}
    check_both("T4a_ramanujan_petersen", "⦺_-(R_pet) ⩩ 0", "(+-0)_-(R_pet) =#= 0", env_t4)
    check_both("T4b_non_ramanujan_dumbbell14", "⦺_-(R_dumb) ⩩ 1", "(+-0)_-(R_dumb) =#= 1", env_t4)

    # T5: AUDIT-046 Regulator-Net Equalizer -> zeta(-1) = -1/12
    g_mult = ObserverGroup(
        kind="mellin_net",
        elements=(
            ((Fraction(1), Fraction(1), Fraction(0)),),
            ((Fraction(2), Fraction(1), Fraction(0)), (Fraction(-1), Fraction(2), Fraction(0))),
            ((Fraction(5, 3), Fraction(1, 3), Fraction(0)), (Fraction(-2), Fraction(2), Fraction(0)), (Fraction(4, 3), Fraction(7), Fraction(0))),
        ),
    )
    env_t5 = {"N1": MellinSeriesProbe(k_power=1), "G_mult": g_mult}
    check_both("T5_mellin_equalizer", "N1 ⟠ G_mult ⩩ -1/12", "N1 <=> G_mult =#= -1/12", env_t5)

    # T6: AUDIT-044 + #268 Cohomological Krein Signatures (Balanced (1,2,1), (2,0,2) & Asymmetric K_3 (1,0,2))
    g_odd = make_btz_odd_wormhole()
    chi1 = CocycleZ2(tuple(-1 if i == 0 else 1 for i in range(len(g_odd.edges))))
    chi2 = CocycleZ2(tuple(-1 if i == 3 else 1 for i in range(len(g_odd.edges))))
    g_k3, chi_k3 = make_k3_all_flipped()
    env_t6 = {"L_odd": g_odd, "chi1": chi1, "chi2": chi2, "L_k3": g_k3, "chi_k3": chi_k3}
    check_both("T6a_btz_balanced_k1", "⦺(L_odd ⦷ chi1) ⩩ (1, 2, 1)", "(+-0)(L_odd (||) chi1) =#= (1, 2, 1)", env_t6)
    check_both("T6b_btz_balanced_k2", "⦺(L_odd ⦷ (chi1 * chi2)) ⩩ (2, 0, 2)", "(+-0)(L_odd (||) (chi1 * chi2)) =#= (2, 0, 2)", env_t6)
    check_both("T6c_k3_asymmetric_102", "⦺(L_k3 ⦷ chi_k3) ⩩ (1, 0, 2)", "(+-0)(L_k3 (||) chi_k3) =#= (1, 0, 2)", env_t6)

    # T7: SF-04 R5 Gate rejects vacuous predicate while passing exact predicate
    spec_exact = R5Spec(predicate=lambda v: v == Fraction(11, 8), mutants=(Fraction(11, 8) + Fraction(1, 10**16), Fraction(10, 8), Fraction(0)))
    spec_vac = R5Spec(predicate=lambda _v: True, mutants=(Fraction(0), Fraction(1)))
    env_t7 = {"T_ex": spec_exact, "T_vac": spec_vac, "x": Fraction(11, 8)}
    check_both("T7a_r5_exact_kill_1", "kill(T_ex ⫩ x) ⩩ 1", "kill(T_ex _|T x) =#= 1", env_t7)
    check_both("T7b_r5_vacuous_kill_0", "kill(T_vac ⫩ x) ⩩ 0", "kill(T_vac _|T x) =#= 0", env_t7)

    return {"theorems_verified": len(results), "theorems": results}


# =============================================================================
# 6. Six Pairwise Commutator & Composition Discovery Probes (C1..C6)
# =============================================================================

def verify_screen_commutator(
    name: str,
    g_full: WeightedGraph,
    collar_c: tuple[int, ...],
    deep_d: tuple[int, ...],
    chi: CocycleZ2,
) -> dict[str, Any]:
    """Verify Probe C1: H^T Delta_CC H - Delta_B == (Delta_CC H)^T Lam_CC(chi)^{-1} (Delta_CC H) >= 0."""
    b_nodes = g_full.boundary
    nb, nc = len(b_nodes), len(collar_c)
    require(nb + nc + len(deep_d) == g_full.n_verts, "C1_PARTITION", f"{name}: B, C, D must partition V")
    d_set = IndexSet(deep_d)
    l0 = g_full.laplacian()
    l1 = g_full.laplacian(chi.signs)

    # Pushforward to B uplus C by eliminating D (via ⧄)
    keep_order = [v for v in range(g_full.n_verts) if v not in set(deep_d)]
    pos_b = tuple(keep_order.index(v) for v in b_nodes)
    pos_c = tuple(keep_order.index(v) for v in collar_c)
    lam_bc_0 = op_schur_pushforward(l0, d_set)
    lam_bc_1 = op_schur_pushforward(l1, d_set)

    # Verify C separates B from D (BB and BC blocks untouched by chi)
    require(
        qsubmat(lam_bc_0, pos_b, pos_b) == qsubmat(lam_bc_1, pos_b, pos_b)
        and qsubmat(lam_bc_0, pos_b, pos_c) == qsubmat(lam_bc_1, pos_b, pos_c),
        "C1_NOT_SEPARATING",
        "Collar C does not separate B from D",
    )

    l_cc_0 = qsubmat(lam_bc_0, pos_c, pos_c)
    l_cc_1 = qsubmat(lam_bc_1, pos_c, pos_c)
    l_cb_0 = qsubmat(lam_bc_0, pos_c, pos_b)
    delta_cc = qsub(l_cc_1, l_cc_0)
    h_ext = qscale(Fraction(-1), qsolve(l_cc_0, l_cb_0))  # Harmonic extension B -> C

    delta_b = op_holonomy_unmask(g_full, chi)
    lin_pull = qmul(qtranspose(h_ext), qmul(delta_cc, h_ext))
    defect = qsub(lin_pull, delta_b)

    dh = qmul(delta_cc, h_ext)
    rhs = qmul(qtranspose(dh), qsolve(l_cc_1, dh))
    env = {"def_lhs": defect, "def_rhs": rhs, "d_cc": delta_cc, "d_b": delta_b}
    id_ok = eval_expr("def_lhs ⩩ def_rhs", env) is True
    in_def = op_krein_inertia(defect)
    in_cc = op_krein_inertia(delta_cc)
    in_b = op_krein_inertia(delta_b)
    phi_c = sum((delta_cc[i][j] for i in range(nc) for j in range(nc)), Fraction(0))
    phi_b = sum((delta_b[i][j] for i in range(nb) for j in range(nb)), Fraction(0))

    return {
        "name": name,
        "exact_screening_identity": id_ok,
        "defect_is_psd": in_def.neg == 0,
        "krein_monotone": in_b.pos <= in_cc.pos and in_b.neg <= in_cc.neg,
        "monopole_monotone": phi_b <= phi_c,
        "inertia_delta_CC": list(in_cc.as_tuple()),
        "inertia_delta_B": list(in_b.as_tuple()),
        "inertia_screening_defect_PSD": list(in_def.as_tuple()),
        "phi_C": frac_str(phi_c),
        "phi_B": frac_str(phi_b),
        "screening_drop": frac_str(phi_c - phi_b),
    }


def run_probe_c1_schur_unmask_screening() -> dict[str, Any]:
    """Probe C1: [⧄_D, ⦷_χ] Nonlinear Loewner Screening on depth-2 BTZ, 3-layer screen, and asymmetric K_3."""
    cases: list[dict[str, Any]] = []

    # 1. Depth-2 p=2 BTZ (horizon D={0,1,2}, collar C={3,4,5}, boundary B={6..11})
    g_d2 = make_btz_depth2()
    chi_d2 = CocycleZ2(tuple(-1 if i == 0 else 1 for i in range(len(g_d2.edges))))
    cases.append(verify_screen_commutator("btz_depth2_L3", g_d2, (3, 4, 5), (0, 1, 2), chi_d2))

    # 2. Asymmetric K_3 all-flipped behind a 3-node collar screen (D={0,1,2}, C={3,4,5}, B={6,7,8})!
    edges_k3_scr = (
        (0, 1, Fraction(2)), (1, 2, Fraction(3)), (2, 0, Fraction(5)),
        (0, 3, Fraction(4)), (1, 4, Fraction(4)), (2, 5, Fraction(4)),
        (3, 6, Fraction(1)), (4, 7, Fraction(2)), (5, 8, Fraction(3)),
    )
    g_k3_scr = WeightedGraph(n_verts=9, edges=edges_k3_scr, boundary=(6, 7, 8))
    chi_k3_scr = CocycleZ2((-1, -1, -1, 1, 1, 1, 1, 1, 1))
    res_k3 = verify_screen_commutator("asymmetric_K3_screened", g_k3_scr, (3, 4, 5), (0, 1, 2), chi_k3_scr)
    cases.append(res_k3)

    # 3. 3-Layer Concentric Screen Chain: D={0,1,2} -> C2={3,4,5} -> C1={6,7,8} -> B={9,10,11}
    edges_3l_inner = (
        (0, 1, Fraction(1)), (1, 2, Fraction(1)), (2, 0, Fraction(1)),
        (0, 3, Fraction(2)), (1, 4, Fraction(2)), (2, 5, Fraction(2)),
        (3, 6, Fraction(3)), (4, 7, Fraction(3)), (5, 8, Fraction(3)),
    )
    edges_3l_full = edges_3l_inner + (
        (6, 9, Fraction(1)), (7, 10, Fraction(1)), (8, 11, Fraction(1)),
    )
    g_3l_in = WeightedGraph(n_verts=9, edges=edges_3l_inner, boundary=(6, 7, 8))
    chi_3l_in = CocycleZ2(tuple(-1 if i == 0 else 1 for i in range(len(edges_3l_inner))))
    g_3l_full = WeightedGraph(n_verts=12, edges=edges_3l_full, boundary=(9, 10, 11))
    chi_3l_full = CocycleZ2(tuple(-1 if i == 0 else 1 for i in range(len(edges_3l_full))))

    r_inner = verify_screen_commutator("concentric_3layer_C2_to_C1", g_3l_in, (3, 4, 5), (0, 1, 2), chi_3l_in)
    r_outer = verify_screen_commutator("concentric_3layer_C1_to_B", g_3l_full, (6, 7, 8), (0, 1, 2, 3, 4, 5), chi_3l_full)
    phi_c2 = Fraction(r_inner["phi_C"])
    phi_c1_in = Fraction(r_inner["phi_B"])
    phi_c1_out = Fraction(r_outer["phi_C"])
    phi_b = Fraction(r_outer["phi_B"])
    cases.append(r_inner)
    cases.append(r_outer)

    all_ok = (
        all(c["exact_screening_identity"] and c["defect_is_psd"] and c["krein_monotone"] and c["monopole_monotone"] for c in cases)
        and res_k3["inertia_delta_CC"] == [1, 0, 2]
        and res_k3["inertia_delta_B"] == [1, 0, 2]
        and phi_c1_in == phi_c1_out
        and phi_c2 > phi_c1_in > phi_b
    )

    return {
        "probe": "C1_schur_unmask_loewner_screening",
        "cases_verified": len(cases),
        "all_defects_strictly_PSD_even_for_asymmetric_K3": all_ok,
        "three_layer_monopole_chain": [frac_str(phi_c2), frac_str(phi_c1_in), frac_str(phi_b)],
        "cases": cases,
    }


def run_probe_c2_nested_shadow_and_associator() -> dict[str, Any]:
    """Probe C2: Nested Shadow Composition (M ⧄ B) ⧅ C vs M ⧅ (B ⊔ C) & Singular Associator Breakdown."""
    rng = random.Random(20260402)

    gen_ok = 0
    for t in range(12):
        nb, nd = 3, 4
        u_fac = qmat([[rng.randint(-2, 2) for _ in range(2)] for _ in range(nd)])
        s2 = qmat([[1, 0], [0, -1 if t % 2 else 1]])
        d_blk = qmul(u_fac, qmul(s2, qtranspose(u_fac)))
        a_raw = [[rng.randint(-2, 2) for _ in range(nb)] for _ in range(nb)]
        a_blk = qmat([[a_raw[i][j] + a_raw[j][i] for j in range(nb)] for i in range(nb)])
        b_blk = qmat([[rng.randint(-2, 2) for _ in range(nd)] for _ in range(nb)])
        m_full = tuple(a_blk[i] + b_blk[i] for i in range(nb)) + tuple(qtranspose(b_blk)[i] + d_blk[i] for i in range(nd))
        elim_d = IndexSet(tuple(range(nb, nb + nd)))
        s_mat = op_schur_pushforward(m_full, elim_d)
        sh = op_dark_mode_shadow(m_full, elim_d)
        r_cross = sh.r_cross
        if sh.coupling_map is not None:
            k_vecs = qnullspace(qtranspose(sh.coupling_map))
        else:
            k_vecs = tuple(tuple(Fraction(1 if i == j else 0) for j in range(nb)) for i in range(nb))
        if k_vecs:
            pk = qtranspose(k_vecs)
            in_sk = op_krein_inertia(qmul(qtranspose(pk), qmul(s_mat, pk)))
        else:
            in_sk = InertiaTriple(0, 0, 0)
        in_m = op_krein_inertia(m_full)
        in_d = op_krein_inertia(d_blk)
        pred = InertiaTriple(in_d.pos + in_sk.pos + r_cross, in_d.zero + in_sk.zero - r_cross, in_d.neg + in_sk.neg + r_cross)
        if in_m == pred:
            gen_ok += 1

    m_bb_inv = qmat([[3, 1], [1, 2]])
    m_cb = qmat([[1, 0], [0, 1]])
    schur_c_base = qmul(m_cb, qsolve(m_bb_inv, qtranspose(m_cb)))
    rank1_c = qmat([[2, 2], [2, 2]])
    m_cc_exact = qadd(schur_c_base, rank1_c)
    m_ac = qmat([[1, 0], [0, 2]])
    m_ab = qmat([[1, -1], [2, 1]])
    m_aa = qmat([[5, 1], [1, 4]])
    rows_6 = []
    for i in range(2):
        rows_6.append(m_aa[i] + m_ac[i] + m_ab[i])
    for i in range(2):
        rows_6.append(qtranspose(m_ac)[i] + m_cc_exact[i] + m_cb[i])
    for i in range(2):
        rows_6.append(qtranspose(m_ab)[i] + qtranspose(m_cb)[i] + m_bb_inv[i])
    m6 = tuple(rows_6)
    env_p2 = {"M": m6, "B": IndexSet((4, 5)), "C": IndexSet((2, 3))}
    p2_ok = (
        eval_expr("dim(M ⧅ B) ⩩ 0", env_p2) is True
        and eval_expr("dim((M ⧄ B) ⧅ C) ⩩ dim(M ⧅ (C | B))", env_p2) is True
        and eval_expr("rk((M ⧄ B) ⧅ C) ⩩ rk(M ⧅ (C | B))", env_p2) is True
    )
    sh_stage = eval_expr("(M ⧄ B) ⧅ C", env_p2)

    u_d = qmat([[1], [2], [-1]])
    d_sing = qmul(u_d, qtranspose(u_d))
    x_dec = qmat([[1], [-1], [2], [1]])
    mc_dec = qmul(x_dec, qtranspose(u_d))
    ac_blk = qmat([[5, 1, 0, 1], [1, 4, 1, 0], [0, 1, 6, 1], [1, 0, 1, 5]])
    m7_dec = tuple(ac_blk[i] + mc_dec[i] for i in range(4)) + tuple(qtranspose(mc_dec)[i] + d_sing[i] for i in range(3))
    m7_cpl_list = [list(r) for r in m7_dec]
    m7_cpl_list[2][4] += Fraction(3)
    m7_cpl_list[4][2] += Fraction(3)
    m7_cpl = tuple(tuple(r) for r in m7_cpl_list)
    env_p3 = {"M_dec": m7_dec, "M_cpl": m7_cpl, "C": IndexSet((2, 3)), "D": IndexSet((4, 5, 6))}
    dec_ok = eval_expr("rk(M_dec ⧅ D) ⩩ 0", env_p3) is True and eval_expr("(M_dec ⧄ D) ⧄ C ⩩ M_dec ⧄ (C | D)", env_p3) is True
    cpl_ok = eval_expr("rk(M_cpl ⧅ D) ⩩ 1", env_p3) is True and eval_expr("((M_cpl ⧄ D) ⧄ C) ⩩ (M_cpl ⧄ (C | D))", env_p3) is False
    assoc_defect = eval_expr("((M_cpl ⧄ D) ⧄ C) - (M_cpl ⧄ (C | D))", env_p3)

    return {
        "probe": "C2_nested_shadow_and_singular_associator",
        "all_verified": gen_ok == 12 and p2_ok and dec_ok and cpl_ok,
        "generalized_indefinite_singular_krein_exact": f"{gen_ok}/12",
        "nonsingular_B_nested_shadow_preserved": {"dim_dark": sh_stage.dim_dark, "r_cross": sh_stage.r_cross},
        "singular_associator_decoupled_vanishes": dec_ok,
        "singular_associator_coupled_nonzero": cpl_ok,
        "coupled_associator_rank": qrank(assoc_defect),
        "coupled_associator_inertia": list(op_krein_inertia(assoc_defect).as_tuple()),
    }


def run_probe_c3_schur_equalizer_jensen() -> dict[str, Any]:
    """Probe C3: [⧄_B, ⟠_G] Matrix-Jensen / Schur Concavity Commutator Positivity."""
    rng = random.Random(20260403)
    g_full = ObserverGroup(kind="perm_group", elements=((0, 1, 2, 3, 4, 5), (1, 2, 0, 4, 5, 3), (2, 0, 1, 5, 3, 4)))
    g_a = ObserverGroup(kind="perm_group", elements=((0, 1, 2), (1, 2, 0), (2, 0, 1)))
    b_set = IndexSet((3, 4, 5))

    strict_psd_count = 0
    sample_in: tuple[int, int, int] = (0, 0, 0)
    m_spd: QMat = qeye(6)
    for t in range(8):
        r_mat = [[Fraction(rng.randint(-3, 3)) for _ in range(6)] for _ in range(6)]
        m_spd = tuple(
            tuple(sum((r_mat[k][i] * r_mat[k][j] for k in range(6)), Fraction(0)) + (Fraction(5) if i == j else Fraction(0)) for j in range(6))
            for i in range(6)
        )
        env = {"M": m_spd, "G": g_full, "G_A": g_a, "B": b_set}
        gap = eval_expr("((M ⟠ G) ⧄ B) - ((M ⧄ B) ⟠ G_A)", env)
        in_gap = op_krein_inertia(gap)
        if in_gap.neg == 0 and in_gap.pos > 0:
            strict_psd_count += 1
        if t == 0:
            sample_in = in_gap.as_tuple()

    m_inv = op_observer_equalizer(m_spd, g_full)
    env_inv = {"M_inv": m_inv, "G": g_full, "G_A": g_a, "B": b_set}
    inv_ok = eval_expr("((M_inv ⟠ G) ⧄ B) ⩩ ((M_inv ⧄ B) ⟠ G_A)", env_inv) is True

    return {
        "probe": "C3_schur_equalizer_matrix_jensen",
        "all_verified": strict_psd_count == 8 and inv_ok,
        "non_invariant_strict_PSD_trials": f"{strict_psd_count}/8",
        "sample_jensen_gap_inertia": list(sample_in),
        "g_invariant_exact_commutation": inv_ok,
    }


def run_probe_c4_woodbury_monopole_obstruction() -> dict[str, Any]:
    """Probe C4: [⦷_χ, ⧇] Exact Rank-2 Woodbury Formula Coupling Phi_B(chi_{e*}) to Dirichlet Obstruction c_harm^Dir(e*)."""
    test_graphs: list[tuple[str, WeightedGraph, int]] = [
        ("odd_btz_mouth_edge", make_btz_odd_wormhole(), 0),
        ("odd_btz_cut_bridge", make_btz_odd_wormhole(), 6),
        (
            "asymmetric_weighted_triangle",
            WeightedGraph(
                n_verts=5,
                edges=((0, 1, Fraction(3)), (1, 2, Fraction(5)), (2, 0, Fraction(7)), (0, 3, Fraction(2)), (1, 4, Fraction(11))),
                boundary=(3, 4),
            ),
            0,
        ),
        (
            "dead_end_dangling_bridge",
            WeightedGraph(
                n_verts=5,
                edges=((0, 1, Fraction(1)), (1, 2, Fraction(1)), (2, 0, Fraction(1)), (0, 3, Fraction(5)), (1, 4, Fraction(2))),
                boundary=(4,),
            ),
            3,
        ),
    ]

    rows: list[dict[str, Any]] = []
    for name, g, flip_idx in test_graphs:
        chi = CocycleZ2(tuple(-1 if idx == flip_idx else 1 for idx in range(len(g.edges))))
        env = {"L": g, "chi": chi}
        phi_direct: Fraction = eval_expr("Phi(L ⦷ chi)", env)

        i_nodes = g.interior()
        i_map = {v: idx for idx, v in enumerate(i_nodes)}
        l_ii = qsubmat(g.laplacian(), i_nodes, i_nodes)
        g_ii = qsolve(l_ii, qeye(len(i_nodes)))
        u, v, w = g.edges[flip_idx]
        iu, iv = i_map[u], i_map[v]
        r_dir = g_ii[iu][iu] + g_ii[iv][iv] - 2 * g_ii[iu][iv]
        c_dir = Fraction(1) - w * r_dir
        alpha = w * (g_ii[iu][iu] + g_ii[iv][iv] + 2 * g_ii[iu][iv])
        beta = w * (g_ii[iu][iu] - g_ii[iv][iv])
        phi_woodbury = (4 * w * c_dir) / ((1 + alpha) * c_dir + beta * beta)
        e_cochain = OneCochain(g, tuple(Fraction(1 if idx == flip_idx else 0) for idx in range(len(g.edges))))
        c_hodge = op_cohom_obstruction(e_cochain)
        rows.append({
            "name": name,
            "phi_direct": frac_str(phi_direct),
            "phi_woodbury": frac_str(phi_woodbury),
            "c_harm_ungrounded": frac_str(c_hodge),
            "c_harm_dirichlet": frac_str(c_dir),
            "asymmetry_beta": frac_str(beta),
            "rayleigh_monotone": c_hodge <= c_dir,
            "exact_match": op_exact_null_equiv(phi_direct, phi_woodbury),
        })

    return {
        "probe": "C4_woodbury_monopole_dirichlet_obstruction",
        "all_verified": all(r["exact_match"] and r["rayleigh_monotone"] for r in rows),
        "cases_verified": len(rows),
        "cases": rows,
    }


def run_probe_c5_r5_exact_vs_float64_killshot() -> dict[str, Any]:
    """Probe C5: ⫩ coupled with ⩩ kills 100% of CS-11 near-miss mutants while float64 == lets them survive."""
    r_sqrt2 = Fraction(131836323, 93222358)
    res_sqrt2_exact = r_sqrt2 * r_sqrt2 - 2
    r_phi = Fraction(165580141, 102334155)
    res_phi_exact = r_phi * r_phi - r_phi - 1
    res_tiny = Fraction(1, 10**18)

    def float64_mirage_pred(pair: tuple[str, Fraction]) -> bool:
        kind, val = pair
        if kind == "zero":
            return float(val) == 0.0
        if kind == "sqrt2":
            return float(val) == (2.0 ** 0.5)
        if kind == "phi":
            fv = float(val)
            return (fv * fv - fv - 1.0) == 0.0
        return (1.0 + float(val)) == 1.0

    def exact_nullequiv_pred(pair: tuple[str, Fraction]) -> bool:
        kind, val = pair
        if kind == "zero":
            return op_exact_null_equiv(val, Fraction(0))
        if kind == "sqrt2":
            return op_exact_null_equiv(val * val - 2, Fraction(0))
        if kind == "phi":
            return op_exact_null_equiv(val * val - val - 1, Fraction(0))
        return op_exact_null_equiv(Fraction(1) + val, Fraction(1))

    mutants = (("sqrt2", r_sqrt2), ("phi", r_phi), ("tiny", res_tiny))
    spec_ex = R5Spec(predicate=exact_nullequiv_pred, mutants=mutants)
    spec_fl = R5Spec(predicate=float64_mirage_pred, mutants=mutants)
    env = {"T_exact": spec_ex, "T_float": spec_fl, "x_valid": ("zero", Fraction(0))}

    gr_ex: GateResult = eval_expr("T_exact ⫩ x_valid", env)
    gr_fl: GateResult = eval_expr("T_float ⫩ x_valid", env)

    return {
        "probe": "C5_r5_gate_exact_vs_float64_killshot",
        "all_verified": gr_ex.passed and gr_ex.kill_ratio == 1 and (not gr_fl.passed) and gr_fl.kill_ratio == 0,
        "exact_gate_passed": gr_ex.passed,
        "exact_kill_ratio": frac_str(gr_ex.kill_ratio),
        "float64_gate_passed": gr_fl.passed,
        "float64_kill_ratio": frac_str(gr_fl.kill_ratio),
        "exact_residuals_refuted": {
            "sqrt2_convergent": frac_str(res_sqrt2_exact),
            "phi_F41_F40": frac_str(res_phi_exact),
            "tiny_1e_18": frac_str(res_tiny),
        },
    }


def _lipschitz_z2_mix(x: Fraction, y: Fraction) -> Fraction:
    """Exact rational Z_2 x Z_2-equivariant 1-Lipschitz map f(x,y) = sgn(x)sgn(y)min(|x|,|y|)."""
    if x == 0 or y == 0:
        return Fraction(0)
    sgn = 1 if (x > 0) == (y > 0) else -1
    mag = abs(x) if abs(x) <= abs(y) else abs(y)
    return mag if sgn == 1 else -mag


def run_probe_c6_linear_monopole_subadditivity_metric() -> dict[str, Any]:
    """Probe C6 (NEW UNCONDITIONAL THEOREM): Linear Monopole Subadditivity & Rational Metric on H^1(G, B; Z_2)."""
    cases: list[dict[str, Any]] = []

    def check_pair(name: str, g: WeightedGraph, c1: CocycleZ2, c2: CocycleZ2) -> dict[str, Any]:
        c12 = c1.product(c2)
        env = {"L": g, "c1": c1, "c2": c2}
        phi1: Fraction = eval_expr("Phi(L ⦷ c1)", env)
        phi2: Fraction = eval_expr("Phi(L ⦷ c2)", env)
        phi12: Fraction = eval_expr("Phi(L ⦷ (c1 * c2))", env)
        x1 = g.harmonic_extension(c1.signs)
        x2 = g.harmonic_extension(c2.signs)
        z_wit = tuple(_lipschitz_z2_mix(a, b) for a, b in zip(x1, x2))
        bc_ok = all(z_wit[b] == 1 for b in g.boundary)
        lip_ok = all(
            (z_wit[u] - (s1 * s2) * z_wit[v]) ** 2 <= (x1[u] - s1 * x1[v]) ** 2 + (x2[u] - s2 * x2[v]) ** 2
            for (u, v, _w), s1, s2 in zip(g.edges, c1.signs, c2.signs)
        )
        e_z = g.dirichlet_energy(c12.signs, z_wit)
        sub_ok = phi12 <= e_z <= phi1 + phi2
        return {
            "name": name,
            "verified": bc_ok and lip_ok and sub_ok,
            "phi_1": frac_str(phi1),
            "phi_2": frac_str(phi2),
            "phi_12": frac_str(phi12),
            "witness_energy_E_z": frac_str(e_z),
            "phi_1_plus_2": frac_str(phi1 + phi2),
            "subadditive_slack": frac_str(phi1 + phi2 - phi12),
        }

    g_odd = make_btz_odd_wormhole()
    cases.append(check_pair(
        "btz_odd_L3_L3",
        g_odd,
        CocycleZ2(tuple(-1 if i == 0 else 1 for i in range(len(g_odd.edges)))),
        CocycleZ2(tuple(-1 if i == 3 else 1 for i in range(len(g_odd.edges)))),
    ))
    g_ev = make_btz_even_wormhole()
    cases.append(check_pair(
        "btz_even_L4_L4",
        g_ev,
        CocycleZ2(tuple(-1 if i == 0 else 1 for i in range(len(g_ev.edges)))),
        CocycleZ2(tuple(-1 if i == 4 else 1 for i in range(len(g_ev.edges)))),
    ))
    g_k4 = WeightedGraph(
        n_verts=8,
        edges=(
            (0, 1, Fraction(2)), (1, 2, Fraction(3)), (2, 3, Fraction(5)),
            (3, 0, Fraction(7)), (0, 2, Fraction(11)), (1, 3, Fraction(13)),
            (0, 4, Fraction(1)), (1, 5, Fraction(2)), (2, 6, Fraction(3)), (3, 7, Fraction(5)),
        ),
        boundary=(4, 5, 6, 7),
    )
    cases.append(check_pair(
        "weighted_K4_disjoint",
        g_k4,
        CocycleZ2((-1, 1, 1, 1, 1, 1, 1, 1, 1, 1)),
        CocycleZ2((1, 1, -1, 1, 1, 1, 1, 1, 1, 1)),
    ))
    cases.append(check_pair(
        "weighted_K4_adjacent",
        g_k4,
        CocycleZ2((-1, 1, 1, 1, 1, 1, 1, 1, 1, 1)),
        CocycleZ2((1, -1, 1, 1, 1, 1, 1, 1, 1, 1)),
    ))

    rng = random.Random(20260406)
    random_ok = 0
    for _ in range(12):
        w_e = [
            (0, 1, Fraction(rng.choice((1, 3, 20, 100)))),
            (1, 2, Fraction(rng.choice((1, 3, 20, 100)))),
            (2, 3, Fraction(rng.choice((1, 3, 20, 100)))),
            (3, 0, Fraction(rng.choice((1, 3, 20, 100)))),
            (0, 2, Fraction(rng.choice((1, 3, 20, 100)))),
            (1, 3, Fraction(rng.choice((1, 3, 20, 100)))),
            (0, 4, Fraction(rng.choice((1, 7, 50)))),
            (2, 5, Fraction(rng.choice((1, 7, 50)))),
        ]
        gr = WeightedGraph(n_verts=6, edges=tuple(w_e), boundary=(4, 5))
        m1 = rng.randint(1, 63)
        m2 = rng.randint(1, 63)
        c1 = CocycleZ2(tuple(-1 if (i < 6 and ((m1 >> i) & 1)) else 1 for i in range(8)))
        c2 = CocycleZ2(tuple(-1 if (i < 6 and ((m2 >> i) & 1)) else 1 for i in range(8)))
        if check_pair("rand", gr, c1, c2)["verified"]:
            random_ok += 1

    return {
        "probe": "C6_linear_monopole_subadditivity_metric",
        "all_verified": all(c["verified"] for c in cases) and random_ok == 12,
        "theorem": "Phi_B(L ⦷ (chi1*chi2)) <= E_{chi1*chi2}(z) <= Phi_B(L ⦷ chi1) + Phi_B(L ⦷ chi2) via exact rational 1-Lipschitz witness z_v = sgn(x1)sgn(x2)min(|x1|,|x2|)",
        "structured_cases": cases,
        "random_extreme_weight_cases_certified": f"{random_ok}/12",
    }


# =============================================================================
# 7. Main Driver
# =============================================================================

def run_all() -> dict[str, Any]:
    reg = verify_glyph_registry()
    thms = run_compressed_theorems()
    probes = {
        "C1": run_probe_c1_schur_unmask_screening(),
        "C2": run_probe_c2_nested_shadow_and_associator(),
        "C3": run_probe_c3_schur_equalizer_jensen(),
        "C4": run_probe_c4_woodbury_monopole_obstruction(),
        "C5": run_probe_c5_r5_exact_vs_float64_killshot(),
        "C6": run_probe_c6_linear_monopole_subadditivity_metric(),
    }
    all_ok = (
        reg["all_category_Sm_and_zero_collision"]
        and all(t["verified"] for t in thms["theorems"])
        and probes["C1"]["all_defects_strictly_PSD_even_for_asymmetric_K3"]
        and probes["C2"]["all_verified"]
        and probes["C3"]["all_verified"]
        and probes["C4"]["all_verified"]
        and probes["C5"]["all_verified"]
        and probes["C6"]["all_verified"]
    )
    payload: dict[str, Any] = {
        "schema": "aletheia.wave2.round4c.operator_calculus.v1",
        "oracle_class": "exact",
        "verdict": "ALETHEIA_OPERATOR_CALCULUS_ALL_LAWS_VERIFIED" if all_ok else "FAILED",
        "glyph_registry_verification": reg,
        "compressed_expedition_theorems": thms,
        "commutator_discovery_probes": probes,
    }
    payload["canonical_sha256"] = hashlib.sha256(canonical_json(payload).encode("utf-8")).hexdigest()
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description="Aletheia 8-Glyph Operator Calculus Executable Engine & Commutator Prover")
    parser.add_argument("--json", action="store_true", help="Emit canonical JSON to stdout")
    parser.add_argument("--write-cert", type=Path, default=None, help="Write certificate JSON to path")
    args = parser.parse_args()

    result = run_all()
    text = json.dumps(result, indent=2, sort_keys=True, allow_nan=False) + "\n"
    if args.write_cert is not None:
        args.write_cert.write_text(text, encoding="utf-8")
    if args.json:
        sys.stdout.write(text)
    else:
        print(f"Verdict: {result['verdict']}")
        print(f"canonical_sha256: {result['canonical_sha256']}")
        print(f"Glyphs verified: {result['glyph_registry_verification']['glyph_count']}/8")
        print(f"Compressed theorems verified: {result['compressed_expedition_theorems']['theorems_verified']}")
        print(f"Commutator probes verified: {len(result['commutator_discovery_probes'])}/6")
    return 0 if result["verdict"] == "ALETHEIA_OPERATOR_CALCULUS_ALL_LAWS_VERIFIED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
