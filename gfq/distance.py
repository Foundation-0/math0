"""Exact minimum distance of a linear code over GF(q).

Two exact methods:

``brute``
    Enumerate every codeword (up to the harmless normalisation that the
    first nonzero message coefficient is 1, which does not change weights).
    Cost is (q^k - 1)/(q - 1) codewords.  Exact, but only feasible for
    small q^k.

``bz`` (Brouwer-Zimmermann style)
    Find g pairwise disjoint information sets.  In each corresponding
    systematic form, enumerate all row combinations whose message weight
    is <= s, for s = 1, 2, ...  This gives an upper bound ``ub`` (the
    lightest codeword seen).  It also gives a *proved* lower bound:
    any codeword c with weight < g*(s+1) has, by pigeonhole on the g
    disjoint information sets, at most s nonzero coordinates in one of
    them, so c would have been enumerated in that form.  Hence
    d >= min(ub, g*(s+1)).  The loop stops when the two bounds meet,
    which is an exact proof, or when an enumeration budget is exhausted,
    in which case the (honest) interval [lower_bound, upper_bound] is
    returned with ``complete=False`` and no claim of exactness.

``auto`` picks brute force when its estimated cost is below
``brute_limit``, else Brouwer-Zimmermann.

No method here is a heuristic search: a result with ``complete=True``
is exact (the finite enumeration above).  Such finite checks are
labelled VERIFIED in project reporting, not "proved" in the
human-mathematics sense, although the certificate codeword plus the
enumeration argument above let anyone re-verify them independently.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations, product
from math import comb

from .field import GF
from .matrix import Matrix, find_disjoint_info_sets, rref, validate_matrix, weight


@dataclass
class MinDistanceResult:
    n: int
    k: int
    d: int | None            # exact distance, or None if incomplete
    lower_bound: int
    upper_bound: int
    codeword: list[int]      # a minimum- (or lightest-found-) weight codeword
    method: str
    enumerated: int          # number of (normalised) combinations examined
    num_info_sets: int = 0   # g, for the BZ method
    complete: bool = True

    def params(self) -> str:
        if self.complete:
            return f"[{self.n},{self.k},{self.d}]"
        return f"[{self.n},{self.k},d in [{self.lower_bound},{self.upper_bound}]] (incomplete)"


def _basis(G: Matrix, F: GF) -> Matrix:
    rows, _ = rref(G, F)
    if not rows:
        raise ValueError("generator matrix has rank 0: the code is {0} and "
                         "minimum distance is undefined")
    return rows


def _combos(k: int, s: int, F: GF):
    """Yield coeff vectors (tuples, length k) of weight exactly s whose
    first nonzero entry is 1 (one representative per scalar multiple)."""
    nz = F.nonzero()
    for supp in combinations(range(k), s):
        for rest in product(nz, repeat=s - 1):
            coeffs = [0] * k
            coeffs[supp[0]] = 1
            for pos, val in zip(supp[1:], rest):
                coeffs[pos] = val
            yield coeffs


def _combo_count(k: int, s: int, q: int) -> int:
    return comb(k, s) * (q - 1) ** (s - 1) if s >= 1 else 0


def _eval_combo(rows: Matrix, coeffs, F: GF, cutoff: int):
    """Return (weight, codeword); weight may be reported as > cutoff early
    only after the full combination is formed (cancellation forbids
    earlier pruning), but counting stops once it reaches cutoff."""
    n = len(rows[0])
    out = [0] * n
    add, mul = F._add, F._mul
    for c, row in zip(coeffs, rows):
        if c == 1:
            out = [add[a][b] for a, b in zip(out, row)]
        elif c:
            out = [add[a][mul[c][b]] for a, b in zip(out, row)]
    w = 0
    for a in out:
        if a:
            w += 1
            if w >= cutoff:
                break
    return w, out


def brute_force_min_distance(G: Matrix, F: GF) -> MinDistanceResult:
    validate_matrix(G, F)
    basis = _basis(G, F)
    k, n = len(basis), len(basis[0])
    best_w, best_c, total = n + 1, None, 0
    for s in range(1, k + 1):
        for coeffs in _combos(k, s, F):
            total += 1
            w, c = _eval_combo(basis, coeffs, F, best_w)
            if w < best_w:
                best_w, best_c = w, c
                if best_w == 1:
                    break
        if best_w == 1:
            break
    return MinDistanceResult(n, k, best_w, best_w, best_w, best_c,
                             "brute", total, 0, True)


def bz_min_distance(G: Matrix, F: GF, max_enum: int = 2_000_000) -> MinDistanceResult:
    validate_matrix(G, F)
    basis = _basis(G, F)
    k, n = len(basis), len(basis[0])

    # Upper bound seed: every nonzero row of the *given* G is a codeword.
    ub, best_c = n + 1, None
    for row in G:
        w = weight(row)
        if 0 < w < ub:
            ub, best_c = w, list(row)

    info_sets = find_disjoint_info_sets(basis, F)
    g = len(info_sets)
    enumerated = 0
    lb = 1
    s = 0
    while lb < ub:
        s += 1
        if s > k:  # everything enumerated in the first form: exact
            lb = ub
            break
        level_cost = g * _combo_count(k, s, F.q)
        if enumerated + level_cost > max_enum:
            return MinDistanceResult(n, k, None, lb, ub, best_c, "bz",
                                     enumerated, g, False)
        for rows, _info in info_sets:
            for coeffs in _combos(k, s, F):
                enumerated += 1
                w, c = _eval_combo(rows, coeffs, F, ub)
                if 0 < w < ub:
                    ub, best_c = w, c
        lb = min(ub, g * (s + 1))
    return MinDistanceResult(n, k, ub, ub, ub, best_c, "bz",
                             enumerated, g, True)


def min_distance(G: Matrix, F: GF, method: str = "auto",
                 brute_limit: int = 400_000,
                 max_enum: int = 2_000_000) -> MinDistanceResult:
    """Exact minimum distance.  See module docstring for methods/limits."""
    if method not in ("auto", "brute", "bz"):
        raise ValueError(f"unknown method {method!r}; use auto|brute|bz")
    validate_matrix(G, F)
    k = len(_basis(G, F))
    if method == "brute":
        return brute_force_min_distance(G, F)
    if method == "bz":
        return bz_min_distance(G, F, max_enum=max_enum)
    brute_cost = (F.q ** k - 1) // (F.q - 1) if F.q > 1 else 0
    if brute_cost <= brute_limit:
        return brute_force_min_distance(G, F)
    return bz_min_distance(G, F, max_enum=max_enum)
