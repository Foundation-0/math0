"""Matrices over GF(q): parsing, row reduction, systematic forms.

A matrix is a list of rows; each row is a list of field elements (ints).
"""
from __future__ import annotations

import re

from .field import GF

Matrix = list[list[int]]


def validate_matrix(G: Matrix, F: GF) -> tuple[int, int]:
    """Return (rows, cols); raise ValueError on ragged/out-of-field input."""
    if not G or not G[0]:
        raise ValueError("matrix must have at least one row and one column")
    n = len(G[0])
    for row in G:
        if len(row) != n:
            raise ValueError("matrix rows have different lengths")
        for a in row:
            F._check(a)
    return len(G), n


def parse_matrix(text: str, F: GF) -> Matrix:
    """Parse a generator matrix from text.

    Accepted layouts (auto-detected per line):
      * whitespace- or comma-separated integers: ``1 0 2`` / ``1,0,2``
      * bracketed rows as pasted from Magma/Sage/Python: ``[1,0,2]``
      * compact digit strings (only unambiguous because q <= 9): ``102``
    Blank lines and ``#`` comments are ignored.  A leading header line of
    the form ``q k n`` or ``k n`` (three/two integers on their own line,
    where the remaining row count matches) is also accepted.
    """
    lines = []
    for raw in text.splitlines():
        line = raw.split("#", 1)[0].strip().rstrip(";")
        if line:
            lines.append(line)
    if not lines:
        raise ValueError("no matrix data found")

    rows: Matrix = []
    for idx, line in enumerate(lines):
        s = line.strip().strip("[]")
        if re.fullmatch(r"[0-9]+", s) and len(s) > 1 and (rows or len(lines) > 1):
            # compact row, unless it is a lone header candidate handled below
            vals = [int(ch) for ch in s]
            # Heuristic: a first line like "3 6 11" never reaches here (spaces),
            # and a single compact line is one row. Keep it as a row.
        else:
            toks = [t for t in re.split(r"[\s,\[\]]+", s) if t != ""]
            if not toks:
                continue
            if idx == 0 and len(toks) in (2, 3) and len(lines) > 1:
                # Possible header "k n" / "q k n": only treat as header when
                # the numbers are inconsistent with being a matrix row of the
                # width determined by the second line.
                second = lines[1].strip().strip("[]")
                if re.fullmatch(r"[0-9]+", second):
                    width2 = len(second)
                else:
                    width2 = len([t for t in re.split(r"[\s,\[\]]+", second) if t])
                hdr = [int(t) for t in toks]
                # Header only when the values read as (q,k,n)/(k,n)
                # consistent with the remaining rows; otherwise the line
                # is a matrix row (and raggedness is reported as such).
                consistent = (
                    (len(hdr) == 3 and hdr[1] == len(lines) - 1 and hdr[2] == width2)
                    or (len(hdr) == 2 and hdr[0] == len(lines) - 1 and hdr[1] == width2))
                if consistent:
                    if len(hdr) == 3 and hdr[0] != F.q:
                        raise ValueError(
                            f"header says q={hdr[0]} but --q is {F.q}")
                    continue
            try:
                vals = [int(t) for t in toks]
            except ValueError as e:
                raise ValueError(f"cannot parse matrix line {idx + 1}: {raw!r}") from e
        rows.append(vals)
    validate_matrix(rows, F)
    return rows


def rref(G: Matrix, F: GF, col_order: list[int] | None = None):
    """Reduced row echelon form.

    Columns are considered as pivot candidates in ``col_order`` (default
    left-to-right).  Returns (rref_rows, pivot_cols) with zero rows dropped;
    row i has its pivot in column pivot_cols[i].  The returned matrix is in
    the original column order (not permuted).
    """
    rows = [list(r) for r in G]
    ncols = len(rows[0]) if rows else 0
    order = list(range(ncols)) if col_order is None else list(col_order)
    pivots: list[int] = []
    r = 0
    for c in order:
        if r >= len(rows):
            break
        piv = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = F.inv(rows[r][c])
        rows[r] = [F.mul(inv, a) for a in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [F.sub(a, F.mul(f, b)) for a, b in zip(rows[i], rows[r])]
        pivots.append(c)
        r += 1
    return rows[:r], pivots


def rank(G: Matrix, F: GF) -> int:
    return len(rref(G, F)[0])


def nullspace_basis(H: Matrix, F: GF) -> Matrix:
    """Basis (as rows) of {x : H x^T = 0}; used to turn a parity-check
    matrix into a generator matrix."""
    R, pivots = rref(H, F)
    n = len(H[0])
    free = [c for c in range(n) if c not in set(pivots)]
    basis = []
    for f in free:
        x = [0] * n
        x[f] = 1
        for i, pc in enumerate(pivots):
            x[pc] = F.neg(R[i][f])
        basis.append(x)
    return basis


def row_space_contains(G: Matrix, F: GF, vec: list[int]) -> bool:
    """True iff ``vec`` is a GF(q)-linear combination of the rows of G."""
    R, _ = rref(G, F)
    return rank(R + [list(vec)], F) == len(R)


def systematic_form(G: Matrix, F: GF, col_order: list[int]):
    """Return (rows, info_cols) where rows form [I | *] on ``info_cols``:
    row i is 1 in column info_cols[i] and 0 in the other info columns.
    ``col_order`` lists preferred information columns first."""
    R, pivots = rref(G, F, col_order=col_order)
    return R, pivots


def find_disjoint_info_sets(G: Matrix, F: GF, max_sets: int | None = None):
    """Greedily find pairwise disjoint information sets (pivot column sets).

    Returns a list of (systematic_rows, info_cols).  Each successive set is
    searched with the already-used columns deprioritised; a set counts only
    if its pivots avoid every column used by earlier sets.  At least one set
    is always returned for a nonzero code.  Finding the maximum number of
    disjoint information sets is not attempted (greedy is enough for the
    Brouwer-Zimmermann lower bound; fewer sets only slow the proof).
    """
    n = len(G[0])
    k = rank(G, F)
    used: set[int] = set()
    out = []
    cap = max_sets if max_sets is not None else max(1, n // max(k, 1))
    while len(out) < cap:
        order = [c for c in range(n) if c not in used] + sorted(used)
        rows, pivots = systematic_form(G, F, order)
        if len(pivots) < k:
            break
        if out and any(c in used for c in pivots):
            break
        out.append((rows, pivots))
        used.update(pivots)
    return out


def weight(vec: list[int]) -> int:
    return sum(1 for a in vec if a != 0)


def combine(rows: Matrix, coeffs: list[int], F: GF) -> list[int]:
    n = len(rows[0])
    out = [0] * n
    for c, row in zip(coeffs, rows):
        if c:
            out = [F.add(a, F.mul(c, b)) for a, b in zip(out, row)]
    return out
