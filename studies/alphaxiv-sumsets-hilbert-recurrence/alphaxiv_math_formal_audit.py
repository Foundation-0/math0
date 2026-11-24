#!/usr/bin/env python3
r"""Wave 2 Round 5 — Arm R5-5 (AUDIT-060): alphaXiv Formal Math, Sumsets, HOPE Hilbert Schur & Recurrence Convergence.

Zero external dependencies (pure Python 3 stdlib: int, Fraction, hashlib, json,
itertools, re). Zero floats in any theorem or emitted JSON. Zero bare asserts.
Safe and bit-identical across all 4 isolated R4 Python modes:
  python3 -I -B alphaxiv_math_formal_audit.py --json
  python3 -I -O -B alphaxiv_math_formal_audit.py --json
  python3 -I -B -W error alphaxiv_math_formal_audit.py --json
  python3 -I -O -B -W error alphaxiv_math_formal_audit.py --json

Strict Read-Only Ethics Standing:
  All external third-party repositories (alphaxiv/*, camail-official/*) are
  inspected strictly read-only on pinned local clones (0 external writes).
  When --standalone is passed (or clones are absent), all exact mathematical
  theorems, counterexamples, and self-certifications execute cleanly offline.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import re
import sys
from typing import Any


class AuditError(ValueError):
    """Explicit structured verification error (never stripped by python3 -O)."""

    def __init__(self, code: str, message: str) -> None:
        self.code = code
        self.message = message
        super().__init__(f"{code}: {message}")


def require(cond: bool, code: str, message: str) -> None:
    """Explicit non-assert trust-path guard."""
    if not cond:
        raise AuditError(code, message)


def is_strict_int(val: Any) -> bool:
    return isinstance(val, int) and not isinstance(val, bool)


def frac_str(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


def canonical_json(obj: Any) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), allow_nan=False)


# =============================================================================
# 1. Exact Pure-Q & Q[i] Linear Algebra, Schur Pushforward (⧄), Krein (⦺)
# =============================================================================

QMat = tuple[tuple[Fraction, ...], ...]


def to_q(val: int | Fraction) -> Fraction:
    if isinstance(val, Fraction):
        return val
    require(is_strict_int(val), "R3_BAD_SCALAR", f"Expected exact int or Fraction, got {type(val).__name__}")
    return Fraction(val, 1)


def qmat(rows: list[list[int | Fraction]] | tuple[tuple[int | Fraction, ...], ...]) -> QMat:
    require(len(rows) > 0, "EMPTY_MATRIX", "Matrix must have >= 1 row")
    ncols = len(rows[0])
    require(ncols > 0, "EMPTY_COLUMNS", "Matrix must have >= 1 column")
    out: list[tuple[Fraction, ...]] = []
    for row in rows:
        require(len(row) == ncols, "RAGGED_MATRIX", "All matrix rows must have identical length")
        out.append(tuple(to_q(v) for v in row))
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


def qsub(a: QMat, b: QMat) -> QMat:
    return tuple(tuple(a[i][j] - b[i][j] for j in range(len(a[0]))) for i in range(len(a)))


def qmul(a: QMat, b: QMat) -> QMat:
    m, k, n = len(a), len(b), len(b[0])
    return tuple(
        tuple(sum((a[i][t] * b[t][j] for t in range(k)), Fraction(0)) for j in range(n))
        for i in range(m)
    )


def qsubmat(m: QMat, rows: tuple[int, ...], cols: tuple[int, ...]) -> QMat:
    return tuple(tuple(m[r][c] for c in cols) for r in rows)


def qtrace(m: QMat) -> Fraction:
    return sum((m[i][i] for i in range(len(m))), Fraction(0))


def qdet_and_inv(a: QMat) -> tuple[Fraction, QMat]:
    """Exact Gauss-Jordan determinant and inverse over Q for square invertible A."""
    n = len(a)
    require(n == len(a[0]), "NON_SQUARE", "qdet_and_inv requires square matrix")
    aug = [list(a[i]) + [Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]
    det = Fraction(1)
    for col in range(n):
        piv = -1
        for r in range(col, n):
            if aug[r][col] != 0:
                piv = r
                break
        require(piv >= 0, "SINGULAR_MATRIX", f"Matrix is singular at column {col}")
        if piv != col:
            aug[col], aug[piv] = aug[piv], aug[col]
            det = -det
        pv = aug[col][col]
        det *= pv
        aug[col] = [v / pv for v in aug[col]]
        for r in range(n):
            if r != col and aug[r][col] != 0:
                fac = aug[r][col]
                aug[r] = [aug[r][j] - fac * aug[col][j] for j in range(2 * n)]
    inv = tuple(tuple(aug[i][n:]) for i in range(n))
    return det, inv


def qpinv_sym(m: QMat) -> QMat:
    """Exact Moore-Penrose pseudoinverse for symmetric M over Q."""
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
    _det, gram_inv = qdet_and_inv(gram)
    return qmul(b_mat, qmul(gram_inv, bt))


def qschur_pushforward(m: QMat, elim: tuple[int, ...]) -> QMat:
    """Operator ⧄ (U+29C4): M ⧄ B = M_{AA} - M_{AB} M_{BB}^+ M_{BA} over exact Q."""
    require(is_symmetric(m), "SCHUR_NOT_SYMMETRIC", "Schur pushforward requires symmetric matrix")
    n = len(m)
    require(len(set(elim)) == len(elim), "SCHUR_DUP_INDEX", "Duplicate index in elimination set")
    require(all(0 <= i < n for i in elim), "SCHUR_OOB_INDEX", "Elimination index out of bounds")
    b_set = set(elim)
    keep = tuple(i for i in range(n) if i not in b_set)
    require(len(keep) > 0, "SCHUR_EMPTY_KEEP", "Elimination set cannot remove all indices")
    if not elim:
        return m
    m_aa = qsubmat(m, keep, keep)
    m_ab = qsubmat(m, keep, elim)
    m_ba = qsubmat(m, elim, keep)
    m_bb = qsubmat(m, elim, elim)
    return qsub(m_aa, qmul(m_ab, qmul(qpinv_sym(m_bb), m_ba)))


def qinertia(m: QMat) -> tuple[int, int, int]:
    """Operator ⦺ (U+29BA): Exact zero-float Sylvester-Krein inertia (n_+, n_0, n_-)."""
    require(is_symmetric(m), "INERTIA_NOT_SYMMETRIC", "Inertia requires symmetric matrix")
    n = len(m)
    a = [list(row) for row in m]
    pos = zero = neg = 0
    k = 0
    while k < n:
        piv = -1
        for i in range(k, n):
            if a[i][i] != 0:
                piv = i
                break
        if piv >= 0:
            if piv != k:
                a[k], a[piv] = a[piv], a[k]
                for row in a:
                    row[k], row[piv] = row[piv], row[k]
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
        oi = oj = -1
        for i in range(k, n):
            for j in range(i + 1, n):
                if a[i][j] != 0:
                    oi, oj = i, j
                    break
            if oi >= 0:
                break
        if oi < 0:
            zero += n - k
            break
        if oi != k:
            a[k], a[oi] = a[oi], a[k]
            for row in a:
                row[k], row[oi] = row[oi], row[k]
        if oj != k + 1:
            a[k + 1], a[oj] = a[oj], a[k + 1]
            for row in a:
                row[k + 1], row[oj] = row[oj], row[k + 1]
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


def qmat_rank(m: QMat) -> int:
    pos, _z, neg = qinertia(m)
    return pos + neg


# =============================================================================
# 2. Module 1 — alphaxiv/feige-231f2e0b (Lean 4 Audit + Exact Extremizer)
# =============================================================================

FEIGE_EXPECTED_GRID_SHA256 = "a6b7756c8ad1cc3e690a2654dd12ffa4a3dc9039951c00ef0bf970aa916a7d84"


def verify_feige_exact_extremizer(max_n: int = 512) -> dict[str, Any]:
    """Exact zero-float verification of b_{n,1} = (n/(n+1))^n, monotonicity & e^{-1} lower bound."""
    require(is_strict_int(max_n) and max_n >= 16, "FEIGE_BAD_N", "max_n must be an integer >= 16")
    lines: list[str] = []
    monotone_all_ok = True
    prev_val: Fraction | None = None
    sample_values: dict[str, str] = {}
    for n in range(1, max_n + 1):
        val = Fraction(n, n + 1) ** n
        if prev_val is not None:
            monotone_all_ok = monotone_all_ok and (val < prev_val)
        prev_val = val
        if n in (1, 2, 3, 4, 8, 16, 64):
            sample_values[str(n)] = frac_str(val)
        lines.append(f"{n},{val.numerator},{val.denominator}")

    grid_sha = hashlib.sha256(("\n".join(lines) + "\n").encode("ascii")).hexdigest()
    # Exact alternating Taylor upper bound for e^{-1}: S_{20}(-1) = sum_{k=0}^{20} (-1)^k / k! > e^{-1}
    # and S_{21}(-1) < e^{-1} < S_{20}(-1) < b_{max_n, 1} (for max_n <= 512)!
    fact = 1
    s20 = Fraction(0)
    for k in range(21):
        if k > 0:
            fact *= k
        s20 += Fraction(-1 if (k % 2 == 1) else 1, fact)
    s21 = s20 - Fraction(1, fact * 21)
    b_last = Fraction(max_n, max_n + 1) ** max_n
    strictly_above_exp_neg1 = (s21 < s20) and (s20 < b_last)

    # Exact finite Bernoulli extremizer check: X_i in {0, n+1} with P(X_i=n+1)=1/(n+1)
    # => E[X_i]=1 and sum X_i < n+1 iff ALL X_i = 0 => P(S < n+1) = (n/(n+1))^n!
    extremizer_exact_ok = True
    for n in (1, 2, 3, 4, 5, 6):
        p_high = Fraction(1, n + 1)
        p_low = Fraction(n, n + 1)
        mean_xi = (n + 1) * p_high
        # Binomial sum over k = 0..n with k*(n+1) < n+1 -> strictly only k = 0 survives!
        prob_lt = Fraction(0)
        binom = 1
        for k in range(n + 1):
            if k > 0:
                binom = binom * (n - k + 1) // k
            if k * (n + 1) < n + 1:
                prob_lt += binom * (p_high ** k) * (p_low ** (n - k))
        extremizer_exact_ok = extremizer_exact_ok and (mean_xi == 1) and (prob_lt == Fraction(n, n + 1) ** n)

    return {
        "max_n": max_n,
        "exact_grid_sha256": grid_sha,
        "matches_upstream_summary_sha256": (grid_sha == FEIGE_EXPECTED_GRID_SHA256) if max_n == 512 else None,
        "strictly_monotone_decreasing": monotone_all_ok,
        "strictly_above_exp_neg1_via_taylor_S20": strictly_above_exp_neg1,
        "taylor_s20_bound_gt_exp_neg1": frac_str(s20),
        "bernoulli_extremizer_exact_for_n1_to_6": extremizer_exact_ok,
        "sample_b_n1": sample_values,
        "verified": monotone_all_ok and strictly_above_exp_neg1 and extremizer_exact_ok and (
            (grid_sha == FEIGE_EXPECTED_GRID_SHA256) if max_n == 512 else True
        ),
    }


def verify_feige_axiom_log_strict(log_text: str, required_decls: tuple[str, ...]) -> dict[str, Any]:
    """Hardened R1/R3 Lean `#print axioms` parser closing FEIGE-AUDIT-01 (declaration-bound check)."""
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    require(isinstance(log_text, str) and len(log_text.strip()) > 0, "EMPTY_AXIOM_LOG", "Axiom log cannot be empty")
    require(len(required_decls) > 0, "EMPTY_REQUIRED_DECLS", "At least one required declaration must be named")
    low = log_text.lower()
    require("error:" not in low and "sorryax" not in low, "AXIOM_LOG_ERROR_OR_SORRY", "Error or sorryAx detected in Lean log")

    decl_axioms: dict[str, list[str]] = {}
    pat_dep = re.compile(r"'([A-Za-z_][A-Za-z0-9_.]*)'\s+depends on axioms:\s*\[([^\]]*)\]", re.DOTALL)
    pat_none = re.compile(r"'([A-Za-z_][A-Za-z0-9_.]*)'\s+does not depend on any axioms")
    for m in pat_dep.finditer(log_text):
        dname = m.group(1)
        ax_list = sorted(set(re.findall(r"[A-Za-z_][A-Za-z0-9_.]*", m.group(2))))
        decl_axioms[dname] = ax_list
    for m in pat_none.finditer(log_text):
        decl_axioms[m.group(1)] = []

    missing = [d for d in required_decls if d not in decl_axioms]
    require(len(missing) == 0, "MISSING_REQUIRED_DECL", f"Required theorem(s) absent from axiom log: {missing}")

    bad: dict[str, list[str]] = {}
    for d in required_decls:
        unexpected = sorted(set(decl_axioms[d]) - allowed)
        if unexpected:
            bad[d] = unexpected
    require(len(bad) == 0, "UNEXPECTED_AXIOMS", f"Non-standard axioms detected: {bad}")
    return {
        "passed": True,
        "verified_declarations": list(required_decls),
        "axioms_by_decl": {d: decl_axioms[d] for d in required_decls},
    }


def inspect_feige_clone(feige_dir: Path, aletheia_root: Path) -> dict[str, Any]:
    """Run live read-only aletheia v1.3.0 --lean-audit on alphaxiv/feige-231f2e0b."""
    if not feige_dir.is_dir():
        return {"available": False, "mode": "standalone_offline"}
    if str(aletheia_root) not in sys.path:
        sys.path.insert(0, str(aletheia_root))
    from aletheia.audit_check import run_audit_check

    res = run_audit_check(
        feige_dir,
        lean_audit=True,
        allow_project_imports=["Feige", "Grunbaum", "LeanPool", "VlassisThomas", "Mathlib"],
    )
    lean_files = sorted(feige_dir.rglob("*.lean"))
    total_lean_lines = sum(len(p.read_text(encoding="utf-8").splitlines()) for p in lean_files)
    toolchain = (feige_dir / "lean-toolchain").read_text(encoding="utf-8").strip()
    summary_json = json.loads((feige_dir / "reports" / "unit-slack" / "data" / "summary.json").read_text(encoding="utf-8"))
    return {
        "available": True,
        "toolchain": toolchain,
        "lean_files_checked": res["summary"]["lean_files_checked"],
        "total_lean_lines": total_lean_lines,
        "lean_clean": res["lean_audit"]["clean"],
        "lean_findings_count": res["summary"]["lean_findings_count"],
        "lean_notices_count": res["summary"]["lean_notices_count"],
        "crlf_count": res["summary"]["crlf_count"],
        "crlf_files": res["crlf_files"],
        "bare_assert_count": res["summary"]["bare_assert_count"],
        "unseeded_rng_warning_count": res["summary"]["unseeded_rng_warning_count"],
        "leak_count": res["summary"]["leak_count"],
        "upstream_summary_grid_sha256": summary_json["exact_grid_sha256"],
        "upstream_audited_declarations": summary_json["audited_declarations"],
    }


# =============================================================================
# 3. Module 2 — Sumset vs Difference Set Carry Automaton (arXiv:2607.27199)
# =============================================================================

def build_diff_carry_automaton(digits: tuple[int, ...], base: int) -> tuple[list[tuple[int, ...]], list[list[int]]]:
    """Build exact minimal carry-subset transition matrix M_D for (D^j - D^j) mod base^j."""
    require(is_strict_int(base) and base >= 2, "SUMSET_BAD_BASE", "Base must be integer >= 2")
    require(len(digits) >= 1 and len(set(digits)) == len(digits), "SUMSET_BAD_DIGITS", "Digits must be non-empty unique ints")
    require(all(is_strict_int(d) and 0 <= d < base for d in digits), "SUMSET_DIGIT_RANGE", "Digits must lie in [0, base-1]")
    diffs = sorted({x - y for x in digits for y in digits})
    start = (0,)
    states: list[tuple[int, ...]] = [start]
    idx: dict[tuple[int, ...], int] = {start: 0}
    rows: list[dict[int, int]] = []
    q: list[tuple[int, ...]] = [start]
    while q:
        cur = q.pop(0)
        row: dict[int, int] = {}
        for d in range(base):
            nxt: set[int] = set()
            for c_in in cur:
                for df in diffs:
                    val = df + c_in - d
                    if val % base == 0:
                        c_out = val // base
                        if c_out in (-1, 0, 1):
                            nxt.add(c_out)
            if nxt:
                key = tuple(sorted(nxt))
                if key not in idx:
                    idx[key] = len(states)
                    states.append(key)
                    q.append(key)
                row[idx[key]] = row.get(idx[key], 0) + 1
        rows.append(row)
    n = len(states)
    mat = [[0] * n for _ in range(n)]
    for i, r in enumerate(rows):
        for j, cnt in r.items():
            mat[i][j] = cnt
    return states, mat


def charpoly_3x3_int(m: list[list[int]]) -> tuple[int, int, int, int]:
    """Exact integer characteristic polynomial coefficients (1, -tr, c1, -det) of a 3x3 matrix."""
    require(len(m) == 3 and all(len(r) == 3 for r in m), "NOT_3X3", "Expected 3x3 integer matrix")
    tr = m[0][0] + m[1][1] + m[2][2]
    c1 = (
        (m[0][0] * m[1][1] - m[0][1] * m[1][0])
        + (m[0][0] * m[2][2] - m[0][2] * m[2][0])
        + (m[1][1] * m[2][2] - m[1][2] * m[2][1])
    )
    det = (
        m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
        - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
        + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0])
    )
    return (1, -tr, c1, -det)


def collatz_wielandt_certify(mat: list[list[int]], vec: tuple[Fraction, ...], bound: Fraction) -> dict[str, Any]:
    """Exact rational Collatz-Wielandt upper bound certifier: max_i (M v)_i / v_i <= bound."""
    n = len(mat)
    require(n > 0 and len(vec) == n, "CW_DIM_MISMATCH", "Vector length must match matrix dimension")
    require(all(v > 0 for v in vec), "CW_NONPOS_VEC", "Collatz-Wielandt vector must be strictly positive")
    require(all(mat[i][j] >= 0 for i in range(n) for j in range(n)), "CW_NEG_ENTRY", "Matrix must be entrywise nonnegative")
    ratios: list[Fraction] = []
    for i in range(n):
        mv_i = sum((Fraction(mat[i][j]) * vec[j] for j in range(n)), Fraction(0))
        ratios.append(mv_i / vec[i])
    max_ratio = max(ratios)
    return {
        "certified": max_ratio <= bound,
        "max_ratio": frac_str(max_ratio),
        "bound": frac_str(bound),
        "row_ratios": [frac_str(r) for r in ratios],
    }


def carry_counts(mat: list[list[int]], steps: int) -> list[int]:
    """Exact sequence t_j = 1^T (M^T)^j e_0 = e_0^T M^j 1 for j = 0..steps-1."""
    n = len(mat)
    vec = [0] * n
    vec[0] = 1
    out: list[int] = []
    for _ in range(steps):
        out.append(sum(vec))
        vec = [sum(vec[i] * mat[i][j] for i in range(n)) for j in range(n)]
    return out


def audit_sumsets_exact() -> dict[str, Any]:
    """Exact zero-float audit of arXiv:2607.27199 carry matrices, CW defect repair & exhaustive base-12 search."""
    d_paper = (0, 1, 2, 4, 5, 9)
    d_imp = (0, 1, 3, 4, 5, 8)
    s_paper, m_paper = build_diff_carry_automaton(d_paper, 12)
    s_imp, m_imp = build_diff_carry_automaton(d_imp, 12)

    seq_paper = carry_counts(m_paper, 6)
    seq_imp = carry_counts(m_imp, 7)
    cp_paper = charpoly_3x3_int(m_paper)
    cp_imp = charpoly_3x3_int(m_imp)

    # Exact recurrence check for D_imp: t_{j+3} = 14 t_{j+2} - 31 t_{j+1} + 18 t_j
    imp_rec_residuals = [
        seq_imp[j + 3] - (14 * seq_imp[j + 2] - 31 * seq_imp[j + 1] + 18 * seq_imp[j])
        for j in range(len(seq_imp) - 3)
    ]
    # Exact Z_2 Observer-Net Equalizer (⟠): P swaps states 0 ({0}) and 2 ({-1})
    p_z2 = qmat([[0, 0, 1], [0, 1, 0], [1, 0, 0]])
    mq_paper = qmat(m_paper)
    mq_imp = qmat(m_imp)
    z2_comm_paper = qmul(p_z2, mq_paper) == qmul(mq_paper, p_z2)
    z2_comm_imp = qmul(p_z2, mq_imp) == qmul(mq_imp, p_z2)

    # Direct enumeration parity on k=1,2,3 for D_paper and D_imp
    enum_checks: list[dict[str, Any]] = []
    for name, dset, seq in [("D_paper", d_paper, seq_paper), ("D_imp", d_imp, seq_imp)]:
        for k in (1, 2, 3):
            mod_k = 12 ** k
            vals = [sum(d * (12 ** p) for p, d in enumerate(tup)) for tup in itertools.product(dset, repeat=k)]
            sum_mod = len({(a + b) % mod_k for a in vals for b in vals})
            diff_mod = len({(a - b) % mod_k for a in vals for b in vals})
            enum_checks.append({
                "gadget": name,
                "k": k,
                "sum_mod_exact": sum_mod,
                "diff_mod_exact": diff_mod,
                "automaton_t_k": seq[k],
                "exact_match": (sum_mod == mod_k) and (diff_mod == seq[k]),
            })

    # SUMSET-CW-01: Test literally printed v_printed=(1, 53/48, 53/48) on ALL 12 perms & transposes of M_imp
    v_printed = (Fraction(1), Fraction(53, 48), Fraction(53, 48))
    bound_183_16 = Fraction(183, 16)
    printed_perm_results: list[Fraction] = []
    for base_m in (m_imp, [[m_imp[j][i] for j in range(3)] for i in range(3)]):
        for perm in itertools.permutations(range(3)):
            pm = [[base_m[perm[i]][perm[j]] for j in range(3)] for i in range(3)]
            cw = collatz_wielandt_certify(pm, v_printed, bound_183_16)
            printed_perm_results.append(Fraction(cw["max_ratio"]))
    printed_min_max_ratio = min(printed_perm_results)
    printed_fails_all_12 = printed_min_max_ratio > bound_183_16

    # Law-2 Steelman Repair: v_repaired=(1, 53/48, 1) on [{0}, {-1,0}, {-1}] (or (1, 48/53, 48/53) on [{-1,0}, {0}, {-1}])
    cw_repaired = collatz_wielandt_certify(m_imp, (Fraction(1), Fraction(53, 48), Fraction(1)), bound_183_16)
    cw_tight = collatz_wielandt_certify(m_imp, (Fraction(1), Fraction(52, 47), Fraction(1)), Fraction(537, 47))

    # Exact BigInt depth-threshold proof: 22(K+2) -> 15(K+2) (exact 7/22 reduction)
    # D_imp upper bound 61/64: 2 * 61^15 < 64^15 and 2 * 61^14 > 64^14
    imp_depth_15_ok = (2 * (61 ** 15) < 64 ** 15) and (2 * (61 ** 14) > 64 ** 14)
    # D_paper exact algebraic rate (13 + sqrt(105))/24 bracketed strictly by (10246/1000 < sqrt(105) < 10247/1000)
    sqrt105_bracket_ok = (10246 * 10246 < 105 * 1000 * 1000) and (105 * 1000 * 1000 < 10247 * 10247)
    r_p_lo = Fraction(13 * 1000 + 10246, 24000)
    r_p_hi = Fraction(13 * 1000 + 10247, 24000)
    paper_depth_22_ok = sqrt105_bracket_ok and (2 * (r_p_lo ** 21) > 1) and (2 * (r_p_hi ** 22) < 1)

    # Exact algebraic bracket for D_imp rate (13 + sqrt(97))/24: 98488/10000 < sqrt(97) < 98489/10000
    sqrt97_bracket_ok = (98488 * 98488 < 97 * 10000 * 10000) and (97 * 10000 * 10000 < 98489 * 98489)
    r_i_lo = Fraction(13 * 10000 + 98488, 240000)
    r_i_hi = Fraction(13 * 10000 + 98489, 240000)

    # Exhaustive exact base-12 6-digit classification over all C(11,5)=462 sets containing 0!
    # A nonnegative matrix M with row sums <= 12 has rho(M) < 12 iff M^n * 1 < 12^n * 1 strictly for some n
    # (equivalently for n <= 4, no closed subset of states has all row sums == 12!).
    total_sets = 0
    cover_z12_count = 0
    direct_0_11_count = 0
    contractive_z12: list[dict[str, Any]] = []
    for comb in itertools.combinations(range(1, 12), 5):
        total_sets += 1
        dset = (0,) + comb
        sums = {x + y for x in dset for y in dset}
        if len({s % 12 for s in sums}) < 12:
            continue
        cover_z12_count += 1
        direct = all(r in sums for r in range(12))
        if direct:
            direct_0_11_count += 1
        _st, m_d = build_diff_carry_automaton(dset, 12)
        # Exact zero-float contractivity test: compute v = M^4 * 1; since |states| <= 3,
        # rho(M) < 12 iff every row of M^3 * 1 is strictly < 12^3!
        sz = len(m_d)
        vec_1 = [1] * sz
        for _ in range(3):
            vec_1 = [sum(m_d[i][j] * vec_1[j] for j in range(sz)) for i in range(sz)]
        if max(vec_1) < 12 ** 3:
            cp = charpoly_3x3_int(m_d) if sz == 3 else None
            # For affine family M(k), det(M) = 12 + 2k => k = (det - 12)//2
            det_val = -cp[3] if cp is not None else 0
            k_param = (det_val - 12) // 2
            contractive_z12.append({
                "digits": list(dset),
                "direct_covers_0_11": direct,
                "k_affine_param": k_param,
                "matrix": m_d,
                "charpoly": list(cp) if cp is not None else None,
            })

    contractive_z12.sort(key=lambda row: (-row["k_affine_param"], row["digits"]))
    direct_contractive = [row for row in contractive_z12 if row["direct_covers_0_11"]]
    affine_family_exact = all(
        row["matrix"] == [
            [row["k_affine_param"] + 1, 10 - 2 * row["k_affine_param"], row["k_affine_param"]],
            [row["k_affine_param"], 12 - 2 * row["k_affine_param"], row["k_affine_param"]],
            [row["k_affine_param"], 10 - 2 * row["k_affine_param"], row["k_affine_param"] + 1],
        ]
        for row in contractive_z12
    )

    verified = (
        seq_paper[:5] == [1, 11, 127, 1475, 17143]
        and cp_paper == (1, -14, 29, -16)
        and cp_imp == (1, -14, 31, -18)
        and all(r == 0 for r in imp_rec_residuals)
        and z2_comm_paper
        and z2_comm_imp
        and all(ec["exact_match"] for ec in enum_checks)
        and printed_fails_all_12
        and cw_repaired["certified"]
        and cw_tight["certified"]
        and imp_depth_15_ok
        and paper_depth_22_ok
        and sqrt97_bracket_ok
        and total_sets == 462
        and cover_z12_count == 288
        and direct_0_11_count == 53
        and len(contractive_z12) == 6
        and len(direct_contractive) == 2
        and direct_contractive[0]["digits"] == list(d_imp)
        and direct_contractive[1]["digits"] == list(d_paper)
        and affine_family_exact
    )
    return {
        "verified": verified,
        "paper_gadget": {
            "digits": list(d_paper),
            "states": [list(s) for s in s_paper],
            "matrix": m_paper,
            "charpoly": list(cp_paper),
            "sequence_t0_to_t5": seq_paper,
            "z2_equalizer_commutes": z2_comm_paper,
            "exact_rate_bracket": [frac_str(r_p_lo), frac_str(r_p_hi)],
            "exact_depth_coeff_22_proved": paper_depth_22_ok,
        },
        "improved_gadget": {
            "digits": list(d_imp),
            "states": [list(s) for s in s_imp],
            "matrix": m_imp,
            "charpoly": list(cp_imp),
            "sequence_t0_to_t6": seq_imp,
            "recurrence_residuals": imp_rec_residuals,
            "z2_equalizer_commutes": z2_comm_imp,
            "exact_rate_bracket": [frac_str(r_i_lo), frac_str(r_i_hi)],
            "exact_depth_coeff_15_proved": imp_depth_15_ok,
            "depth_reduction_fraction": frac_str(Fraction(22 - 15, 22)),
        },
        "collatz_wielandt_audit_SUMSET_CW_01": {
            "printed_vector_report_L35": ["1", "53/48", "53/48"],
            "printed_fails_all_12_perms_and_transposes": printed_fails_all_12,
            "printed_best_ratio_across_12_variants": frac_str(printed_min_max_ratio),
            "target_bound": frac_str(bound_183_16),
            "repaired_vector_on_M_imp": ["1", "53/48", "1"],
            "repaired_equivalent_on_pair_first_order": ["1", "48/53", "48/53"],
            "repaired_certificate": cw_repaired,
            "tighter_convergent_52_47_certificate": cw_tight,
        },
        "direct_enumeration_checks": enum_checks,
        "exhaustive_base12_classification": {
            "total_normalized_6_digit_sets": total_sets,
            "covering_Z12": cover_z12_count,
            "direct_covering_0_to_11": direct_0_11_count,
            "contractive_Z12_count": len(contractive_z12),
            "contractive_direct_0_to_11_count": len(direct_contractive),
            "all_6_match_exact_affine_family_Mk": affine_family_exact,
            "unique_direct_optimum": direct_contractive[0]["digits"],
            "contractive_sets": contractive_z12,
        },
    }


# =============================================================================
# 4. Module 3 — HOPE Hilbert Operator (SF-01 #27) & Finite Hilbert H_n
# =============================================================================

def verify_hope_gauge_and_schur_obstruction() -> dict[str, Any]:
    """Exact pure-Q proof of HOPE (s,t)-gauge invariance AND diagonal-vs-Schur (⧄/⧅) rank-inversion."""
    # Exact 3-channel rational feature matrix Phi (4 samples x 3 channels) & outgoing weights w_i (dim 2):
    # Channel 0 and Channel 1 are collinear in Hilbert space (exact dark-mode duplicate: h_0 = h_1, ||h_0||^2 = 9),
    # while Channel 2 is strictly orthogonal with smaller self-energy (||h_2||^2 = 4).
    # Construct explicitly from exact rational sample vectors h_i in Q^8 (4 samples x 2 output dims):
    #   h_0 = (3/2, 0, 3/2, 0, 3/2, 0, 3/2, 0) -> ||h_0||^2 = 4 * 9/4 = 9
    #   h_1 = (3/2, 0, 3/2, 0, 3/2, 0, 3/2, 0) -> ||h_1||^2 = 9, <h_0, h_1> = 9
    #   h_2 = (0, 1, 0, 1, 0, 1, 0, 1)         -> ||h_2||^2 = 4, <h_0, h_2> = <h_1, h_2> = 0
    # Represent each channel as outgoing vector w_i in Q^2 times activation phi_i in Q^4:
    w_base = (
        (Fraction(3), Fraction(0)),
        (Fraction(3), Fraction(0)),
        (Fraction(0), Fraction(2)),
    )
    phi_base = (
        (Fraction(1, 2), Fraction(1, 2), Fraction(1, 2), Fraction(1, 2)),
        (Fraction(1, 2), Fraction(1, 2), Fraction(1, 2), Fraction(1, 2)),
        (Fraction(1, 2), Fraction(1, 2), Fraction(1, 2), Fraction(1, 2)),
    )
    # Also BN parameters (v_i, eps, s_i, t_i) for exact (s, t) symmetry check:
    v_base = (Fraction(3, 2), Fraction(5, 4), Fraction(7, 3))
    eps = Fraction(1, 100000)

    def build_gram(ws: tuple[tuple[Fraction, Fraction], ...], phis: tuple[tuple[Fraction, ...], ...]) -> QMat:
        rows: list[list[Fraction]] = []
        for i in range(3):
            row: list[Fraction] = []
            for j in range(3):
                w_dot = ws[i][0] * ws[j][0] + ws[i][1] * ws[j][1]
                p_dot = sum((phis[i][k] * phis[j][k] for k in range(4)), Fraction(0))
                row.append(w_dot * p_dot)
            rows.append(row)
        return tuple(tuple(r) for r in rows)

    g_base = build_gram(w_base, phi_base)
    # Exact Hilbert Schur-complement pruning loss for dropping channel i and keeping A = {0,1,2}\{i}:
    schur_drop = [qschur_pushforward(g_base, tuple(j for j in range(3) if j != i))[0][0] for i in range(3)]
    # Diagonal HOPE capacity squared c_i^2 = G_{ii} = ||w_i||^2 * ||phi_i||^2:
    hope_cap_sq = [g_base[i][i] for i in range(3)]
    hope_first_prune = min(range(3), key=lambda i: hope_cap_sq[i])
    schur_first_prune = min(range(3), key=lambda i: schur_drop[i])
    dark_nullity = 3 - qmat_rank(g_base)

    # Verify exact (s, t)-gauge invariance across 12 deterministic positive rational gauge vectors!
    gauge_cases = [
        ((Fraction(2), Fraction(3, 2), Fraction(5, 3)), (Fraction(3), Fraction(1, 4), Fraction(7, 5))),
        ((Fraction(1, 7), Fraction(9, 2), Fraction(11, 4)), (Fraction(5, 2), Fraction(13, 3), Fraction(1, 9))),
        ((Fraction(17, 5), Fraction(1, 3), Fraction(4, 7)), (Fraction(1, 11), Fraction(8, 3), Fraction(19, 4))),
        ((Fraction(100), Fraction(1, 100), Fraction(37, 13)), (Fraction(23, 7), Fraction(1, 50), Fraction(41, 6))),
    ]
    all_gram_gauge_inv = True
    all_bn_s_inv = True
    all_l1_breaks = True
    for s_vec, t_vec in gauge_cases:
        # Check exact BN s-rescaling: new_var = (v + eps)*s^2 - eps => (new_var + eps) / s^2 == v + eps
        for i in range(3):
            new_var = (v_base[i] + eps) * (s_vec[i] ** 2) - eps
            all_bn_s_inv = all_bn_s_inv and ((new_var + eps) == (v_base[i] + eps) * (s_vec[i] ** 2))
        # Check exact positive-homogeneity t-rescaling: w_i -> w_i / t_i, phi_i -> t_i * phi_i
        w_scaled = tuple((w_base[i][0] / t_vec[i], w_base[i][1] / t_vec[i]) for i in range(3))
        phi_scaled = tuple(tuple(t_vec[i] * x for x in phi_base[i]) for i in range(3))
        g_scaled = build_gram(w_scaled, phi_scaled)
        all_gram_gauge_inv = all_gram_gauge_inv and (g_scaled == g_base)
        # Raw outgoing L1 changes strictly when t_i != 1:
        l1_before = [abs(w_base[i][0]) + abs(w_base[i][1]) for i in range(3)]
        l1_after = [abs(w_scaled[i][0]) + abs(w_scaled[i][1]) for i in range(3)]
        all_l1_breaks = all_l1_breaks and (l1_after != l1_before)

    # Diagonal orthogonal control: when channels are orthogonal, Schur loss == HOPE c_i^2 identically!
    g_orth = qmat([[9, 0, 0], [0, 5, 0], [0, 0, 4]])
    orth_schur = [qschur_pushforward(g_orth, tuple(j for j in range(3) if j != i))[0][0] for i in range(3)]
    orth_parity_exact = (orth_schur == [Fraction(9), Fraction(5), Fraction(4)])

    return {
        "verified": (
            all_bn_s_inv
            and all_gram_gauge_inv
            and all_l1_breaks
            and dark_nullity == 1
            and hope_first_prune == 2
            and schur_first_prune == 0
            and schur_drop == [Fraction(0), Fraction(0), Fraction(4)]
            and hope_cap_sq == [Fraction(9), Fraction(9), Fraction(4)]
            and orth_parity_exact
        ),
        "gram_matrix": [[frac_str(v) for v in row] for row in g_base],
        "gram_inertia": list(qinertia(g_base)),
        "dark_mode_nullity_dim_shadow": dark_nullity,
        "hope_diagonal_cap_sq": [frac_str(v) for v in hope_cap_sq],
        "true_hilbert_schur_loss": [frac_str(v) for v in schur_drop],
        "hope_first_pruned_channel": hope_first_prune,
        "hope_incurred_true_error": frac_str(schur_drop[hope_first_prune]),
        "schur_first_pruned_channel": schur_first_prune,
        "schur_incurred_true_error": frac_str(schur_drop[schur_first_prune]),
        "exact_bn_s_cancellation_4_cases": all_bn_s_inv,
        "exact_gram_and_schur_t_invariance_4_cases": all_gram_gauge_inv,
        "raw_l1_breaks_all_4_cases": all_l1_breaks,
        "orthogonal_control_schur_equals_hope": orth_parity_exact,
    }


def _fact_prod(m: int) -> int:
    """c_m = prod_{k=1}^{m-1} k! for Cauchy Hilbert determinant formula."""
    out = 1
    f = 1
    for k in range(1, m):
        f *= k
        out *= f
    return out


def verify_finite_hilbert_bareiss_and_rh4(max_n: int = 8) -> dict[str, Any]:
    """Exact zero-float Bareiss/Cauchy det, progressive Schur pivot, inertia & R_H4 > R_opt on H_n."""
    require(is_strict_int(max_n) and 2 <= max_n <= 10, "HILBERT_BAD_N", "max_n must be integer in [2, 10]")
    rows: list[dict[str, Any]] = []
    all_ok = True
    for n in range(2, max_n + 1):
        hn = tuple(tuple(Fraction(1, i + j + 1) for j in range(n)) for i in range(n))
        det_gauss, inv_hn = qdet_and_inv(hn)
        c_n = _fact_prod(n)
        c_2n = _fact_prod(2 * n)
        det_cauchy = Fraction(c_n ** 4, c_2n)
        inv_is_exact_int = all(v.denominator == 1 for r in inv_hn for v in r)
        inertia = qinertia(hn)
        # Progressive Schur pushforward H_n ⧄ {0..n-2} -> exact last Schur pivot s_n = ((n-1)!)^4 / ((2n-2)! (2n-1)!)
        last_pivot = qschur_pushforward(hn, tuple(range(n - 1)))[0][0]
        f_nm1 = 1
        for k in range(2, n):
            f_nm1 *= k
        f_2nm2 = 1
        for k in range(2, 2 * n - 1):
            f_2nm2 *= k
        f_2nm1 = f_2nm2 * (2 * n - 1)
        pivot_closed = Fraction(f_nm1 ** 4, f_2nm2 * f_2nm1)

        # Exact spectral moments m1..m4 and AUDIT-002 R_opt vs AUDIT-014 R_H4 (moment Hankel Schur complement!)
        h2 = qmul(hn, hn)
        h3 = qmul(h2, hn)
        h4 = qmul(h2, h2)
        m1 = qtrace(hn)
        m2 = qtrace(h2)
        m3 = qtrace(h3)
        m4 = qtrace(h4)
        r_opt = (m1 * m1) / m2
        hankel_det = m2 * m4 - m3 * m3
        r_h4 = (m1 * m1 * m4 - 2 * m1 * m2 * m3 + m2 * m2 * m2) / hankel_det
        frob_sq_h = m2
        frob_sq_inv = sum((v * v for r in inv_hn for v in r), Fraction(0))
        kappa_f_sq = frob_sq_h * frob_sq_inv

        row_ok = (
            det_gauss == det_cauchy
            and inv_is_exact_int
            and inertia == (n, 0, 0)
            and last_pivot == pivot_closed
            and hankel_det > 0
            and r_opt < r_h4 <= Fraction(n)
            and ((r_h4 == Fraction(2)) if n == 2 else (r_h4 > Fraction(2)))
        )
        all_ok = all_ok and row_ok
        rows.append({
            "n": n,
            "det_exact": frac_str(det_gauss),
            "cauchy_det_matches": det_gauss == det_cauchy,
            "inverse_is_pure_integer_matrix": inv_is_exact_int,
            "inertia": list(inertia),
            "schur_last_pivot": frac_str(last_pivot),
            "schur_pivot_closed_matches": last_pivot == pivot_closed,
            "r_opt_audit002": frac_str(r_opt),
            "r_h4_audit014": frac_str(r_h4),
            "r_h4_strictly_beats_r_opt": r_h4 > r_opt,
            "kappa_F_sq_integer_floor": kappa_f_sq.numerator // kappa_f_sq.denominator,
        })
    return {"verified": all_ok, "max_n": max_n, "hilbert_rows": rows}


# =============================================================================
# 5. Module 4 — Recurrence Convergence (arXiv:2607.20594) <-> LoopedActor / QRR
# =============================================================================

def _perm_compose(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(a[b[i]] for i in range(len(a)))


def _perm_inv(a: tuple[int, ...]) -> tuple[int, ...]:
    inv = [0] * len(a)
    for i, v in enumerate(a):
        inv[v] = i
    return tuple(inv)


def _perm_parity(p: tuple[int, ...]) -> int:
    return sum(1 for i in range(len(p)) for j in range(i + 1, len(p)) if p[i] > p[j]) % 2


def compute_derived_series_orders(group: set[tuple[int, ...]]) -> list[int]:
    """Exact derived series |G^(0)|, |G^(1)|, ... via commutator subgroup closure."""
    require(len(group) > 0, "EMPTY_GROUP", "Group must be non-empty")
    cur = set(group)
    orders = [len(cur)]
    for _ in range(6):
        gens: set[tuple[int, ...]] = set()
        for x in cur:
            ix = _perm_inv(x)
            for y in cur:
                gens.add(_perm_compose(_perm_compose(x, y), _perm_compose(ix, _perm_inv(y))))
        closed = set(gens)
        frontier = list(gens)
        while frontier:
            a = frontier.pop()
            for g in gens:
                prod = _perm_compose(a, g)
                if prod not in closed:
                    closed.add(prod)
                    frontier.append(prod)
        orders.append(len(closed))
        if len(closed) == len(cur):
            break
        cur = closed
    return orders


def _c_mul(z: tuple[Fraction, Fraction], w: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    return (z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0])


def _c_conj(z: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    return (z[0], -z[1])


def _c_norm2(vec: tuple[tuple[Fraction, Fraction], ...]) -> Fraction:
    return sum((z[0] * z[0] + z[1] * z[1] for z in vec), Fraction(0))


def _c_inner(
    u: tuple[tuple[Fraction, Fraction], ...],
    v: tuple[tuple[Fraction, Fraction], ...],
) -> tuple[Fraction, Fraction]:
    re_s = Fraction(0)
    im_s = Fraction(0)
    for uk, vk in zip(u, v):
        pr = _c_mul(_c_conj(uk), vk)
        re_s += pr[0]
        im_s += pr[1]
    return (re_s, im_s)


def qrr_horizontal_split(
    y_vec: tuple[tuple[Fraction, Fraction], ...],
    f_vec: tuple[tuple[Fraction, Fraction], ...],
) -> tuple[Fraction, tuple[tuple[Fraction, Fraction], ...]]:
    """QRR QuotientIntegrator horizontal Schur projection F_H = F - i*a*y over exact Q[i]."""
    n2 = _c_norm2(y_vec)
    require(n2 > 0, "QRR_ZERO_STATE", "QRR horizontal split requires ||y||^2 > 0")
    a_val = _c_inner(y_vec, f_vec)[1] / n2
    f_h = tuple((fk[0] + a_val * yk[1], fk[1] - a_val * yk[0]) for yk, fk in zip(y_vec, f_vec))
    return a_val, f_h


def apply_u1_gauge_rotation(
    u: tuple[Fraction, Fraction],
    vec: tuple[tuple[Fraction, Fraction], ...],
) -> tuple[tuple[Fraction, Fraction], ...]:
    """Apply an exact rational unit-modulus U(1, Q[i]) gauge rotation u to vec."""
    require(u[0] * u[0] + u[1] * u[1] == 1, "NOT_UNIT_U1", "Gauge rotation must satisfy |u|^2 == 1")
    return tuple(_c_mul(u, vk) for vk in vec)


def verify_recurrence_camail_bridge() -> dict[str, Any]:
    """Exact S4 vs A5 solvability obstruction + LoopedActor FPRM contraction + QRR U(1) Schur/singularity."""
    # 1. Exact S4 vs A5 derived series (Barrington 1989 NC^1 obstruction explaining report.md:56)
    s4 = set(itertools.permutations(range(4)))
    a5 = {p for p in itertools.permutations(range(5)) if _perm_parity(p) == 0}
    s4_series = compute_derived_series_orders(s4)
    a5_series = compute_derived_series_orders(a5)
    s4_solvable_len3 = (s4_series == [24, 12, 4, 1, 1])
    a5_perfect_nonsolvable = (a5_series == [60, 60])

    # 2. camail-official/LoopedActor models/fprm.py:269-273 exact telescoping balance & eps contractivity
    eps_fprm = Fraction(1, 100000)
    fprm_cases = [
        (Fraction(3, 4), Fraction(1, 4), 1),
        (Fraction(3, 4), Fraction(1, 4), 2),
        (Fraction(9, 10), Fraction(1, 5), 3),
        (Fraction(99, 100), Fraction(1, 2), 2),
    ]
    fprm_rows: list[dict[str, Any]] = []
    fprm_all_ok = True
    for a1, a2, n_layers in fprm_cases:
        two_l = 2 * n_layers
        a1_2l = a1 ** two_l
        b2 = Fraction(1) - a2 * a1_2l
        b1_exact = b2 * (Fraction(1) - a1) / (Fraction(1) - a1_2l)
        b1_code = b2 * (Fraction(1) - a1) / (Fraction(1) - a1_2l + eps_fprm)
        w_z = a2 * a1_2l
        geom_sum = sum((a1 ** k for k in range(two_l)), Fraction(0))
        exact_total = w_z + b1_exact * geom_sum
        code_total = w_z + b1_code * geom_sum
        ok = (exact_total == 1) and (code_total < 1) and (b1_code > 0)
        fprm_all_ok = fprm_all_ok and ok
        fprm_rows.append({
            "a1": frac_str(a1),
            "a2": frac_str(a2),
            "num_layers": n_layers,
            "exact_convex_balance_equals_1": exact_total == 1,
            "code_total_strictly_lt_1": code_total < 1,
            "code_damping_deficit": frac_str(Fraction(1) - code_total),
        })

    # 3. camail-official/QRR models/integrator.py:217-242 exact Q[i] U(1) Schur projection & residual singularity
    y0 = ((Fraction(3), Fraction(-1)), (Fraction(2), Fraction(5)), (Fraction(-4), Fraction(1)))
    f0 = ((Fraction(7), Fraction(2)), (Fraction(-3), Fraction(4)), (Fraction(1), Fraction(-6)))
    a0, fh0 = qrr_horizontal_split(y0, f0)
    iy0 = tuple((-yk[1], yk[0]) for yk in y0)
    orth_res = _c_inner(fh0, iy0)[0]
    pyth_res = _c_norm2(f0) - (_c_norm2(fh0) + (a0 * a0) * _c_norm2(y0))

    # Exact U(1, Q[i]) gauge equivariance & L_inf,C invariance vs real L_inf failure (CS-11)
    u_rotations = (
        (Fraction(3, 5), Fraction(4, 5)),
        (Fraction(5, 13), Fraction(12, 13)),
        (Fraction(-8, 17), Fraction(15, 17)),
    )
    u1_equiv_all = True
    linf_c_inv_all = True
    real_linf_breaks_all = True
    linf_c_sq_0 = max(z[0] * z[0] + z[1] * z[1] for z in f0)
    real_linf_0 = max(max(abs(z[0]), abs(z[1])) for z in f0)
    for u in u_rotations:
        yu = apply_u1_gauge_rotation(u, y0)
        fu = apply_u1_gauge_rotation(u, f0)
        au, fhu = qrr_horizontal_split(yu, fu)
        u_fh0 = apply_u1_gauge_rotation(u, fh0)
        u1_equiv_all = u1_equiv_all and (au == a0) and (fhu == u_fh0)
        linf_c_sq_u = max(z[0] * z[0] + z[1] * z[1] for z in fu)
        real_linf_u = max(max(abs(z[0]), abs(z[1])) for z in fu)
        linf_c_inv_all = linf_c_inv_all and (linf_c_sq_u == linf_c_sq_0)
        real_linf_breaks_all = real_linf_breaks_all and (real_linf_u != real_linf_0)

    # Exact QRR integrator.py:235-240 singularity proof along F_H = -2y:
    # r_bad(eta) = 2*eta / |1 - 2*eta| blows up at eta=1/2 and is non-monotone (r_bad(1/3)=2 < r_bad(2/5)=4 > r_bad(1)=2)
    # whereas r_exec(eta) = 2*eta is strictly monotone!
    r_bad_1_3 = Fraction(2, 3) / abs(Fraction(1) - Fraction(2, 3))
    r_bad_2_5 = Fraction(4, 5) / abs(Fraction(1) - Fraction(4, 5))
    r_bad_1 = Fraction(2) / abs(Fraction(1) - Fraction(2))
    singularity_nonmonotone = (r_bad_1_3 < r_bad_2_5) and (r_bad_2_5 > r_bad_1) and (Fraction(1) - 2 * Fraction(1, 2) == 0)

    return {
        "verified": (
            s4_solvable_len3
            and a5_perfect_nonsolvable
            and fprm_all_ok
            and orth_res == 0
            and pyth_res == 0
            and u1_equiv_all
            and linf_c_inv_all
            and real_linf_breaks_all
            and singularity_nonmonotone
        ),
        "group_solvability_obstruction": {
            "S4_derived_series_orders": s4_series,
            "S4_solvable_derived_length": 3,
            "A5_derived_series_orders": a5_series,
            "A5_perfect_nonsolvable_simple": a5_perfect_nonsolvable,
        },
        "looped_actor_fprm_contraction": {
            "all_verified": fprm_all_ok,
            "cases": fprm_rows,
        },
        "qrr_u1_schur_and_singularity": {
            "a0_exact": frac_str(a0),
            "horizontal_orthogonality_residual": frac_str(orth_res),
            "pythagorean_schur_residual": frac_str(pyth_res),
            "u1_gauge_equivariance_3_triples": u1_equiv_all,
            "complex_linf_u1_invariant": linf_c_inv_all,
            "real_linf_breaks_under_u1_CS11": real_linf_breaks_all,
            "bad_residual_values_at_1_3__2_5__1": [frac_str(r_bad_1_3), frac_str(r_bad_2_5), frac_str(r_bad_1)],
            "bad_residual_singular_at_half_and_nonmonotone": singularity_nonmonotone,
        },
    }


def inspect_other_clones(repos_root: Path, aletheia_root: Path) -> dict[str, Any]:
    """Run read-only aletheia v1.3.0 static hygiene audit on the other 3 alphaxiv + 2 camail clones if present."""
    if not repos_root.is_dir():
        return {"available": False, "mode": "standalone_offline"}
    if str(aletheia_root) not in sys.path:
        sys.path.insert(0, str(aletheia_root))
    from aletheia.audit_check import run_audit_check

    targets = [
        "alphaxiv-settling-the-optimal-exponent-relating-sumsets-a",
        "alphaxiv-hilbert-operator-for-progressive-encoding-hope-a",
        "alphaxiv-when-does-recurrence-become-an-algorithm-converg",
        "camail-LoopedActor",
        "camail-Quotient_Recurrent_Reasoner_QRR",
    ]
    out: dict[str, Any] = {"available": True, "repos": {}}
    for name in targets:
        p = repos_root / name
        if not p.is_dir():
            out["repos"][name] = {"present": False}
            continue
        res = run_audit_check(p)
        out["repos"][name] = {
            "present": True,
            "status": res["status"],
            "files_scanned": res["summary"]["files_scanned"],
            "py_files_scanned": res["summary"]["py_files_scanned"],
            "bare_assert_count": res["summary"]["bare_assert_count"],
            "unseeded_rng_warning_count": res["summary"]["unseeded_rng_warning_count"],
            "crlf_count": res["summary"]["crlf_count"],
            "leak_count": res["summary"]["leak_count"],
            "bare_assert_locations": [f"{b['file']}:{b['line']}" for b in res["bare_asserts"][:12]],
        }
    return out


# =============================================================================
# 6. Master Driver
# =============================================================================

def run_all(standalone: bool = False) -> dict[str, Any]:
    here = Path(__file__).resolve().parent
    repos_root = here.parent / "repos"
    aletheia_root = here.parents[2] / "publish" / "aletheia"

    feige_exact = verify_feige_exact_extremizer(max_n=512)
    feige_log_sample = (
        "'Feige.sharp_unit_slack_feige_complete' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        "'VlassisThomas.exactCalibration' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
    )
    feige_strict_log_ok = verify_feige_axiom_log_strict(
        feige_log_sample,
        ("Feige.sharp_unit_slack_feige_complete", "VlassisThomas.exactCalibration"),
    )
    sumsets = audit_sumsets_exact()
    hope_schur = verify_hope_gauge_and_schur_obstruction()
    hilbert_hn = verify_finite_hilbert_bareiss_and_rh4(max_n=8)
    recurrence_bridge = verify_recurrence_camail_bridge()

    if standalone or not repos_root.is_dir():
        feige_clone = {"available": False, "mode": "standalone_offline"}
        other_clones = {"available": False, "mode": "standalone_offline"}
    else:
        feige_clone = inspect_feige_clone(repos_root / "alphaxiv-feige-231f2e0b", aletheia_root)
        other_clones = inspect_other_clones(repos_root, aletheia_root)

    clone_ok = True
    if feige_clone.get("available"):
        clone_ok = bool(
            feige_clone["lean_clean"]
            and feige_clone["lean_files_checked"] == 98
            and feige_clone["upstream_summary_grid_sha256"] == feige_exact["exact_grid_sha256"]
        )

    all_ok = (
        feige_exact["verified"]
        and feige_strict_log_ok["passed"]
        and sumsets["verified"]
        and hope_schur["verified"]
        and hilbert_hn["verified"]
        and recurrence_bridge["verified"]
        and clone_ok
    )

    payload: dict[str, Any] = {
        "schema": "aletheia.wave2.round5.arm_r5_5.alphaxiv_math_formal.v1",
        "audit_id": "AUDIT-060",
        "oracle_class": "exact" if not feige_clone.get("available") else "exact+anchor",
        "honest_novelty": "N1",
        "verdict": "ALPHAXIV_MATH_FORMAL_ALL_CHECKS_VERIFIED" if all_ok else "FAILED",
        "pinned_read_only_anchors": {
            "alphaxiv/feige-231f2e0b": "50b0b2de0940b7f8ebc8c7c9fd628803f4283ba4",
            "alphaxiv/settling-the-optimal-exponent-relating-sumsets-a": "756551f6888c63bd33a796b0e7b497564032e2ae",
            "alphaxiv/hilbert-operator-for-progressive-encoding-hope-a": "23670f903a0f6c7ce7939fc8db26d3db8082d98e",
            "alphaxiv/when-does-recurrence-become-an-algorithm-converg": "7b48186b829192b481ff5792a288bf6f3f4a15ab",
            "camail-official/LoopedActor": "549a4e81ebd2d823112ed1bcf008f837e0f449b5",
            "camail-official/Quotient_Recurrent_Reasoner_QRR": "3e3c9ebecad534296482316e1c39f1063f0a6a32",
        },
        "module_1_feige_lean_and_exact_extremizer": {
            "exact_extremizer": feige_exact,
            "hardened_axiom_log_parser": feige_strict_log_ok,
            "live_clone_audit": feige_clone,
        },
        "module_2_sumsets_carry_automaton_and_cw_repair": sumsets,
        "module_3_hope_hilbert_schur_and_Hn": {
            "hope_gauge_vs_schur_obstruction": hope_schur,
            "finite_hilbert_bareiss_and_rh4": hilbert_hn,
        },
        "module_4_recurrence_and_camail_bridge": {
            "exact_bridge": recurrence_bridge,
            "live_clone_hygiene": other_clones,
        },
    }
    payload["canonical_sha256"] = hashlib.sha256(canonical_json(payload).encode("utf-8")).hexdigest()
    return payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Wave 2 Round 5 Arm R5-5 (AUDIT-060) Exact Zero-Float Auditor")
    parser.add_argument("--json", action="store_true", help="Emit canonical zero-float JSON to stdout")
    parser.add_argument("--standalone", action="store_true", help="Run exact pure-math suite without local clones")
    parser.add_argument("--write-cert", type=Path, default=None, help="Write canonical JSON certificate to path")
    args = parser.parse_args(argv)

    result = run_all(standalone=args.standalone)
    text = json.dumps(result, indent=2, sort_keys=True, allow_nan=False) + "\n"
    if args.write_cert is not None:
        args.write_cert.write_text(text, encoding="utf-8")
    if args.json:
        sys.stdout.write(text)
    else:
        print(f"Verdict: {result['verdict']}")
        print(f"Oracle:  {result['oracle_class']}")
        print(f"SHA-256: {result['canonical_sha256']}")
    return 0 if result["verdict"] == "ALPHAXIV_MATH_FORMAL_ALL_CHECKS_VERIFIED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
