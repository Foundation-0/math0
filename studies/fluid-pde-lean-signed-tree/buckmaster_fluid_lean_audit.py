#!/usr/bin/env python3
"""Round 4D Arm R4D-1 (AUDIT-052): Forensic Tomography of tristanbuckmaster/navier-stokes,
tristanbuckmaster/fluid_lean, and openai/NavierStokesAndEuler + Exact Pure-Q Verifier for
Alpoege-Buckmaster's Multifrontal SignedTree Schur-Complement Coercivity Certifier
(CellLayerChallenge.lean:2051-2210), 20-Nov-2026 Weight Patch, and FixedPointBox Sperner Grid.

100% pure Python 3 stdlib (int + fractions.Fraction). ZERO floating-point
arithmetic anywhere in theorems or emitted JSON. ZERO bare assert statements.
Strictly READ-ONLY on all external repositories.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Any


# ============================================================================
# Strict R3 Validation & Exact Rational Linear Algebra (Zero Floats, Zero Asserts)
# ============================================================================

def require_exact_int(val: Any, name: str) -> int:
    if isinstance(val, bool) or not isinstance(val, int):
        raise TypeError(f"{name} must be an exact int (got {type(val).__name__})")
    return val


def require_exact_rational(val: Any, name: str) -> Fraction:
    if isinstance(val, bool) or not isinstance(val, (int, Fraction)):
        raise TypeError(f"{name} must be exact int or Fraction (got {type(val).__name__})")
    return Fraction(val)


def frac_str(x: Fraction) -> str:
    f = require_exact_rational(x, "x")
    return f"{f.numerator}" if f.denominator == 1 else f"{f.numerator}/{f.denominator}"


def verify_no_floats(obj: Any, path: str = "$") -> None:
    if isinstance(obj, float):
        raise ValueError(f"Forbidden float detected at {path}: {obj!r}")
    if isinstance(obj, dict):
        for k, v in obj.items():
            verify_no_floats(v, f"{path}.{k}")
    elif isinstance(obj, (list, tuple)):
        for idx, v in enumerate(obj):
            verify_no_floats(v, f"{path}[{idx}]")


def mat_zero(rows: int, cols: int) -> list[list[Fraction]]:
    return [[Fraction(0) for _ in range(cols)] for _ in range(rows)]


def mat_add(A: list[list[Fraction]], B: list[list[Fraction]]) -> list[list[Fraction]]:
    m = len(A)
    n = len(A[0])
    if len(B) != m or len(B[0]) != n:
        raise ValueError("Matrix dimension mismatch in mat_add")
    return [[A[i][j] + B[i][j] for j in range(n)] for i in range(m)]


def mat_sub(A: list[list[Fraction]], B: list[list[Fraction]]) -> list[list[Fraction]]:
    m = len(A)
    n = len(A[0])
    if len(B) != m or len(B[0]) != n:
        raise ValueError("Matrix dimension mismatch in mat_sub")
    return [[A[i][j] - B[i][j] for j in range(n)] for i in range(m)]


def mat_neg(A: list[list[Fraction]]) -> list[list[Fraction]]:
    return [[-x for x in row] for row in A]


def mat_transpose(A: list[list[Fraction]]) -> list[list[Fraction]]:
    if not A:
        return []
    m = len(A)
    n = len(A[0])
    return [[A[i][j] for i in range(m)] for j in range(n)]


def mat_mul(A: list[list[Fraction]], B: list[list[Fraction]]) -> list[list[Fraction]]:
    m = len(A)
    k = len(A[0])
    if len(B) != k:
        raise ValueError("Inner dimension mismatch in mat_mul")
    n = len(B[0])
    return [
        [sum((A[i][t] * B[t][j] for t in range(k)), Fraction(0)) for j in range(n)]
        for i in range(m)
    ]


def mat_gram_cols(cols: list[list[Fraction]], dim: int) -> list[list[Fraction]]:
    """Compute F F^T from a list of column vectors in Q^dim."""
    out = mat_zero(dim, dim)
    for col in cols:
        if len(col) != dim:
            raise ValueError(f"Column length {len(col)} != dim {dim}")
        for i in range(dim):
            ci = require_exact_rational(col[i], f"col[{i}]")
            if ci != 0:
                for j in range(dim):
                    out[i][j] += ci * require_exact_rational(col[j], f"col[{j}]")
    return out


def is_symmetric(M: list[list[Fraction]]) -> bool:
    if not M or not isinstance(M, list):
        return False
    m = len(M)
    for row in M:
        if len(row) != m:
            return False
    for i in range(m):
        for j in range(i + 1, m):
            if M[i][j] != M[j][i]:
                return False
    return True


def exact_symmetric_inertia(mat: list[list[int | Fraction]]) -> tuple[int, int, int]:
    """Exact (n_pos, n_zero, n_neg) inertia of a symmetric rational matrix
    via exact 1x1 / 2x2 Bunch-Kaufman rational congruence over Q.
    """
    if not isinstance(mat, list) or not mat:
        raise ValueError("Matrix must be non-empty")
    m = len(mat)
    A: list[list[Fraction]] = []
    for i, row in enumerate(mat):
        if not isinstance(row, list) or len(row) != m:
            raise ValueError(f"Non-square matrix at row {i}")
        A.append([require_exact_rational(x, f"mat[{i}][{j}]") for j, x in enumerate(row)])
    for i in range(m):
        for j in range(i + 1, m):
            if A[i][j] != A[j][i]:
                raise ValueError(f"Asymmetric matrix at ({i},{j})")

    n_pos = 0
    n_neg = 0
    n_zero = 0
    i = 0
    while i < m:
        piv = next((r for r in range(i, m) if A[r][r] != 0), None)
        if piv is not None:
            if piv != i:
                A[i], A[piv] = A[piv], A[i]
                for row in A:
                    row[i], row[piv] = row[piv], row[i]
            d = A[i][i]
            if d > 0:
                n_pos += 1
            else:
                n_neg += 1
            for r in range(i + 1, m):
                if A[r][i] != 0:
                    fac = A[r][i] / d
                    for c in range(i + 1, m):
                        A[r][c] -= fac * A[i][c]
                    A[r][i] = Fraction(0)
            i += 1
        else:
            pair = None
            for r in range(i, m):
                for c in range(r + 1, m):
                    if A[r][c] != 0:
                        pair = (r, c)
                        break
                if pair is not None:
                    break
            if pair is None:
                n_zero += m - i
                break
            r, c = pair
            if r != i:
                A[i], A[r] = A[r], A[i]
                for row in A:
                    row[i], row[r] = row[r], row[i]
                if c == i:
                    c = r
            if c != i + 1:
                A[i + 1], A[c] = A[c], A[i + 1]
                for row in A:
                    row[i + 1], row[c] = row[c], row[i + 1]
            b = A[i][i + 1]
            n_pos += 1
            n_neg += 1
            for r2 in range(i + 2, m):
                u = A[r2][i]
                v = A[r2][i + 1]
                if u != 0 or v != 0:
                    fu = v / b
                    fv = u / b
                    for c2 in range(i + 2, m):
                        A[r2][c2] -= fu * A[i][c2] + fv * A[i + 1][c2]
                    A[r2][i] = Fraction(0)
                    A[r2][i + 1] = Fraction(0)
            i += 2
    return (n_pos, n_zero, n_neg)


def exact_bareiss_leading_minors(mat: list[list[Fraction]]) -> list[Fraction]:
    m = len(mat)
    minors: list[Fraction] = []
    for k in range(1, m + 1):
        sub = [[require_exact_rational(mat[i][j], "e") for j in range(k)] for i in range(k)]
        det = Fraction(1)
        for col in range(k):
            piv = next((r for r in range(col, k) if sub[r][col] != 0), None)
            if piv is None:
                det = Fraction(0)
                break
            if piv != col:
                sub[col], sub[piv] = sub[piv], sub[col]
                det = -det
            d = sub[col][col]
            det *= d
            for r in range(col + 1, k):
                if sub[r][col] != 0:
                    fac = sub[r][col] / d
                    for j in range(col + 1, k):
                        sub[r][j] -= fac * sub[col][j]
        minors.append(det)
    return minors


def exact_nullspace_basis(rows: list[list[Fraction]], dim: int) -> list[list[Fraction]]:
    """Compute an exact basis of {x in Q^dim : rows * x = 0} via RREF."""
    if not rows:
        return [[Fraction(1 if i == j else 0) for j in range(dim)] for i in range(dim)]
    m = len(rows)
    A = [[require_exact_rational(rows[i][j], "e") for j in range(dim)] for i in range(m)]
    pivots: list[int] = []
    r = 0
    for c in range(dim):
        piv = next((i for i in range(r, m) if A[i][c] != 0), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        d = A[r][c]
        A[r] = [x / d for x in A[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [A[i][j] - f * A[r][j] for j in range(dim)]
        pivots.append(c)
        r += 1
    free_cols = [c for c in range(dim) if c not in pivots]
    basis: list[list[Fraction]] = []
    for fc in free_cols:
        vec = [Fraction(0)] * dim
        vec[fc] = Fraction(1)
        for idx, pc in enumerate(pivots):
            vec[pc] = -A[idx][fc]
        basis.append(vec)
    return basis


def psd_r_opt_and_r_h4(M: list[list[Fraction]]) -> dict[str, Any]:
    """Exact rational spectral lower bounds on rank(M) for PSD M >= 0."""
    m = len(M)
    M2 = mat_mul(M, M)
    M3 = mat_mul(M2, M)
    M4 = mat_mul(M2, M2)
    t1 = sum((M[i][i] for i in range(m)), Fraction(0))
    t2 = sum((M2[i][i] for i in range(m)), Fraction(0))
    t3 = sum((M3[i][i] for i in range(m)), Fraction(0))
    t4 = sum((M4[i][i] for i in range(m)), Fraction(0))
    r_opt = (t1 * t1) / t2 if t2 > 0 else Fraction(0)
    det2 = t2 * t4 - t3 * t3
    r_h4 = (t1 * t1 * t4 - 2 * t1 * t2 * t3 + t2 * t2 * t2) / det2 if det2 > 0 else r_opt
    return {
        "r_opt": r_opt,
        "r_opt_str": frac_str(r_opt),
        "r_h4": r_h4,
        "r_h4_str": frac_str(r_h4),
        "r_opt_x10000": int((r_opt * 10000).numerator // (r_opt * 10000).denominator),
        "r_h4_x10000": int((r_h4 * 10000).numerator // (r_h4 * 10000).denominator),
    }


def r_opt_noncommuting(u: Fraction, t: Fraction, s_frob: Fraction, b: int) -> Fraction:
    """Exact AUDIT-002 R_opt(u, t, S, b) lower bound for P >= 0, n_+(Q) <= b."""
    b_int = require_exact_int(b, "b")
    if b_int < 0:
        raise ValueError("b must be non-negative")
    if u <= 0 or u + t <= 0 or s_frob <= 0:
        return Fraction(0)
    if b_int > 0 and t > 0 and t * (u + t) >= b_int * s_frob:
        denom = s_frob - (t * t) / b_int
        if denom <= 0:
            raise ValueError("Infeasible (u, t, S, b) with S <= t^2/b")
        return (u * u) / denom
    val = ((u + t) * (u + t)) / s_frob - b_int
    return val if val > 0 else Fraction(0)


# ============================================================================
# Part 1: Live Commit-Pinned 3-Repo aletheia v1.2.0 Forensic Tomography
# ============================================================================

_HARD_ESCAPE_PREFILTER_RE = re.compile(
    r"\b(?:sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|csimp)\b"
    r"|debug\.skipKernelTC|public\s+import|\bpartial\s+(?:def|instance|abbrev|/-)",
    flags=re.DOTALL,
)


def run_three_repo_lean4_tomography() -> dict[str, Any]:
    """Commit-pinned live aletheia v1.2.0 tomography across:
      1. tristanbuckmaster/navier-stokes (2,271 Lean files + 6 comparator*.json + paper/)
      2. tristanbuckmaster/fluid_lean ({affinecore, boussinesq-blowup, euler-blowup}, 3,748 Lean files + 3 comparator.json)
      3. openai/NavierStokesAndEuler (2,659 Lean files + 2 ComparatorChallenges/*.json)
    Resolves all paths relative to __file__ (zero personal path leaks).
    """
    here = Path(__file__).resolve()
    aletheia_root = here.parents[3] / "publish" / "aletheia" if len(here.parents) > 3 else None
    r4_repos = here.parents[1] / "repos" if len(here.parents) > 1 else None
    r3_repos = here.parents[2] / "round3" / "repos" if len(here.parents) > 2 else None

    aletheia_ok = aletheia_root is not None and (aletheia_root / "aletheia" / "audit_check.py").is_file()
    repo_dirs = (
        {
            "tristanbuckmaster/navier-stokes": r4_repos / "tristanbuckmaster-navier-stokes",
            "tristanbuckmaster/fluid_lean": r4_repos / "tristanbuckmaster-fluid_lean",
            "openai/NavierStokesAndEuler": r3_repos / "openai-NavierStokesAndEuler",
        }
        if r4_repos is not None and r3_repos is not None
        else {}
    )
    clones_ok = bool(repo_dirs) and all((rdir / ".git").exists() for rdir in repo_dirs.values())
    if not (aletheia_ok and clones_ok):
        return {
            "mode": "standalone_no_external_clones",
            "note": (
                "External third-party Lean 4 repositories (tristanbuckmaster/navier-stokes@ad53419d, "
                "tristanbuckmaster/fluid_lean@d0124689, openai/NavierStokesAndEuler@f9e8bc5b) are not "
                "vendored in standalone math0; see buckmaster_fluid_lean_certificate.json for the "
                "sealed 8,678-file AUDIT-052 aletheia v1.2.0 forensics record."
            ),
            "total_lean_files_scanned": 0,
            "total_lean_lines_scanned": 0,
            "subprojects": {},
        }

    if str(aletheia_root) not in sys.path:
        sys.path.insert(0, str(aletheia_root))
    import aletheia  # noqa: PLC0415
    from aletheia.audit_check import audit_lean4_source, validate_comparator_config  # noqa: PLC0415

    pinned_commits: dict[str, str] = {}
    for label, rdir in repo_dirs.items():
        proc = subprocess.run(
            ["git", "-C", str(rdir), "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            check=True,
        )
        pinned_commits[label] = proc.stdout.strip()

    subprojects = [
        ("tb_navier_stokes", repo_dirs["tristanbuckmaster/navier-stokes"] / "lean", "comparator*.json"),
        ("tb_fluid_affinecore", repo_dirs["tristanbuckmaster/fluid_lean"] / "affinecore", "comparator*.json"),
        ("tb_fluid_boussinesq", repo_dirs["tristanbuckmaster/fluid_lean"] / "boussinesq-blowup", "comparator*.json"),
        ("tb_fluid_euler", repo_dirs["tristanbuckmaster/fluid_lean"] / "euler-blowup", "comparator*.json"),
        ("oai_nse", repo_dirs["openai/NavierStokesAndEuler"], "ComparatorChallenges/*.json"),
    ]

    subproject_reports: dict[str, Any] = {}
    hashes_by_sub: dict[str, set[str]] = {}
    total_files_all = 0
    total_lines_all = 0

    for sub_name, sub_root, comp_glob in subprojects:
        tc_path = sub_root / "lean-toolchain"
        toolchain = tc_path.read_text(encoding="utf-8").strip() if tc_path.is_file() else "none"

        # 1. Comparator config audit via aletheia v1.2.0
        comp_results: list[dict[str, Any]] = []
        for cfg in sorted(sub_root.glob(comp_glob)):
            res = validate_comparator_config(cfg, lean_root=sub_root)
            raw_cfg = json.loads(cfg.read_text(encoding="utf-8"))
            comp_results.append({
                "config_file": str(cfg.relative_to(sub_root)).replace("\\", "/"),
                "passed": bool(res["passed"]),
                "enable_nanoda": raw_cfg.get("enable_nanoda"),
                "theorem_count": len(raw_cfg.get("theorem_names", [])),
                "failures": res.get("failures", []),
            })

        # 2. Full-corpus scan (prefilter + exact aletheia audit_lean4_source on all keyword-bearing files)
        lean_files = sorted(p for p in sub_root.rglob("*.lean") if ".lake" not in p.parts)
        code_counts: Counter[str] = Counter()
        unclean_files: list[dict[str, Any]] = []
        file_hashes: set[str] = set()
        total_lines = 0
        decide_kernel_count = 0
        native_decide_count = 0
        prefilter_hits = 0

        for fp in lean_files:
            raw_bytes = fp.read_bytes()
            file_hashes.add(hashlib.sha256(raw_bytes).hexdigest())
            src = raw_bytes.decode("utf-8", errors="replace")
            total_lines += src.count("\n") + 1
            decide_kernel_count += src.count("decide +kernel")
            native_decide_count += src.count("native_decide")
            if _HARD_ESCAPE_PREFILTER_RE.search(src):
                prefilter_hits += 1
                res = audit_lean4_source(src, allow_non_init_imports=True)
                for f in res["findings"]:
                    code_counts[f["code"]] += 1
                if not res["clean"]:
                    unclean_files.append({
                        "file": str(fp.relative_to(sub_root)).replace("\\", "/"),
                        "finding_count": len(res["findings"]),
                        "codes": sorted({f["code"] for f in res["findings"]}),
                        "lines": [f["line"] for f in res["findings"]],
                    })

        hashes_by_sub[sub_name] = file_hashes
        total_files_all += len(lean_files)
        total_lines_all += total_lines

        subproject_reports[sub_name] = {
            "toolchain": toolchain,
            "lean_files": len(lean_files),
            "total_lines": total_lines,
            "prefilter_audited_by_aletheia": prefilter_hits,
            "clean_proof_files": len(lean_files) - len(unclean_files),
            "unclean_files_count": len(unclean_files),
            "finding_codes": dict(sorted(code_counts.items())),
            "non_sorry_trust_escapes": sum(v for k, v in code_counts.items() if k != "LEAN4_SORRY"),
            "decide_plus_kernel_calls": decide_kernel_count,
            "native_decide_calls": native_decide_count,
            "comparator_configs": comp_results,
            "comparator_passed_count": sum(1 for c in comp_results if c["passed"]),
            "comparator_total_count": len(comp_results),
            "unclean_files": unclean_files,
        }

    # 3. Pairwise SHA-256 overlap (exact file deduplication check across all 5 subprojects)
    sub_names = [s[0] for s in subprojects]
    overlaps: dict[str, int] = {}
    for i in range(len(sub_names)):
        for j in range(i + 1, len(sub_names)):
            n_shared = len(hashes_by_sub[sub_names[i]] & hashes_by_sub[sub_names[j]])
            overlaps[f"{sub_names[i]}<->{sub_names[j]}"] = n_shared

    # 4. Forensic audit of tristanbuckmaster/navier-stokes specific gaps:
    #    (a) PrintAxioms vs 6 comparator*.json coverage gap
    #    (b) 20-Nov-2026 unrebuilt patch consistency across CellLayerChallenge, StatementDefs, AdjointRemainderAzimuthal*
    ns_lean = repo_dirs["tristanbuckmaster/navier-stokes"] / "lean"
    pa_src = (ns_lean / "scripts/PrintAxioms.lean").read_text(encoding="utf-8")
    pa_thms = re.findall(r"#print axioms\s+(\S+)", pa_src)
    comp_thms: list[str] = []
    for cfg in sorted(ns_lean.glob("comparator*.json")):
        comp_thms.extend(json.loads(cfg.read_text(encoding="utf-8")).get("theorem_names", []))
    unlisted_in_comparator = [t for t in pa_thms if t not in set(comp_thms)]

    parts_src = (ns_lean / "Breakdown/CellReduction/AdjointRemainderAzimuthalParts.lean").read_text(encoding="utf-8")
    azim_src = (ns_lean / "Breakdown/CellReduction/AdjointRemainderAzimuthal.lean").read_text(encoding="utf-8")
    clc_src = (ns_lean / "CellLayerChallenge.lean").read_text(encoding="utf-8")
    sdefs_src = (ns_lean / "Breakdown/CertCell/StatementDefs.lean").read_text(encoding="utf-8")
    pdf_path = repo_dirs["tristanbuckmaster/navier-stokes"] / "paper/finite-time-blow-up-navier-stokes.pdf"
    pdf_sha256 = hashlib.sha256(pdf_path.read_bytes()).hexdigest()

    patch_checks = {
        "modeWeight_defined_as_abs_plus_half": "def modeWeight (k : ℤ) : ℝ := |(k : ℝ)| + 1 / 2" in parts_src,
        "weight_le_uses_unfold_modeWeight_le_rfl": ("unfold modeWeight" in azim_src and "exact le_rfl" in azim_src),
        "cell_layer_and_statement_defs_have_patched_weight": (
            "(|(order p : ℝ)| + 1 / 2) ^ 2" in clc_src and "(|(order p : ℝ)| + 1 / 2) ^ 2" in sdefs_src
        ),
        "azimuthal_bounded_lines_synced": (
            [ln.strip() for ln in clc_src.splitlines() if "AzimuthalBounded" in ln]
            == [ln.strip() for ln in sdefs_src.splitlines() if "AzimuthalBounded" in ln]
        ),
        "vanish_lines_synced": (
            [ln.strip() for ln in clc_src.splitlines() if "vanish" in ln]
            == [ln.strip() for ln in sdefs_src.splitlines() if "vanish" in ln]
        ),
    }

    # Verify hard expectations programmatically
    if total_files_all != 8678:
        raise RuntimeError(f"Expected 8678 total Lean files, got {total_files_all}")
    if any(r["non_sorry_trust_escapes"] != 0 for r in subproject_reports.values()):
        raise RuntimeError("Unexpected non-sorry trust escape found!")
    if subproject_reports["tb_navier_stokes"]["comparator_passed_count"] != 0:
        raise RuntimeError("Expected 0/6 comparator pass on tb_navier_stokes due to enable_nanoda: false")
    if subproject_reports["tb_fluid_boussinesq"]["decide_plus_kernel_calls"] != 13547:
        raise RuntimeError("Unexpected decide +kernel count in boussinesq-blowup")
    if subproject_reports["tb_fluid_euler"]["decide_plus_kernel_calls"] != 8750:
        raise RuntimeError("Unexpected decide +kernel count in euler-blowup")
    if not all(patch_checks.values()):
        raise RuntimeError(f"20-Nov-2026 patch consistency check failed: {patch_checks}")

    return {
        "aletheia_version": aletheia.__version__,
        "pinned_commits": pinned_commits,
        "total_lean_files_scanned": total_files_all,
        "total_lean_lines_scanned": total_lines_all,
        "subprojects": subproject_reports,
        "pairwise_sha256_file_overlaps": overlaps,
        "navier_stokes_forensics": {
            "paper_pdf_bytes": pdf_path.stat().st_size,
            "paper_pdf_sha256": pdf_sha256,
            "paper_cited_unreleased_cert_sha256": "3f7a335b84b6c7631742cacc5343dfcd11cf72f5221ff79b2b9268790b4b22c5",
            "print_axioms_theorem_count": len(pa_thms),
            "comparator_listed_theorem_count": len(comp_thms),
            "unlisted_in_comparator_count": len(unlisted_in_comparator),
            "unlisted_in_comparator_theorems": unlisted_in_comparator,
            "nov20_unrebuilt_patch_static_sync": patch_checks,
        },
    }


# ============================================================================
# Part 2: Pure-Q Exact Verbatim Verifier for Alpoege-Buckmaster's
#         Certificate.SignedTree Multifrontal Schur-Complement Coercivity Engine
#         (CellLayerChallenge.lean:2051-2210, SF-01 #24)
# ============================================================================

def pivot_diagonal(dim: int, pivots: set[int], delta: list[Fraction]) -> list[list[Fraction]]:
    out = mat_zero(dim, dim)
    for j in pivots:
        out[j][j] = require_exact_rational(delta[j], f"delta[{j}]")
    return out


def slack_remainder(
    M: list[list[Fraction]],
    S: list[list[Fraction]],
    pivots: set[int],
    delta: list[Fraction],
    pos_cols: list[list[Fraction]],
    neg_cols: list[list[Fraction]],
) -> list[list[Fraction]]:
    """Exact CellLayerChallenge.lean:2089-2092:
    slackRemainder M S pivot delta Fp Fm := M - pivotDiagonal pivot delta - Fp Fp^T + Fm Fm^T - S.
    """
    dim = len(M)
    D_piv = pivot_diagonal(dim, pivots, delta)
    FpFpT = mat_gram_cols(pos_cols, dim)
    FmFmT = mat_gram_cols(neg_cols, dim)
    res = mat_sub(M, D_piv)
    res = mat_sub(res, FpFpT)
    res = mat_add(res, FmFmT)
    res = mat_sub(res, S)
    return res


def check_abs_quad_bound(diff_mat: list[list[Fraction]], err_mat: list[list[Fraction]]) -> bool:
    """Sufficient & exact PSD certificate for:
      forall x, quadValue (diff_mat) x + quadValue err_mat (|x|) >= 0
    We check the exact stronger condition: err_mat >= 0 entrywise, symmetric, and
    when err_mat == 0, diff_mat >= 0 (exact Bunch-Kaufman inertia n_neg == 0);
    when err_mat != 0, we check entrywise |M_err| <= err_mat or exact PSD decomposition
    diff_mat = P - Delta with P >= 0 and |Delta_{ij}| <= err_mat_{ij}!
    Even sharper: for any symmetric err_mat >= 0, if diff_mat is split as diff_mat + err_mat_diag >= 0?
    No: in our exact verifier, we pass an explicit PSD part + bounded remainder OR check directly
    that diff_mat is PSD when err_mat == 0, and when err_mat != 0 we verify the exact entrywise
    majorization |(-diff_mat)_{ij}| <= err_mat_{ij} (which implies forall x, x^T diff_mat x + |x|^T err_mat |x| >= 0
    by triangle inequality!) OR exact PSD of diff_mat itself!
    """
    m = len(diff_mat)
    if not is_symmetric(diff_mat) or not is_symmetric(err_mat):
        return False
    for i in range(m):
        for j in range(m):
            if err_mat[i][j] < 0:
                return False
    # Case 1: diff_mat itself is PSD -> since err_mat >= 0 entrywise, |x|^T err_mat |x| >= 0, so sum >= 0!
    if exact_symmetric_inertia(diff_mat)[2] == 0:
        return True
    # Case 2: entrywise majorization |diff_mat_{ij}| <= err_mat_{ij} -> x^T diff_mat x >= -|x|^T |diff_mat| |x| >= -|x|^T err_mat |x|!
    if all(abs(diff_mat[i][j]) <= err_mat[i][j] for i in range(m) for j in range(m)):
        return True
    return False


def verify_signed_tree_certificate(tree: dict[str, Any]) -> dict[str, Any]:
    """Verify verbatim CellLayerChallenge.lean:2051-2210 SignedTree,
    PassesRealNodeEnclosure at every node, PassesPivotCount, AND verify
    the resulting global Tree-Telescoping Coercivity Theorem over exact Q.
    Raises ValueError on any structural/enclosure violation (fail-closed R3/R5).
    """
    n_slaved = require_exact_int(tree["n_slaved"], "n_slaved")
    n_free = require_exact_int(tree["n_free"], "n_free")
    if n_slaved < 1 or n_free < 0:
        raise ValueError("Invalid (n_slaved, n_free)")
    dim = n_slaved + n_free

    nodes: list[str] = list(tree["nodes"])
    root: str = tree["root"]
    parent: dict[str, str | None] = dict(tree["parent"])
    if root not in nodes or parent.get(root) is not None:
        raise ValueError("Root must be in nodes with parent None")
    if sum(1 for v in nodes if parent.get(v) is None) != 1:
        raise ValueError("Tree must have exactly one root (only_root violated)")
    # Verify acyclic parent pointers
    for v in nodes:
        seen = set()
        cur: str | None = v
        while cur is not None:
            if cur in seen or cur not in nodes:
                raise ValueError(f"Cycle or unknown parent at node {v}")
            seen.add(cur)
            cur = parent.get(cur)

    # Leaves: list of {"node": str, "matrix": dim x dim}
    leaves = tree["leaves"]
    # Optional null pairs: list of {"pos_node": str, "neg_node": str, "matrix": dim x dim}
    null_pairs = tree.get("null_pairs", [])
    expanded_leaves: list[tuple[str, list[list[Fraction]]]] = []
    for lf in leaves:
        nd = lf["node"]
        if nd not in nodes:
            raise ValueError(f"Leaf attached to unknown node {nd}")
        mat = [[require_exact_rational(x, "leaf") for x in row] for row in lf["matrix"]]
        if not is_symmetric(mat) or len(mat) != dim:
            raise ValueError("Leaf matrix must be symmetric of size dim")
        expanded_leaves.append((nd, mat))
    for np_item in null_pairs:
        pn, nn = np_item["pos_node"], np_item["neg_node"]
        if pn not in nodes or nn not in nodes:
            raise ValueError("NullPair attached to unknown node")
        mat = [[require_exact_rational(x, "null_pair") for x in row] for row in np_item["matrix"]]
        if not is_symmetric(mat) or len(mat) != dim:
            raise ValueError("NullPair matrix must be symmetric of size dim")
        expanded_leaves.append((pn, mat))
        expanded_leaves.append((nn, mat_neg(mat)))

    fronts: dict[str, list[list[Fraction]]] = {}
    for v in nodes:
        fm = [[require_exact_rational(x, f"front[{v}]") for x in row] for row in tree["fronts"][v]]
        if not is_symmetric(fm) or len(fm) != dim:
            raise ValueError(f"Front matrix at {v} must be symmetric of size dim")
        fronts[v] = fm

    # Compute nodeInput(v) = sum_{leaves at v} leafForm + sum_{children u of v} front(u)
    node_inputs: dict[str, list[list[Fraction]]] = {}
    for v in nodes:
        acc = mat_zero(dim, dim)
        for nd, mat in expanded_leaves:
            if nd == v:
                acc = mat_add(acc, mat)
        for u in nodes:
            if parent.get(u) == v:
                acc = mat_add(acc, fronts[u])
        node_inputs[v] = acc

    pivots_map: dict[str, set[int]] = {v: set(require_exact_int(j, "piv") for j in tree["pivots"][v]) for v in nodes}
    slack_map: dict[str, list[Fraction]] = {
        v: [require_exact_rational(x, "slack") for x in tree["slacks"][v]] for v in nodes
    }
    columns = tree["columns"]  # list of {"node": str, "vec": list[Fraction]}
    for c_item in columns:
        if c_item["node"] not in nodes or len(c_item["vec"]) != dim:
            raise ValueError("Invalid negative column specification")

    # --- Check PassesPivotCount (CellLayerChallenge.lean:2080-2084) ---
    all_pivoted: set[int] = set()
    for v in nodes:
        for j in pivots_map[v]:
            if j < 0 or j >= dim:
                raise ValueError(f"Pivot index out of range: {j}")
            if slack_map[v][j] <= 0:
                raise ValueError(f"slack_positive violated at node {v}, j={j}: {slack_map[v][j]}")
            all_pivoted.add(j)
    if all_pivoted != set(range(dim)):
        raise ValueError(f"every_variable_pivoted violated: missing {sorted(set(range(dim)) - all_pivoted)}")
    if exact_symmetric_inertia(fronts[root])[2] != 0:
        raise ValueError("root_front_nonneg violated: front[root] has negative eigenvalue")
    if len(columns) > n_free:
        raise ValueError(f"column_count violated: {len(columns)} > n_free={n_free}")

    # --- Check PassesRealNodeEnclosure at EVERY node (CellLayerChallenge.lean:2194-2210) ---
    node_diags: dict[str, Any] = {}
    for v in nodes:
        nd_data = tree["node_enclosures"][v]
        D_input = [[require_exact_rational(x, "D.input") for x in row] for row in nd_data["D_input"]]
        D_base = [[require_exact_rational(x, "D.base") for x in row] for row in nd_data["D_base"]]
        D_piv_val = [require_exact_rational(x, "D.pivotValue") for x in nd_data["D_pivotValue"]]
        D_weight = [require_exact_rational(x, "D.weight") for x in nd_data["D_weight"]]
        D_radius = [require_exact_rational(x, "D.radius") for x in nd_data["D_radius"]]
        pos_cols = [[require_exact_rational(x, "Fp") for x in col] for col in nd_data["pos_columns"]]
        E_mat = [[require_exact_rational(x, "E") for x in row] for row in nd_data["E"]]
        F_mat = [[require_exact_rational(x, "F") for x in row] for row in nd_data["F"]]

        if not (is_symmetric(D_input) and is_symmetric(D_base) and is_symmetric(E_mat) and is_symmetric(F_mat)):
            raise ValueError(f"Symmetry violated in node enclosure at {v}")
        if any(w <= 0 for w in D_weight):
            raise ValueError(f"weight_pos violated at {v}")
        if any(E_mat[i][j] < 0 or F_mat[i][j] < 0 for i in range(dim) for j in range(dim)):
            raise ValueError(f"Error matrix nonnegativity violated at {v}")

        # input_lower: nodeInput - D_input + E(|x|) >= 0
        if not check_abs_quad_bound(mat_sub(node_inputs[v], D_input), E_mat):
            raise ValueError(f"input_lower violated at node {v}")

        # row_bound (weighted Gershgorin): w_i * sum_j (|R_{ij}| + E_{ij} + F_{ij}) / w_j <= radius_i
        neg_cols_v = [[require_exact_rational(x, "Fm") for x in c["vec"]] for c in columns if c["node"] == v]
        R_mat = slack_remainder(D_input, D_base, pivots_map[v], D_piv_val, pos_cols, neg_cols_v)
        max_row_ratio = Fraction(0)
        for i in range(dim):
            lhs = D_weight[i] * sum(
                ((abs(R_mat[i][j]) + E_mat[i][j] + F_mat[i][j]) / D_weight[j] for j in range(dim)),
                Fraction(0),
            )
            if lhs > D_radius[i]:
                raise ValueError(f"row_bound violated at node {v}, row {i}: {lhs} > {D_radius[i]}")
            if D_radius[i] > 0:
                ratio = lhs / D_radius[i]
                if ratio > max_row_ratio:
                    max_row_ratio = ratio

        # front_upper: (D_base - diag_{j not in piv}(radius)) - front(v) + F(|x|) >= 0
        non_piv = set(range(dim)) - pivots_map[v]
        D_base_shrunk = mat_sub(D_base, pivot_diagonal(dim, non_piv, D_radius))
        if not check_abs_quad_bound(mat_sub(D_base_shrunk, fronts[v]), F_mat):
            raise ValueError(f"front_upper violated at node {v}")

        # slack_le: forall j in piv, slack(v, j) <= pivotValue(j) - radius(j)
        for j in pivots_map[v]:
            if slack_map[v][j] > D_piv_val[j] - D_radius[j]:
                raise ValueError(f"slack_le violated at node {v}, j={j}")

        node_diags[v] = {
            "pivots": sorted(pivots_map[v]),
            "pos_col_count": len(pos_cols),
            "neg_col_count": len(neg_cols_v),
            "max_gershgorin_ratio": frac_str(max_row_ratio),
        }

    # --- Global Tree-Telescoping Coercivity & Sylvester Inertia Verification ---
    M_total = mat_zero(dim, dim)
    for _, mat in expanded_leaves:
        M_total = mat_add(M_total, mat)

    # Total positive diagonal slack D_slack = sum_v pivotDiagonal(piv_v, slack_v)
    D_slack = mat_zero(dim, dim)
    for v in nodes:
        D_slack = mat_add(D_slack, pivot_diagonal(dim, pivots_map[v], slack_map[v]))
    all_neg_cols = [[require_exact_rational(x, "Fm") for x in c["vec"]] for c in columns]
    FmFmT_all = mat_gram_cols(all_neg_cols, dim)

    # Theorem: M_total - (D_slack - Fm Fm^T) >= 0 (verified by exact Bunch-Kaufman PSD!)
    P_lifted = mat_add(M_total, FmFmT_all)
    surplus = mat_sub(P_lifted, D_slack)
    in_surplus = exact_symmetric_inertia(surplus)
    if in_surplus[2] != 0:
        raise RuntimeError(f"Global tree telescoping inequality failed! Surplus inertia: {in_surplus}")

    in_total = exact_symmetric_inertia(M_total)
    if in_total[2] > n_free or in_total[0] < n_slaved:
        raise RuntimeError(f"Global inertia bound failed: {in_total} for (|A|={n_slaved}, |B|={n_free})")

    # Verify strict PD on ker(Fm^T) (codimension <= |B|, dim >= |A|)
    ker_basis = exact_nullspace_basis(all_neg_cols, dim)
    K_mat = mat_transpose(ker_basis)  # dim x ker_dim
    M_restr = mat_mul(mat_mul(mat_transpose(K_mat), M_total), K_mat)
    in_restr = exact_symmetric_inertia(M_restr)
    minors_restr = exact_bareiss_leading_minors(M_restr)
    if in_restr[0] != len(ker_basis) or in_restr[1] != 0 or in_restr[2] != 0 or not all(x > 0 for x in minors_restr):
        raise RuntimeError(f"Restricted operator on ker(Fm^T) not strictly PD: {in_restr}")

    # AUDIT-002 R_opt & AUDIT-014 R_H4 on lifted PSD P = M_total + Fm Fm^T, Q = -Fm Fm^T
    # Note: for AUDIT-002 P >= 0, Q with n_+(Q) <= b: apply to H = M_total = P + Q where P >= 0 and n_+(-Q) = len(columns)
    # Wait: AUDIT-002 bounds rank(P) >= n_+(Pi_{W^perp} (P+Q) Pi_{W^perp}) >= R_opt(tr P, tr Q, ||P+Q||_F^2, b) where b >= n_+(Q)!
    # Here Q = -Fm Fm^T <= 0 has n_+(Q) = 0 (so b = 0!), AND if we reverse sign:
    # Write P_pos = P_lifted >= 0, Q_neg = -Fm Fm^T <= 0 -> n_+(Q_neg) = 0 -> R_opt(u, t, S, 0) = max(0, (u+t)^2/S) <= n_+(M_total)!
    # Even better: take M_total = P_total - N_total with P_total = D_slack + surplus >= 0, Q_pos = FmFmT_all (n_+ <= |B|) on -M_total!
    u_p = sum((P_lifted[i][i] for i in range(dim)), Fraction(0))
    t_q = -sum((FmFmT_all[i][i] for i in range(dim)), Fraction(0))
    s_frob = sum((M_total[i][j] * M_total[i][j] for i in range(dim) for j in range(dim)), Fraction(0))
    r_opt_val = r_opt_noncommuting(u_p, t_q, s_frob, 0)
    spec_restr = psd_r_opt_and_r_h4(M_restr)

    # O(dim, Q) Householder orthogonal invariance check on M_total & P_lifted
    u_house = [Fraction(1 if (i & 1) == 0 else -2) for i in range(dim)]
    uu = sum((x * x for x in u_house), Fraction(0))
    Q_orth = [
        [Fraction(1 if i == j else 0) - Fraction(2) * u_house[i] * u_house[j] / uu for j in range(dim)]
        for i in range(dim)
    ]
    M_rot = mat_mul(mat_mul(Q_orth, M_total), Q_orth)
    if exact_symmetric_inertia(M_rot) != in_total:
        raise RuntimeError("O(dim, Q) invariance failed on M_total")

    return {
        "dim": dim,
        "n_slaved": n_slaved,
        "n_free": n_free,
        "node_count": len(nodes),
        "null_pair_count": len(null_pairs),
        "neg_column_count": len(columns),
        "passes_all_node_enclosures": True,
        "passes_pivot_count": True,
        "global_inertia": list(in_total),
        "surplus_psd_inertia": list(in_surplus),
        "ker_FmT_dim": len(ker_basis),
        "restricted_ker_FmT_inertia": list(in_restr),
        "restricted_ker_FmT_all_bareiss_minors_pos": True,
        "restricted_r_opt_x10000": spec_restr["r_opt_x10000"],
        "restricted_r_h4_x10000": spec_restr["r_h4_x10000"],
        "audit002_r_opt_on_M_total": frac_str(r_opt_val),
        "O_dim_Q_householder_invariant": True,
        "node_diagnostics": node_diags,
    }


def build_exact_multifrontal_tree() -> dict[str, Any]:
    """Construct an exact 3-node multifrontal SignedTree (dim=6: |A|=4 slaved, |B|=2 free)
    with NullPair (+N, -N) balancing, 2 negative columns (exact Krein inertia (4,0,2)),
    and exact Schur-complement front pushforward (zero remainder R=0, E=F=0).
    """
    dim = 6
    # Coordinate partitioning:
    #   leaf_L eliminates pivots {0, 1} using 2 positive columns + pushes 4x4 Schur front to root
    #   leaf_R eliminates pivots {2, 3} using 2 positive columns + pushes 4x4 Schur front to root
    #   root eliminates pivots {4, 5} using 2 negative columns (in B!) + slack > 0 + front[root] = 0 >= 0
    piv_L = [0, 1]
    piv_R = [2, 3]
    piv_root = [4, 5]

    slack_L = [Fraction(1), Fraction(1), Fraction(0), Fraction(0), Fraction(0), Fraction(0)]
    slack_R = [Fraction(0), Fraction(0), Fraction(1), Fraction(1), Fraction(0), Fraction(0)]
    slack_root = [Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(1), Fraction(1)]

    # Positive Cholesky-like columns at leaf_L (coupling slaved 0,1 with free 4,5)
    fp_L = [
        [Fraction(2), Fraction(0), Fraction(0), Fraction(0), Fraction(1), Fraction(0)],
        [Fraction(0), Fraction(2), Fraction(0), Fraction(0), Fraction(0), Fraction(1)],
    ]
    # Positive columns at leaf_R (coupling slaved 2,3 with free 4,5)
    fp_R = [
        [Fraction(0), Fraction(0), Fraction(2), Fraction(0), Fraction(-1), Fraction(1)],
        [Fraction(0), Fraction(0), Fraction(0), Fraction(2), Fraction(1), Fraction(1)],
    ]
    # Exact Schur complements pushed to root (PSD matrices supported on free coords {4, 5}!)
    front_L = mat_zero(dim, dim)
    front_L[4][4] = Fraction(2)
    front_L[4][5] = Fraction(1)
    front_L[5][4] = Fraction(1)
    front_L[5][5] = Fraction(3)

    front_R = mat_zero(dim, dim)
    front_R[4][4] = Fraction(3)
    front_R[4][5] = Fraction(-1)
    front_R[5][4] = Fraction(-1)
    front_R[5][5] = Fraction(2)

    # Exact leaf inputs = D_piv(slack) + Fp Fp^T + front (so R == 0 identically!)
    inp_L = mat_add(mat_add(pivot_diagonal(dim, set(piv_L), slack_L), mat_gram_cols(fp_L, dim)), front_L)
    inp_R = mat_add(mat_add(pivot_diagonal(dim, set(piv_R), slack_R), mat_gram_cols(fp_R, dim)), front_R)

    # Add a nontrivial NullPair (+N at leaf_L, -N at leaf_R) that cancels globally!
    # Wait: NullPair (+N at leaf_L, -N at leaf_R) shifts nodeInput(leaf_L) by +N and nodeInput(leaf_R) by -N;
    # to keep exact telescoping, attach +N to leaf_L and -N to root (carried up via front_L += N)!
    N_pair = mat_zero(dim, dim)
    N_pair[4][4] = Fraction(1)
    N_pair[4][5] = Fraction(1, 2)
    N_pair[5][4] = Fraction(1, 2)
    N_pair[5][5] = Fraction(1)

    front_L_with_N = mat_add(front_L, N_pair)
    # At leaf_L: leaf_form = inp_L, plus +N from NullPair -> nodeInput(L) = inp_L + N_pair = D_piv + FpFpT + (front_L + N_pair)!
    # At root: nodeInput(root) = front_L_with_N + front_R + (-N_pair) + leaf_root = front_L + front_R + leaf_root!
    # Choose leaf_root so that M_total has EXACTLY 2 negative eigenvalues (inertia (4, 0, 2)):
    # nodeInput(root) = D_piv(slack_root) - Fm Fm^T + front_root (with front_root = 0, Fp_root = [])
    # Choose Fm columns on {4, 5} large enough to flip both eigenvalues on {4, 5} negative!
    fm_root = [
        [Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(3), Fraction(0)],
        [Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(3)],
    ]
    # Desired nodeInput(root) = D_piv(slack_root) - FmFmT_root
    target_root_inp = mat_sub(pivot_diagonal(dim, set(piv_root), slack_root), mat_gram_cols(fm_root, dim))
    # Since nodeInput(root) = front_L + front_R + leaf_root, set leaf_root = target_root_inp - front_L - front_R
    leaf_root = mat_sub(mat_sub(target_root_inp, front_L), front_R)
    front_root = mat_zero(dim, dim)

    zero_m = mat_zero(dim, dim)
    zero_v = [Fraction(0)] * dim
    ones_v = [Fraction(1)] * dim

    return {
        "n_slaved": 4,
        "n_free": 2,
        "nodes": ["leaf_L", "leaf_R", "root"],
        "root": "root",
        "parent": {"leaf_L": "root", "leaf_R": "root", "root": None},
        "leaves": [
            {"node": "leaf_L", "matrix": inp_L},
            {"node": "leaf_R", "matrix": inp_R},
            {"node": "root", "matrix": leaf_root},
        ],
        "null_pairs": [
            {"pos_node": "leaf_L", "neg_node": "root", "matrix": N_pair},
        ],
        "fronts": {"leaf_L": front_L_with_N, "leaf_R": front_R, "root": front_root},
        "pivots": {"leaf_L": piv_L, "leaf_R": piv_R, "root": piv_root},
        "slacks": {"leaf_L": slack_L, "leaf_R": slack_R, "root": slack_root},
        "columns": [
            {"node": "root", "vec": fm_root[0]},
            {"node": "root", "vec": fm_root[1]},
        ],
        "node_enclosures": {
            "leaf_L": {
                "D_input": mat_add(inp_L, N_pair),
                "D_base": front_L_with_N,
                "D_pivotValue": slack_L,
                "D_weight": ones_v,
                "D_radius": zero_v,
                "pos_columns": fp_L,
                "E": zero_m,
                "F": zero_m,
            },
            "leaf_R": {
                "D_input": inp_R,
                "D_base": front_R,
                "D_pivotValue": slack_R,
                "D_weight": ones_v,
                "D_radius": zero_v,
                "pos_columns": fp_R,
                "E": zero_m,
                "F": zero_m,
            },
            "root": {
                "D_input": target_root_inp,
                "D_base": front_root,
                "D_pivotValue": slack_root,
                "D_weight": ones_v,
                "D_radius": zero_v,
                "pos_columns": [],
                "E": zero_m,
                "F": zero_m,
            },
        },
    }


def build_perturbed_gershgorin_tree() -> dict[str, Any]:
    """Construct a perturbed approximate-factorization SignedTree modeling
    128-bit Arb/FLINT interval enclosure absorption: nonzero slackRemainder R != 0,
    nonzero symmetric E, F >= 0, non-uniform weights w_j > 0, and radii r_i > 0,
    still certifying strict coercivity via PassesRealNodeEnclosure + PassesPivotCount!
    """
    base = build_exact_multifrontal_tree()
    dim = 6
    # Perturb leaf_L's D_input slightly by delta_in, absorb with E_L >= |delta_in|
    # Perturb leaf_L's D_base upward on non-pivots {2,3,4,5} by +1/4 so front_L <= D_base - diag(r) + F
    delta_in = mat_zero(dim, dim)
    delta_in[0][4] = Fraction(1, 32)
    delta_in[4][0] = Fraction(1, 32)
    E_L = mat_zero(dim, dim)
    E_L[0][4] = Fraction(1, 32)
    E_L[4][0] = Fraction(1, 32)

    F_L = mat_zero(dim, dim)
    F_L[4][5] = Fraction(1, 64)
    F_L[5][4] = Fraction(1, 64)

    enc_L = base["node_enclosures"]["leaf_L"]
    enc_L["D_input"] = mat_add(enc_L["D_input"], delta_in)
    # Increase D_pivotValue on pivots {0, 1} to absorb radius r_0, r_1 while keeping slack = 1/2 > 0
    # Wait: D_input is fixed; keep slack_L = [1/2, 1/2, 0, 0, 0, 0], D_pivotValue = [1, 1, 0, 0, 0, 0]
    # so slack_L[j] = 1/2 <= 1 - r_j whenever r_j <= 1/2!
    base["slacks"]["leaf_L"] = [Fraction(1, 2), Fraction(1, 2), Fraction(0), Fraction(0), Fraction(0), Fraction(0)]
    # Shift front_L DOWN slightly on non-pivots {2,3,4,5} by -r_j (with D_base unchanged, wait:
    # if front_L shrinks by -diag_{non_piv}(r_L), we also compensate in leaf_root so root remains exact!)
    weights_L = [Fraction(1), Fraction(2), Fraction(1), Fraction(1), Fraction(3, 2), Fraction(2)]
    # Compute exact weighted Gershgorin row sums for R_L + E_L + F_L!
    # Here R_L = delta_in (since D_input increased by delta_in, D_base/D_piv/Fp unchanged).
    R_L = slack_remainder(
        enc_L["D_input"],
        enc_L["D_base"],
        set(base["pivots"]["leaf_L"]),
        enc_L["D_pivotValue"],
        enc_L["pos_columns"],
        [],
    )
    radii_L = [
        weights_L[i] * sum(((abs(R_L[i][j]) + E_L[i][j] + F_L[i][j]) / weights_L[j] for j in range(dim)), Fraction(0))
        for i in range(dim)
    ]
    # Push down front["leaf_L"] on non-pivots by radii_L so front_upper holds with room to spare!
    non_piv_L = set(range(dim)) - set(base["pivots"]["leaf_L"])
    shrink_L = pivot_diagonal(dim, non_piv_L, radii_L)
    base["fronts"]["leaf_L"] = mat_sub(base["fronts"]["leaf_L"], shrink_L)
    # Compensate in root's leaf matrix so root's nodeInput stays exact (realistic: tighter front lowers root margin,
    # here we add shrink_L to leaf_root so root's D_input remains identical!)
    base["leaves"][2]["matrix"] = mat_add(base["leaves"][2]["matrix"], shrink_L)

    enc_L["D_weight"] = weights_L
    enc_L["D_radius"] = radii_L
    enc_L["E"] = E_L
    enc_L["F"] = F_L
    return base


def run_signed_tree_adversarial_suite() -> dict[str, Any]:
    """Verify exact tree, perturbed Gershgorin tree, and 6 adversarial refutation mutants."""
    exact_cert = verify_signed_tree_certificate(build_exact_multifrontal_tree())
    pert_cert = verify_signed_tree_certificate(build_perturbed_gershgorin_tree())

    # 6 adversarial mutants proving every clause of PassesRealNodeEnclosure & PassesPivotCount is load-bearing
    def mut_row_bound() -> dict[str, Any]:
        t = build_perturbed_gershgorin_tree()
        t["node_enclosures"]["leaf_L"]["D_radius"][0] -= Fraction(1, 1000)
        return t

    def mut_slack_le() -> dict[str, Any]:
        t = build_perturbed_gershgorin_tree()
        t["slacks"]["leaf_L"][0] = Fraction(1)  # exceeds pivotValue(1) - radius(>0)!
        return t

    def mut_root_front_indef() -> dict[str, Any]:
        t = build_exact_multifrontal_tree()
        t["fronts"]["root"][4][4] = Fraction(-1, 10)
        return t

    def mut_too_many_neg_cols() -> dict[str, Any]:
        t = build_exact_multifrontal_tree()
        t["columns"].append({"node": "root", "vec": [Fraction(0)] * 6})
        return t

    def mut_missing_pivot() -> dict[str, Any]:
        t = build_exact_multifrontal_tree()
        t["pivots"]["leaf_L"] = [1]  # omit j=0!
        return t

    def mut_negative_error_entry() -> dict[str, Any]:
        t = build_perturbed_gershgorin_tree()
        t["node_enclosures"]["leaf_L"]["E"][0][0] = Fraction(-1, 100)
        return t

    mutants = [
        ("mut1_violate_gershgorin_row_bound", mut_row_bound),
        ("mut2_violate_slack_le_margin", mut_slack_le),
        ("mut3_violate_root_front_nonneg", mut_root_front_indef),
        ("mut4_violate_column_count_gt_B", mut_too_many_neg_cols),
        ("mut5_violate_every_variable_pivoted", mut_missing_pivot),
        ("mut6_violate_error_matrix_nonneg", mut_negative_error_entry),
    ]
    killed = 0
    mutant_results: dict[str, str] = {}
    for label, builder in mutants:
        try:
            verify_signed_tree_certificate(builder())
        except ValueError as exc:
            killed += 1
            mutant_results[label] = f"REJECTED:{exc}"
        else:
            raise RuntimeError(f"SignedTree mutant survived: {label}")

    return {
        "exact_multifrontal_tree_with_nullpair": exact_cert,
        "perturbed_gershgorin_enclosure_tree": pert_cert,
        "adversarial_mutants_killed": killed,
        "adversarial_mutants_total": len(mutants),
        "adversarial_mutants_all_killed": killed == len(mutants),
        "mutant_details": mutant_results,
    }


# ============================================================================
# Part 3: 20-Nov-2026 Weight-Shift Algebra & FixedPointBox 2D Sperner Grid
# ============================================================================

def run_patch_weight_and_sperner_box_check() -> dict[str, Any]:
    """(A) Exact algebraic audit of the 20-Nov-2026 azimuthal weight patch:
        (|m| + 1/2)^2 - (m^2 + 1/4) == |m| >= 0, relaxing AzimuthalBounded by
        exact rational factor (|m| + 1/2)^2 / (m^2 + 1/4) for all m != 0.
    (B) Exact pure-Q discrete 2D Sperner grid-simplex check mirroring
        Breakdown/Cert/FixedPointBox.lean:49-61 on [0, 1]^2.
    """
    # (A) Exact weight-shift verification for m in -30..30
    for m in range(-30, 31):
        old_w = Fraction(m * m) + Fraction(1, 4)
        new_w = (Fraction(abs(m)) + Fraction(1, 2)) ** 2
        if new_w - old_w != Fraction(abs(m)):
            raise RuntimeError(f"Weight identity failed at m={m}")
        if (m == 0 and new_w != old_w) or (m != 0 and new_w <= old_w):
            raise RuntimeError(f"Weight ordering failed at m={m}")
    old_19 = Fraction(19 * 19) + Fraction(1, 4)
    new_19 = (Fraction(19) + Fraction(1, 2)) ** 2
    ratio_19 = new_19 / old_19  # 1521 / 1445

    # (B) Discrete 2D Kuhn triangulation Sperner labeling from FixedPointBox.lean:49-61
    # Map f(x, y) = (1/4 + x/3 + y/6, 1/5 + x/5 + 2y/5) mapping [0,1]^2 -> [0,1]^2
    # Exact unique fixed point solves:
    #   2/3 x - 1/6 y = 1/4  => 8x - 2y = 3
    #  -1/5 x + 3/5 y = 1/5  => -x + 3y = 1 => x = 3y - 1 => 24y - 8 - 2y = 3 => 22y = 11 => y = 1/2, x = 1/2!
    def f_box(pt: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
        x, y = pt
        return (Fraction(1, 4) + x / 3 + y / 6, Fraction(1, 5) + x / 5 + Fraction(2, 5) * y)

    fp_exact = (Fraction(1, 2), Fraction(1, 2))
    if f_box(fp_exact) != fp_exact:
        raise RuntimeError("Exact fixed point check failed")

    p_grid = 7  # odd resolution so (1/2, 1/2) lies strictly inside a cell (not on grid line!)

    def pt_of(ix: int, iy: int) -> tuple[Fraction, Fraction]:
        return (Fraction(ix, p_grid), Fraction(iy, p_grid))

    def lab(ix: int, iy: int) -> tuple[bool, bool]:
        # FixedPointBox.lean:49: lab x i := x i != 0 ∧ f (pt x) i <= pt x i
        px, py = pt_of(ix, iy)
        fx, fy = f_box((px, py))
        return (ix != 0 and fx <= px, iy != 0 and fy <= py)

    # Verify FixedPointBox boundary conditions h0 (x_i = 0 => not lab_i) and h1 (x_i = p => lab_i)
    for ix in range(p_grid + 1):
        for iy in range(p_grid + 1):
            l0, l1 = lab(ix, iy)
            if ix == 0 and l0:
                raise RuntimeError("Boundary h0 violated at ix=0")
            if iy == 0 and l1:
                raise RuntimeError("Boundary h0 violated at iy=0")
            if ix == p_grid and not l0:
                raise RuntimeError("Boundary h1 violated at ix=p")
            if iy == p_grid and not l1:
                raise RuntimeError("Boundary h1 violated at iy=p")

    # Enumerate all 2 * p_grid^2 Kuhn simplices in [0..p_grid]^2:
    # A 2D simplex (v0, v1, v2) is complete (FixedPointBox.lean:88) iff for each i in {0, 1}
    # it has a vertex with not lab_i AND a vertex with lab_i (equivalently Sperner colors {0, 1, 2}
    # where color = first index with not lab, or 2 if both lab!).
    def sperner_color(ix: int, iy: int) -> int:
        l0, l1 = lab(ix, iy)
        if not l0:
            return 0
        if not l1:
            return 1
        return 2

    complete_simplices: list[dict[str, Any]] = []
    for ix in range(p_grid):
        for iy in range(p_grid):
            # Two Kuhn triangles in square [ix, ix+1] x [iy, iy+1]
            tris = [
                ((ix, iy), (ix + 1, iy), (ix + 1, iy + 1)),
                ((ix, iy), (ix, iy + 1), (ix + 1, iy + 1)),
            ]
            for tri in tris:
                cols = {sperner_color(vx, vy) for vx, vy in tri}
                if cols == {0, 1, 2}:
                    # Check if exact fixed point (1/2, 1/2) lies in this cell
                    in_cell = (
                        Fraction(ix, p_grid) <= fp_exact[0] <= Fraction(ix + 1, p_grid)
                        and Fraction(iy, p_grid) <= fp_exact[1] <= Fraction(iy + 1, p_grid)
                    )
                    complete_simplices.append({
                        "vertices_grid": [list(v) for v in tri],
                        "contains_exact_fixed_point": in_cell,
                    })

    if len(complete_simplices) % 2 != 1 or not any(s["contains_exact_fixed_point"] for s in complete_simplices):
        raise RuntimeError(f"Sperner odd-parity / fixed-point enclosure failed: {complete_simplices}")

    return {
        "nov20_weight_shift": {
            "range_m_verified": [-30, 30],
            "exact_identity": "(|m| + 1/2)^2 - (m^2 + 1/4) == |m|",
            "kappa_19_old_weight": frac_str(old_19),
            "kappa_19_patched_weight": frac_str(new_19),
            "kappa_19_relaxation_factor": frac_str(ratio_19),
        },
        "fixed_point_box_sperner_2d": {
            "grid_resolution_p": p_grid,
            "total_kuhn_simplices": 2 * p_grid * p_grid,
            "boundary_h0_h1_verified": True,
            "complete_sperner_simplex_count": len(complete_simplices),
            "odd_parity_certified": len(complete_simplices) % 2 == 1,
            "exact_fixed_point": [frac_str(fp_exact[0]), frac_str(fp_exact[1])],
            "complete_simplices": complete_simplices,
        },
    }


# ============================================================================
# Part 4: Built-in R3 Strict Domain / Type Negative Controls
# ============================================================================

def run_r3_negative_controls() -> dict[str, Any]:
    controls: list[tuple[str, Any]] = [
        ("reject_float_exact_int", lambda: require_exact_int(3.0, "x")),
        ("reject_bool_exact_int", lambda: require_exact_int(True, "x")),
        ("reject_float_exact_rational", lambda: require_exact_rational(0.25, "x")),
        ("reject_bool_exact_rational", lambda: require_exact_rational(False, "x")),
        ("reject_float_json_guard", lambda: verify_no_floats({"nested": [1.5]})),
        ("reject_asymmetric_inertia", lambda: exact_symmetric_inertia([[1, 2], [3, 4]])),
        ("reject_empty_inertia", lambda: exact_symmetric_inertia([])),
        ("reject_negative_b_r_opt", lambda: r_opt_noncommuting(Fraction(1), Fraction(0), Fraction(1), -1)),
        ("reject_infeasible_r_opt", lambda: r_opt_noncommuting(Fraction(2), Fraction(2), Fraction(1), 1)),
        ("reject_dim_mismatch_mat_add", lambda: mat_add([[Fraction(1)]], [[Fraction(1), Fraction(2)]])),
    ]
    passed = 0
    details: dict[str, str] = {}
    for label, fn in controls:
        try:
            fn()
        except (TypeError, ValueError) as exc:
            passed += 1
            details[label] = f"REJECTED:{type(exc).__name__}"
        else:
            raise RuntimeError(f"R3 negative control failed to reject: {label}")
    return {
        "controls_passed": passed,
        "controls_total": len(controls),
        "all_rejected": passed == len(controls),
        "details": details,
    }


def run_all_audits(write_certificate: bool = False) -> dict[str, Any]:
    part1 = run_three_repo_lean4_tomography()
    part2 = run_signed_tree_adversarial_suite()
    part3 = run_patch_weight_and_sperner_box_check()
    part4 = run_r3_negative_controls()

    payload: dict[str, Any] = {
        "probe_id": "AUDIT-052",
        "arm": "R4D-1",
        "title": "3-Repo Fluid-PDE Lean 4 Forensics (tristanbuckmaster/navier-stokes, fluid_lean, openai/NavierStokesAndEuler) & Pure-Q SignedTree Multifrontal Schur-Complement Verifier",
        "oracle_class": "exact+anchor",
        "honest_novelty_claim": "N1",
        "zero_floats_certified": True,
        "part1_three_repo_lean4_tomography": part1,
        "part2_signed_tree_multifrontal_schur": part2,
        "part3_nov20_weight_and_sperner_box": part3,
        "part4_r3_negative_controls": part4,
    }
    verify_no_floats(payload)
    canon = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    payload["canonical_sha256"] = hashlib.sha256(canon).hexdigest()

    if write_certificate:
        out_path = Path(__file__).resolve().parent / "buckmaster_fluid_lean_certificate.json"
        out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def main(argv: list[str] | None = None) -> int:
    args = sys.argv[1:] if argv is None else argv
    write_cert = "--write-cert" in args
    res = run_all_audits(write_certificate=write_cert)
    p1 = res["part1_three_repo_lean4_tomography"]
    p2 = res["part2_signed_tree_multifrontal_schur"]
    p3 = res["part3_nov20_weight_and_sperner_box"]
    standalone = p1.get("mode") == "standalone_no_external_clones"
    summary = {
        "probe_id": res["probe_id"],
        "honest_novelty_claim": res["honest_novelty_claim"],
        "zero_floats_certified": res["zero_floats_certified"],
        "lean_tomography_mode": p1.get("mode", "live"),
        "total_lean_files_scanned": p1["total_lean_files_scanned"],
        "total_lean_lines_scanned": p1["total_lean_lines_scanned"],
        "tb_ns_comparator_pass": (
            "standalone_sealed"
            if standalone
            else f"{p1['subprojects']['tb_navier_stokes']['comparator_passed_count']}/{p1['subprojects']['tb_navier_stokes']['comparator_total_count']}"
        ),
        "fluid_lean_decide_plus_kernel": (
            0
            if standalone
            else (
                p1["subprojects"]["tb_fluid_boussinesq"]["decide_plus_kernel_calls"]
                + p1["subprojects"]["tb_fluid_euler"]["decide_plus_kernel_calls"]
            )
        ),
        "tb_ns_decide_plus_kernel": (
            0 if standalone else p1["subprojects"]["tb_navier_stokes"]["decide_plus_kernel_calls"]
        ),
        "exact_tree_global_inertia": p2["exact_multifrontal_tree_with_nullpair"]["global_inertia"],
        "perturbed_tree_global_inertia": p2["perturbed_gershgorin_enclosure_tree"]["global_inertia"],
        "signed_tree_mutants_killed": f"{p2['adversarial_mutants_killed']}/{p2['adversarial_mutants_total']}",
        "kappa19_weight_relaxation": p3["nov20_weight_shift"]["kappa_19_relaxation_factor"],
        "sperner_complete_count": p3["fixed_point_box_sperner_2d"]["complete_sperner_simplex_count"],
        "r3_controls": f"{res['part4_r3_negative_controls']['controls_passed']}/{res['part4_r3_negative_controls']['controls_total']}",
        "canonical_sha256": res["canonical_sha256"],
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
