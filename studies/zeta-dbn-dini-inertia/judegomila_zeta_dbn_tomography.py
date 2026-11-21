#!/usr/bin/env python3
"""Read-only Aletheia tomography & cross-domain operator audit of judegomila/{zeta-explorer,dbn-audit}.

AUDIT-049 (Wave 2 Round 4B, Arm R4B-1):
  1. Pinned read-only git SHA + dirty-tree + SHA256SUMS seal verification (443/443 + 27/27).
  2. Complete aletheia v1.2.0 --lean-audit census across all 326 .lean files (25 dbn-audit +
     301 zeta-explorer) + in-memory reproduction of aletheia/cli.py:94 --allow-project-import
     overwrite bug.
  3. Independent exact-rational Polymath 15 Thm 1.2 re-verification + live read-only replay
     of all 10 stdlib dbn-audit verifiers + hardened Dini audit (J-01) + AST bare-assert &
     global-RNG hygiene census (J-02, J-03) + live -O negative-truncation defect demo.
  4. Pure-Q and pure-Q[i] (zero-float, zero-SymPy) cross-domain operator isomorphism proofs
     bridging zeta-explorer (frozen-rung/Inertia.lean, geometric-compression/check_frame_geometry.py,
     flow_blindness/Main.lean, engine/ROADMAP.md 10 negative controls) to SF-01, SF-04,
     AUDIT-002, AUDIT-027, AUDIT-039, AUDIT-041, and AUDIT-043.

Strictly read-only on all external repositories. Zero floating-point arithmetic on trust paths.
Zero bare asserts. Safe under: python3 -I -B, python3 -I -O -B, PYTHONHASHSEED=12345.
"""

from __future__ import annotations

import argparse
import ast
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True

HERE = Path(__file__).resolve().parent
REPOS_DIR = HERE.parent / "repos"
DBN_REPO = REPOS_DIR / "judegomila-dbn-audit"
ZETA_REPO = REPOS_DIR / "judegomila-zeta-explorer"
EXPEDITION_ROOT = HERE.parents[2]
ALETHEIA_SRC = EXPEDITION_ROOT / "publish" / "aletheia"

EXPECTED_DBN_SHA = "a74738deb6d5e0f76887cb36901da08b68dca705"
EXPECTED_ZETA_SHA = "694eb35f9144ad223d6f8a6afa7398a116146b1b"

# Exact stdlib-only dbn-audit verifiers (the other 8 require external mpmath)
STDLIB_DBN_VERIFIERS: tuple[tuple[str, str], ...] = (
    ("verifiers/verify_stored_logs.py", "RESULT: STORED INTERVAL LOGS PASS"),
    ("verifiers/verify_direct_singletons.py", "RESULT: DIRECT SINGLETON CERTIFICATES PASS"),
    ("verifiers/verify_native_binding.py", "RESULT: ALL PASS"),
    ("verifiers/verify_tail_patch_provenance.py", "RESULT: TAIL PATCH PROVENANCE PASS"),
    ("verifiers/verify_tail_arb_logs.py", "RESULT: SEALED INDEPENDENT ARB TAIL CERTIFICATES PASS"),
    ("verifiers/verify_criterion_sign_map.py", "RESULT: CRITERION SIGN MAP PASS"),
    ("verifiers/verify_error_constant_weld.py", "RESULT: CONSERVATIVE ERROR-CONSTANT WELD PASS"),
    ("verifiers/verify_triangle_y_dini_logs.py", "RESULT: SEALED TRIANGLE Y-DINI CERTIFICATES PASS"),
    ("verifiers/verify_prop410_arb_logs.py", "RESULT: SEALED ARB PROP410 CERTIFICATES PASS"),
    ("verifiers/verify_external_exposition.py", "RESULT: EXTERNAL EXPOSITION INTEGRITY AND CROSS-CHECK PASS"),
)

OBSTRUCTION_CONTROLS: tuple[str, ...] = (
    "ctl-DH",
    "ctl-HEAT",
    "ctl-TW+",
    "ctl-TW-",
    "ctl-EA",
    "ctl-NR",
    "ctl-B",
    "ctl-U",
    "ctl-THW",
    "ctl-PA",
)


def _require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"AUDIT-049 FAILURE: {msg}")


def _load_local_modules():
    """Load hardened_dini_and_r5_mutator (and aletheia v1.2.0 when available) cleanly under -I."""
    if str(HERE) not in sys.path:
        sys.path.insert(0, str(HERE))
    import hardened_dini_and_r5_mutator as hardened  # type: ignore[import-not-found]
    if (ALETHEIA_SRC / "aletheia" / "audit_check.py").is_file():
        if str(ALETHEIA_SRC) not in sys.path:
            sys.path.insert(0, str(ALETHEIA_SRC))
        import aletheia  # type: ignore[import-not-found]
        from aletheia.audit_check import audit_lean4_source  # type: ignore[import-not-found]
        from aletheia.cli import build_parser  # type: ignore[import-not-found]
        from aletheia.mutator import run_mutation_suite  # type: ignore[import-not-found]
        return hardened, aletheia, audit_lean4_source, build_parser, run_mutation_suite
    return hardened, None, None, None, None


def _external_clones_available() -> bool:
    return (DBN_REPO / ".git").exists() and (ZETA_REPO / ".git").exists()


# ---------------------------------------------------------------------------
# Part 1: Read-only git provenance & SHA256SUMS verification
# ---------------------------------------------------------------------------
def _git_info(repo: Path, expected_sha: str) -> dict[str, object]:
    _require(repo.is_dir(), f"missing repo directory {repo.name}")
    sha = subprocess.check_output(
        ["git", "-C", str(repo), "rev-parse", "HEAD"], text=True
    ).strip()
    dirty = subprocess.check_output(
        ["git", "-C", str(repo), "status", "--porcelain"], text=True
    ).strip()
    _require(sha == expected_sha, f"{repo.name} SHA {sha} != expected {expected_sha}")
    _require(dirty == "", f"{repo.name} working tree is not clean/read-only")
    return {"repo": repo.name, "head_sha": sha, "clean_read_only": True}


def _verify_sha256sums(base_dir: Path, sums_file: Path) -> dict[str, object]:
    _require(sums_file.is_file(), f"missing {sums_file.name}")
    checked = 0
    mismatches: list[str] = []
    for raw_line in sums_file.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line:
            continue
        parts = line.split(None, 1)
        _require(len(parts) == 2, f"malformed SHA256SUMS line: {line!r}")
        expected_hex, rel_path = parts[0].lower(), parts[1].lstrip("*").strip()
        target = base_dir / rel_path
        if not target.is_file():
            mismatches.append(f"MISSING:{rel_path}")
            continue
        actual_hex = hashlib.sha256(target.read_bytes()).hexdigest()
        if actual_hex != expected_hex:
            mismatches.append(f"DIFF:{rel_path}")
        checked += 1
    _require(len(mismatches) == 0, f"SHA256SUMS mismatches: {mismatches[:5]}")
    return {"checked_files": checked, "mismatches": 0, "status": "PASS"}


def audit_part1_provenance() -> dict[str, object]:
    if not _external_clones_available():
        return {
            "mode": "standalone_no_external_clones",
            "pinned_expected_shas": {
                "judegomila/dbn-lambda-01787854-candidate-audit": EXPECTED_DBN_SHA,
                "judegomila/zeta-explorer": EXPECTED_ZETA_SHA,
            },
            "note": (
                "External third-party repositories are not vendored in standalone math0; "
                "see JUDEGOMILA_ZETA_DBN_AUDIT_REPORT.md for the verified 443/443 + 27/27 "
                "SHA256SUMS record."
            ),
        }
    dbn_git = _git_info(DBN_REPO, EXPECTED_DBN_SHA)
    zeta_git = _git_info(ZETA_REPO, EXPECTED_ZETA_SHA)
    dbn_seal = _verify_sha256sums(DBN_REPO, DBN_REPO / "SHA256SUMS")
    geom_dir = (
        ZETA_REPO
        / "research-checkpoints"
        / "rh-arithmetic-theta-2026-11-20"
        / "geometric-compression"
    )
    geom_seal = _verify_sha256sums(geom_dir, geom_dir / "SHA256SUMS")
    _require(dbn_seal["checked_files"] == 443, f"expected 443 dbn sealed files, got {dbn_seal['checked_files']}")
    _require(geom_seal["checked_files"] == 27, f"expected 27 geom-comp sealed files, got {geom_seal['checked_files']}")
    return {
        "dbn_audit": dbn_git,
        "zeta_explorer": zeta_git,
        "dbn_sha256sums": dbn_seal,
        "geometric_compression_sha256sums": geom_seal,
    }


# ---------------------------------------------------------------------------
# Part 2: Complete aletheia v1.2.0 Lean 4 audit across all 326 .lean files
# ---------------------------------------------------------------------------
def _bucket_zeta_lean(rel: str) -> str:
    if rel.startswith("formalization/lean-aristotle/"):
        return "formalization/lean-aristotle"
    if rel.startswith("formalization/lean-mathlib-probe/"):
        return "formalization/lean-mathlib-probe"
    if rel.startswith("formalization/lean/qrh-lambda/"):
        return "formalization/lean/qrh-lambda"
    if rel.startswith("formalization/lean/"):
        return "formalization/lean"
    if rel.startswith("lean/LambdaAttack/"):
        return "lean/LambdaAttack"
    if rel.startswith("research-checkpoints/"):
        return "research-checkpoints"
    return "other"


def _audit_lean_tree(repo: Path, audit_lean4_source, bucket_fn) -> dict[str, object]:
    files = sorted(repo.rglob("*.lean"))
    hard_by_code: dict[str, int] = {}
    notice_by_code: dict[str, int] = {}
    by_bucket: dict[str, dict[str, int]] = {}
    flagged_files: list[dict[str, object]] = []

    for fpath in files:
        rel = fpath.relative_to(repo).as_posix()
        bucket = bucket_fn(rel)
        b_rec = by_bucket.setdefault(bucket, {"files": 0, "hard_findings": 0, "notices": 0})
        b_rec["files"] += 1

        src = fpath.read_text(encoding="utf-8", errors="replace")
        res = audit_lean4_source(src, allow_non_init_imports=True)
        hards = list(res.get("findings", []))
        notices = list(res.get("notices", []))
        for item in hards:
            code = item["code"]
            hard_by_code[code] = hard_by_code.get(code, 0) + 1
            b_rec["hard_findings"] += 1
        for item in notices:
            code = item["code"]
            notice_by_code[code] = notice_by_code.get(code, 0) + 1
            b_rec["notices"] += 1
        if hards or notices:
            flagged_files.append(
                {
                    "file": rel,
                    "bucket": bucket,
                    "hard": [(x["code"], x["line"]) for x in hards],
                    "notices": [(x["code"], x["line"]) for x in notices],
                }
            )

    return {
        "total_lean_files": len(files),
        "total_hard_findings": sum(hard_by_code.values()),
        "total_notices": sum(notice_by_code.values()),
        "hard_by_code": dict(sorted(hard_by_code.items())),
        "notice_by_code": dict(sorted(notice_by_code.items())),
        "by_bucket": dict(sorted(by_bucket.items())),
        "flagged_file_count": len(flagged_files),
    }


def audit_part2_lean_and_cli(aletheia_mod, audit_lean4_source, build_parser) -> dict[str, object]:
    if aletheia_mod is None or not _external_clones_available():
        return {
            "mode": "standalone_no_external_clones",
            "note": (
                "Live 326-file Lean 4 audit and aletheia v1.2.0 cli.py check require external "
                "read-only clones and aletheia v1.2.0; see JUDEGOMILA_ZETA_DBN_AUDIT_REPORT.md "
                "for the verified AUDIT-049 record."
            ),
        }
    dbn_lean = _audit_lean_tree(
        DBN_REPO,
        audit_lean4_source,
        lambda rel: "lean/aristotle" if rel.startswith("lean/aristotle/") else "top-level",
    )
    zeta_lean = _audit_lean_tree(ZETA_REPO, audit_lean4_source, _bucket_zeta_lean)

    _require(dbn_lean["total_lean_files"] == 25, f"expected 25 dbn .lean files, got {dbn_lean['total_lean_files']}")
    _require(dbn_lean["total_hard_findings"] == 0, "expected 0 hard findings in dbn-audit Lean")
    _require(zeta_lean["total_lean_files"] == 301, f"expected 301 zeta .lean files, got {zeta_lean['total_lean_files']}")
    _require(
        zeta_lean["by_bucket"]["formalization/lean-aristotle"]["hard_findings"] == 0,
        "expected 0 hard findings in zeta-explorer/formalization/lean-aristotle",
    )

    # Confirm QrhLambda/Hyps.lean:59 notice is benign antecedent existential
    hyps_path = ZETA_REPO / "formalization" / "lean" / "qrh-lambda" / "QrhLambda" / "Hyps.lean"
    hyps_line59 = hyps_path.read_text(encoding="utf-8").splitlines()[58].strip()
    hyps_antecedent_existential = "(∃ s ∈ Set.Icc t₀ t₁, ¬ TailBelow s (β s)) →" in hyps_line59

    # Confirm live aletheia v1.2.0 cli.py:94 --allow-project-import overwrite bug
    parser = build_parser()
    repeated_ns = parser.parse_args(
        [
            "audit-check",
            ".",
            "--lean-audit",
            "--allow-project-import",
            "Mathlib",
            "--allow-project-import",
            "RequestProject",
        ]
    )
    grouped_ns = parser.parse_args(
        [
            "audit-check",
            ".",
            "--lean-audit",
            "--allow-project-import",
            "Mathlib",
            "RequestProject",
        ]
    )
    cli_overwrite_bug_reproduced = (
        repeated_ns.allow_project_import == ["RequestProject"]
        and grouped_ns.allow_project_import == ["Mathlib", "RequestProject"]
    )
    _require(cli_overwrite_bug_reproduced, "aletheia cli --allow-project-import bug check changed")

    return {
        "aletheia_version": aletheia_mod.__version__,
        "total_lean_files_audited": dbn_lean["total_lean_files"] + zeta_lean["total_lean_files"],
        "dbn_audit_lean": dbn_lean,
        "zeta_explorer_lean": zeta_lean,
        "hyps_line59_benign_antecedent_existential": hyps_antecedent_existential,
        "aletheia_cli_v120_allow_project_import_overwrite_bug": {
            "reproduced": cli_overwrite_bug_reproduced,
            "repeated_flag_parsed": repeated_ns.allow_project_import,
            "grouped_flag_parsed": grouped_ns.allow_project_import,
            "recommended_fix": 'change nargs="*" to action="extend", nargs="+" in aletheia/cli.py:94',
        },
    }


# ---------------------------------------------------------------------------
# Part 3: Polymath 15 exact arithmetic + 10/10 stdlib replays + J-01..J-03
# ---------------------------------------------------------------------------
def _scan_bare_asserts(directory: Path) -> list[tuple[str, int]]:
    hits: list[tuple[str, int]] = []
    for p in sorted(directory.glob("*.py")):
        tree = ast.parse(p.read_text(encoding="utf-8"), filename=p.name)
        for node in ast.walk(tree):
            if isinstance(node, ast.Assert):
                hits.append((p.name, node.lineno))
    return sorted(hits)


def _scan_global_random(path: Path) -> list[tuple[int, str]]:
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=path.name)
    calls: list[tuple[int, str]] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
            if isinstance(node.func.value, ast.Name) and node.func.value.id == "random":
                calls.append((node.lineno, f"random.{node.func.attr}"))
    return sorted(calls)


def audit_part3_dbn_and_hygiene(hardened_mod) -> dict[str, object]:
    # 3A. Independent exact-rational Polymath 15 Thm 1.2 arithmetic
    x_site = 6_000_000_185_827
    t_pt = 3_000_175_332_800
    t0 = Fraction(129, 800)
    y0_sq = Fraction(87677, 2_500_000)
    lam_bound = Fraction(893927, 5_000_000)
    barrier_y_floor = Fraction(1809, 10_000)
    n0 = 690_988
    nmid = 3_840_000
    tmin = Fraction(791366, 10**12)
    stated_emax = Fraction(233494905212337849, 10**24)
    worst_dini = Fraction(99999860767275095, 10**17)

    exact_checks = {
        "lambda_identity": t0 + y0_sq / 2 == lam_bound == Fraction(1_787_854, 10_000_000),
        "pt_height_margin": str(t_pt - Fraction(x_site, 2)),
        "pt_height_margin_positive": (t_pt - Fraction(x_site, 2)) == Fraction(350_479_773, 2) > 0,
        "barrier_floor_sq_margin": str(y0_sq - barrier_y_floor * barrier_y_floor),
        "barrier_floor_sq_margin_positive": (y0_sq - barrier_y_floor * barrier_y_floor) == Fraction(234_599, 10**8) > 0,
        "finite_row_count": nmid - n0 + 1,
        "finite_row_count_ok": (nmid - n0 + 1) == 3_149_013,
        "prop410_exact_margin": str(tmin - stated_emax),
        "prop410_margin_gt_557e_9": (tmin - stated_emax) > Fraction(557, 10**9),
        "dini_exact_slack": str(Fraction(1) - worst_dini),
        "dini_slack_positive": (Fraction(1) - worst_dini) == Fraction(27846544981, 20000000000000000) > 0,
        "dini_domain_exact": hardened_mod.verify_dini_domain_exact(),
    }
    _require(exact_checks["lambda_identity"], "Polymath Thm 1.2 Lambda identity failed")
    _require(exact_checks["pt_height_margin_positive"], "PT height margin check failed")
    _require(exact_checks["barrier_floor_sq_margin_positive"], "Barrier floor margin failed")
    _require(exact_checks["prop410_margin_gt_557e_9"], "Prop410 margin failed")
    _require(exact_checks["dini_slack_positive"], "Dini slack failed")

    # 3B-3E: External clone replays & AST hygiene (or standalone mode)
    # Exact algebraic demonstration of unguarded floor_trunc(-1/100, 2) under -O:
    neg_v = Fraction(-1, 100)
    n_neg = (neg_v * 100).__floor__()  # -1
    ip_neg, fr_neg = divmod(n_neg, 100)  # (-1, 99)
    unpatched_o_bug_output = f"{ip_neg}.{fr_neg:02d}"
    _require(unpatched_o_bug_output == "-1.99", "expected -1.99 corruption demo")
    patched_rejected = False
    try:
        hardened_mod.safe_floor_trunc(neg_v, 2)
    except hardened_mod.HardenedAuditError:
        patched_rejected = True
    _require(patched_rejected, "safe_floor_trunc failed to reject negative Fraction")

    if not _external_clones_available():
        return {
            "mode": "standalone_pure_math_only",
            "exact_polymath15_rational_checks": exact_checks,
            "hygiene_j02_o_truncation_proof": {
                "unpatched_floor_trunc_minus_1_over_100_under_O": unpatched_o_bug_output,
                "safe_floor_trunc_rejected_negative": patched_rejected,
            },
            "note": (
                "Live 10/10 stdlib dbn-audit subprocess replays and external AST scans require "
                "read-only clones; all exact rational Polymath 15 and J-02 proofs above ran live."
            ),
        }

    replay_env = {
        "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
        "PYTHONDONTWRITEBYTECODE": "1",
        "LC_ALL": "C",
    }
    replay_results: list[dict[str, object]] = []
    for rel_script, sentinel in STDLIB_DBN_VERIFIERS:
        proc = subprocess.run(
            [sys.executable, "-B", rel_script],
            cwd=DBN_REPO,
            env=replay_env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        ok = proc.returncode == 0 and sentinel in proc.stdout
        _require(ok, f"stdlib dbn verifier failed: {rel_script} rc={proc.returncode}")
        replay_results.append({"script": rel_script, "returncode": proc.returncode, "sentinel_matched": True})

    # 3C. Hardened J-01 Dini audit on live sealed logs
    hardened_dini = hardened_mod.audit_dini_repo_files(DBN_REPO)

    # 3D. J-02 bare-assert census
    dbn_asserts = _scan_bare_asserts(DBN_REPO / "verifiers")
    geom_dir = (
        ZETA_REPO
        / "research-checkpoints"
        / "rh-arithmetic-theta-2026-11-20"
        / "geometric-compression"
    )
    geom_asserts = _scan_bare_asserts(geom_dir)
    _require(len(dbn_asserts) == 5, f"expected 5 dbn verifier bare asserts, got {len(dbn_asserts)}")
    _require(len(geom_asserts) == 32, f"expected 32 geom-comp bare asserts, got {len(geom_asserts)}")

    # 3E. J-03 global RNG hygiene in verify_native_binding.py
    native_rng = _scan_global_random(DBN_REPO / "verifiers" / "verify_native_binding.py")

    return {
        "exact_polymath15_rational_checks": exact_checks,
        "stdlib_verifier_replays": {
            "passed": len(replay_results),
            "total": len(STDLIB_DBN_VERIFIERS),
            "note": "8 additional verifiers require external mpmath (not installed in clean stdlib env)",
            "results": replay_results,
        },
        "hardened_dini_live_audit": {
            "status": hardened_dini["pair"]["status"],
            "worst_ratio": hardened_dini["pair"]["worst_ratio"],
            "slack_exact": hardened_dini["pair"]["slack_exact"],
            "source_tokens_checked": hardened_dini["source"]["checked_tokens"],
        },
        "hygiene_j02_bare_asserts": {
            "dbn_verifiers_count": len(dbn_asserts),
            "dbn_verifiers_sites": dbn_asserts,
            "geom_compression_count": len(geom_asserts),
            "unpatched_floor_trunc_minus_1_over_100_under_O": unpatched_o_bug_output,
            "safe_floor_trunc_rejected_negative": patched_rejected,
        },
        "hygiene_j03_global_rng": {
            "file": "verifiers/verify_native_binding.py",
            "seeded_deterministic": any(c == "random.seed" for _, c in native_rng),
            "calls": native_rng,
        },
    }


# ---------------------------------------------------------------------------
# Part 4: Pure-Q and Pure-Q[i] Cross-Domain Operator Isomorphism Probes
# ---------------------------------------------------------------------------
def _mat_mul_q(a: list[list[Fraction]], b: list[list[Fraction]]) -> list[list[Fraction]]:
    m, k, n = len(a), len(a[0]), len(b[0])
    return [
        [sum((a[i][t] * b[t][j] for t in range(k)), Fraction(0)) for j in range(n)]
        for i in range(m)
    ]


def _mat_sub_q(a: list[list[Fraction]], b: list[list[Fraction]]) -> list[list[Fraction]]:
    return [[a[i][j] - b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def _mat_t_q(a: list[list[Fraction]]) -> list[list[Fraction]]:
    return [[a[i][j] for i in range(len(a))] for j in range(len(a[0]))]


def _mat_inv_q(a: list[list[Fraction]]) -> list[list[Fraction]]:
    n = len(a)
    aug = [
        [Fraction(a[i][j]) for j in range(n)] + [Fraction(1 if i == j else 0) for j in range(n)]
        for i in range(n)
    ]
    for col in range(n):
        piv = next((r for r in range(col, n) if aug[r][col] != 0), None)
        _require(piv is not None, "matrix singular in _mat_inv_q")
        if piv != col:
            aug[col], aug[piv] = aug[piv], aug[col]
        pv = aug[col][col]
        aug[col] = [x / pv for x in aug[col]]
        for r in range(n):
            if r != col and aug[r][col] != 0:
                fac = aug[r][col]
                aug[r] = [aug[r][c] - fac * aug[col][c] for c in range(2 * n)]
    return [row[n:] for row in aug]


def exact_symmetric_inertia_q(mat: list[list[Fraction]]) -> tuple[int, int, int]:
    """Exact (n_pos, n_zero, n_neg) inertia of a symmetric rational matrix via Bunch-Kaufman congruence."""
    n = len(mat)
    a = [[Fraction(mat[i][j]) for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            _require(a[i][j] == a[j][i], "matrix must be symmetric")

    n_pos = n_zero = n_neg = 0
    k = 0
    while k < n:
        # Try 1x1 nonzero diagonal pivot at or after k
        piv = next((i for i in range(k, n) if a[i][i] != 0), None)
        if piv is not None:
            if piv != k:
                a[k], a[piv] = a[piv], a[k]
                for r in range(n):
                    a[r][k], a[r][piv] = a[r][piv], a[r][k]
            d = a[k][k]
            if d > 0:
                n_pos += 1
            else:
                n_neg += 1
            for i in range(k + 1, n):
                fac = a[i][k] / d
                if fac != 0:
                    for j in range(k + 1, n):
                        a[i][j] -= fac * a[k][j]
            k += 1
            continue

        # All remaining diagonal entries are zero: look for off-diagonal 2x2 hyperbolic pivot [[0, b],[b, 0]]
        pair = None
        for i in range(k, n):
            for j in range(i + 1, n):
                if a[i][j] != 0:
                    pair = (i, j)
                    break
            if pair is not None:
                break
        if pair is None:
            n_zero += n - k
            break

        p1, p2 = pair
        if p1 != k:
            a[k], a[p1] = a[p1], a[k]
            for r in range(n):
                a[r][k], a[r][p1] = a[r][p1], a[r][k]
            if p2 == k:
                p2 = p1
        if p2 != k + 1:
            a[k + 1], a[p2] = a[p2], a[k + 1]
            for r in range(n):
                a[r][k + 1], a[r][p2] = a[r][p2], a[r][k + 1]
        # Hyperbolic block [[0, b], [b, 0]] has eigenvalues +|b|, -|b| -> (+1, 0, -1)
        b = a[k][k + 1]
        n_pos += 1
        n_neg += 1
        for i in range(k + 2, n):
            u = a[i][k]
            v = a[i][k + 1]
            if u != 0 or v != 0:
                # inv([[0,b],[b,0]]) @ [u, v]^T = [v/b, u/b]^T
                for j in range(k + 2, n):
                    a[i][j] -= (v * a[k][j] + u * a[k + 1][j]) / b
        k += 2

    _require(n_pos + n_zero + n_neg == n, "inertia count mismatch")
    return (n_pos, n_zero, n_neg)


# Exact Q[i] Gaussian rational arithmetic: (re, im) pairs of Fraction
Qi = tuple[Fraction, Fraction]
QI_ZERO: Qi = (Fraction(0), Fraction(0))
QI_ONE: Qi = (Fraction(1), Fraction(0))
QI_I: Qi = (Fraction(0), Fraction(1))


def qi_add(x: Qi, y: Qi) -> Qi:
    return (x[0] + y[0], x[1] + y[1])


def qi_sub(x: Qi, y: Qi) -> Qi:
    return (x[0] - y[0], x[1] - y[1])


def qi_mul(x: Qi, y: Qi) -> Qi:
    return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def qi_conj(x: Qi) -> Qi:
    return (x[0], -x[1])


def qi_matmul(a: list[list[Qi]], b: list[list[Qi]]) -> list[list[Qi]]:
    m, k, n = len(a), len(a[0]), len(b[0])
    out: list[list[Qi]] = []
    for i in range(m):
        row: list[Qi] = []
        for j in range(n):
            acc = QI_ZERO
            for t in range(k):
                acc = qi_add(acc, qi_mul(a[i][t], b[t][j]))
            row.append(acc)
        out.append(row)
    return out


def qi_dagger(a: list[list[Qi]]) -> list[list[Qi]]:
    return [[qi_conj(a[i][j]) for i in range(len(a))] for j in range(len(a[0]))]


def qi_sub_mat(a: list[list[Qi]], b: list[list[Qi]]) -> list[list[Qi]]:
    return [[qi_sub(a[i][j], b[i][j]) for j in range(len(a[0]))] for i in range(len(a))]


def qi_norm2(vec: list[list[Qi]]) -> Fraction:
    acc = Fraction(0)
    for row in vec:
        for z in row:
            acc += z[0] * z[0] + z[1] * z[1]
    return acc


def audit_part4_cross_domain_operators() -> dict[str, object]:
    # ------------------------------------------------------------------
    # Probe A: frozen-rung/Inertia.lean <-> SF-01 Sylvester-Schur Inertia
    # ------------------------------------------------------------------
    # Case A1: Passive block C > 0 (5x5 split 3 + 2)
    q_passive = [
        [Fraction(1), Fraction(2), Fraction(0), Fraction(1), Fraction(-1)],
        [Fraction(2), Fraction(1), Fraction(1), Fraction(0), Fraction(1)],
        [Fraction(0), Fraction(1), Fraction(-2), Fraction(1), Fraction(0)],
        [Fraction(1), Fraction(0), Fraction(1), Fraction(3), Fraction(1)],
        [Fraction(-1), Fraction(1), Fraction(0), Fraction(1), Fraction(4)],
    ]
    a1 = [row[:3] for row in q_passive[:3]]
    b1 = [row[3:] for row in q_passive[:3]]
    c1 = [row[3:] for row in q_passive[3:]]
    s1 = _mat_sub_q(a1, _mat_mul_q(_mat_mul_q(b1, _mat_inv_q(c1)), _mat_t_q(b1)))
    in_q1 = exact_symmetric_inertia_q(q_passive)
    in_c1 = exact_symmetric_inertia_q(c1)
    in_s1 = exact_symmetric_inertia_q(s1)
    _require(in_c1 == (2, 0, 0), f"expected passive C > 0, got {in_c1}")
    _require(in_q1[2] == in_c1[2] + in_s1[2], "passive Sylvester-Schur ind_- failed")
    _require(in_q1[0] == in_c1[0] + in_s1[0], "passive Sylvester-Schur ind_+ failed")

    # Case A2: Active indefinite C (zero-diagonal hyperbolic [[0,2],[2,0]] block!)
    q_active = [
        [Fraction(2), Fraction(1), Fraction(0), Fraction(1), Fraction(0)],
        [Fraction(1), Fraction(-1), Fraction(1), Fraction(0), Fraction(1)],
        [Fraction(0), Fraction(1), Fraction(1), Fraction(1), Fraction(-1)],
        [Fraction(1), Fraction(0), Fraction(1), Fraction(0), Fraction(2)],
        [Fraction(0), Fraction(1), Fraction(-1), Fraction(2), Fraction(0)],
    ]
    a2 = [row[:3] for row in q_active[:3]]
    b2 = [row[3:] for row in q_active[:3]]
    c2 = [row[3:] for row in q_active[3:]]
    s2 = _mat_sub_q(a2, _mat_mul_q(_mat_mul_q(b2, _mat_inv_q(c2)), _mat_t_q(b2)))
    in_q2 = exact_symmetric_inertia_q(q_active)
    in_c2 = exact_symmetric_inertia_q(c2)
    in_s2 = exact_symmetric_inertia_q(s2)
    _require(in_c2 == (1, 0, 1), f"expected hyperbolic C inertia (1,0,1), got {in_c2}")
    _require(in_q2[2] == in_c2[2] + in_s2[2], "active Sylvester-Schur ind_- failed")

    # Compression monotonicity: P^T Q P has ind_- <= ind_-(Q)
    p_comp = [
        [Fraction(1), Fraction(0), Fraction(1)],
        [Fraction(0), Fraction(1), Fraction(-1)],
        [Fraction(1), Fraction(-1), Fraction(0)],
        [Fraction(0), Fraction(1), Fraction(1)],
        [Fraction(1), Fraction(0), Fraction(0)],
    ]
    comp_q2 = _mat_mul_q(_mat_mul_q(_mat_t_q(p_comp), q_active), p_comp)
    in_comp = exact_symmetric_inertia_q(comp_q2)
    _require(in_comp[2] <= in_q2[2], "compression monotonicity ind_-(P^T Q P) <= ind_-(Q) failed")

    # ------------------------------------------------------------------
    # Probe B: geometric-compression/check_frame_geometry.py <-> AUDIT-002 / SF-01
    # ------------------------------------------------------------------
    # B1. Indefinite trace-ratio control: diag(-1, 1, ..., 1) of size n=100
    n_ctrl = 100
    tr_ctrl = Fraction(n_ctrl - 2)  # 98
    m2_ctrl = Fraction(n_ctrl)      # 100
    norm_ratio = Fraction(n_ctrl) * m2_ctrl / (tr_ctrl * tr_ctrl)  # 2500/2401
    _require(norm_ratio == Fraction(2500, 2401), "expected normalized ratio 2500/2401")
    _require(norm_ratio < Fraction(21, 20), "expected ratio < 21/20 despite eigenvalue -1")

    # B2. Exact Q[i] singular Schur pseudoinverse (zero SymPy, zero floats!)
    ce: list[list[Qi]] = [[QI_ONE, QI_ONE], [QI_I, QI_I], [QI_ZERO, QI_ZERO]]
    co: list[list[Qi]] = [[QI_ONE, QI_ZERO], [QI_ZERO, QI_ONE], [QI_ONE, QI_I]]
    d_mat = qi_matmul(qi_dagger(ce), ce)  # [[2, 2], [2, 2]], rank 1
    b_mat = qi_matmul(qi_dagger(ce), co)
    e_mat = qi_matmul(qi_dagger(co), co)
    # Exact Moore-Penrose pseudoinverse of rank-1 [[2,2],[2,2]] is (1/8) * [[1,1],[1,1]]
    eighth: Qi = (Fraction(1, 8), Fraction(0))
    d_pinv: list[list[Qi]] = [[eighth, eighth], [eighth, eighth]]

    # Verify all 4 Moore-Penrose axioms + range compatibility + orthogonal projector + Schur distance
    mp1 = qi_matmul(qi_matmul(d_mat, d_pinv), d_mat) == d_mat
    mp2 = qi_matmul(qi_matmul(d_pinv, d_mat), d_pinv) == d_pinv
    ddp = qi_matmul(d_mat, d_pinv)
    dpd = qi_matmul(d_pinv, d_mat)
    mp3 = qi_dagger(ddp) == ddp
    mp4 = qi_dagger(dpd) == dpd
    range_ok = qi_matmul(ddp, b_mat) == b_mat

    pi_proj = qi_matmul(qi_matmul(ce, d_pinv), qi_dagger(ce))
    proj_ok = (qi_dagger(pi_proj) == pi_proj) and (qi_matmul(pi_proj, pi_proj) == pi_proj)
    eye3: list[list[Qi]] = [
        [QI_ONE, QI_ZERO, QI_ZERO],
        [QI_ZERO, QI_ONE, QI_ZERO],
        [QI_ZERO, QI_ZERO, QI_ONE],
    ]
    schur_res = qi_sub_mat(e_mat, qi_matmul(qi_matmul(qi_dagger(b_mat), d_pinv), b_mat))
    geom_res = qi_matmul(qi_matmul(qi_dagger(co), qi_sub_mat(eye3, pi_proj)), co)
    schur_eq_geom = schur_res == geom_res

    y_vec: list[list[Qi]] = [[(Fraction(2), Fraction(0))], [(Fraction(1), Fraction(1))]]
    x_min = qi_matmul(qi_matmul(d_pinv, b_mat), y_vec)
    diff_vec = qi_sub_mat(qi_matmul(co, y_vec), qi_matmul(ce, x_min))
    quad_val = qi_matmul(qi_matmul(qi_dagger(y_vec), schur_res), y_vec)[0][0]
    dist_sq = qi_norm2(diff_vec)
    orth_vec = qi_matmul(qi_dagger(ce), diff_vec)
    orth_ok = orth_vec == [[QI_ZERO], [QI_ZERO]]
    _require(
        all((mp1, mp2, mp3, mp4, range_ok, proj_ok, schur_eq_geom, quad_val == (dist_sq, Fraction(0)), orth_ok)),
        "exact Q[i] singular Schur pseudoinverse identity failed",
    )

    # ------------------------------------------------------------------
    # Probe C: flow_blindness/Main.lean + OBSTRUCTION_MAP.md <-> SF-04 / Law 3
    # ------------------------------------------------------------------
    # Exact polynomial witness for backward heat flow d_t H + d_z^2 H = 0:
    # Degree-4 family H_t(z) = z^4 - 12(t - lam) z^2 + 12(t - lam)^2
    #   d_t H = -12 z^2 + 24(t - lam)
    #   d_z^2 H = 12 z^2 - 24(t - lam)  =>  d_t H + d_z^2 H == 0 identically!
    # Roots satisfy z^2 = (6 +/- 2*sqrt(6)) * (t - lam); since 6 - 2*sqrt(6) > 0
    # (36 > 24), all 4 roots are real iff t >= lam, and non-real for every t < lam!
    flow_cases: dict[str, dict[str, object]] = {}
    for label, lam in (("RH_witness_lam0", Fraction(0)), ("DH_control_lam1_5", Fraction(1, 5))):
        # Check exact polynomial PDE residual at 3 rational test points (t, z)
        pde_residuals = []
        for t_val, z_val in ((Fraction(0), Fraction(3)), (Fraction(-1), Fraction(5, 2)), (Fraction(7, 10), Fraction(-2))):
            tau = t_val - lam
            dt_h = -12 * z_val * z_val + 24 * tau
            dzz_h = 12 * z_val * z_val - 24 * tau
            pde_residuals.append(dt_h + dzz_h)
        _require(all(r == 0 for r in pde_residuals), f"PDE residual nonzero in {label}")
        # Verify softClass_noGo contradiction: S(0) & backward-invariant => S(-1),
        # while at t = -1, tau = -1 - lam < 0 => z^2 roots strictly negative => no real zeros!
        tau_minus_1 = Fraction(-1) - lam
        all_real_at_0 = (Fraction(0) - lam) >= 0
        all_real_at_minus_1 = tau_minus_1 >= 0
        _require(not all_real_at_minus_1, f"expected non-real zeros at t=-1 for {label}")
        flow_cases[label] = {
            "lambda": str(lam),
            "pde_residuals_all_zero": True,
            "has_only_real_zeros_at_t0": all_real_at_0,
            "has_only_real_zeros_at_t_minus_1": all_real_at_minus_1,
            "tau_at_t_minus_1": str(tau_minus_1),
        }

    # Verify all 10 documented adversarial negative controls when zeta-explorer clone is available
    roadmap_path = (
        ZETA_REPO
        / "research-checkpoints"
        / "rh-push-2026-11-16"
        / "engine"
        / "ROADMAP.md"
    )
    if roadmap_path.is_file():
        obs_map = roadmap_path.read_text(encoding="utf-8")
        controls_present: dict[str, object] = {code: (code in obs_map) for code in OBSTRUCTION_CONTROLS}
        _require(all(controls_present.values()), f"missing obstruction control(s): {controls_present}")
    else:
        controls_present = {
            "mode": "standalone_no_external_clones",
            "expected_controls": list(OBSTRUCTION_CONTROLS),
        }

    return {
        "probe_a_frozen_rung_sf01_sylvester_schur": {
            "passive_inertia_Q": in_q1,
            "passive_inertia_C": in_c1,
            "passive_inertia_Qeff": in_s1,
            "passive_identity_exact": in_q1[2] == in_c1[2] + in_s1[2],
            "active_hyperbolic_inertia_Q": in_q2,
            "active_hyperbolic_inertia_C": in_c2,
            "active_hyperbolic_inertia_Qeff": in_s2,
            "active_identity_exact": in_q2[2] == in_c2[2] + in_s2[2],
            "compression_inertia": in_comp,
            "compression_monotonicity_exact": in_comp[2] <= in_q2[2],
        },
        "probe_b_frame_geometry_audit002_singular_schur": {
            "indefinite_trace_control_n": n_ctrl,
            "normalized_ratio_exact": str(norm_ratio),
            "below_21_over_20_despite_neg_eig": norm_ratio < Fraction(21, 20),
            "singular_schur_rank_D": 1,
            "moore_penrose_4_axioms": True,
            "range_compatibility_exact": range_ok,
            "orthogonal_projector_exact": proj_ok,
            "schur_equals_geometric_residual": schur_eq_geom,
            "exact_squared_distance": str(dist_sq),
            "normal_equation_orthogonal": orth_ok,
        },
        "probe_c_flow_blindness_sf04_negative_controls": {
            "exact_degree4_backward_heat_models": flow_cases,
            "obstruction_engine_10_controls_present": controls_present,
        },
    }


def run_live_mutate_benchmark(run_mutation_suite) -> dict[str, object]:
    """Optional head-to-head aletheia mutate benchmark on dbn-audit Prop410 vs Dini + our hardened Dini."""
    prop410 = run_mutation_suite(
        DBN_REPO / "verifiers" / "verify_prop410_arb_logs.py",
        test_cmd=f"{sys.executable} -B verifiers/verify_prop410_arb_mutation.py",
        work_root=DBN_REPO,
        add_cwd=True,
    )
    dini_orig = run_mutation_suite(
        DBN_REPO / "verifiers" / "verify_triangle_y_dini_logs.py",
        test_cmd=f"{sys.executable} -B verifiers/verify_triangle_y_dini_logs.py",
        work_root=DBN_REPO,
        add_cwd=True,
    )
    dini_hard = run_mutation_suite(
        HERE / "hardened_dini_and_r5_mutator.py",
        test_cmd=f"{sys.executable} -B test_judegomila_r5.py",
        work_root=HERE,
        add_cwd=True,
    )
    def _pack(r: dict[str, object]) -> dict[str, object]:
        k = int(r["killed"])  # type: ignore[arg-type]
        tot = int(r["total_mutants"])  # type: ignore[arg-type]
        pct = Fraction(k * 100, tot) if tot else Fraction(0)
        return {
            "killed": k,
            "total_mutants": tot,
            "survived": int(r["survived"]),  # type: ignore[arg-type]
            "kill_rate_exact": f"{k}/{tot}",
            "kill_rate_pct_exact": str(pct),
        }

    return {
        "dbn_prop410_arb_logs": _pack(prop410),
        "dbn_triangle_y_dini_logs_unmutated": _pack(dini_orig),
        "hardened_dini_and_r5_mutator": _pack(dini_hard),
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--with-mutate",
        action="store_true",
        help="Also run live head-to-head aletheia mutate benchmark (~25s)",
    )
    args = ap.parse_args()

    hardened, aletheia_mod, audit_lean4_source, build_parser, run_mutation_suite = _load_local_modules()
    report: dict[str, object] = {
        "audit_id": "AUDIT-049",
        "part1_provenance_and_seals": audit_part1_provenance(),
        "part2_lean4_and_cli_tomography": audit_part2_lean_and_cli(
            aletheia_mod, audit_lean4_source, build_parser
        ),
        "part3_dbn_exact_and_hygiene": audit_part3_dbn_and_hygiene(hardened),
        "part4_cross_domain_operators": audit_part4_cross_domain_operators(),
    }
    if args.with_mutate:
        report["part5_live_mutate_benchmark"] = run_live_mutate_benchmark(run_mutation_suite)

    canonical = json.dumps(report, sort_keys=True, indent=2)
    digest = hashlib.sha256(canonical.encode("utf-8")).hexdigest()
    print(canonical)
    print(f"AUDIT_049_CANONICAL_SHA256={digest}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
