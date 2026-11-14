#!/usr/bin/env python3
"""
verify.py — Scoped Verification & Adversarial Tamper Suite
for `research/conservation-quotient-bounds/` (`CrocSwap/integer-mult-bounds`).

Usage:
  python3 -B research/conservation-quotient-bounds/verify.py --check
"""

from __future__ import annotations

import copy
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

# Fail closed on optimized Python (`-O`, `-OO`, `PYTHONOPTIMIZE`)
if sys.flags.optimize > 0 or os.environ.get("PYTHONOPTIMIZE", "").strip() not in ("", "0"):
    sys.stderr.write("FATAL: optimized Python (-O / PYTHONOPTIMIZE) is forbidden.\n")
    sys.exit(2)

PKG_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(PKG_DIR))
import check_certificate  # noqa: E402


FORBIDDEN_LEAN_PATTERNS = [
    ("sorry_token", re.compile(r"\bsorry\b")),
    ("guillemet_sorry", re.compile(r"«sorry»")),
    ("admit_token", re.compile(r"\badmit\b")),
    ("axiom_decl", re.compile(r"\baxiom\b")),
    ("opaque_decl", re.compile(r"\bopaque\b")),
    ("partial_def", re.compile(r"\bpartial\b")),
    ("unsafe_def", re.compile(r"\bunsafe\b")),
    ("native_decide", re.compile(r"\bnative_decide\b")),
    ("csimp_attr", re.compile(r"@\[[^\]]*\bcsimp\b")),
    ("extern_attr", re.compile(r"@\[[^\]]*\bextern\b")),
    ("implemented_by_attr", re.compile(r"@\[[^\]]*\bimplemented_by\b")),
    ("metaprogramming_import", re.compile(r"^\s*import\s+Lean\b", re.MULTILINE)),
]


def strip_lean_comments_and_strings(src: str) -> str:
    """Strip `-- ...` line comments and `/- ... -/` nested block comments before token scanning."""
    out: list[str] = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth == 0 and src[i : i + 2] == "--":
            while i < n and src[i] != "\n":
                i += 1
        elif src[i : i + 2] == "/-":
            depth += 1
            i += 2
        elif depth > 0 and src[i : i + 2] == "-/":
            depth -= 1
            i += 2
        else:
            if depth == 0:
                out.append(src[i])
            i += 1
    if depth != 0:
        raise ValueError("Unclosed `/- ... -/` block comment in Lean file")
    return "".join(out)


def audit_lean_surface(lean_path: Path) -> dict[str, int]:
    raw = lean_path.read_text(encoding="utf-8")
    code = strip_lean_comments_and_strings(raw)
    for name, pat in FORBIDDEN_LEAN_PATTERNS:
        m = pat.search(code)
        if m:
            raise ValueError(f"Forbidden Lean surface vector `{name}` matched: {m.group(0)!r}")
    theorems = re.findall(r"\btheorem\s+([A-Za-z0-9_']+)", code)
    if len(theorems) < 7:
        raise ValueError(f"Expected >= 7 formal theorems in {lean_path.name}, found {len(theorems)}")
    return {"theorems_scanned": len(theorems), "forbidden_hits": 0}


def rehash_cert(c: dict) -> dict:
    d = copy.deepcopy(c)
    d.pop("certificate_sha256", None)
    d["certificate_sha256"] = hashlib.sha256(
        json.dumps(d, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    return d


def run_18_adversarial_controls(base_cert: dict) -> int:
    """Verify 18 distinct semantic & cryptographic tamper vectors all fail closed."""
    mutations: list[tuple[str, callable]] = [
        ("01_bad_sha256", lambda c: {**copy.deepcopy(c), "certificate_sha256": "0" * 64}),
        ("02_float_literal_injected", lambda c: _mut(c, ["pillar_3_power_sum_and_farkas", "farkas_histogram_ceiling", "a_ceiling"], "0.0014")),
        ("03_incomplete_cut_edge_deleted", lambda c: _mut(c, ["pillar_1_cut_rank", "cut_edge_indices"], [6, 8])),
        ("04_cut_capacity_equals_target_rank", lambda c: _mut(c, ["pillar_1_cut_rank", "required_target_rank"], 3)),
        ("05_pq_lattice_inverted", lambda c: _mut(c, ["pillar_1_cut_rank", "source_minimal_U"], [0, 1, 2, 3, 4, 5, 6, 14]) or _mut(c, ["pillar_1_cut_rank", "sink_minimal_U"], [0, 1, 2, 3, 4, 5, 6])),
        ("06_factorization_corrupted", lambda c: _mut(c, ["pillar_1_cut_rank", "transfer_matrix_M", 0, 0], "999")),
        ("07_degenerate_ambient_H", lambda c: _mut(c, ["pillar_2_orthogonality_and_decoder", "indefinite_form_H", 4, 4], "0")),
        ("08_non_idempotent_projector", lambda c: _mut(c, ["pillar_2_orthogonality_and_decoder", "projector_P_z", 0, 0], "2")),
        ("09_broken_forward_span_inclusion", lambda c: _mut(c, ["pillar_2_orthogonality_and_decoder", "basis_B_z", 4, 0], "1")),
        ("10_isotropic_span_made_nondegenerate", lambda c: _mut(c, ["pillar_2_orthogonality_and_decoder", "isotropic_counterexample_B", 3, 0], "0")),
        ("11_persistent_nullspace_leak", lambda c: _mut(c, ["pillar_2_orthogonality_and_decoder", "helper_K_null", 0, 0], "99")),
        ("12_cache_probe_blinded", lambda c: _mut(c, ["pillar_2_orthogonality_and_decoder", "helper_C_cache", 0], ["0"] * 28)),
        ("13_left_inverse_entry_perturbed", lambda c: _mut(c, ["pillar_2_orthogonality_and_decoder", "helper_L_left_inverse", 0, 28], "99")),
        ("14_overclaimed_a_lower_bound", lambda c: _mut(c, ["pillar_3_power_sum_and_farkas", "certified_blocks", 2, "a_lower_certified"], "1400000000000000/1000000000000000000")),
        ("15_underclaimed_a_upper_bound", lambda c: _mut(c, ["pillar_3_power_sum_and_farkas", "certified_blocks", 2, "a_upper_certified"], "1300000000000000/1000000000000000000")),
        ("16_negative_farkas_multiplier", lambda c: _mut(c, ["pillar_3_power_sum_and_farkas", "farkas_histogram_ceiling", "farkas_dual_y", 1], "-1/1000")),
        ("17_farkas_dual_constraint_violated", lambda c: _mut(c, ["pillar_3_power_sum_and_farkas", "farkas_histogram_ceiling", "farkas_dual_y", 0], "1")),
        ("18_frontier7000_kappa_inflated", lambda c: _mut(c, ["pillar_3_power_sum_and_farkas", "frontier_7000_audit", "kappa_rational"], "400000000/100000000000")),
    ]

    rejected = 0
    for label, fn in mutations:
        tampered = copy.deepcopy(base_cert)
        res = fn(tampered)
        if isinstance(res, dict):
            tampered = res
        if label != "01_bad_sha256":
            tampered = rehash_cert(tampered)
        try:
            check_certificate.verify_certificate_dict(tampered)
        except (ValueError, AssertionError):
            rejected += 1
            continue
        raise RuntimeError(f"Adversarial control {label} unexpectedly PASSED!")
    return rejected


def _mut(obj: dict, path: list, val):
    cur = obj
    for key in path[:-1]:
        cur = cur[key]
    cur[path[-1]] = val
    return None


def compile_and_run_c11(c_src: Path) -> str:
    gcc = shutil.which("gcc") or shutil.which("clang")
    if not gcc:
        raise RuntimeError("Neither gcc nor clang found for C11 differential verification")
    candidate_dirs = [None, str(Path.cwd()), str(Path.home())]
    last_err: Exception | None = None
    for base_d in candidate_dirs:
        try:
            with tempfile.TemporaryDirectory(prefix=".c11_mult_bounds_", dir=base_d) as tmp:
                bin_path = Path(tmp) / "c11_base_verifier"
                subprocess.run(
                    [gcc, "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", str(c_src), "-o", str(bin_path)],
                    check=True,
                    capture_output=True,
                    text=True,
                )
                bin_path.chmod(0o755)
                proc = subprocess.run([str(bin_path)], check=True, capture_output=True, text=True)
                out = proc.stdout.strip()
                if "C11_BASE_VERIFIER_OK" not in out:
                    raise RuntimeError(f"Unexpected C11 output: {out}")
                return out
        except PermissionError as e:
            last_err = e
            continue
    raise RuntimeError(f"Could not execute compiled C11 binary in any temp dir: {last_err}")


def main() -> int:
    cert_path = PKG_DIR / "certificates" / "conservation_quotient_certificate.json"
    c_src = PKG_DIR / "c11_base_verifier.c"
    lean_src = PKG_DIR / "formal" / "BaseMathConvergence.lean"

    cert = json.loads(cert_path.read_text(encoding="utf-8"))
    summary = check_certificate.verify_certificate_dict(cert)
    c11_out = compile_and_run_c11(c_src)
    lean_scan = audit_lean_surface(lean_src)
    rejected = run_18_adversarial_controls(cert)

    print(json.dumps({
        "status": "VERIFIED",
        "certificate_sha256": summary["certificate_sha256"],
        "python_exact_fraction_checker": "PASS",
        "c11_int128_differential_checker": c11_out,
        "lean4_surface_scanner": lean_scan,
        "adversarial_controls_rejected": f"{rejected}/18",
        "aska469_567_concavity_penalty_lower": summary["aska469_567_penalty_lower"],
        "farkas_ceiling_kappa": summary["farkas_ceiling_kappa"],
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
