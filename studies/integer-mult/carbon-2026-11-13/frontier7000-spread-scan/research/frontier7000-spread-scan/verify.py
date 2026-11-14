#!/usr/bin/env python3
"""
verify.py — Scoped Verification & 20-Control Adversarial Tamper Suite
for `research/frontier7000-spread-scan/` (`CrocSwap/integer-mult-bounds`).
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

if sys.flags.optimize > 0 or os.environ.get("PYTHONOPTIMIZE", "").strip() not in ("", "0"):
    sys.stderr.write("FATAL: optimized Python (-O / PYTHONOPTIMIZE) is forbidden.\n")
    sys.exit(2)

PKG_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(PKG_DIR))
import check_spread_scan  # noqa: E402


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


def strip_lean_comments(src: str) -> str:
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
        raise ValueError("Unclosed Lean block comment")
    return "".join(out)


def audit_lean_surface(lean_path: Path) -> dict[str, int]:
    code = strip_lean_comments(lean_path.read_text(encoding="utf-8"))
    for name, pat in FORBIDDEN_LEAN_PATTERNS:
        m = pat.search(code)
        if m:
            raise ValueError(f"Forbidden Lean surface vector `{name}` matched: {m.group(0)!r}")
    theorems = re.findall(r"\btheorem\s+([A-Za-z0-9_']+)", code)
    if len(theorems) < 18:
        raise ValueError(f"Expected >= 18 formal theorems, found {len(theorems)}")
    return {"theorems_scanned": len(theorems), "forbidden_hits": 0}


def rehash_cert(c: dict) -> dict:
    d = copy.deepcopy(c)
    d.pop("certificate_sha256", None)
    d["certificate_sha256"] = hashlib.sha256(
        json.dumps(d, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    return d


def _mut(obj: dict, path: list, val):
    cur = obj
    for k in path[:-1]:
        cur = cur[k]
    cur[path[-1]] = val
    return None


def run_20_adversarial_controls(base_cert: dict) -> int:
    mutations = [
        ("01_bad_sha256", lambda c: {**copy.deepcopy(c), "certificate_sha256": "f" * 64}),
        ("02_float_decimal_in_bracket", lambda c: _mut(c, ["frontier7000_baseline", "raw_bracket_lo"], "0.00363")),
        ("03_corrupt_productive_count", lambda c: _mut(c, ["frontier7000_baseline", "productive_T", "9"], 11127)),
        ("04_corrupt_paid_count", lambda c: _mut(c, ["frontier7000_baseline", "paid_P", "1"], 73765)),
        ("05_corrupt_native_stratum", lambda c: _mut(c, ["frontier7000_baseline", "native_paid", "5"], 321)),
        ("06_non_multiple_of_8_whole_idle", lambda c: _mut(c, ["frontier7000_baseline", "caller_whole_idles"], {"7": 704, "16": 2912})),
        ("07_inflated_raw_bracket_lo", lambda c: _mut(c, ["frontier7000_baseline", "raw_bracket_lo"], "36300582/10000000000")),
        ("08_deflated_raw_bracket_hi", lambda c: _mut(c, ["frontier7000_baseline", "raw_bracket_hi"], "36300581/10000000000")),
        ("09_out_of_cap_rank9_spread", lambda c: _mut(c, ["symmetric_pairwise_spreads", 8, "d"], 4)),
        ("10_wrong_integer_concavity_rhs", lambda c: _mut(c, ["symmetric_pairwise_spreads", 0, "integer_witness_rhs"], 16)),
        ("11_overdrawn_max_local_pairs", lambda c: _mut(c, ["symmetric_pairwise_spreads", 0, "max_local_pairs"], 415)),
        ("12_inflated_spread_k_lo", lambda c: _mut(c, ["symmetric_pairwise_spreads", 2, "saturated_k_lo"], "40/10000")),
        ("13_balayage_mass_violation", lambda c: _mut(c, ["bauer_karamata_balayage", "balayage_native_paid", "8"], 665)),
        ("14_balayage_inflated_k_lo", lambda c: _mut(c, ["bauer_karamata_balayage", "k_balayage_lo"], "42/10000")),
        ("15_crossing_under_threshold", lambda c: _mut(c, ["bit_premise_crossing_recipe", "local_pair_moves", 2, "local_pairs"], 10)),
        ("16_crossing_overdraws_bucket", lambda c: _mut(c, ["bit_premise_crossing_recipe", "local_pair_moves", 0, "local_pairs"], 200)),
        ("17_gl9_wrong_step1_rank", lambda c: _mut(c, ["gl9_flag_repivoting_witness", "Q1_repiv_18x18", 2, 2], -1)),
        ("18_gl9_broken_operator_equivalence", lambda c: _mut(c, ["gl9_flag_repivoting_witness", "Q2_repiv_18x18", 8, 8], 1)),
        ("19_gl9_trivial_zero_contact", lambda c: _mut(c, ["gl9_flag_repivoting_witness", "C_commuting_contact_18x18", 9, 0], 0) or _mut(c, ["gl9_flag_repivoting_witness", "C_commuting_contact_18x18", 10, 1], 0)),
        ("20_gl9_obstructed_contact_disabled", lambda c: _mut(c, ["gl9_flag_repivoting_witness", "C_coupled_contact_18x18"], copy.deepcopy(c["gl9_flag_repivoting_witness"]["C_commuting_contact_18x18"]))),
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
            check_spread_scan.verify_certificate_dict(tampered)
        except (ValueError, AssertionError, KeyError):
            rejected += 1
            continue
        raise RuntimeError(f"Adversarial control {label} unexpectedly PASSED!")
    return rejected


def compile_and_run_c11(c_src: Path) -> str:
    gcc = shutil.which("gcc") or shutil.which("clang")
    if not gcc:
        raise RuntimeError("Neither gcc nor clang found")
    for base_d in (None, str(Path.cwd()), str(Path.home())):
        try:
            with tempfile.TemporaryDirectory(prefix=".c11_f7000_", dir=base_d) as tmp:
                bin_path = Path(tmp) / "c11_frontier7000_scanner"
                subprocess.run(
                    [gcc, "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", str(c_src), "-o", str(bin_path)],
                    check=True,
                    capture_output=True,
                    text=True,
                )
                bin_path.chmod(0o755)
                proc = subprocess.run([str(bin_path)], check=True, capture_output=True, text=True)
                out = proc.stdout.strip()
                if "C11_FRONTIER7000_SCANNER_OK" not in out:
                    raise RuntimeError(f"Unexpected C11 output: {out}")
                return out
        except PermissionError:
            continue
    raise RuntimeError("No executable temporary directory found for C11 scanner")


def main() -> int:
    cert_path = PKG_DIR / "certificates" / "frontier7000_spread_scan_certificate.json"
    c_src = PKG_DIR / "c11_frontier7000_scanner.c"
    lean_src = PKG_DIR / "formal" / "Frontier7000SpreadBounds.lean"

    cert = json.loads(cert_path.read_text(encoding="utf-8"))
    summary = check_spread_scan.verify_certificate_dict(cert)
    c11_out = compile_and_run_c11(c_src)
    lean_scan = audit_lean_surface(lean_src)
    rejected = run_20_adversarial_controls(cert)

    print(json.dumps({
        "status": "VERIFIED",
        "certificate_sha256": summary["certificate_sha256"],
        "python_exact_fraction_checker": "PASS",
        "c11_int128_differential_scanner": c11_out,
        "lean4_surface_scanner": lean_scan,
        "adversarial_controls_rejected": f"{rejected}/20",
        "min_local_pairs_to_cross_BIT_premise": summary["crossing_local_pairs"],
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
