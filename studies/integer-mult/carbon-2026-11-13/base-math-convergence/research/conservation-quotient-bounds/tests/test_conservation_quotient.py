#!/usr/bin/env python3
"""Unit and regression tests for `research/conservation-quotient-bounds/`."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import unittest
from fractions import Fraction
from pathlib import Path

PKG_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PKG_DIR))
import check_certificate  # noqa: E402
import verify  # noqa: E402


class ConservationQuotientTests(unittest.TestCase):
    def setUp(self) -> None:
        self.cert_path = PKG_DIR / "certificates" / "conservation_quotient_certificate.json"
        self.cert = json.loads(self.cert_path.read_text(encoding="utf-8"))

    def test_01_primary_certificate_passes_exact_fraction_checker(self) -> None:
        res = check_certificate.verify_certificate_dict(self.cert)
        self.assertEqual(res["status"], "OK")
        self.assertEqual(res["cut_capacity"], 3)
        self.assertEqual(res["certified_rank_M"], 3)
        self.assertEqual(res["helper_nullity_closed"], 8)

    def test_02_optimized_python_and_env_rejected_fail_closed(self) -> None:
        proc_o = subprocess.run(
            [sys.executable, "-O", str(PKG_DIR / "verify.py")],
            capture_output=True,
            text=True,
        )
        self.assertEqual(proc_o.returncode, 2)
        self.assertIn("forbidden", proc_o.stderr)

        env = dict(os.environ)
        env["PYTHONOPTIMIZE"] = "1"
        proc_env = subprocess.run(
            [sys.executable, "-B", str(PKG_DIR / "check_certificate.py")],
            env=env,
            capture_output=True,
            text=True,
        )
        self.assertEqual(proc_env.returncode, 2)

    def test_03_all_18_rehashed_tamper_controls_rejected(self) -> None:
        rejected = verify.run_18_adversarial_controls(self.cert)
        self.assertEqual(rejected, 18)

    def test_04_c11_differential_verifier_agrees(self) -> None:
        out = verify.compile_and_run_c11(PKG_DIR / "c11_base_verifier.c")
        self.assertIn("C11_BASE_VERIFIER_OK", out)

    def test_05_lean4_surface_scanner_catches_sorry_and_axiom(self) -> None:
        scan = verify.audit_lean_surface(PKG_DIR / "formal" / "BaseMathConvergence.lean")
        self.assertEqual(scan["forbidden_hits"], 0)
        self.assertGreaterEqual(scan["theorems_scanned"], 7)

    def test_06_aska469_concavity_pruning_beats_published_469(self) -> None:
        blocks = {
            b["name"]: b
            for b in self.cert["pillar_3_power_sum_and_farkas"]["certified_blocks"]
        }
        a469_hi = Fraction(blocks["PR_469_Aska_Retiming"]["a_upper_certified"])
        a_unc_lo = Fraction(blocks["PR_469_ConcavityPruned_123Only"]["a_lower_certified"])
        self.assertGreater(a_unc_lo, a469_hi)

    def test_07_package_metadata_binding_consistency(self) -> None:
        sources = json.loads((PKG_DIR / "SOURCES.json").read_text(encoding="utf-8"))
        ver_meta = json.loads((PKG_DIR / "VERIFY.json").read_text(encoding="utf-8"))
        input_paths = {e["path"] for e in sources["entries"] if e["usage"] == "input"}
        declared_inputs = set(ver_meta["inputs"])
        self.assertTrue(input_paths.issubset(declared_inputs))


if __name__ == "__main__":
    unittest.main()
