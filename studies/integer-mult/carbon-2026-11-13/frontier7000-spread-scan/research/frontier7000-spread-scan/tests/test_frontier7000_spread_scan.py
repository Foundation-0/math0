#!/usr/bin/env python3
"""Unit tests for `research/frontier7000-spread-scan/`."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import unittest
from pathlib import Path

PKG_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PKG_DIR))
import check_spread_scan  # noqa: E402
import verify  # noqa: E402


class Frontier7000SpreadScanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.cert_path = PKG_DIR / "certificates" / "frontier7000_spread_scan_certificate.json"
        self.cert = json.loads(self.cert_path.read_text(encoding="utf-8"))

    def test_01_primary_certificate_passes(self) -> None:
        res = check_spread_scan.verify_certificate_dict(self.cert)
        self.assertEqual(res["status"], "OK")

    def test_02_optimized_python_rejected(self) -> None:
        p1 = subprocess.run([sys.executable, "-O", str(PKG_DIR / "verify.py")], capture_output=True, text=True)
        self.assertEqual(p1.returncode, 2)
        env = {**os.environ, "PYTHONOPTIMIZE": "1"}
        p2 = subprocess.run([sys.executable, "-B", str(PKG_DIR / "check_spread_scan.py")], env=env, capture_output=True, text=True)
        self.assertEqual(p2.returncode, 2)

    def test_03_all_20_rehashed_tamper_controls_rejected(self) -> None:
        self.assertEqual(verify.run_20_adversarial_controls(self.cert), 20)

    def test_04_c11_differential_scanner_passes(self) -> None:
        self.assertIn("C11_FRONTIER7000_SCANNER_OK", verify.compile_and_run_c11(PKG_DIR / "c11_frontier7000_scanner.c"))

    def test_05_lean4_surface_scanner_passes(self) -> None:
        scan = verify.audit_lean_surface(PKG_DIR / "formal" / "Frontier7000SpreadBounds.lean")
        self.assertEqual(scan["forbidden_hits"], 0)
        self.assertGreaterEqual(scan["theorems_scanned"], 18)

    def test_06_sources_and_verify_metadata_consistent(self) -> None:
        sources = json.loads((PKG_DIR / "SOURCES.json").read_text(encoding="utf-8"))
        vmeta = json.loads((PKG_DIR / "VERIFY.json").read_text(encoding="utf-8"))
        in_paths = {e["path"] for e in sources["entries"] if e["usage"] == "input"}
        self.assertTrue(in_paths.issubset(set(vmeta["inputs"])))


if __name__ == "__main__":
    unittest.main()
