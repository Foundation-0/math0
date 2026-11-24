#!/usr/bin/env python3
"""
R5 Refusal-Site Mutation Test Suite for buckmaster_euler_cc_audit.py (AUDIT-053).
Pure unittest stdlib, zero bare asserts; tests every refusal guard, boundary
inequality, Farkas infeasibility witness, Leray Schur complement, and exact identity.
"""
from __future__ import annotations

from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
import unittest

_HERE = str(Path(__file__).resolve().parent)
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import buckmaster_euler_cc_audit as mod


def _assert_no_floats(tc: unittest.TestCase, obj: object) -> None:
    if isinstance(obj, float):
        tc.fail(f"float found in zero-float JSON payload: {obj!r}")
    if isinstance(obj, dict):
        for val in obj.values():
            _assert_no_floats(tc, val)
    elif isinstance(obj, list):
        for val in obj:
            _assert_no_floats(tc, val)


class TestBuckmasterEulerCCAudit(unittest.TestCase):
    def test_type_and_matrix_refusals(self) -> None:
        with self.assertRaisesRegex(TypeError, "int or Fraction"):
            mod._as_frac(True)
        with self.assertRaisesRegex(TypeError, "int or Fraction"):
            mod._as_frac(1.5)  # type: ignore[arg-type]

        with self.assertRaisesRegex(ValueError, "3x3"):
            mod._inv3([[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)]])
        with self.assertRaisesRegex(ValueError, "3x3"):
            mod._inv3([[Fraction(1)], [Fraction(0), Fraction(1), Fraction(0)], [Fraction(0), Fraction(0), Fraction(1)]])
        with self.assertRaisesRegex(ValueError, "singular"):
            mod._inv3([
                [Fraction(1), Fraction(2), Fraction(3)],
                [Fraction(2), Fraction(4), Fraction(6)],
                [Fraction(0), Fraction(0), Fraction(1)],
            ])

        # Exact SPD refusal cases: non-symmetric, d1 <= 0, d2 <= 0, d3 <= 0
        self.assertFalse(mod._is_spd3([
            [Fraction(2), Fraction(1), Fraction(0)],
            [Fraction(0), Fraction(2), Fraction(0)],
            [Fraction(0), Fraction(0), Fraction(2)],
        ]))
        self.assertFalse(mod._is_spd3([
            [Fraction(0), Fraction(0), Fraction(0)],
            [Fraction(0), Fraction(1), Fraction(0)],
            [Fraction(0), Fraction(0), Fraction(1)],
        ]))
        self.assertFalse(mod._is_spd3([
            [Fraction(1), Fraction(1), Fraction(0)],
            [Fraction(1), Fraction(1), Fraction(0)],
            [Fraction(0), Fraction(0), Fraction(1)],
        ]))
        self.assertFalse(mod._is_spd3([
            [Fraction(1), Fraction(0), Fraction(0)],
            [Fraction(0), Fraction(1), Fraction(0)],
            [Fraction(0), Fraction(0), Fraction(0)],
        ]))
        self.assertTrue(mod._is_spd3([
            [Fraction(2), Fraction(1), Fraction(0)],
            [Fraction(1), Fraction(2), Fraction(0)],
            [Fraction(0), Fraction(0), Fraction(3)],
        ]))

    def test_step_polytope_boundaries_and_refusals(self) -> None:
        paper = mod.evaluate_step_polytope_exact(
            Fraction(3, 4), Fraction(1, 2), Fraction(2, 3), Fraction(1, 12)
        )
        self.assertTrue(paper["all_satisfied"])
        self.assertEqual(
            paper["tight_zero_slack_facets"],
            [
                "E3_div_corr_phase_advection",
                "E6_mean_induction_shift_5_40",
                "E9_central_gradient_err_5_50",
            ],
        )
        self.assertTrue(paper["transverse_trick_5_16_strictly_required"])

        # Strict boundary refusal tests (slack == 0 fails strict constraints E1/E2/E7/E8/E10)
        at_alpha1 = mod.evaluate_step_polytope_exact(
            Fraction(1), Fraction(1, 2), Fraction(2, 3), Fraction(1, 12)
        )
        self.assertFalse(at_alpha1["all_satisfied"])
        self.assertIn("E1_positive_wave_strength", at_alpha1["violated"])

        # Domain refusals on every branch of alpha_a <= 0, beta_h < 0, delta_lvl <= 0, eta_d <= 0
        with self.assertRaisesRegex(ValueError, "exponents must satisfy"):
            mod.evaluate_step_polytope_exact(0, Fraction(1, 2), Fraction(2, 3), Fraction(1, 12))
        with self.assertRaisesRegex(ValueError, "exponents must satisfy"):
            mod.evaluate_step_polytope_exact(Fraction(3, 4), Fraction(-1, 10), Fraction(2, 3), Fraction(1, 12))
        with self.assertRaisesRegex(ValueError, "exponents must satisfy"):
            mod.evaluate_step_polytope_exact(Fraction(3, 4), Fraction(1, 2), 0, Fraction(1, 12))
        with self.assertRaisesRegex(ValueError, "exponents must satisfy"):
            mod.evaluate_step_polytope_exact(Fraction(3, 4), Fraction(1, 2), Fraction(2, 3), 0)

        # Positive feasible point where naive 2-deriv trick is NOT required:
        # (alpha_a=7/8, beta_h=1/2, delta_lvl=3/4, eta_d=1/12) satisfies E1..E10 AND naive slack = +1/8 > 0!
        no_trick = mod.evaluate_step_polytope_exact(
            Fraction(7, 8), Fraction(1, 2), Fraction(3, 4), Fraction(1, 12)
        )
        self.assertTrue(no_trick["all_satisfied"])
        self.assertFalse(no_trick["transverse_trick_5_16_strictly_required"])

        # Exact boundary naive_p2_hessian_slack == 0 still requires (5.16) (<= 0)
        # 1 + aa + bh + dl - 2*(1 + bh) = aa + dl - bh - 1 == 0 at aa=3/4, dl=2/3, bh=5/12
        boundary_trick = mod.evaluate_step_polytope_exact(
            Fraction(3, 4), Fraction(5, 12), Fraction(2, 3), Fraction(1, 12)
        )
        self.assertEqual(boundary_trick["naive_p2_hessian_without_5_16_slack"], "0")
        self.assertTrue(boundary_trick["transverse_trick_5_16_strictly_required"])

    def test_multiscale_appendix_c_and_refusals(self) -> None:
        self.assertEqual(mod.k_exponent_exact(1, 1), 640)
        with self.assertRaisesRegex(TypeError, "non-bool ints"):
            mod.k_exponent_exact(True, 1)
        with self.assertRaisesRegex(TypeError, "non-bool ints"):
            mod.k_exponent_exact(1, False)
        with self.assertRaisesRegex(ValueError, ">= 1"):
            mod.k_exponent_exact(0, 1)
        with self.assertRaisesRegex(ValueError, ">= 1"):
            mod.k_exponent_exact(1, 0)

        # Admissible and inadmissible order transitions
        ok = mod.audit_multiscale_step_exact(1, 1, 2, 2)
        self.assertTrue(ok["all_satisfied"])
        self.assertTrue(ok["C10_exact_zero_residual"])
        with self.assertRaisesRegex(ValueError, "derivative orders"):
            mod.audit_multiscale_step_exact(1, 2, 1, 1)
        with self.assertRaisesRegex(ValueError, "derivative orders"):
            mod.audit_multiscale_step_exact(1, 1, 3, 3)
        with self.assertRaisesRegex(ValueError, "derivative orders"):
            mod.audit_multiscale_step_exact(1, 1, 2, 1)
        with self.assertRaisesRegex(ValueError, "derivative orders"):
            mod.audit_multiscale_step_exact(1, 1, 2, 4)

        # Log tower exact replay & refusals
        tower = mod.simulate_appendix_c_log_tower_exact(b=1, steps=2)
        self.assertTrue(tower["lemma_1_3_all_steps_exact"])
        with self.assertRaisesRegex(ValueError, "int >= 2"):
            mod.simulate_appendix_c_log_tower_exact(b=1, steps=1)
        with self.assertRaisesRegex(ValueError, "int >= 2"):
            mod.simulate_appendix_c_log_tower_exact(b=1, steps=True)  # type: ignore[arg-type]

    def test_leray_schur_refusals_and_full_audit(self) -> None:
        with self.assertRaisesRegex(ValueError, "3-vectors"):
            mod.leray_schur_complement_exact([1, 2], [1, 2, 3])
        with self.assertRaisesRegex(ValueError, "3-vectors"):
            mod.leray_schur_complement_exact([1, 2, 3], [1, 2])
        with self.assertRaisesRegex(ValueError, "nonzero"):
            mod.leray_schur_complement_exact([0, 0, 0], [1, 2, 3])
        with self.assertRaisesRegex(ValueError, "3x3 matrix"):
            mod.leray_schur_complement_exact([1, 0, 0], [1, 2, 3], [[1, 0], [0, 1]])
        with self.assertRaisesRegex(ValueError, "3x3 matrix"):
            mod.leray_schur_complement_exact([1, 0, 0], [1, 2, 3], [[1, 0], [0, 1, 0], [0, 0, 1]])
        with self.assertRaisesRegex(ValueError, "symmetric positive definite"):
            mod.leray_schur_complement_exact(
                [1, 0, 0],
                [1, 2, 3],
                [[1, 0, 0], [0, -1, 0], [0, 0, 1]],
            )

        res = mod.run_full_audit()
        self.assertTrue(res["all_passed"])
        _assert_no_floats(self, json.loads(json.dumps(res)))
        self.assertEqual(mod.main([]), 0)

    def test_certificate_integrity_and_farkas_row_derivation(self) -> None:
        cert_path = Path(__file__).resolve().parent / "buckmaster_euler_cc_results.json"
        self.assertTrue(cert_path.is_file(), "buckmaster_euler_cc_results.json missing")
        raw = json.loads(cert_path.read_text(encoding="utf-8"))
        _assert_no_floats(self, raw)
        saved_sha = raw.pop("canonical_sha256")
        recomputed = hashlib.sha256(
            json.dumps(raw, sort_keys=True, separators=(",", ":"), allow_nan=False).encode("utf-8")
        ).hexdigest()
        self.assertEqual(saved_sha, recomputed)
        live = mod.run_full_audit()
        self.assertEqual(live["canonical_sha256"], saved_sha)
        self.assertEqual(len(mod.STEP_POLYTOPE_CONSTRAINTS), 10)


if __name__ == "__main__":
    unittest.main()
