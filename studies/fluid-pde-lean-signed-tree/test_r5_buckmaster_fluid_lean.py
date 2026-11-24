#!/usr/bin/env python3
"""Adversarial R3 + R5 verification suite for Round 4D Arm R4D-1 (AUDIT-052):
buckmaster_fluid_lean_audit.py.

100% pure Python 3 stdlib, ZERO floats, ZERO bare asserts.
"""

from __future__ import annotations

import hashlib
import json
import sys
import unittest
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import buckmaster_fluid_lean_audit as bfl  # noqa: E402


class TestBuckmasterFluidLeanR5(unittest.TestCase):
    """Comprehensive R1-R5 tests (zero bare asserts, zero floats)."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.cert_path = HERE / "buckmaster_fluid_lean_certificate.json"
        cls.live_all = bfl.run_all_audits(write_certificate=False)

    def test_01_r3_scalar_matrix_and_r_opt_guards(self) -> None:
        self.assertEqual(bfl.require_exact_int(7, "x"), 7)
        self.assertEqual(bfl.require_exact_rational(Fraction(5, 4), "q"), Fraction(5, 4))
        self.assertEqual(bfl.frac_str(Fraction(8, 2)), "4")
        self.assertEqual(bfl.frac_str(Fraction(1521, 1445)), "1521/1445")

        for bad in (1.5, True, False, "2", None):
            with self.assertRaises(TypeError):
                bfl.require_exact_int(bad, "bad")
            with self.assertRaises(TypeError):
                bfl.require_exact_rational(bad, "bad")

        bfl.verify_no_floats({"ok": [1, "3/4", {"flag": True, "none": None}]})
        with self.assertRaises(ValueError):
            bfl.verify_no_floats({"bad": [0.1]})

        with self.assertRaises(ValueError):
            bfl.mat_add([[Fraction(1)]], [[Fraction(1), Fraction(2)]])
        with self.assertRaises(ValueError):
            bfl.mat_sub([[Fraction(1)]], [[Fraction(1), Fraction(2)]])
        with self.assertRaises(ValueError):
            bfl.mat_mul([[Fraction(1), Fraction(2)]], [[Fraction(1)]])
        with self.assertRaises(ValueError):
            bfl.mat_gram_cols([[Fraction(1)]], 2)
        with self.assertRaises(ValueError):
            bfl.exact_symmetric_inertia([])
        with self.assertRaises(ValueError):
            bfl.exact_symmetric_inertia([[1, 2, 3], [4, 5, 6]])
        with self.assertRaises(ValueError):
            bfl.exact_symmetric_inertia([[1, 2], [3, 4]])
        self.assertEqual(bfl.exact_symmetric_inertia([[0, 5], [5, 0]]), (1, 0, 1))
        self.assertEqual(bfl.exact_symmetric_inertia([[0, 0, 3], [0, 0, 0], [3, 0, 0]]), (1, 1, 1))

        # AUDIT-002 R_opt branches & guards
        with self.assertRaises(ValueError):
            bfl.r_opt_noncommuting(Fraction(1), Fraction(0), Fraction(1), -1)
        with self.assertRaises(ValueError):
            bfl.r_opt_noncommuting(Fraction(2), Fraction(2), Fraction(1), 1)
        self.assertEqual(bfl.r_opt_noncommuting(Fraction(0), Fraction(1), Fraction(1), 0), Fraction(0))
        self.assertEqual(bfl.r_opt_noncommuting(Fraction(2), Fraction(2), Fraction(5), 1), Fraction(4, 1))
        self.assertEqual(bfl.r_opt_noncommuting(Fraction(3), Fraction(0), Fraction(3), 0), Fraction(3, 1))

    def test_02_part1_three_repo_tomography(self) -> None:
        p1 = self.live_all["part1_three_repo_lean4_tomography"]
        if p1.get("mode") == "standalone_no_external_clones":
            # Standalone checkout does not vendor third-party Lean 4 repos; verify honest stub
            # and verify fail-closed --require-live-repos refusal (zero circular cert self-reads).
            self.assertIs(p1["external_repos_verified_in_this_run"], False)
            self.assertEqual(p1["total_lean_files_scanned"], 0)
            self.assertEqual(p1["total_lean_lines_scanned"], 0)
            self.assertEqual(p1["subprojects"], {})
            with self.assertRaises(FileNotFoundError):
                bfl.run_three_repo_lean4_tomography(require_live_repos=True)
            return

        self.assertEqual(p1["total_lean_files_scanned"], 8678)
        self.assertEqual(p1["total_lean_lines_scanned"], 3077719)
        subs = p1["subprojects"]
        for nm in subs:
            self.assertEqual(subs[nm]["non_sorry_trust_escapes"], 0)
            self.assertEqual(subs[nm]["native_decide_calls"], 0)
        # Key forensic contrast: 0/6 comparator pass on navier-stokes vs 3/3 fluid_lean & 2/2 oai_nse
        self.assertEqual(subs["tb_navier_stokes"]["comparator_passed_count"], 0)
        self.assertEqual(subs["tb_navier_stokes"]["comparator_total_count"], 6)
        self.assertEqual(subs["tb_fluid_affinecore"]["comparator_passed_count"], 1)
        self.assertEqual(subs["tb_fluid_boussinesq"]["comparator_passed_count"], 1)
        self.assertEqual(subs["tb_fluid_euler"]["comparator_passed_count"], 1)
        self.assertEqual(subs["oai_nse"]["comparator_passed_count"], 2)
        self.assertEqual(subs["tb_fluid_boussinesq"]["decide_plus_kernel_calls"], 13547)
        self.assertEqual(subs["tb_fluid_euler"]["decide_plus_kernel_calls"], 8750)
        self.assertEqual(subs["tb_navier_stokes"]["decide_plus_kernel_calls"], 0)
        # Zero file overlap between tristanbuckmaster/* and openai/NavierStokesAndEuler
        self.assertEqual(p1["pairwise_sha256_file_overlaps"]["tb_navier_stokes<->oai_nse"], 0)
        self.assertEqual(p1["pairwise_sha256_file_overlaps"]["tb_fluid_boussinesq<->oai_nse"], 0)
        # PrintAxioms vs comparator coverage gap (8 unlisted theorems matching NOTICE L13)
        self.assertEqual(p1["navier_stokes_forensics"]["print_axioms_theorem_count"], 27)
        self.assertEqual(p1["navier_stokes_forensics"]["comparator_listed_theorem_count"], 19)
        self.assertEqual(p1["navier_stokes_forensics"]["unlisted_in_comparator_count"], 8)
        self.assertTrue(all(p1["navier_stokes_forensics"]["nov20_unrebuilt_patch_static_sync"].values()))

    def test_03_part2_signed_tree_exact_perturbed_and_all_mutants(self) -> None:
        p2 = bfl.run_signed_tree_adversarial_suite()
        ex = p2["exact_multifrontal_tree_with_nullpair"]
        pt = p2["perturbed_gershgorin_enclosure_tree"]
        self.assertEqual(ex["global_inertia"], [4, 0, 2])
        self.assertEqual(pt["global_inertia"], [4, 0, 2])
        self.assertEqual(ex["restricted_ker_FmT_inertia"], [4, 0, 0])
        self.assertEqual(pt["restricted_ker_FmT_inertia"], [4, 0, 0])
        self.assertTrue(p2["adversarial_mutants_all_killed"])
        self.assertEqual(p2["adversarial_mutants_killed"], 6)

        # Additional structural guards: cyclic tree, two roots, unknown leaf node, non-positive slack, negative weight, input_lower violation
        t_cyc = bfl.build_exact_multifrontal_tree()
        t_cyc["parent"]["leaf_L"] = "leaf_R"
        t_cyc["parent"]["leaf_R"] = "leaf_L"
        with self.assertRaises(ValueError):
            bfl.verify_signed_tree_certificate(t_cyc)

        t_2root = bfl.build_exact_multifrontal_tree()
        t_2root["parent"]["leaf_R"] = None
        with self.assertRaises(ValueError):
            bfl.verify_signed_tree_certificate(t_2root)

        t_bad_w = bfl.build_exact_multifrontal_tree()
        t_bad_w["node_enclosures"]["leaf_L"]["D_weight"][0] = Fraction(0)
        with self.assertRaises(ValueError):
            bfl.verify_signed_tree_certificate(t_bad_w)

        t_bad_in = bfl.build_exact_multifrontal_tree()
        t_bad_in["node_enclosures"]["leaf_L"]["D_input"][0][0] += Fraction(1)  # breaks input_lower!
        with self.assertRaises(ValueError):
            bfl.verify_signed_tree_certificate(t_bad_in)

        t_bad_fr = bfl.build_exact_multifrontal_tree()
        t_bad_fr["fronts"]["leaf_L"][4][4] += Fraction(1)  # breaks front_upper!
        with self.assertRaises(ValueError):
            bfl.verify_signed_tree_certificate(t_bad_fr)

        t_bad_sl = bfl.build_exact_multifrontal_tree()
        t_bad_sl["slacks"]["leaf_L"][0] = Fraction(0)  # breaks slack_positive!
        with self.assertRaises(ValueError):
            bfl.verify_signed_tree_certificate(t_bad_sl)

    def test_04_part3_nov20_weight_and_sperner_box(self) -> None:
        p3 = bfl.run_patch_weight_and_sperner_box_check()
        self.assertEqual(p3["nov20_weight_shift"]["kappa_19_old_weight"], "1445/4")
        self.assertEqual(p3["nov20_weight_shift"]["kappa_19_patched_weight"], "1521/4")
        self.assertEqual(p3["nov20_weight_shift"]["kappa_19_relaxation_factor"], "1521/1445")
        self.assertTrue(p3["fixed_point_box_sperner_2d"]["odd_parity_certified"])
        self.assertEqual(p3["fixed_point_box_sperner_2d"]["complete_sperner_simplex_count"], 1)

    def test_05_certificate_file_integrity_and_zero_floats(self) -> None:
        self.assertTrue(self.cert_path.is_file(), "Certificate JSON missing")
        raw = json.loads(self.cert_path.read_text(encoding="utf-8"))
        bfl.verify_no_floats(raw)
        saved_sha = raw.pop("canonical_sha256")
        recomputed = hashlib.sha256(
            json.dumps(raw, sort_keys=True, separators=(",", ":")).encode("utf-8")
        ).hexdigest()
        self.assertEqual(saved_sha, recomputed)
        for section in (
            "part2_signed_tree_multifrontal_schur",
            "part3_nov20_weight_and_sperner_box",
            "part4_r3_negative_controls",
        ):
            self.assertEqual(self.live_all[section], raw[section], f"Live/sealed mismatch in {section}")
        live_mode = self.live_all["part1_three_repo_lean4_tomography"].get("mode")
        raw_mode = raw["part1_three_repo_lean4_tomography"].get("mode")
        if live_mode == raw_mode:
            self.assertEqual(self.live_all["canonical_sha256"], saved_sha)


def main() -> int:
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(TestBuckmasterFluidLeanR5)
    runner = unittest.TextTestRunner(verbosity=2, stream=sys.stderr)
    res = runner.run(suite)
    out = {
        "suite": "test_r5_buckmaster_fluid_lean",
        "tests_run": res.testsRun,
        "failures": len(res.failures),
        "errors": len(res.errors),
        "ok": res.wasSuccessful(),
    }
    print(json.dumps(out, indent=2, sort_keys=True))
    return 0 if res.wasSuccessful() else 1


if __name__ == "__main__":
    raise SystemExit(main())
