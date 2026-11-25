#!/usr/bin/env python3
"""
Track S21e — Assertion-Free R5 Adversarial & Mutation-Killing Test Suite.

Zero bare `assert`s (unittest methods only), zero float literals, fast (< 2s)
for full live `aletheia v2.0.0 mutate --max-mutants 0` and exhaustive AST BoolOp
verification on both `metamorphosis_symmetry_oracle.py` and
`metamorphosis_symmetry_audit.py`.
"""
from __future__ import annotations

import copy
from fractions import Fraction
import io
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

_HERE = str(Path(__file__).resolve().parent)
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import metamorphosis_symmetry_audit as audit  # noqa: E402
import metamorphosis_symmetry_oracle as oracle  # noqa: E402


class _EvilInt(int):
    pass


class _EvilStr(str):
    pass


class _EvilPath(Path):
    _flavour = Path(".")._flavour if hasattr(Path("."), "_flavour") else None


class _EvilDict(dict):
    pass


class _EvilList(list):
    pass


class TestMetamorphosisSymmetryR5(unittest.TestCase):
    """Comprehensive mathematical + Zone-B + mutation-killing test suite."""

    def test_01_oracle_certificate_and_exact_math(self) -> None:
        cert = oracle.build_certificate()
        self.assertEqual(cert["schema"], oracle.CERT_SCHEMA)
        self.assertEqual(cert["track_id"], oracle.CERT_TRACK_ID)
        verified = oracle.verify_certificate_object(cert)
        self.assertEqual(verified["certificate_sha256"], cert["certificate_sha256"])

        p = cert["payload"]
        self.assertTrue(p["all_theorems_verified"])

        # Frontier 1: siliquant E8
        f1 = p["frontier1_siliquant_e8"]
        self.assertEqual(f1["e8_root_count"], 240)
        self.assertTrue(f1["intertwiner_A_orthogonal"])
        self.assertTrue(f1["intertwiner_U_WHT8_equals_U_BH2_A"])
        self.assertTrue(f1["intertwiner_A_in_W_E8"])
        self.assertEqual(f1["std_e8_root_support_weights"], {"2": 112, "8": 128})
        self.assertEqual(f1["had_e8_root_support_weights"], {"1": 16, "4": 224})
        self.assertEqual(f1["steiner_3_8_4_1_quad_count"], 14)
        self.assertEqual(f1["steiner_probe_min_d2"], "9801/20000")
        self.assertEqual(f1["steiner_probe_unique_nearest_count"], 1)
        self.assertTrue(f1["steiner_probe_forced_coord4_nonzero"])
        self.assertEqual(f1["antipodal_group_order"], 2)
        self.assertEqual(f1["antipodal_triv_projector_rank"], 0)
        for ch_name, exp_rho in (
            ("siliquant_default", ["2", "10", "1", "-17", "11", "4", "-5", "8"]),
            ("lexicographic", ["23", "6", "5", "4", "3", "2", "1", "0"]),
        ):
            ch = f1["weyl_chambers"][ch_name]
            self.assertEqual(ch["positive_roots"], 120)
            self.assertEqual(ch["ties"], 0)
            self.assertEqual(ch["rho"], exp_rho)
            self.assertEqual(ch["mu_norm_sq"], "31/45")
            self.assertEqual(ch["max_root_dot"], "29/30")
            self.assertTrue(ch["strictly_interior_voronoi"])
            self.assertEqual(ch["shifted_roots_inside_open_sqrt2_ball"], 52)
            self.assertEqual(ch["min_shifted_root_dist_sq"], "34/45")

        # Frontier 2: point-charges harmonic Hessian walls
        f2 = p["frontier2_point_charges_harmonic"]
        self.assertEqual(f2["group_orders"], {"Td": 24, "C3v": 6, "D4h": 16, "D2h": 8})
        self.assertEqual(f2["td_triv_projector_rank"], 0)
        self.assertEqual(f2["c3v_isotypic_ranks"], {"A1": 1, "E": 2})
        self.assertEqual(f2["d4h_isotypic_ranks"], {"A2u": 1, "Eu": 2})
        self.assertEqual(f2["d2h_isotypic_ranks"], [1, 1, 1])

        pyr = f2["pyramid_Td_to_C3v"]
        self.assertEqual(pyr["unbroken_Td_wall"]["inertia"], [0, 0, 3])
        self.assertTrue(pyr["unbroken_Td_wall"]["td_equivariant"])
        self.assertTrue(pyr["unbroken_Td_wall"]["grad_zero"])
        self.assertTrue(pyr["unbroken_Td_wall"]["trace_zero"])
        self.assertEqual(pyr["compressed_C3v"]["inertia"], [1, 2, 0])
        self.assertEqual(pyr["compressed_C3v"]["lambda_A1"], "6")
        self.assertEqual(pyr["compressed_C3v"]["lambda_E"], "-3")
        self.assertFalse(pyr["compressed_C3v"]["td_equivariant"])
        self.assertTrue(pyr["compressed_C3v"]["c3v_schur"]["equivariant"])
        self.assertTrue(pyr["compressed_C3v"]["c3v_schur"]["coupling_vanishes"])
        self.assertEqual(pyr["extended_C3v"]["inertia"], [2, 1, 0])
        self.assertEqual(pyr["extended_C3v"]["lambda_A1"], "-3")
        self.assertEqual(pyr["extended_C3v"]["lambda_E"], "3/2")
        self.assertEqual(f2["pyramid_poincare_hopf_sign_jump"], 2)

        sq = f2["square_D4h_to_D2h"]
        self.assertEqual(sq["unbroken_D4h"]["diag"], ["2", "2", "-4"])
        self.assertTrue(sq["unbroken_D4h"]["d4h_equivariant"])
        self.assertEqual(sq["unbroken_D4h"]["inertia"], [2, 1, 0])
        self.assertEqual(sq["degenerate_B2u_wall"]["diag"], ["6", "0", "-6"])
        self.assertFalse(sq["degenerate_B2u_wall"]["d4h_equivariant"])
        self.assertEqual(sq["degenerate_B2u_wall"]["inertia"], [1, 1, 1])
        self.assertEqual(sq["broken_D2h_post_pitchfork"]["diag"], ["10", "-2", "-8"])
        self.assertEqual(sq["broken_D2h_post_pitchfork"]["inertia"], [1, 2, 0])
        self.assertTrue(f2["n4_c1_fold_poincare_hopf"]["poincare_hopf_preserved"])

        # Frontier 3: aska-physical Voigt coupling, Z_2 truss & 6-spoke prestress
        f3 = p["frontier3_aska_physical_voigt_truss"]
        self.assertEqual(f3["voigt_group_orders"], {"D2_faithful_from_D2h": 4, "C3": 3})
        self.assertEqual(f3["d2h_voigt_isotypic_ranks"], {"Ag_axial": 3, "B1g_xy": 1, "B2g_xz": 1, "B3g_yz": 1})
        modes = f3["f3_periodic_modes"]
        self.assertEqual(modes["none"]["C11"], "2/9")
        self.assertEqual(modes["none"]["C12"], "1/18")
        self.assertEqual(modes["none"]["C44"], "0")
        self.assertEqual(modes["none"]["inertia"], [3, 0, 3])
        self.assertTrue(modes["none"]["d2h_schur"]["coupling_vanishes"])
        self.assertEqual(modes["one_per_plane"]["C14_axial_shear"], "-26/253")
        self.assertEqual(modes["one_per_plane"]["C44"], "34/253")
        self.assertFalse(modes["one_per_plane"]["d2h_schur"]["equivariant"])
        self.assertFalse(modes["one_per_plane"]["d2h_schur"]["coupling_vanishes"])
        self.assertTrue(modes["one_per_plane"]["c3_equivariant"])
        self.assertEqual(modes["half_2_opp"]["C11"], "31/55")
        self.assertEqual(modes["half_2_opp"]["C12"], "29/110")
        self.assertEqual(modes["half_2_opp"]["C44"], "1/4")
        self.assertEqual(modes["half_2_opp"]["C14_axial_shear"], "0")
        self.assertEqual(modes["half_2_opp"]["shear_per_tie"], "1/24")
        self.assertEqual(modes["half_2_opp"]["inertia"], [6, 0, 0])
        self.assertTrue(modes["half_2_opp"]["d2h_schur"]["equivariant"])
        self.assertTrue(modes["half_2_opp"]["d2h_schur"]["coupling_vanishes"])
        self.assertEqual(modes["full_4"]["C11"], "1")
        self.assertEqual(modes["full_4"]["C12"], "1/2")
        self.assertEqual(modes["full_4"]["C44"], "1/2")
        self.assertEqual(modes["full_4"]["shear_per_tie"], "1/24")
        self.assertEqual(modes["full_4"]["C14_axial_shear"], "0")

        truss = f3["two_bar_z2_truss"]
        self.assertEqual(truss["flat_singular_9_10_11_10"]["H_q"], [["200/99", "0"], ["0", "0"]])
        self.assertEqual(truss["flat_singular_9_10_11_10"]["quartic_y4_coeff"], "257500/970299")
        self.assertTrue(truss["flat_singular_9_10_11_10"]["schur_z2"]["coupling_vanishes"])
        self.assertEqual(truss["online_saddle_9_10_11_10"]["H_q"], [["200/99", "0"], ["0", "-2000/209"]])
        self.assertEqual(truss["broken_z2_corner_7_10_3_2"]["det_H"], "64/105")
        self.assertEqual(truss["broken_z2_corner_7_10_3_2"]["tr_H"], "44/21")
        self.assertTrue(truss["broken_z2_corner_7_10_3_2"]["exact_pythagorean_check"])
        self.assertFalse(truss["broken_z2_corner_7_10_3_2"]["schur_z2"]["coupling_vanishes"])

        pre = f3["anchored_6spoke_prestress"]
        self.assertTrue(pre["tension_1_10_11"]["equilibrium_zero_residual"])
        self.assertEqual(pre["tension_1_10_11"]["omega_int_inertia"], [7, 0, 0])
        self.assertEqual(pre["tension_1_10_11"]["omega_full_inertia"], [12, 0, 1])
        self.assertEqual(pre["compression_1_neg10_neg9"]["omega_int_inertia"], [0, 7, 0])

    def test_02_linear_algebra_and_group_error_branches(self) -> None:
        # 2x2 off-diagonal Bunch-Kaufman pivot with row swaps and Schur update (size 4)
        M_bk = [
            [Fraction(0), Fraction(0), Fraction(0), Fraction(0)],
            [Fraction(0), Fraction(0), Fraction(0), Fraction(2)],
            [Fraction(0), Fraction(0), Fraction(0), Fraction(1)],
            [Fraction(0), Fraction(2), Fraction(1), Fraction(0)],
        ]
        self.assertEqual(oracle.sylvester_inertia_q(M_bk), (1, 1, 2))
        M_swap_diag = [[Fraction(0), Fraction(0)], [Fraction(0), Fraction(-3)]]
        self.assertEqual(oracle.sylvester_inertia_q(M_swap_diag), (0, 1, 1))
        M_3bk = [
            [Fraction(0), Fraction(0), Fraction(2)],
            [Fraction(0), Fraction(0), Fraction(3)],
            [Fraction(2), Fraction(3), Fraction(0)],
        ]
        self.assertEqual(oracle.sylvester_inertia_q(M_3bk), (1, 1, 1))
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.sylvester_inertia_q([[0, 1], [0, 0]])
        self.assertEqual(cm.exception.code, "NON_SYMMETRIC_MATRIX")

        # Singular linear solve & rank edge cases
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.solve_linear_multi_q([[Fraction(1), Fraction(0)], [Fraction(0), Fraction(0)]], [[Fraction(1)], [Fraction(1)]])
        self.assertEqual(cm.exception.code, "SINGULAR_MATRIX")
        rk, pivs = oracle.matrix_rank_q([[Fraction(0), Fraction(2)], [Fraction(1), Fraction(0)]], 2)
        self.assertEqual((rk, pivs), (2, [0, 1]))
        rk0, pivs0 = oracle.matrix_rank_q([[Fraction(0), Fraction(0)]], 2)
        self.assertEqual((rk0, pivs0), (0, []))

        # Group verification rejections
        I2 = oracle.eye_q(2)
        negI2 = [[Fraction(-1), Fraction(0)], [Fraction(0), Fraction(-1)]]
        rot90 = [[Fraction(0), Fraction(-1)], [Fraction(1), Fraction(0)]]
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.verify_finite_orthogonal_group([I2, oracle.eye_q(3)])
        self.assertEqual(cm.exception.code, "DIM_MISMATCH")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.verify_finite_orthogonal_group([[[Fraction(2), Fraction(0)], [Fraction(0), Fraction(1)]]])
        self.assertEqual(cm.exception.code, "NON_ORTHOGONAL")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.verify_finite_orthogonal_group([I2, I2])
        self.assertEqual(cm.exception.code, "DUPLICATE_GROUP_ELEMENT")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.verify_finite_orthogonal_group([negI2])
        self.assertEqual(cm.exception.code, "MISSING_IDENTITY")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.verify_finite_orthogonal_group([I2, rot90])
        self.assertEqual(cm.exception.code, "GROUP_NOT_CLOSED")

        # Projector & partition rejections
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.build_isotypic_projector_q([I2, negI2], [Fraction(1)], 1)
        self.assertEqual(cm.exception.code, "CHAR_LEN_MISMATCH")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.build_isotypic_projector_q([I2, negI2], [Fraction(4), Fraction(0)], 1)
        self.assertEqual(cm.exception.code, "INVALID_PROJECTOR")
        # Valid trace non-integer cannot occur when P^2=P=P^T over Q, test partition mismatch & non-orthogonal
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.verify_isotypic_partition([I2, I2], 2)
        self.assertEqual(cm.exception.code, "PARTITION_SUM_MISMATCH")
        half = [[Fraction(1, 2), Fraction(0)], [Fraction(0), Fraction(1, 2)]]
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.verify_isotypic_partition([half, half], 2)
        self.assertEqual(cm.exception.code, "NON_ORTHOGONAL_PROJECTORS")

        # Unknown tie mode & unbalanced prestress control
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.homogenize_f3_cell_q("bad_mode")
        self.assertEqual(cm.exception.code, "UNKNOWN_TIE_MODE")
        unbal = oracle._verify_anchored_6spoke_prestress(Fraction(1), Fraction(1), Fraction(1))
        self.assertFalse(unbal["equilibrium_zero_residual"])

    def test_03_zone_b_validators_and_json_hardening(self) -> None:
        # Strict int / rat / seq / str / hex bounds (including bool & subclass rejections)
        for bad in (True, False, _EvilInt(1), "1", None):
            with self.assertRaises(oracle.SymmetryBridgeError):
                oracle.require_exact_int(bad, "x")
        self.assertEqual(oracle.require_exact_int((1 << 2048) - 1, "edge_ok"), (1 << 2048) - 1)
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.require_exact_int(1 << 2048, "big")
        self.assertEqual(cm.exception.code, "INT_BITS_EXCEEDED")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.require_exact_int(5, "x", lo=True)  # type: ignore[arg-type]
        self.assertEqual(cm.exception.code, "INVALID_BOUND")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.require_exact_int(5, "x", hi=_EvilInt(10))
        self.assertEqual(cm.exception.code, "INVALID_BOUND")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.require_exact_int(1, "x", lo=2)
        self.assertEqual(cm.exception.code, "INT_OUT_OF_RANGE")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.require_exact_int(5, "x", hi=4)
        self.assertEqual(cm.exception.code, "INT_OUT_OF_RANGE")
        self.assertEqual(oracle.require_exact_int(3, "x", lo=3, hi=3), 3)

        self.assertEqual(oracle.require_exact_rat(2, "q"), Fraction(2))
        self.assertEqual(oracle.require_exact_rat(Fraction(3, 5), "q"), Fraction(3, 5))
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.require_exact_rat(Fraction(1 << 2049, 1), "q")
        self.assertEqual(cm.exception.code, "RAT_BITS_EXCEEDED")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.require_exact_rat(Fraction(1, 1 << 2049), "q")
        self.assertEqual(cm.exception.code, "RAT_BITS_EXCEEDED")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.require_exact_rat("3/5", "q")
        self.assertEqual(cm.exception.code, "INVALID_RATIONAL")

        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.require_exact_seq(_EvilList([1]), "s")
        self.assertEqual(cm.exception.code, "INVALID_SEQ")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.require_exact_seq([1], "s", min_len=2, max_len=3)
        self.assertEqual(cm.exception.code, "SEQ_LEN_ERROR")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.require_exact_seq([1, 2, 3], "s", min_len=1, max_len=2)
        self.assertEqual(cm.exception.code, "SEQ_LEN_ERROR")

        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.require_exact_str(_EvilStr("a"), "s")
        self.assertEqual(cm.exception.code, "INVALID_STR")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.require_exact_str("\ud800", "s")
        self.assertEqual(cm.exception.code, "INVALID_UTF8_STR")

        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.require_hex_sha256("A" * 64, "h")
        self.assertEqual(cm.exception.code, "INVALID_SHA256")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.require_hex_sha256("a" * 63, "h")
        self.assertEqual(cm.exception.code, "INVALID_SHA256")

        # Strict JSON text rejections
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.parse_strict_json_text("{}", require_object=1)  # type: ignore[arg-type]
        self.assertEqual(cm.exception.code, "INVALID_FLAG")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.parse_strict_json_text("{}\r\n")
        self.assertEqual(cm.exception.code, "CRLF_FORBIDDEN")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.parse_strict_json_text('{"a": 1.5}')
        self.assertEqual(cm.exception.code, "FLOAT_FORBIDDEN")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.parse_strict_json_text('{"a": NaN}')
        self.assertEqual(cm.exception.code, "NONFINITE_FORBIDDEN")
        max_2048_str = str((1 << 2048) - 1)
        self.assertEqual(len(max_2048_str), oracle.MAX_INT_DIGITS)
        self.assertEqual(oracle.parse_strict_json_text('{"a":' + max_2048_str + "}")["a"], (1 << 2048) - 1)
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.parse_strict_json_text('{"a": ' + ("9" * (oracle.MAX_INT_DIGITS + 1)) + "}")
        self.assertEqual(cm.exception.code, "INT_DIGITS_EXCEEDED")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.parse_strict_json_text('{"a": ' + str(1 << 2048) + "}")
        self.assertEqual(cm.exception.code, "INT_BITS_EXCEEDED")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.parse_strict_json_text('{"a": 1, "\\u0061": 2}')
        self.assertEqual(cm.exception.code, "DUPLICATE_KEY")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.parse_strict_json_text("[1, 2]", require_object=True)
        self.assertEqual(cm.exception.code, "NON_OBJECT_ROOT")
        self.assertEqual(oracle.parse_strict_json_text("[1, null, true]", require_object=False), [1, None, True])
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.parse_strict_json_text('{"a": "\\ud800"}')
        self.assertEqual(cm.exception.code, "INVALID_UTF8_STR")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.parse_strict_json_text("{bad")
        self.assertEqual(cm.exception.code, "INVALID_JSON")

        oracle.validate_json_tree_iterative([0], max_depth=1)
        oracle.validate_json_tree_iterative({"ok": (1 << 2048) - 1})
        deep = "[" * 70 + "0" + "]" * 70
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.parse_strict_json_text(deep, require_object=False)
        self.assertEqual(cm.exception.code, "JSON_DEPTH_EXCEEDED")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.validate_json_tree_iterative({"a": (1, 2)})
        self.assertEqual(cm.exception.code, "FORBIDDEN_JSON_TYPE")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.validate_json_tree_iterative({"a": 1 << 2048})
        self.assertEqual(cm.exception.code, "INT_BITS_EXCEEDED")
        with patch.object(oracle, "MAX_JSON_BYTES", 8):
            self.assertEqual(oracle.parse_strict_json_text('{"a": 1}'), {"a": 1})
            with self.assertRaises(oracle.SymmetryBridgeError) as cm:
                oracle.parse_strict_json_text('{"long_key": 12345}')
            self.assertEqual(cm.exception.code, "JSON_TOO_LARGE")

        # Oracle invariant fail-closed guard (kills M058)
        bad_f1 = copy.deepcopy(oracle.analyze_frontier1_siliquant_e8())
        bad_f1["e8_root_count"] = 239
        with patch.object(oracle, "analyze_frontier1_siliquant_e8", return_value=bad_f1):
            with self.assertRaises(oracle.SymmetryBridgeError) as cm:
                oracle.build_payload()
            self.assertEqual(cm.exception.code, "ORACLE_INVARIANT_FAILED")

    def test_04_certificate_tamper_paths_and_cli(self) -> None:
        cert = oracle.build_certificate()
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.verify_certificate_object(_EvilDict(cert))
        self.assertEqual(cm.exception.code, "NON_OBJECT_CERT")

        bad_keys = dict(cert)
        bad_keys["extra"] = 1
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.verify_certificate_object(bad_keys)
        self.assertEqual(cm.exception.code, "INVALID_CERT_KEYS")

        bad_schema = dict(cert, schema="wrong")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.verify_certificate_object(bad_schema)
        self.assertEqual(cm.exception.code, "INVALID_SCHEMA")

        bad_track = dict(cert, track_id="wrong")
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.verify_certificate_object(bad_track)
        self.assertEqual(cm.exception.code, "INVALID_TRACK_ID")

        bad_payload_type = dict(cert, payload=[])
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.verify_certificate_object(bad_payload_type)
        self.assertEqual(cm.exception.code, "INVALID_PAYLOAD_TYPE")

        bad_p_sha = dict(cert, payload_sha256="0" * 64)
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.verify_certificate_object(bad_p_sha)
        self.assertEqual(cm.exception.code, "PAYLOAD_SHA_MISMATCH")

        bad_c_sha = dict(cert, certificate_sha256="0" * 64)
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.verify_certificate_object(bad_c_sha)
        self.assertEqual(cm.exception.code, "CERT_SHA_MISMATCH")

        # Hollow re-signed forgery (ZB13)
        hollow_payload = {"hollow": True}
        hp_sha = oracle.sha256_canonical(hollow_payload)
        h_outer = {"schema": oracle.CERT_SCHEMA, "track_id": oracle.CERT_TRACK_ID, "payload_sha256": hp_sha, "payload": hollow_payload}
        hc_sha = oracle.sha256_canonical(h_outer)
        hollow_cert = dict(h_outer, certificate_sha256=hc_sha)
        with self.assertRaises(oracle.SymmetryBridgeError) as cm:
            oracle.verify_certificate_object(hollow_cert)
        self.assertEqual(cm.exception.code, "ORACLE_RECOMPUTATION_MISMATCH")

        # Path / Symlink / FIFO / CRLF / Non-canonical / CLI tests in isolated tempdir
        with tempfile.TemporaryDirectory() as td:
            td_path = Path(td)
            cert_path = td_path / "cert.json"

            # Standalone text + default no-arg + json + write + check
            buf = io.StringIO()
            with patch.object(audit, "build_certificate", return_value=cert), patch("sys.stdout", buf):
                self.assertEqual(audit.main(["--standalone"]), 0)
            self.assertIn("PASS TRACK-S21E", buf.getvalue())

            buf = io.StringIO()
            with patch.object(audit, "build_certificate", return_value=cert), patch("sys.stdout", buf):
                self.assertEqual(audit.main([]), 0)
            self.assertIn("PASS TRACK-S21E", buf.getvalue())

            buf = io.StringIO()
            with patch.object(audit, "build_certificate", return_value=cert), patch("sys.stdout", buf):
                self.assertEqual(audit.main(["--standalone", "--json"]), 0)
            self.assertEqual(buf.getvalue().encode("ascii"), oracle.canonical_json_bytes(cert))

            # Overwrite existing regular file cleanly via --write (real oracle)
            cert_path.write_text("stale", encoding="ascii")
            buf = io.StringIO()
            with patch("sys.stdout", buf):
                self.assertEqual(audit.main(["--write", str(cert_path)]), 0)
            self.assertIn("WROTE cert.json", buf.getvalue())

            buf = io.StringIO()
            with patch("sys.stdout", buf):
                self.assertEqual(audit.main(["--check", str(cert_path)]), 0)
            self.assertIn("OK TRACK-S21E", buf.getvalue())

            # Unreadable file (OSError on os.read) fails closed
            with patch("os.read", side_effect=PermissionError("denied")):
                with self.assertRaises(oracle.SymmetryBridgeError) as cm:
                    oracle.verify_certificate_file(cert_path)
                self.assertEqual(cm.exception.code, "FILE_MISSING_OR_UNREADABLE")

            # Non-canonical bytes (extra trailing space) rejected
            non_canon = td_path / "non_canon.json"
            non_canon.write_bytes(cert_path.read_bytes() + b"\n")
            with self.assertRaises(oracle.SymmetryBridgeError) as cm:
                oracle.verify_certificate_file(non_canon)
            self.assertEqual(cm.exception.code, "NON_CANONICAL_BYTES")

            # CRLF bytes rejected
            crlf_path = td_path / "crlf.json"
            crlf_path.write_bytes(cert_path.read_bytes().replace(b"\n", b"\r\n"))
            with self.assertRaises(oracle.SymmetryBridgeError) as cm:
                oracle.verify_certificate_file(crlf_path)
            self.assertEqual(cm.exception.code, "CRLF_FORBIDDEN")

            # Invalid UTF-8 rejected
            bad_utf8 = td_path / "bad_utf8.json"
            bad_utf8.write_bytes(b"\xff\xfe")
            with self.assertRaises(oracle.SymmetryBridgeError) as cm:
                oracle.verify_certificate_file(bad_utf8)
            self.assertEqual(cm.exception.code, "INVALID_UTF8")

            # Exact MAX_JSON_BYTES file boundary passes; oversize rejected BEFORE os.read();
            # AND st_size==0 pseudofile (/proc/kallsyms-style) is bounded by streaming cap!
            exact_size = cert_path.stat().st_size
            with patch.object(oracle, "MAX_JSON_BYTES", exact_size), patch.object(oracle, "build_certificate", return_value=cert):
                self.assertEqual(oracle.verify_certificate_file(cert_path)["certificate_sha256"], cert["certificate_sha256"])
            with patch.object(oracle, "MAX_JSON_BYTES", 10), patch("os.read", side_effect=RuntimeError("must_not_read")):
                with self.assertRaises(oracle.SymmetryBridgeError) as cm:
                    oracle.verify_certificate_file(cert_path)
                self.assertEqual(cm.exception.code, "JSON_TOO_LARGE")

            real_fstat = os.fstat

            def _zero_size_fstat(fd: int) -> os.stat_result:
                st = real_fstat(fd)
                return os.stat_result((st.st_mode, st.st_ino, st.st_dev, st.st_nlink, st.st_uid, st.st_gid, 0, st.st_atime, st.st_mtime, st.st_ctime))

            with patch("os.fstat", side_effect=_zero_size_fstat), patch.object(oracle, "MAX_JSON_BYTES", exact_size), patch.object(oracle, "build_certificate", return_value=cert):
                self.assertEqual(oracle.verify_certificate_file(cert_path)["certificate_sha256"], cert["certificate_sha256"])
            with patch("os.fstat", side_effect=_zero_size_fstat), patch.object(oracle, "MAX_JSON_BYTES", 10), patch.object(oracle, "parse_strict_json_text", side_effect=RuntimeError("must_not_parse")):
                with self.assertRaises(oracle.SymmetryBridgeError) as cm:
                    oracle.verify_certificate_file(cert_path)
                self.assertEqual(cm.exception.code, "JSON_TOO_LARGE")

            # Missing file & directory & FIFO rejected
            with self.assertRaises(oracle.SymmetryBridgeError) as cm:
                oracle.verify_certificate_file(td_path / "missing.json")
            self.assertEqual(cm.exception.code, "FILE_MISSING_OR_UNREADABLE")
            with self.assertRaises(oracle.SymmetryBridgeError) as cm:
                oracle.verify_certificate_file(td_path)
            self.assertEqual(cm.exception.code, "NON_REGULAR_FILE")

            fifo_path = td_path / "pipe.fifo"
            os.mkfifo(fifo_path)
            with self.assertRaises(oracle.SymmetryBridgeError) as cm:
                oracle.verify_certificate_file(fifo_path)
            self.assertEqual(cm.exception.code, "NON_REGULAR_FILE")
            with self.assertRaises(oracle.SymmetryBridgeError) as cm:
                audit.write_certificate_file(fifo_path)
            self.assertEqual(cm.exception.code, "INVALID_WRITE_TARGET")

            # Symlink target, symlink ancestor, symlink PWD, EvilPath, NUL, empty path
            sym_file = td_path / "sym.json"
            os.symlink(cert_path, sym_file)
            with self.assertRaises(oracle.SymmetryBridgeError) as cm:
                oracle.verify_certificate_file(sym_file)
            self.assertEqual(cm.exception.code, "SYMLINK_ANCESTOR_FORBIDDEN")

            real_sub = td_path / "real_sub"
            real_sub.mkdir()
            (real_sub / "c.json").write_bytes(cert_path.read_bytes())
            sym_dir = td_path / "sym_dir"
            os.symlink(real_sub, sym_dir)
            with self.assertRaises(oracle.SymmetryBridgeError) as cm:
                oracle.verify_certificate_file(sym_dir / "c.json")
            self.assertEqual(cm.exception.code, "SYMLINK_ANCESTOR_FORBIDDEN")
            with self.assertRaises(oracle.SymmetryBridgeError) as cm:
                oracle.require_no_symlink_path(str(sym_dir) + "/../cert.json")
            self.assertEqual(cm.exception.code, "SYMLINK_ANCESTOR_FORBIDDEN")

            # Symlinked PWD with relative path rejected
            old_cwd = os.getcwd()
            try:
                os.chdir(real_sub)
                with patch.dict(os.environ, {"PWD": str(sym_dir)}):
                    with self.assertRaises(oracle.SymmetryBridgeError) as cm:
                        oracle.verify_certificate_file("c.json")
                    self.assertEqual(cm.exception.code, "SYMLINK_ANCESTOR_FORBIDDEN")
                # Clean relative path succeeds when PWD is real or unset
                with patch.object(oracle, "build_certificate", return_value=cert):
                    with patch.dict(os.environ, {"PWD": str(real_sub)}):
                        self.assertEqual(oracle.verify_certificate_file("c.json")["certificate_sha256"], cert["certificate_sha256"])
                    with patch.dict(os.environ, {"PWD": ""}):
                        self.assertEqual(oracle.verify_certificate_file("c.json")["certificate_sha256"], cert["certificate_sha256"])
            finally:
                os.chdir(old_cwd)

            for bad_path in (123, _EvilStr(str(cert_path)), _EvilPath(str(cert_path)), "", "a\x00b"):
                with self.assertRaises(oracle.SymmetryBridgeError):
                    oracle.require_no_symlink_path(bad_path)

            # Write parent missing / non-dir
            with self.assertRaises(oracle.SymmetryBridgeError) as cm:
                audit.write_certificate_file(td_path / "no_parent" / "c.json")
            self.assertEqual(cm.exception.code, "PARENT_MISSING")
            with self.assertRaises(oracle.SymmetryBridgeError) as cm:
                audit.write_certificate_file(cert_path / "child.json")
            self.assertEqual(cm.exception.code, "INVALID_PARENT")

            # CLI error branches with exact error codes (kills every fallthrough mutant!)
            for bad_argv, expected_code in (
                (123, "INVALID_ARGV"),
                ([123], "INVALID_STR"),
                (["a\x00b"], "INVALID_ARGV_NUL"),
                (["--bogus"], "UNKNOWN_FLAG"),
                (["--write"], "MISSING_ARG"),
                (["--check"], "MISSING_ARG"),
                (["--standalone", "--check", str(cert_path)], "CONFLICTING_MODE"),
                (["--write", str(cert_path), "--standalone"], "CONFLICTING_MODE"),
                (["--check", str(cert_path), "--json"], "INVALID_FLAG_COMBO"),
            ):
                err = io.StringIO()
                with patch("sys.stderr", err):
                    rc = audit.main(bad_argv)
                self.assertEqual(rc, 1)
                self.assertIn(expected_code, err.getvalue())

            # main(None) uses sys.argv[1:]
            buf = io.StringIO()
            with patch.object(audit, "build_certificate", return_value=cert), patch("sys.argv", ["audit.py", "--standalone"]), patch("sys.stdout", buf):
                self.assertEqual(audit.main(None), 0)
            self.assertIn("PASS TRACK-S21E", buf.getvalue())

            # Write failure cleans up temp file
            with patch.object(audit, "build_certificate", return_value=cert), patch("os.replace", side_effect=OSError("disk full")):
                with self.assertRaises(oracle.SymmetryBridgeError) as cm:
                    audit.write_certificate_file(td_path / "fail_write.json")
                self.assertEqual(cm.exception.code, "WRITE_FAILED")
            leftovers = [f for f in td_path.iterdir() if ".tmp." in f.name]
            self.assertEqual(leftovers, [])


if __name__ == "__main__":
    unittest.main()
