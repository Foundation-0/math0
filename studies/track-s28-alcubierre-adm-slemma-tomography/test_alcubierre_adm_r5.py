#!/usr/bin/env python3
"""Track S28: R5 Pure-Q Adversarial, Algebraic, Mutation & Zone-B Test Suite.

Pure Python 3 standard library: zero floats, zero bare asserts, zero RNG.
Covers all 5 exact-Q pillars, negative controls, exact Krein inertia / S-lemma
boundaries, full-replay tampering, secondary algebraic audit tampering, and
race-free dir_fd / atomic O_EXCL + os.replace / CLI Zone-B enforcement.
"""
from __future__ import annotations

import copy
from fractions import Fraction
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

_THIS_DIR = str(Path(__file__).resolve().parent)
if _THIS_DIR not in sys.path:
    sys.path.insert(0, _THIS_DIR)

import alcubierre_adm_audit as audit
import alcubierre_adm_oracle as oracle


class _PathSubclass(type(Path("."))):
    pass


def _resign_cert(cert: dict) -> dict:
    out = copy.deepcopy(cert)
    payload_sha = oracle.canonical_sha256(out["payload"])
    out["payload_sha256"] = payload_sha
    env = {
        "schema": out["schema"],
        "track_id": out["track_id"],
        "payload_sha256": payload_sha,
        "payload": out["payload"],
    }
    out["certificate_sha256"] = oracle.canonical_sha256(env)
    return out


class TestPillarMathematicsAndControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.cert = oracle.build_standalone_certificate()
        cls.payload = cls.cert["payload"]

    def test_top_level_certificate_and_determinism(self) -> None:
        cert2 = oracle.build_standalone_certificate()
        self.assertEqual(self.cert["payload_sha256"], cert2["payload_sha256"])
        self.assertEqual(self.cert["certificate_sha256"], cert2["certificate_sha256"])
        self.assertEqual(self.cert["schema"], oracle.SCHEMA_VERSION)
        self.assertEqual(self.cert["track_id"], oracle.TRACK_ID)
        self.assertEqual(self.payload["oracle_class"], "exact")
        self.assertEqual(self.payload["novelty_tier"], "N1")
        self.assertIs(self.payload["zero_trust_path_floats"], True)
        self.assertIs(self.payload["zero_rng"], True)
        self.assertIs(self.payload["zero_bare_asserts"], True)
        res = oracle.validate_certificate_payload(self.cert, full_replay=True)
        self.assertIs(res["valid"], True)
        self.assertIs(res["full_replay"], True)
        sec = audit.secondary_algebraic_audit(self.payload)
        self.assertIs(sec["secondary_audit_passed"], True)
        self.assertEqual(sec["gp_radii_checked"], 4)
        self.assertEqual(sec["equatorial_stations_checked"], 3)
        self.assertEqual(sec["stokes_ratios_checked"], 4)

    def test_pillar1_adm_gp_duality_and_type_iv_trigger(self) -> None:
        p1 = self.payload["pillar1_arbitrary_lapse_adm"]
        self.assertIs(p1["arbitrary_lapse_hamiltonian_residual_zero"], True)
        self.assertIs(p1["arbitrary_lapse_momentum_residuals_zero"], True)
        self.assertIs(p1["unit_lapse_pointwise_sign_flip_residual_zero"], True)
        self.assertIs(p1["compact_bubble_int_div_J_zero"], True)
        self.assertIs(p1["compact_bubble_sign_flip_duality_exact"], True)
        self.assertEqual(p1["gullstrand_painleve_M"], "2")
        self.assertEqual(len(p1["gullstrand_painleve_checks"]), 4)
        for gp, expected_r, expected_b in zip(
            p1["gullstrand_painleve_checks"], ("1", "4", "9", "16"), ("2", "1", "2/3", "1/2")
        ):
            self.assertEqual(gp["r"], expected_r)
            self.assertEqual(gp["beta_r"], expected_b)
            self.assertIs(gp["vacuum_G_zero"], True)
            self.assertIs(gp["rho_E_zero"], True)
            self.assertIs(gp["omega_zero"], True)
            self.assertEqual(gp["flux_J_ADM_over_pi"], "32")
            self.assertIs(gp["flux_equals_16M"], True)

        om_sq = oracle.parse_exact_rational(p1["compact_bubble_int_omega_sq"])
        rho16 = oracle.parse_exact_rational(p1["compact_bubble_int_16pi_rhoE"])
        neg2 = oracle.parse_exact_rational(p1["compact_bubble_int_neg_2G00"])
        self.assertEqual(om_sq, Fraction(65536, 7875))
        self.assertEqual(rho16, -Fraction(1, 2) * om_sq)
        self.assertEqual(neg2, -rho16)

        iv = p1["irrotational_non_unit_lapse_type_iv"]
        self.assertEqual(iv["N"], "3/2")
        self.assertEqual(iv["grad_N_x"], "5")
        self.assertIs(iv["omega_zero"], True)
        self.assertEqual(iv["G_hat_00"], "4/3")
        self.assertEqual(iv["G_hat_01"], "-40/9")
        self.assertEqual(iv["G_hat_11"], "-4/3")
        self.assertEqual(iv["discriminant_01"], "-6400/81")
        self.assertIs(iv["eulerian_rho_strictly_positive"], True)
        self.assertIs(iv["hawking_ellis_type_iv_certified"], True)
        self.assertIs(iv["unit_lapse_control_flux_zero"], True)
        self.assertEqual(iv["null_nec_violation_witness"]["witness_value"], "-80/9")
        self.assertIs(iv["null_nec_violation_witness"]["violation_certified"], True)

    def test_pillar2_alcubierre_eos_and_two_type_iv_annuli(self) -> None:
        p2 = self.payload["pillar2_alcubierre_eos_type_iv"]
        self.assertIs(p2["off_equatorial_g00_formula_exact"], True)
        self.assertIs(p2["off_equatorial_wx_plus3_exact"], True)
        self.assertIs(p2["septic_profile_c3_smooth"], True)
        self.assertIs(p2["two_concentric_type_iv_annuli_certified"], True)
        self.assertIs(p2["type_iv_fraction_increases_as_v_to_0"], True)

        stations = p2["equatorial_stations"]
        self.assertEqual([s["hawking_ellis_type"] for s in stations], ["Type_IV", "Type_I", "Type_IV"])
        for st in stations:
            self.assertIs(st["w_x_equals_3"], True)
            self.assertIs(st["G_hat_01_formula_exact"], True)
            self.assertIs(st["discriminant_formula_exact"], True)
        self.assertEqual(stations[1]["rho"], "5")
        self.assertEqual(stations[1]["G_hat_00"], "-1225/1024")
        self.assertEqual(stations[1]["G_hat_11"], "-3675/1024")
        self.assertEqual(stations[1]["G_hat_01"], "-7/32")
        self.assertEqual(stations[1]["discriminant_01"], "1488081/65536")

        sweep = p2["velocity_sweep_as_v_decreases"]
        self.assertEqual([row["v"] for row in sweep], ["2", "1", "1/2", "1/5", "1/10"])
        self.assertEqual([row["type_iv_stations_of_19"] for row in sweep], [14, 16, 17, 18, 19])
        self.assertEqual(sweep[-1]["type_iv_fraction"], "1")

    def test_pillar3_slemma_krein_and_eulerian_blind_spot(self) -> None:
        p3 = self.payload["pillar3_slemma_krein_blind_spot"]
        self.assertEqual(p3["eta_inertia"], [3, 0, 1])
        self.assertEqual(p3["hyperbolic_2x2_inertia"], [1, 0, 1])
        self.assertEqual(p3["rank_deficient_3x3_inertia"], [1, 1, 1])
        self.assertIs(p3["boosted_perfect_fluid_offdiag_nonzero"], True)

        fl = p3["boosted_perfect_fluid_slemma"]
        self.assertIs(fl["nec_satisfied_all_observers"], True)
        self.assertIs(fl["wec_satisfied_all_observers"], True)
        self.assertIs(fl["sec_satisfied_all_observers"], True)
        self.assertIs(fl["dec_satisfied_all_observers"], True)
        self.assertEqual(fl["nec_inertia"], [4, 0, 0])
        self.assertEqual(fl["dec_flux_inertia"], [4, 0, 0])

        pw = p3["alcubierre_pythagorean_quadruple_null_witness"]
        self.assertEqual(pw["vector"], ["3", "2", "2", "1"])
        self.assertEqual(pw["eta_norm"], "0")
        self.assertIs(pw["violation_certified"], True)
        self.assertLess(oracle.parse_exact_rational(pw["witness_value"]), 0)

        bs = p3["eulerian_blind_spot_irrotational_type_i"]
        self.assertEqual(bs["G_hat_00"], "3")
        self.assertEqual(bs["G_hat_11"], "-9")
        self.assertIs(bs["G_hat_0i_all_zero"], True)
        self.assertIs(bs["eulerian_rho_positive_blind_spot"], True)
        self.assertEqual(bs["null_nec_violation"]["witness_value"], "-6")
        self.assertEqual(bs["boosted_timelike_wec_violation"]["eta_norm"], "-9")
        self.assertEqual(bs["boosted_timelike_wec_violation"]["witness_value"], "-69")
        self.assertEqual(bs["pythagorean_quadruple_7_6_3_2_null_violation"]["eta_norm"], "0")
        self.assertLess(oracle.parse_exact_rational(bs["pythagorean_quadruple_7_6_3_2_null_violation"]["witness_value"]), 0)

    def test_pillar4_natario_stokes_beltrami_and_horizons(self) -> None:
        p4 = self.payload["pillar4_natario_beltrami_horizons"]
        self.assertEqual(p4["stokes_thin_wall_minimizer_constant"], "1/4")
        self.assertIs(p4["stokes_thin_wall_constant_equals_1_4"], True)
        self.assertEqual(p4["stokes_quintic_competitor_constant"], "5/14")
        self.assertIs(p4["stokes_euler_lagrange_cross_term_zero"], True)
        self.assertIs(p4["stokes_sos_gap_exact"], True)

        expected_e = ["2014683/6616", "41859/908", "1899/376", "93/68"]
        for row, exp_val in zip(p4["stokes_finite_aspect_resistance"], expected_e):
            self.assertEqual(row["E_stokes_over_v2R"], exp_val)
            self.assertIs(row["exceeds_thin_wall_quarter"], True)

        bel = p4["beltrami_s23a_bridge"]
        self.assertEqual(bel["wavevector"], [3, 4, 0])
        self.assertEqual(bel["lambda"], "5")
        self.assertIs(bel["natario_zero_expansion_exact"], True)
        self.assertIs(bel["beltrami_eigenmode_exact"], True)
        self.assertIs(bel["force_free_momentum_exact"], True)
        self.assertEqual(bel["helicity_density_beta_dot_omega"], "5")
        self.assertEqual(bel["energy_16pi_rhoE"], "-25/2")
        self.assertIs(bel["energy_equals_neg_lam_over_2_helicity"], True)
        self.assertEqual(bel["h_coulomb_norm"], "1/5")

        kh = p4["killing_horizons"]
        self.assertEqual(kh["superluminal_v"], "2")
        self.assertEqual(kh["horizon_radius_rH"], "5")
        self.assertEqual(kh["f_at_rH"], "1/2")
        self.assertIs(kh["g_tt_comoving_at_rH_zero"], True)
        self.assertEqual(kh["front_horizon_type"], "white_hole_blueshift")
        self.assertEqual(kh["rear_horizon_type"], "black_hole_hawking")
        self.assertEqual(kh["surface_gravity_front_kappa"], "-35/16")
        self.assertEqual(kh["surface_gravity_rear_kappa"], "35/16")
        self.assertIs(kh["front_christoffel_killing_exact"], True)
        self.assertIs(kh["rear_christoffel_killing_exact"], True)
        self.assertIs(kh["kappa_antisymmetry_and_signs_exact"], True)
        self.assertEqual(kh["subluminal_v"], "3/5")
        self.assertEqual(kh["subluminal_max_g_tt"], "-16/25")
        self.assertIs(kh["subluminal_horizon_free"], True)
        self.assertEqual(kh["pfenning_ford_wall_scaling_exponent_v_sq"], 2)

        # Direct 4D comoving Christoffel Gamma^mu_{00} verification at x' = +5 (front white) & x' = -5 (rear black)
        for sign, expected_k in ((Fraction(1, 1), Fraction(-35, 16)), (Fraction(-1, 1), Fraction(35, 16))):
            df_dxp = sign * Fraction(-35, 32)
            bp = -Fraction(2, 1) * df_dxp
            g_h = [
                [Fraction(0, 1), Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)],
                [Fraction(1, 1), Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)],
                [Fraction(0, 1), Fraction(0, 1), Fraction(1, 1), Fraction(0, 1)],
                [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1), Fraction(1, 1)],
            ]
            dg_h = [[[Fraction(0, 1)] * 4 for _ in range(4)] for _ in range(4)]
            dg_h[0][0][1] = 2 * bp
            dg_h[0][1][1] = dg_h[1][0][1] = bp
            gam = oracle.christoffel_from_metric_jet(g_h, dg_h)
            self.assertEqual(gam[0][0][0], expected_k)
            self.assertEqual([gam[m][0][0] for m in (1, 2, 3)], [Fraction(0, 1)] * 3)

    def test_pillar5_lichnerowicz_vdb_and_physical_shells(self) -> None:
        p5 = self.payload["pillar5_physical_subluminal_shells"]
        self.assertIs(p5["lichnerowicz_general_hamiltonian_residual_zero"], True)
        self.assertIs(p5["vdb_compact_collar_int_psi5_R3_zero"], True)
        self.assertEqual(p5["schwarzschild_tail_ADM_mass_M"], "2")
        self.assertEqual(p5["schwarzschild_tail_int_psi5_R3_over_pi"], "32")
        self.assertEqual(p5["boost_velocity_v"], "3/5")

        sm = p5["smooth_conformally_flat_boosted_shell"]
        self.assertEqual(sm["G_hat_00_rest"], "140800/4084101")
        self.assertIs(sm["boosted_flux_G01_nonzero"], True)
        for cond in ("nec_satisfied_all_observers", "wec_satisfied_all_observers", "sec_satisfied_all_observers", "dec_satisfied_all_observers"):
            self.assertIs(sm["slemma_all_conditions"][cond], True)

        th = p5["israel_thin_shell_boosted"]
        self.assertEqual(th["R_over_M"], "50/9")
        self.assertIs(th["exceeds_buchdahl_9_4"], True)
        self.assertIs(th["exceeds_dec_threshold_25_12"], True)
        self.assertEqual(th["sigma_8piR"], "2/5")
        self.assertEqual(th["p_theta_8piR"], "1/40")
        self.assertIs(th["boosted_flux_nonzero"], True)
        for cond in ("nec_satisfied_all_observers", "wec_satisfied_all_observers", "sec_satisfied_all_observers", "dec_satisfied_all_observers"):
            self.assertIs(th["slemma_all_conditions"][cond], True)

        neg = p5["negative_control_sub_threshold_dec_violation"]
        self.assertEqual(neg["R_over_M"], "72/35")
        self.assertIs(neg["below_dec_threshold_25_12"], True)
        self.assertEqual(neg["dec_flux_violation_witness"]["eta_norm"], "-11")
        self.assertEqual(neg["dec_flux_violation_witness"]["witness_value"], "1225/144")
        self.assertIs(neg["dec_flux_violation_witness"]["violation_certified"], True)


class TestOraclePrimitivesAndGuards(unittest.TestCase):
    def _assert_err(self, code: str, fn, *args, **kwargs) -> None:
        with self.assertRaises(oracle.AlcubierreAdmError) as ctx:
            fn(*args, **kwargs)
        self.assertEqual(ctx.exception.code, code)

    def test_int_bool_str_sha_rational_guards(self) -> None:
        self.assertEqual(oracle.require_exact_int(0, "x", min_val=0, max_val=0), 0)
        self.assertEqual(oracle.require_exact_int(10 ** 999, "x"), 10 ** 999)
        self.assertEqual(oracle.require_exact_int(10 ** 1000 - 1, "x"), 10 ** 1000 - 1)
        self.assertEqual(oracle.require_exact_int(-(10 ** 1000 - 1), "x"), -(10 ** 1000 - 1))
        self._assert_err("INVALID_INT", oracle.require_exact_int, True, "x")
        self._assert_err("INVALID_INT", oracle.require_exact_int, "1", "x")
        self._assert_err("INT_DIGITS_EXCEEDED", oracle.require_exact_int, 10 ** 1000, "x")
        self._assert_err("INT_DIGITS_EXCEEDED", oracle.require_exact_int, 1 << (oracle.MAX_INT_DIGITS * 4 + 1), "x")
        self._assert_err("INT_DIGITS_EXCEEDED", oracle.require_exact_int, 1 << 20000, "huge")
        self._assert_err("INT_TOO_SMALL", oracle.require_exact_int, 4, "x", min_val=5)
        self._assert_err("INT_TOO_LARGE", oracle.require_exact_int, 6, "x", max_val=5)

        self.assertIs(oracle.require_exact_bool(True, "b"), True)
        self.assertIs(oracle.require_exact_bool(False, "b"), False)
        self._assert_err("INVALID_BOOL", oracle.require_exact_bool, 1, "b")
        self._assert_err("INVALID_BOOL", oracle.require_exact_bool, "true", "b")

        self.assertEqual(oracle.require_exact_str("", "s", non_empty=False), "")
        self.assertEqual(oracle.require_exact_str("ok", "s"), "ok")
        self._assert_err("INVALID_STR", oracle.require_exact_str, b"ok", "s")
        self._assert_err("EMPTY_STR", oracle.require_exact_str, "", "s")
        self._assert_err("INVALID_UTF8_SURROGATE", oracle.require_exact_str, "a\ud800b", "s")

        good_sha = "0123456789abcdef" * 4
        self.assertEqual(oracle.require_sha256_hex(good_sha, "h"), good_sha)
        self._assert_err("INVALID_SHA256", oracle.require_sha256_hex, good_sha[:-1], "h")
        self._assert_err("INVALID_SHA256", oracle.require_sha256_hex, good_sha + "0", "h")
        self._assert_err("INVALID_SHA256", oracle.require_sha256_hex, "A" * 64, "h")
        self._assert_err("INVALID_SHA256", oracle.require_sha256_hex, "g" * 64, "h")

        self.assertEqual(oracle.format_exact_rational(Fraction(0, 1)), "0")
        self.assertEqual(oracle.format_exact_rational(Fraction(-5, 1)), "-5")
        self.assertEqual(oracle.format_exact_rational(Fraction(-5, 3)), "-5/3")
        self.assertEqual(oracle.parse_exact_rational("-7"), Fraction(-7, 1))
        self.assertEqual(oracle.parse_exact_rational("7/3"), Fraction(7, 3))
        self.assertEqual(oracle.parse_exact_rational("0/9"), Fraction(0, 1))
        self.assertEqual(oracle.parse_exact_rational("9" * 1000 + "/" + "7" * 1000), Fraction(int("9" * 1000), int("7" * 1000)))
        for bad_q in (
            "1/2/3",
            "a/2",
            "1/b",
            "/2",
            "1/",
            "-/2",
            "1/-2",
            "+1/2",
            ":/1",
            "1/:",
            "²",
            "²/2",
            "1/²",
            "①",
            "1/①",
            "١٢/٣",
            "１２/３",
        ):
            self._assert_err("INVALID_RATIONAL", oracle.parse_exact_rational, bad_q)
        self._assert_err("INT_DIGITS_EXCEEDED", oracle.parse_exact_rational, "9" * 1001 + "/1")
        self._assert_err("INT_DIGITS_EXCEEDED", oracle.parse_exact_rational, "1/" + "9" * 1001)
        self._assert_err("ZERO_DENOMINATOR", oracle.parse_exact_rational, "1/0")

    def test_json_tree_parser_and_canonical_guards(self) -> None:
        oracle.validate_json_tree_iterative({"": ["", True, False, None, 0]}, max_depth=2)
        oracle.validate_json_tree_iterative({"a": 1}, max_depth=1)
        oracle.validate_json_tree_iterative({"a": 1}, max_depth=256)
        self._assert_err("INT_TOO_SMALL", oracle.validate_json_tree_iterative, {}, max_depth=0)
        self._assert_err("INT_TOO_LARGE", oracle.validate_json_tree_iterative, {}, max_depth=257)
        self._assert_err("JSON_DEPTH_EXCEEDED", oracle.validate_json_tree_iterative, {"a": {"b": 1}}, max_depth=1)
        self._assert_err("JSON_DEPTH_EXCEEDED", oracle.validate_json_tree_iterative, [[1]], max_depth=1)
        self._assert_err("INVALID_STR", oracle.validate_json_tree_iterative, {1: "a"})
        self._assert_err("INVALID_UTF8_SURROGATE", oracle.validate_json_tree_iterative, {"\ud800": "a"})
        self._assert_err("INVALID_UTF8_SURROGATE", oracle.validate_json_tree_iterative, {"a": "\ud800"})
        self._assert_err("INT_DIGITS_EXCEEDED", oracle.validate_json_tree_iterative, {"a": 10 ** 1000})
        self._assert_err("FORBIDDEN_JSON_TYPE", oracle.validate_json_tree_iterative, {"a": (1, 2)})
        self._assert_err("FORBIDDEN_JSON_TYPE", oracle.validate_json_tree_iterative, {"a": Fraction(1, 2)})

        # Exact MAX_JSON_BYTES boundary
        pad = oracle.MAX_JSON_BYTES - len('{"a":""}')
        exact_cap = '{"a":"' + ("x" * pad) + '"}'
        self.assertEqual(len(exact_cap.encode("utf-8")), oracle.MAX_JSON_BYTES)
        self.assertEqual(len(oracle.parse_strict_json_text(exact_cap)["a"]), pad)
        self._assert_err("JSON_TOO_LARGE", oracle.parse_strict_json_text, '{"a":"' + ("x" * (pad + 1)) + '"}')

        self._assert_err("FLOAT_FORBIDDEN", oracle.parse_strict_json_text, '{"a": 1.0}')
        self._assert_err("FLOAT_FORBIDDEN", oracle.parse_strict_json_text, '{"a": 1e3}')
        self._assert_err("NONFINITE_JSON_FORBIDDEN", oracle.parse_strict_json_text, '{"a": NaN}')
        self._assert_err("NONFINITE_JSON_FORBIDDEN", oracle.parse_strict_json_text, '{"a": Infinity}')
        self._assert_err("INT_DIGITS_EXCEEDED", oracle.parse_strict_json_text, '{"a": ' + ("9" * 1001) + '}')
        self._assert_err("INT_DIGITS_EXCEEDED", oracle.parse_strict_json_text, '{"a": ' + ("9" * 5000) + '}')
        self._assert_err("INT_DIGITS_EXCEEDED", oracle._strict_parse_int_token, "9" * 1001)
        self._assert_err("INT_DIGITS_EXCEEDED", oracle.parse_strict_json_text, '{"a": -' + ("9" * 1001) + '}')
        self.assertEqual(oracle.parse_strict_json_text('{"a": -' + ("9" * 1000) + '}')["a"], -int("9" * 1000))
        self._assert_err("DUPLICATE_JSON_KEY", oracle.parse_strict_json_text, '{"a": 1, "a": 2}')
        self._assert_err("INVALID_JSON", oracle.parse_strict_json_text, "{not_json")
        self._assert_err("ROOT_NOT_OBJECT", oracle.parse_strict_json_text, "[1, 2]", require_object=True)
        self.assertEqual(oracle.parse_strict_json_text("[1, 2]", require_object=False), [1, 2])
        self._assert_err("JSON_DEPTH_EXCEEDED", oracle.parse_strict_json_text, "[" * 66 + "0" + "]" * 66, require_object=False)

        self.assertEqual(oracle.canonical_json_bytes({"b": "\u00e9", "a": 1}), b'{"a":1,"b":"\\u00e9"}')
        with mock.patch.object(oracle.json, "dumps", side_effect=ValueError("boom")):
            self._assert_err("CANONICAL_ENCODE_ERROR", oracle.canonical_json_bytes, {"a": 1})

    def test_mpoly_linalg_krein_slemma_and_witness_boundaries(self) -> None:
        z_poly = oracle.MPoly.const(2, 0)
        self.assertEqual(z_poly.terms, {})
        x = oracle.MPoly.var(2, 0)
        y = oracle.MPoly.var(2, 1)
        self.assertEqual((x + (-x)).terms, {})
        self.assertEqual(x.scale(0).terms, {})
        self.assertEqual(x.pow(0).terms, {(0, 0): Fraction(1, 1)})
        self.assertEqual(x.pow(3).deriv(0).terms, {(2, 0): Fraction(3, 1)})
        self.assertEqual((x * y).integrate_unit_cube(), Fraction(0, 1))
        self.assertEqual((x.pow(2) * y.pow(2)).integrate_unit_cube(), Fraction(4, 9))
        # MPoly bounds & ring guards
        for bad_var in ((0, 0), (2, -1), (2, 2), (2, True)):
            with self.assertRaises(oracle.AlcubierreAdmError):
                oracle.MPoly.var(*bad_var)  # type: ignore[arg-type]
        self._assert_err("INT_TOO_SMALL", x.pow, -1)
        self._assert_err("INVALID_INT", x.pow, True)
        self._assert_err("INT_TOO_SMALL", x.deriv, -1)
        self._assert_err("INT_TOO_LARGE", x.deriv, 2)
        u1 = oracle.MPoly.var(1, 0)
        for bad_rhs in (u1, "not_poly"):
            with self.assertRaises(oracle.AlcubierreAdmError) as ctx_a:
                _ = x + bad_rhs  # type: ignore[operator]
            self.assertEqual(ctx_a.exception.code, "MPOLY_RING_MISMATCH")
            with self.assertRaises(oracle.AlcubierreAdmError) as ctx_s:
                _ = x - bad_rhs  # type: ignore[operator]
            self.assertEqual(ctx_s.exception.code, "MPOLY_RING_MISMATCH")
            with self.assertRaises(oracle.AlcubierreAdmError) as ctx_m:
                _ = x * bad_rhs  # type: ignore[operator]
            self.assertEqual(ctx_m.exception.code, "MPOLY_RING_MISMATCH")
        self._assert_err("MPOLY_DIM_MISMATCH", x.integrate_01_1d)

        # Strict exact-Fraction, shape, dimension, and symmetry guards across all linear-algebra & S-lemma helpers
        self._assert_err("INVALID_MATRIX", oracle.mat_inv_exact, 123)
        self._assert_err("INVALID_MATRIX", oracle.mat_inv_exact, "ab")
        self._assert_err("INVALID_MATRIX", oracle.mat_transpose_4x4, "ab")
        self._assert_err("INVALID_MATRIX", oracle.mat_inv_exact, [])
        self._assert_err("INVALID_MATRIX", oracle.mat_inv_exact, [123])
        self._assert_err("INVALID_MATRIX", oracle.mat_inv_exact, ["a"])
        self._assert_err(
            "INVALID_MATRIX_SHAPE",
            oracle.mat_inv_exact,
            [[Fraction(1, 1), Fraction(2, 1), Fraction(3, 1)], [Fraction(4, 1), Fraction(5, 1), Fraction(6, 1)]],
        )
        self._assert_err(
            "INVALID_MATRIX_SHAPE",
            oracle.mat_inv_exact,
            [[Fraction(1, 1)], [Fraction(2, 1), Fraction(3, 1)]],
        )
        self._assert_err("INVALID_FRACTION", oracle.mat_inv_exact, [[1, 2], [3, 4]])
        # Exact S28-BUG-03 regression: raw int matrix [[10^17, 10^17+1], [10^17+1, 10^17+2]] MUST fail closed;
        # exact Fraction matrix returns exact (1, 0, 1) (det = -1 < 0, NOT PSD!)
        big = 10 ** 17
        self._assert_err("INVALID_FRACTION", oracle.krein_inertia_exact, [[big, big + 1], [big + 1, big + 2]])
        big_f = [
            [Fraction(big, 1), Fraction(big + 1, 1)],
            [Fraction(big + 1, 1), Fraction(big + 2, 1)],
        ]
        self.assertEqual(oracle.krein_inertia_exact(big_f), (1, 0, 1))
        self.assertIs(oracle.is_psd_exact(big_f), False)

        # mat_inv_exact pivoting & singular
        m_swap = [
            [Fraction(0, 1), Fraction(2, 1)],
            [Fraction(3, 1), Fraction(1, 1)],
        ]
        inv_m = oracle.mat_inv_exact(m_swap)
        self.assertEqual(inv_m, [[Fraction(-1, 6), Fraction(1, 3)], [Fraction(1, 2), Fraction(0, 1)]])
        self._assert_err("SINGULAR_MATRIX", oracle.mat_inv_exact, [[Fraction(1, 1), Fraction(2, 1)], [Fraction(2, 1), Fraction(4, 1)]])
        # 5x5 rejected by 4x4 helpers & S-lemma
        eye5 = [[Fraction(1 if i == j else 0, 1) for j in range(5)] for i in range(5)]
        self._assert_err("INVALID_MATRIX_DIM", oracle.mat_mul_4x4, eye5, eye5)
        self._assert_err("INVALID_MATRIX_DIM", oracle.mat_transpose_4x4, eye5)
        self._assert_err("INVALID_MATRIX_DIM", oracle.quad_form_4, eye5, [Fraction(1, 1)] * 4)
        self._assert_err(
            "INVALID_MATRIX_DIM",
            oracle.certify_slemma_satisfaction,
            eye5,
            lam_nec=Fraction(1, 1),
            lam_wec=Fraction(1, 1),
            lam_sec=Fraction(1, 1),
            mu_dec=Fraction(1, 1),
        )
        self._assert_err("INVALID_FRACTION", oracle.adm_conformal_einstein_jet, 1, [Fraction(0, 1)] * 4, [[Fraction(0, 1)] * 4 for _ in range(4)], [Fraction(0, 1)] * 3, [[Fraction(0, 1)] * 4 for _ in range(3)], [[[Fraction(0, 1)] * 4 for _ in range(4)] for _ in range(3)])

        # krein_inertia_exact non-symmetric, diagonal pivot swap, 2x2 off-diagonal pivot swap with Schur update, pure zero
        self._assert_err("NON_SYMMETRIC_MATRIX", oracle.krein_inertia_exact, [[Fraction(1, 1), Fraction(1, 1)], [Fraction(0, 1), Fraction(1, 1)]])
        self.assertEqual(oracle.krein_inertia_exact([[Fraction(0, 1), Fraction(0, 1)], [Fraction(0, 1), Fraction(0, 1)]]), (0, 2, 0))
        self.assertEqual(
            oracle.krein_inertia_exact(
                [
                    [Fraction(0, 1), Fraction(0, 1)],
                    [Fraction(0, 1), Fraction(-5, 1)],
                ]
            ),
            (0, 1, 1),
        )
        # 4x4 zero-diagonal matrix with nonzero entries forcing p != k, q != k+1, and Schur complement update for i >= k+2
        m_hyp4 = [
            [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)],
            [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1), Fraction(2, 1)],
            [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1), Fraction(3, 1)],
            [Fraction(0, 1), Fraction(2, 1), Fraction(3, 1), Fraction(0, 1)],
        ]
        self.assertEqual(oracle.krein_inertia_exact(m_hyp4), (1, 2, 1))
        self.assertIs(oracle.is_psd_exact([[Fraction(2, 1), Fraction(0, 1)], [Fraction(0, 1), Fraction(0, 1)]]), True)
        self.assertIs(oracle.is_psd_exact(m_hyp4), False)

        # adm_conformal_einstein_jet scale validation
        z4 = [Fraction(0, 1)] * 4
        z44 = [[Fraction(0, 1)] * 4 for _ in range(4)]
        z3 = [Fraction(0, 1)] * 3
        z34 = [[Fraction(0, 1)] * 4 for _ in range(3)]
        z344 = [[[Fraction(0, 1)] * 4 for _ in range(4)] for _ in range(3)]
        self._assert_err("INVALID_ADM_SCALE", oracle.adm_conformal_einstein_jet, Fraction(0, 1), z4, z44, z3, z34, z344)
        self._assert_err("INVALID_ADM_SCALE", oracle.adm_conformal_einstein_jet, Fraction(1, 1), z4, z44, z3, z34, z344, Fraction(0, 1))

        # certify_slemma_satisfaction negative multipliers & inertia failure
        t_ok = [
            [Fraction(5, 1), Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)],
            [Fraction(0, 1), Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)],
            [Fraction(0, 1), Fraction(0, 1), Fraction(1, 1), Fraction(0, 1)],
            [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1), Fraction(1, 1)],
        ]
        bad_wec = oracle.certify_slemma_satisfaction(t_ok, lam_nec=Fraction(2, 1), lam_wec=Fraction(-1, 2), lam_sec=Fraction(2, 1), mu_dec=Fraction(10, 1))
        self.assertIs(bad_wec["nec_satisfied_all_observers"], True)
        self.assertIs(bad_wec["wec_satisfied_all_observers"], False)
        self.assertIs(bad_wec["dec_satisfied_all_observers"], False)
        bad_sec = oracle.certify_slemma_satisfaction(t_ok, lam_nec=Fraction(2, 1), lam_wec=Fraction(2, 1), lam_sec=Fraction(-1, 1), mu_dec=Fraction(10, 1))
        self.assertIs(bad_sec["sec_satisfied_all_observers"], False)
        bad_dec = oracle.certify_slemma_satisfaction(t_ok, lam_nec=Fraction(2, 1), lam_wec=Fraction(2, 1), lam_sec=Fraction(2, 1), mu_dec=Fraction(-1, 1))
        self.assertIs(bad_dec["wec_satisfied_all_observers"], True)
        self.assertIs(bad_dec["dec_satisfied_all_observers"], False)
        bad_mu = oracle.certify_slemma_satisfaction(t_ok, lam_nec=Fraction(2, 1), lam_wec=Fraction(2, 1), lam_sec=Fraction(2, 1), mu_dec=Fraction(30, 1))
        self.assertIs(bad_mu["dec_satisfied_all_observers"], False)

        # certify_causal_violation_witness boundaries (including independent sub-condition triggers!)
        t_neg = [
            [Fraction(-1, 1), Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)],
            [Fraction(0, 1), Fraction(-1, 1), Fraction(0, 1), Fraction(0, 1)],
            [Fraction(0, 1), Fraction(0, 1), Fraction(-1, 1), Fraction(0, 1)],
            [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1), Fraction(-1, 1)],
        ]
        self._assert_err("INVALID_WITNESS_VECTOR", oracle.certify_causal_violation_witness, t_ok, 123, "null")
        self._assert_err("INVALID_WITNESS_VECTOR", oracle.certify_causal_violation_witness, t_ok, "abcd", "null")
        self._assert_err("INVALID_WITNESS_VECTOR", oracle.certify_causal_violation_witness, t_ok, [Fraction(1, 1)], "null")
        self._assert_err("INVALID_FRACTION", oracle.certify_causal_violation_witness, t_ok, [1, 1, 0, 0], "null")
        self._assert_err(
            "INVALID_FRACTION",
            oracle.certify_slemma_satisfaction,
            t_ok,
            lam_nec=2,
            lam_wec=Fraction(2, 1),
            lam_sec=Fraction(2, 1),
            mu_dec=Fraction(10, 1),
        )
        t_nonsym = [
            [Fraction(5, 1), Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)],
            [Fraction(0, 1), Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)],
            [Fraction(0, 1), Fraction(0, 1), Fraction(1, 1), Fraction(0, 1)],
            [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1), Fraction(1, 1)],
        ]
        self._assert_err("NON_SYMMETRIC_MATRIX", oracle.certify_causal_violation_witness, t_nonsym, [Fraction(1, 1), Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)], "null")
        self._assert_err("INVALID_WITNESS_VECTOR", oracle.certify_causal_violation_witness, t_ok, [Fraction(0, 1)] * 4, "null")
        self._assert_err("INVALID_NULL_WITNESS", oracle.certify_causal_violation_witness, t_neg, [Fraction(2, 1), Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)], "null")
        self._assert_err("INVALID_NULL_WITNESS", oracle.certify_causal_violation_witness, t_ok, [Fraction(1, 1), Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)], "null")
        self._assert_err("INVALID_TIMELIKE_WITNESS", oracle.certify_causal_violation_witness, t_neg, [Fraction(1, 1), Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)], "timelike")
        self._assert_err("INVALID_TIMELIKE_WITNESS", oracle.certify_causal_violation_witness, t_neg, [Fraction(0, 1), Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)], "timelike")
        self._assert_err("INVALID_TIMELIKE_WITNESS", oracle.certify_causal_violation_witness, t_ok, [Fraction(2, 1), Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)], "timelike")
        self._assert_err("INVALID_DEC_WITNESS", oracle.certify_causal_violation_witness, t_ok, [Fraction(1, 1), Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)], "dec_flux")
        self._assert_err("INVALID_DEC_WITNESS", oracle.certify_causal_violation_witness, t_ok, [Fraction(2, 1), Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)], "dec_flux")
        # Exact boundary J^2 == 0 on sub-threshold thin shell with u = (5, 0, 4, 0) AND spacelike (0, 0, 1, 0) where J^2 > 0!
        t_sub = [
            [Fraction(5, 3), Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)],
            [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)],
            [Fraction(0, 1), Fraction(0, 1), Fraction(25, 12), Fraction(0, 1)],
            [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1), Fraction(25, 12)],
        ]
        self._assert_err("INVALID_DEC_WITNESS", oracle.certify_causal_violation_witness, t_sub, [Fraction(5, 1), Fraction(0, 1), Fraction(4, 1), Fraction(0, 1)], "dec_flux")
        self._assert_err("INVALID_DEC_WITNESS", oracle.certify_causal_violation_witness, t_sub, [Fraction(0, 1), Fraction(0, 1), Fraction(1, 1), Fraction(0, 1)], "dec_flux")
        self._assert_err("UNKNOWN_WITNESS_KIND", oracle.certify_causal_violation_witness, t_ok, [Fraction(1, 1), Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)], "bogus")

    def test_validate_certificate_payload_guards(self) -> None:
        cert = oracle.build_standalone_certificate()
        self._assert_err("INVALID_BOOL", oracle.validate_certificate_payload, cert, full_replay=1)
        self._assert_err("INVALID_CERT_TYPE", oracle.validate_certificate_payload, [])

        bad_keys = dict(cert)
        bad_keys["extra"] = 1
        self._assert_err("INVALID_CERT_KEYS", oracle.validate_certificate_payload, bad_keys)

        bad_schema = dict(cert)
        bad_schema["schema"] = "wrong"
        self._assert_err("SCHEMA_MISMATCH", oracle.validate_certificate_payload, bad_schema)

        bad_tid = dict(cert)
        bad_tid["track_id"] = "wrong"
        self._assert_err("TRACK_ID_MISMATCH", oracle.validate_certificate_payload, bad_tid)

        bad_pay = dict(cert)
        bad_pay["payload"] = []
        self._assert_err("INVALID_PAYLOAD_TYPE", oracle.validate_certificate_payload, bad_pay)

        bad_psha = dict(cert)
        bad_psha["payload_sha256"] = "0" * 64
        self._assert_err("PAYLOAD_SHA_MISMATCH", oracle.validate_certificate_payload, bad_psha)

        bad_csha = dict(cert)
        bad_csha["certificate_sha256"] = "0" * 64
        self._assert_err("CERT_SHA_MISMATCH", oracle.validate_certificate_payload, bad_csha)

        modified = copy.deepcopy(cert)
        modified["payload"]["novelty_tier"] = "N0"
        resigned = _resign_cert(modified)
        ok_no_replay = oracle.validate_certificate_payload(resigned, full_replay=False)
        self.assertIs(ok_no_replay["valid"], True)
        self.assertIs(ok_no_replay["full_replay"], False)
        self._assert_err("REPLAY_MISMATCH", oracle.validate_certificate_payload, resigned, full_replay=True)


class TestSecondaryAlgebraicAuditTampering(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.base_payload = oracle.build_standalone_certificate()["payload"]

    def _tamper(self, expected_code: str, mutator) -> None:
        p = copy.deepcopy(self.base_payload)
        mutator(p)
        with self.assertRaises(oracle.AlcubierreAdmError) as ctx:
            audit.secondary_algebraic_audit(p)
        self.assertEqual(ctx.exception.code, expected_code)

    def test_all_pillar_tamper_paths(self) -> None:
        # Pillar 1
        for k in (
            "arbitrary_lapse_hamiltonian_residual_zero",
            "arbitrary_lapse_momentum_residuals_zero",
            "unit_lapse_pointwise_sign_flip_residual_zero",
            "compact_bubble_int_div_J_zero",
            "compact_bubble_sign_flip_duality_exact",
        ):
            self._tamper("AUDIT_P1_FAILED", lambda p, key=k: p["pillar1_arbitrary_lapse_adm"].__setitem__(key, False))
        self._tamper("INVALID_RATIONAL", lambda p: p["pillar1_arbitrary_lapse_adm"].__setitem__("gullstrand_painleve_M", "²"))
        self._tamper("AUDIT_P1_GP_BETA", lambda p: p["pillar1_arbitrary_lapse_adm"]["gullstrand_painleve_checks"][0].__setitem__("beta_r", "3"))
        self._tamper("AUDIT_P1_GP_FLUX", lambda p: p["pillar1_arbitrary_lapse_adm"]["gullstrand_painleve_checks"][0].__setitem__("flux_J_ADM_over_pi", "31"))
        self._tamper("AUDIT_P1_GP_VAC", lambda p: p["pillar1_arbitrary_lapse_adm"]["gullstrand_painleve_checks"][0].__setitem__("vacuum_G_zero", False))
        self._tamper("AUDIT_P1_OMSQ", lambda p: p["pillar1_arbitrary_lapse_adm"].__setitem__("compact_bubble_int_omega_sq", "0"))
        self._tamper("AUDIT_P1_RHO16", lambda p: p["pillar1_arbitrary_lapse_adm"].__setitem__("compact_bubble_int_16pi_rhoE", "1"))
        self._tamper("AUDIT_P1_DUALITY", lambda p: p["pillar1_arbitrary_lapse_adm"].__setitem__("compact_bubble_int_neg_2G00", "0"))
        self._tamper("AUDIT_P1_IV_RHO", lambda p: p["pillar1_arbitrary_lapse_adm"]["irrotational_non_unit_lapse_type_iv"].__setitem__("G_hat_00", "0"))
        self._tamper("AUDIT_P1_IV_DISC_EQ", lambda p: p["pillar1_arbitrary_lapse_adm"]["irrotational_non_unit_lapse_type_iv"].__setitem__("discriminant_01", "-1"))
        def _make_iv_nonneg(p):
            iv = p["pillar1_arbitrary_lapse_adm"]["irrotational_non_unit_lapse_type_iv"]
            iv["G_hat_01"] = "0"
            iv["discriminant_01"] = "0"
        self._tamper("AUDIT_P1_IV_DISC_SIGN", _make_iv_nonneg)
        self._tamper("AUDIT_P1_IV_CTRL", lambda p: p["pillar1_arbitrary_lapse_adm"]["irrotational_non_unit_lapse_type_iv"].__setitem__("unit_lapse_control_flux_zero", False))

        # Pillar 2
        for k in (
            "off_equatorial_g00_formula_exact",
            "off_equatorial_wx_plus3_exact",
            "septic_profile_c3_smooth",
            "two_concentric_type_iv_annuli_certified",
            "type_iv_fraction_increases_as_v_to_0",
        ):
            self._tamper("AUDIT_P2_FAILED", lambda p, key=k: p["pillar2_alcubierre_eos_type_iv"].__setitem__(key, False))
        self._tamper("AUDIT_P2_EOS", lambda p: p["pillar2_alcubierre_eos_type_iv"]["equatorial_stations"][0].__setitem__("G_hat_11", "0"))
        self._tamper("AUDIT_P2_DISC", lambda p: p["pillar2_alcubierre_eos_type_iv"]["equatorial_stations"][0].__setitem__("discriminant_01", "0"))
        self._tamper("AUDIT_P2_TYPE", lambda p: p["pillar2_alcubierre_eos_type_iv"]["equatorial_stations"][0].__setitem__("hawking_ellis_type", "Type_I"))
        self._tamper("AUDIT_P2_TYPE", lambda p: p["pillar2_alcubierre_eos_type_iv"]["equatorial_stations"][1].__setitem__("hawking_ellis_type", "Type_IV"))

        # Pillar 3
        self._tamper("AUDIT_P3_ETA", lambda p: p["pillar3_slemma_krein_blind_spot"].__setitem__("eta_inertia", [4, 0, 0]))
        self._tamper("AUDIT_P3_HYP", lambda p: p["pillar3_slemma_krein_blind_spot"].__setitem__("hyperbolic_2x2_inertia", [2, 0, 0]))
        for k in ("nec_satisfied_all_observers", "wec_satisfied_all_observers", "sec_satisfied_all_observers", "dec_satisfied_all_observers"):
            self._tamper("AUDIT_P3_FLUID", lambda p, key=k: p["pillar3_slemma_krein_blind_spot"]["boosted_perfect_fluid_slemma"].__setitem__(key, False))
        self._tamper("AUDIT_P3_BS_RHO", lambda p: p["pillar3_slemma_krein_blind_spot"]["eulerian_blind_spot_irrotational_type_i"].__setitem__("G_hat_00", "0"))
        self._tamper("AUDIT_P3_BS_NEC", lambda p: p["pillar3_slemma_krein_blind_spot"]["eulerian_blind_spot_irrotational_type_i"].__setitem__("G_hat_11", "-3"))
        self._tamper("AUDIT_P3_BS_FLUX", lambda p: p["pillar3_slemma_krein_blind_spot"]["eulerian_blind_spot_irrotational_type_i"].__setitem__("G_hat_0i_all_zero", False))
        self._tamper("AUDIT_P3_NULL_WIT", lambda p: p["pillar3_slemma_krein_blind_spot"]["alcubierre_pythagorean_quadruple_null_witness"].__setitem__("violation_certified", False))

        # Pillar 4
        self._tamper("AUDIT_P4_STOKES_CONST", lambda p: p["pillar4_natario_beltrami_horizons"].__setitem__("stokes_thin_wall_minimizer_constant", "1/3"))
        self._tamper("AUDIT_P4_STOKES_COMP", lambda p: p["pillar4_natario_beltrami_horizons"].__setitem__("stokes_quintic_competitor_constant", "1/4"))
        self._tamper("AUDIT_P4_EL", lambda p: p["pillar4_natario_beltrami_horizons"].__setitem__("stokes_euler_lagrange_cross_term_zero", False))
        self._tamper("AUDIT_P4_SOS", lambda p: p["pillar4_natario_beltrami_horizons"].__setitem__("stokes_sos_gap_exact", False))
        for k in ("natario_zero_expansion_exact", "beltrami_eigenmode_exact", "force_free_momentum_exact", "energy_equals_neg_lam_over_2_helicity"):
            self._tamper("AUDIT_P4_BELTRAMI", lambda p, key=k: p["pillar4_natario_beltrami_horizons"]["beltrami_s23a_bridge"].__setitem__(key, False))
        self._tamper("AUDIT_P4_BEL_BRIDGE", lambda p: p["pillar4_natario_beltrami_horizons"]["beltrami_s23a_bridge"].__setitem__("energy_16pi_rhoE", "0"))
        self._tamper("AUDIT_P4_HORIZON_F", lambda p: p["pillar4_natario_beltrami_horizons"]["killing_horizons"].__setitem__("f_at_rH", "1/3"))
        self._tamper("AUDIT_P4_KAPPA_FRONT_SIGN", lambda p: p["pillar4_natario_beltrami_horizons"]["killing_horizons"].__setitem__("surface_gravity_front_kappa", "0"))
        self._tamper("AUDIT_P4_KAPPA_FRONT_SIGN", lambda p: p["pillar4_natario_beltrami_horizons"]["killing_horizons"].__setitem__("surface_gravity_front_kappa", "35/16"))
        self._tamper("AUDIT_P4_KAPPA_ANTISYM", lambda p: p["pillar4_natario_beltrami_horizons"]["killing_horizons"].__setitem__("surface_gravity_rear_kappa", "1"))
        self._tamper("AUDIT_P4_HORIZON_TYPES", lambda p: p["pillar4_natario_beltrami_horizons"]["killing_horizons"].__setitem__("front_horizon_type", "black_hole_hawking"))
        self._tamper("AUDIT_P4_HORIZON_TYPES", lambda p: p["pillar4_natario_beltrami_horizons"]["killing_horizons"].__setitem__("rear_horizon_type", "white_hole_blueshift"))
        self._tamper("AUDIT_P4_GTT", lambda p: p["pillar4_natario_beltrami_horizons"]["killing_horizons"].__setitem__("g_tt_comoving_at_rH_zero", False))
        self._tamper("AUDIT_P4_CHRISTOFFEL", lambda p: p["pillar4_natario_beltrami_horizons"]["killing_horizons"].__setitem__("front_christoffel_killing_exact", False))
        self._tamper("AUDIT_P4_CHRISTOFFEL", lambda p: p["pillar4_natario_beltrami_horizons"]["killing_horizons"].__setitem__("rear_christoffel_killing_exact", False))
        self._tamper("AUDIT_P4_KAPPA", lambda p: p["pillar4_natario_beltrami_horizons"]["killing_horizons"].__setitem__("kappa_antisymmetry_and_signs_exact", False))
        self._tamper("AUDIT_P4_SUBLUM", lambda p: p["pillar4_natario_beltrami_horizons"]["killing_horizons"].__setitem__("subluminal_horizon_free", False))

        # Pillar 5
        self._tamper("AUDIT_P5_LICH", lambda p: p["pillar5_physical_subluminal_shells"].__setitem__("lichnerowicz_general_hamiltonian_residual_zero", False))
        self._tamper("AUDIT_P5_VDB", lambda p: p["pillar5_physical_subluminal_shells"].__setitem__("vdb_compact_collar_int_psi5_R3_zero", False))
        self._tamper("AUDIT_P5_ADM", lambda p: p["pillar5_physical_subluminal_shells"].__setitem__("schwarzschild_tail_int_psi5_R3_over_pi", "31"))
        for sh in ("smooth_conformally_flat_boosted_shell", "israel_thin_shell_boosted"):
            for cond in ("nec_satisfied_all_observers", "wec_satisfied_all_observers", "sec_satisfied_all_observers", "dec_satisfied_all_observers"):
                self._tamper("AUDIT_P5_SHELL_SLEMMA", lambda p, s=sh, c=cond: p["pillar5_physical_subluminal_shells"][s]["slemma_all_conditions"].__setitem__(c, False))
        self._tamper("AUDIT_P5_DEC_NEG_THRESH", lambda p: p["pillar5_physical_subluminal_shells"]["negative_control_sub_threshold_dec_violation"].__setitem__("below_dec_threshold_25_12", False))
        self._tamper("AUDIT_P5_DEC_NEG_WIT", lambda p: p["pillar5_physical_subluminal_shells"]["negative_control_sub_threshold_dec_violation"]["dec_flux_violation_witness"].__setitem__("violation_certified", False))


class TestZoneBHardeningAndCLI(unittest.TestCase):
    def _assert_err(self, code: str, fn, *args, **kwargs) -> None:
        with self.assertRaises(oracle.AlcubierreAdmError) as ctx:
            fn(*args, **kwargs)
        self.assertEqual(ctx.exception.code, code)

    def test_dir_fd_path_symlink_hardlink_fifo_and_atomic_write(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            self._assert_err("INVALID_PATH_TYPE", audit.require_safe_path, str(root / "a.json"))
            self._assert_err("INVALID_PATH_TYPE", audit.require_safe_path, _PathSubclass(str(root / "a.json")))
            self._assert_err("INVALID_PATH", audit.require_safe_path, Path("bad\x00path"))
            self._assert_err("INVALID_UTF8_SURROGATE", audit.require_safe_path, Path("bad\ud800.json"))
            self.assertEqual(audit.require_safe_path(Path("/")), Path("/"))
            self._assert_err("NON_REGULAR_FILE", audit.read_regular_file_bytes, Path("/"))
            self._assert_err("NON_REGULAR_FILE", audit.write_regular_file_bytes, Path("/"), b"x")
            self._assert_err("INVALID_WRITE_DATA", audit.write_regular_file_bytes, root / "x.json", "not_bytes")

            # Anchor open error
            self._assert_err("PATH_STAT_ERROR", audit._open_dir_chain, "/nonexistent_s28_anchor_xyz", [])

            # Missing intermediate directory, file-as-directory (ENOTDIR), symlinked dir (ELOOP)
            self._assert_err("PATH_NOT_FOUND", audit.require_safe_path, root / "no_dir" / "a.json")
            reg_file = root / "plain.txt"
            reg_file.write_bytes(b"hello")
            self._assert_err("SYMLINK_FORBIDDEN", audit.require_safe_path, reg_file / "child.json")

            real_dir = root / "real"
            real_dir.mkdir()
            sym_dir = root / "sym_dir"
            sym_dir.symlink_to(real_dir)
            self._assert_err("SYMLINK_FORBIDDEN", audit.require_safe_path, sym_dir / "a.json")
            self._assert_err("SYMLINK_FORBIDDEN", audit.require_safe_path, sym_dir / ".." / "plain.txt")
            self._assert_err("SYMLINK_FORBIDDEN", audit.read_regular_file_bytes, sym_dir / "a.json")

            # Unreadable intermediate dir (EACCES -> PATH_STAT_ERROR)
            no_exec = root / "no_exec"
            no_exec.mkdir()
            sub_dir = no_exec / "inner"
            sub_dir.mkdir()
            os.chmod(no_exec, 0o000)
            try:
                if os.geteuid() != 0:
                    self._assert_err("PATH_STAT_ERROR", audit.require_safe_path, sub_dir / "a.json")
            finally:
                os.chmod(no_exec, 0o700)

            # Leaf symlink, missing leaf, lstat error
            sym_leaf = root / "sym_leaf.json"
            sym_leaf.symlink_to(reg_file)
            self._assert_err("SYMLINK_FORBIDDEN", audit.require_safe_path, sym_leaf)
            self._assert_err("SYMLINK_FORBIDDEN", audit.read_regular_file_bytes, sym_leaf)
            self._assert_err("SYMLINK_FORBIDDEN", audit.write_regular_file_bytes, sym_leaf, b"x")
            self.assertEqual(audit.require_safe_path(root / "fresh.json"), root / "fresh.json")
            self.assertEqual(audit.require_safe_path(reg_file), reg_file)
            with mock.patch.object(audit.os, "lstat", side_effect=PermissionError("denied")):
                self._assert_err("PATH_STAT_ERROR", audit.require_safe_path, reg_file)
                self._assert_err("FILE_WRITE_ERROR", audit.write_regular_file_bytes, reg_file, b"x")

            # Missing file read, directory read/write, FIFO read/write, /dev/null read
            self._assert_err("FILE_READ_ERROR", audit.read_regular_file_bytes, root / "missing.json")
            self._assert_err("NON_REGULAR_FILE", audit.read_regular_file_bytes, real_dir)
            self._assert_err("NON_REGULAR_FILE", audit.write_regular_file_bytes, real_dir, b"x")
            self._assert_err("NON_REGULAR_FILE", audit.read_regular_file_bytes, Path("/dev/null"))
            fifo_p = root / "pipe.fifo"
            os.mkfifo(fifo_p)
            self._assert_err("NON_REGULAR_FILE", audit.read_regular_file_bytes, fifo_p)
            self._assert_err("NON_REGULAR_FILE", audit.write_regular_file_bytes, fifo_p, b"x")

            # Hardlink refusal on write
            hl_a = root / "hl_a.json"
            hl_b = root / "hl_b.json"
            hl_a.write_bytes(b"original")
            os.link(hl_a, hl_b)
            self._assert_err("HARDLINK_FORBIDDEN", audit.write_regular_file_bytes, hl_a, b"overwrite")
            self.assertEqual(hl_b.read_bytes(), b"original")

            # Exact cap & oversized read + multi-chunk read + os.read error
            big_ok = root / "exact_cap.bin"
            big_ok.write_bytes(b"a" * oracle.MAX_JSON_BYTES)
            self.assertEqual(len(audit.read_regular_file_bytes(big_ok)), oracle.MAX_JSON_BYTES)
            big_bad = root / "too_big.bin"
            big_bad.write_bytes(b"a" * (oracle.MAX_JSON_BYTES + 1))
            self._assert_err("FILE_TOO_LARGE", audit.read_regular_file_bytes, big_bad)
            with mock.patch.object(audit.os, "read", side_effect=OSError("io fail")):
                self._assert_err("FILE_READ_ERROR", audit.read_regular_file_bytes, reg_file)

            # Atomic write overwrite + partial write loop + temp collision retry & exhaustion + replace failure cleanup
            target = root / "out.bin"
            audit.write_regular_file_bytes(target, b"first")
            self.assertEqual(target.read_bytes(), b"first")
            real_write = os.write
            with mock.patch.object(audit.os, "write", side_effect=lambda fd, buf: real_write(fd, buf[:2])):
                audit.write_regular_file_bytes(target, b"second_payload")
            self.assertEqual(target.read_bytes(), b"second_payload")

            # Temp collision retry (.0 exists -> uses .1)
            coll0 = root / f".{target.name}.s28tmp.{os.getpid()}.0"
            coll0.write_bytes(b"keep")
            audit.write_regular_file_bytes(target, b"after_retry")
            self.assertEqual(target.read_bytes(), b"after_retry")
            self.assertEqual(coll0.read_bytes(), b"keep")

            # Temp collision exhaustion (.0..15 exist)
            for idx in range(1, 16):
                (root / f".{target.name}.s28tmp.{os.getpid()}.{idx}").write_bytes(b"c")
            self._assert_err("FILE_WRITE_ERROR", audit.write_regular_file_bytes, target, b"fail")
            for idx in range(16):
                (root / f".{target.name}.s28tmp.{os.getpid()}.{idx}").unlink()

            # Read-only directory prevents temp creation -> FILE_WRITE_ERROR
            ro_dir = root / "ro"
            ro_dir.mkdir()
            os.chmod(ro_dir, 0o500)
            try:
                if os.geteuid() != 0:
                    self._assert_err("FILE_WRITE_ERROR", audit.write_regular_file_bytes, ro_dir / "x.json", b"x")
            finally:
                os.chmod(ro_dir, 0o700)

            # os.replace failure cleans up temp; also test unlink failure during cleanup
            with mock.patch.object(audit.os, "replace", side_effect=OSError("replace fail")):
                self._assert_err("FILE_WRITE_ERROR", audit.write_regular_file_bytes, target, b"bad")
            self.assertEqual([p.name for p in root.glob(f".{target.name}.s28tmp.*")], [])
            with (
                mock.patch.object(audit.os, "replace", side_effect=OSError("replace fail")),
                mock.patch.object(audit.os, "unlink", side_effect=OSError("unlink fail")),
            ):
                self._assert_err("FILE_WRITE_ERROR", audit.write_regular_file_bytes, target, b"bad2")
            for leftover in root.glob(f".{target.name}.s28tmp.*"):
                leftover.unlink()

    def test_relative_path_pwd_and_deleted_cwd(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            real_sub = root / "sub"
            real_sub.mkdir()
            sym_sub = root / "sym_sub"
            sym_sub.symlink_to(real_sub)

            old_cwd = os.getcwd()
            os.chdir(real_sub)
            try:
                # Valid PWD, stale nonexistent PWD, relative PWD, unset PWD
                with mock.patch.dict(os.environ, {"PWD": str(real_sub)}):
                    self.assertEqual(audit.require_safe_path(Path("local.json")), Path("local.json"))
                with mock.patch.dict(os.environ, {"PWD": str(root / "does_not_exist")}):
                    self.assertEqual(audit.require_safe_path(Path("local.json")), Path("local.json"))
                with mock.patch.dict(os.environ, {"PWD": "relative/pwd"}):
                    self.assertEqual(audit.require_safe_path(Path("local.json")), Path("local.json"))
                with mock.patch.dict(os.environ, {}, clear=True):
                    self.assertEqual(audit.require_safe_path(Path("local.json")), Path("local.json"))
                # Symlinked PWD & lone-surrogate PWD must fail closed!
                with mock.patch.dict(os.environ, {"PWD": str(sym_sub)}):
                    self._assert_err("SYMLINK_FORBIDDEN", audit.require_safe_path, Path("local.json"))
                with mock.patch.dict(os.environ, {"PWD": "/tmp/\udcff"}):
                    self._assert_err("INVALID_UTF8_SURROGATE", audit.require_safe_path, Path("local.json"))
                # Deleted CWD (mocked)
                with mock.patch.object(audit.Path, "cwd", side_effect=FileNotFoundError("no cwd")):
                    self._assert_err("CWD_UNAVAILABLE", audit.require_safe_path, Path("local.json"))
            finally:
                os.chdir(old_cwd)

            # Real live deleted-CWD subprocess check
            gone = root / "gone"
            gone.mkdir()
            script = (
                "import os, sys; "
                f"os.chdir({str(gone)!r}); "
                f"os.rmdir({str(gone)!r}); "
                f"sys.path.insert(0, {_THIS_DIR!r}); "
                "import alcubierre_adm_audit as a; "
                "raise SystemExit(a.main(['--check', 'cert.json', '--json']))"
            )
            proc = subprocess.run(
                [sys.executable, "-I", "-B", "-c", script],
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(proc.returncode, 2)
            self.assertEqual(json.loads(proc.stderr)["error_code"], "CWD_UNAVAILABLE")

    def test_certificate_file_wire_format_and_cli(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            cert_path = root / "cert.json"
            res_w = audit.write_certificate_file(cert_path)
            self.assertIs(res_w["written"], True)
            res_c = audit.check_certificate_file(cert_path)
            self.assertIs(res_c["valid"], True)
            self.assertEqual(res_c["file_sha256"], res_w["file_sha256"])

            raw = cert_path.read_bytes()
            crlf_p = root / "crlf.json"
            crlf_p.write_bytes(raw[:-1] + b"\r\n")
            self._assert_err("CRLF_FORBIDDEN", audit.check_certificate_file, crlf_p)

            nolf_p = root / "nolf.json"
            nolf_p.write_bytes(raw[:-1])
            self._assert_err("MISSING_TRAILING_LF", audit.check_certificate_file, nolf_p)

            bad_utf8 = root / "bad_utf8.json"
            bad_utf8.write_bytes(b"\xff\xfe\n")
            self._assert_err("INVALID_UTF8", audit.check_certificate_file, bad_utf8)

            non_canon = root / "non_canon.json"
            non_canon.write_bytes(b" " + raw)
            self._assert_err("NON_CANONICAL_BYTES", audit.check_certificate_file, non_canon)

            # CLI parser exhaustive branches
            self._assert_err("INVALID_ARGV", audit._parse_cli_argv, "not_a_list")
            self._assert_err("INVALID_STR", audit._parse_cli_argv, [123])
            self._assert_err("INVALID_UTF8_SURROGATE", audit._parse_cli_argv, ["--check", "a\ud800.json"])
            self.assertEqual(audit._parse_cli_argv([]), ("standalone", None, False))
            self.assertEqual(audit._parse_cli_argv(["--standalone", "--json"]), ("standalone", None, True))
            self.assertEqual(audit._parse_cli_argv(["--json", "--check", "a.json"]), ("check", Path("a.json"), True))
            self.assertEqual(audit._parse_cli_argv(["--write", "b.json"]), ("write", Path("b.json"), False))
            self._assert_err("DUPLICATE_FLAG", audit._parse_cli_argv, ["--json", "--json"])
            self._assert_err("CONFLICTING_MODE", audit._parse_cli_argv, ["--standalone", "--standalone"])
            self._assert_err("CONFLICTING_MODE", audit._parse_cli_argv, ["--standalone", "--check", "a.json"])
            self._assert_err("CONFLICTING_MODE", audit._parse_cli_argv, ["--check", "a.json", "--write", "b.json"])
            self._assert_err("MISSING_PATH_ARG", audit._parse_cli_argv, ["--check"])
            self._assert_err("MISSING_PATH_ARG", audit._parse_cli_argv, ["--write"])
            self._assert_err("INVALID_PATH_ARG", audit._parse_cli_argv, ["--check", ""])
            self._assert_err("INVALID_PATH_ARG", audit._parse_cli_argv, ["--write", ""])
            self._assert_err("INVALID_PATH_ARG", audit._parse_cli_argv, ["--check", "--json"])
            self._assert_err("INVALID_PATH_ARG", audit._parse_cli_argv, ["--write", "--json"])
            self._assert_err("UNKNOWN_FLAG", audit._parse_cli_argv, ["--write=--json"])
            self._assert_err("UNKNOWN_FLAG", audit._parse_cli_argv, ["--check=--json"])
            self._assert_err("UNKNOWN_FLAG", audit._parse_cli_argv, ["--bogus"])

            # End-to-end main() calls (both JSON and text output + failure mode creates 0 files!)
            old_cwd = os.getcwd()
            os.chdir(root)
            try:
                for argv_bad, exp_code in (
                    (["--write", "--json"], "INVALID_PATH_ARG"),
                    (["--write=--json"], "UNKNOWN_FLAG"),
                    (["--check=--json"], "UNKNOWN_FLAG"),
                ):
                    out_s, err_s = io.StringIO(), io.StringIO()
                    with mock.patch.object(sys, "stdout", out_s), mock.patch.object(sys, "stderr", err_s):
                        rc = audit.main(argv_bad)
                    self.assertEqual(rc, 2)
                    self.assertEqual(out_s.getvalue(), "")
                    self.assertEqual(json.loads(err_s.getvalue())["error_code"], exp_code)
                    self.assertFalse((root / "--json").exists())

                for argv_ok in (
                    [],
                    ["--standalone", "--json"],
                    ["--write", "cli_cert.json", "--json"],
                    ["--check", "cli_cert.json", "--json"],
                    ["--check", "cli_cert.json"],
                ):
                    out_s, err_s = io.StringIO(), io.StringIO()
                    with mock.patch.object(sys, "stdout", out_s), mock.patch.object(sys, "stderr", err_s):
                        rc = audit.main(argv_ok)
                    self.assertEqual(rc, 0)
                    self.assertEqual(err_s.getvalue(), "")
                    if "--json" in argv_ok:
                        self.assertIsInstance(json.loads(out_s.getvalue()), dict)
                    else:
                        self.assertTrue(out_s.getvalue().startswith("OK "))
            finally:
                os.chdir(old_cwd)


if __name__ == "__main__":
    unittest.main()
