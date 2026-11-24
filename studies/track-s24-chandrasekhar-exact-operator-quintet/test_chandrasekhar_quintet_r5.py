#!/usr/bin/env python3
"""Track S24: R5 Adversarial, Exact-Identity, Mutation-Kill, and Zone-B Verification Suite.

Pure Python 3 standard library: zero external dependencies, zero bare assert statements.
"""
from __future__ import annotations

import copy
from fractions import Fraction
import io
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

_THIS_DIR = str(Path(__file__).resolve().parent)
if _THIS_DIR not in sys.path:
    sys.path.insert(0, _THIS_DIR)

import chandrasekhar_quintet_audit as audit
import chandrasekhar_quintet_oracle as oracle


class _StrSub(str):
    pass


class _IntSub(int):
    pass


class _DictSub(dict):
    pass


class _PathSub(type(Path("."))):
    pass


def _resign(cert: dict) -> dict:
    c = copy.deepcopy(cert)
    psha = oracle.canonical_sha256(c["payload"])
    c["payload_sha256"] = psha
    env = {
        "schema": c["schema"],
        "track_id": c["track_id"],
        "payload_sha256": psha,
        "payload": c["payload"],
    }
    c["certificate_sha256"] = oracle.canonical_sha256(env)
    return c


class TestTrackS24ChandrasekharQuintet(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.cert = oracle.build_standalone_certificate()

    def test_01_all_five_pillars_certified_exact(self) -> None:
        p = self.cert["payload"]
        self.assertEqual(p["oracle_class"], "exact")
        self.assertEqual(p["novelty_tier"], "N1")
        self.assertTrue(p["zero_trust_path_floats"])
        self.assertTrue(p["zero_rng"])
        self.assertTrue(p["zero_bare_asserts"])

        # Pillar 1: Black-Hole Darboux / SUSY
        t1 = p["theorem1_black_hole_darboux"]
        self.assertTrue(t1["zerilli_superpotential_identity_exact"])
        self.assertTrue(t1["regge_wheeler_superpotential_identity_exact"])
        self.assertTrue(t1["darboux_intertwining_zerilli_exact"])
        self.assertTrue(t1["darboux_intertwining_rw_exact"])
        self.assertTrue(t1["asymptotic_superpotential_limit_verified"])
        self.assertTrue(t1["scattering_modulus_equality_exact"])
        self.assertTrue(t1["negative_control_perturbed_beta_2M_rejected"])
        oas = {m["ell"]: m["omega_as_times_M"] for m in t1["multipoles"]}
        self.assertEqual(oas, {2: "2", 3: "10", 4: "30"})

        # Pillar 2: Magnetoconvection SOS
        t2 = p["theorem2_magnetoconvection_sos"]
        self.assertTrue(t2["sos_identity_exact"])
        self.assertTrue(t2["q1_factorization_exact"])
        self.assertTrue(t2["q1_derivative_positive_law_exact"])
        self.assertTrue(t2["supercritical_instability_identity_exact"])
        cps = {c["label"]: (c["Q_over_pi2"], c["R_c_over_pi4"]) for c in t2["critical_points"]}
        self.assertEqual(cps["rayleigh_benard_Q0"], ("0", "27/4"))
        self.assertEqual(cps["exact_integer_Q4"], ("4", "16"))

        # Pillar 3: Lane-Emden Polytropes & n=3 Enclosure
        t3 = p["theorem3_lane_emden_polytropes"]
        self.assertTrue(t3["n0_closed_form_exact"])
        self.assertTrue(t3["n1_series_ode_exact_deg24"])
        self.assertTrue(t3["n5_rational_ode_exact"])
        self.assertTrue(t3["binding_energy_law_exact"])
        self.assertTrue(t3["n3_binding_energy_vanishes"])
        self.assertEqual(t3["n3_series_prefix"][:4], ["1", "-1/6", "1/40", "-19/5040"])
        self.assertTrue(t3["banach_start_verified"])
        self.assertTrue(t3["strictly_decreasing_unique_first_zero"])
        self.assertTrue(t3["widths_strictly_below_1e_8"])
        self.assertTrue(t3["negative_control_interval_div_zero_rejected"])
        xi1_w = oracle.parse_exact_rational(t3["xi1_width"])
        om_w = oracle.parse_exact_rational(t3["omega3_width"])
        self.assertLess(xi1_w, Fraction(1, 10 ** 10))
        self.assertLess(om_w, Fraction(1, 10 ** 10))

        # Pillar 4: Chandrasekhar-Fermi Virial No-Go
        t4 = p["theorem4_chandrasekhar_fermi_virial"]
        self.assertTrue(t4["scalar_virial_energy_elimination_exact"])
        self.assertTrue(t4["gamma_4_3_energy_vanishing_exact"])
        self.assertTrue(t4["critical_mass_to_flux_R_cancels_exact"])
        self.assertTrue(t4["field_div_B_zero_exact"])
        self.assertTrue(t4["pointwise_3d_maxwell_virial_identity_zero"])
        self.assertTrue(t4["gauss_virial_balance_zero"])
        self.assertTrue(t4["self_confined_force_free_R3_obstructed"])
        self.assertTrue(t4["negative_control_unbound_detected"])

        # Pillar 5: Radiative Transfer H-Function & X/Y Riccati
        t5 = p["theorem5_radiative_transfer_riccati"]
        self.assertTrue(t5["alpha0_algebraic_law_exact_Q_q"])
        self.assertTrue(t5["conservative_hopf_invariant_alpha1_sq_4_3_exact"])
        self.assertTrue(t5["gauss_legendre_2pt_Q_sqrt3_exact"])
        self.assertTrue(t5["quad4_pure_Q_cubic_exact"])
        self.assertTrue(t5["finite_slab_riccati_symbolic_conserved"])
        self.assertTrue(t5["finite_slab_riccati_tau0_exact"])
        self.assertTrue(t5["finite_slab_riccati_series_deg8_zero"])
        self.assertTrue(t5["negative_control_spurious_alpha0_branch_rejected"])
        self.assertTrue(t5["negative_control_broken_riccati_sign_rejected"])
        a_map = {c["albedo_w0"]: c["alpha0_exact"] for c in t5["albedo_cases"]}
        self.assertEqual(a_map, {"3/4": "4/3", "8/9": "3/2", "15/16": "8/5", "1": "2"})

    def test_02_exact_primitives_and_guard_boundaries(self) -> None:
        # _int_digit_len & require_exact_int boundaries
        self.assertEqual(oracle.require_exact_int(0, "z", min_val=0, max_val=0), 0)
        self.assertEqual(oracle.require_exact_int(10 ** 999, "edge1000"), 10 ** 999)
        for bad_int in (True, False, "1", _IntSub(1), 10 ** 1000, 10 ** 1500):
            with self.assertRaises(oracle.ChandrasekharError):
                oracle.require_exact_int(bad_int, "x")
        with self.assertRaises(oracle.ChandrasekharError):
            oracle.require_exact_int(4, "x", min_val=5)
        with self.assertRaises(oracle.ChandrasekharError):
            oracle.require_exact_int(6, "x", max_val=5)

        # require_exact_bool & require_exact_str & require_sha256_hex
        self.assertIs(oracle.require_exact_bool(False, "b"), False)
        for bad_b in (0, 1, "true", None):
            with self.assertRaises(oracle.ChandrasekharError):
                oracle.require_exact_bool(bad_b, "b")
        self.assertEqual(oracle.require_exact_str("", "s", non_empty=False), "")
        for bad_s in ("", 123, _StrSub("ok"), "\ud800"):
            with self.assertRaises(oracle.ChandrasekharError):
                oracle.require_exact_str(bad_s, "s")
        self.assertEqual(oracle.require_sha256_hex("0123456789abcdef" * 4, "h"), "0123456789abcdef" * 4)
        for bad_h in ("a" * 63, "a" * 65, "A" * 64, "g" * 64):
            with self.assertRaises(oracle.ChandrasekharError):
                oracle.require_sha256_hex(bad_h, "h")

        # parse_exact_rational boundaries (ASCII digits only; rejects Unicode superscripts/circled/Arabic-Indic/fullwidth)
        self.assertEqual(oracle.parse_exact_rational("-3/4"), Fraction(-3, 4))
        self.assertEqual(oracle.parse_exact_rational("7"), Fraction(7, 1))
        self.assertEqual(oracle.parse_exact_rational("0/9"), Fraction(0, 1))
        for bad_q in (
            " 1/2",
            "1/2 ",
            "1/2/3",
            "/2",
            "1/",
            "-",
            "1a/2",
            "1/2a",
            ":/1",
            "1/:",
            "²",
            "²/2",
            "1/²",
            "①",
            "1/①",
            "١٢/٣",
            "１２/３",
            "1/0",
            ("1" + "0" * 1000) + "/1",
            "1/" + ("1" + "0" * 1000),
        ):
            with self.assertRaises(oracle.ChandrasekharError):
                oracle.parse_exact_rational(bad_q)

        # Decimal formatting with negative values, digits==0, and invalid digits guard
        self.assertEqual(oracle.format_decimal_floor(Fraction(-1, 2), 2), "-0.50")
        self.assertEqual(oracle.format_decimal_ceil(Fraction(-1, 2), 2), "-0.50")
        self.assertEqual(oracle.format_decimal_floor(Fraction(3, 2), 0), "1")
        self.assertEqual(oracle.format_decimal_ceil(Fraction(3, 2), 0), "2")
        for bad_d in (-1, True, "2"):
            with self.assertRaises(oracle.ChandrasekharError):
                oracle.format_decimal_floor(Fraction(1, 2), bad_d)  # type: ignore[arg-type]
            with self.assertRaises(oracle.ChandrasekharError):
                oracle.format_decimal_ceil(Fraction(1, 2), bad_d)  # type: ignore[arg-type]

        # MPoly bounds & ring-arity guards
        x1 = oracle.MPoly.var(1, 0)
        x2 = oracle.MPoly.var(2, 1)
        self.assertEqual(x1.pow(0).terms, {(0,): Fraction(1, 1)})
        for bad_var in ((0, 0), (2, -1), (2, 2), (2, True)):
            with self.assertRaises(oracle.ChandrasekharError):
                oracle.MPoly.var(*bad_var)  # type: ignore[arg-type]
        for bad_exp in (-1, True):
            with self.assertRaises(oracle.ChandrasekharError):
                x1.pow(bad_exp)  # type: ignore[arg-type]
        for bad_idx in (-1, 1, True):
            with self.assertRaises(oracle.ChandrasekharError):
                x1.deriv(bad_idx)  # type: ignore[arg-type]
        for bad_rhs in (x2, "not_poly"):
            with self.assertRaises(oracle.ChandrasekharError):
                _ = x1 + bad_rhs  # type: ignore[operator]
            with self.assertRaises(oracle.ChandrasekharError):
                _ = x1 - bad_rhs  # type: ignore[operator]
            with self.assertRaises(oracle.ChandrasekharError):
                _ = x1 * bad_rhs  # type: ignore[operator]
        for bad_pt in ([], [Fraction(1, 1), Fraction(2, 1)]):
            with self.assertRaises(oracle.ChandrasekharError):
                x1.eval_point(bad_pt)

        # Rational function, interval, QSqrt3, and Lohner guards
        zero_p = oracle.MPoly.const(1, 0)
        one_p = oracle.MPoly.const(1, 1)
        self.assertTrue(one_p.scale(0).is_zero())
        with self.assertRaises(oracle.ChandrasekharError):
            oracle._rf_equal((one_p, zero_p), (one_p, one_p))
        with self.assertRaises(oracle.ChandrasekharError):
            oracle._rf_equal((one_p, one_p), (one_p, zero_p))

        for bad_div in ((-1, 1), (0, 5), (-5, 0)):
            with self.assertRaises(oracle.ChandrasekharError):
                oracle._iv_div((oracle._IV_ONE, oracle._IV_ONE), bad_div)
        neg_q = oracle._iv_div((oracle._IV_ONE, oracle._IV_ONE), (-2 * oracle._IV_ONE, -oracle._IV_ONE))
        self.assertLess(neg_q[1], 0)
        self.assertFalse(oracle._iv_contains((0, 5), (1, 6)))
        self.assertFalse(oracle._iv_contains((0, 5), (-1, 4)))

        q1 = oracle.QSqrt3(1, 1)
        q2 = oracle.QSqrt3(2, -1)
        quot = q1 / q2
        self.assertTrue((quot * q2 - q1).is_zero())
        self.assertFalse(oracle.QSqrt3(0, 1).is_zero())
        self.assertFalse(oracle.QSqrt3(1, 0).is_zero())
        with self.assertRaises(oracle.ChandrasekharError):
            _ = q1 / oracle.QSqrt3(0, 0)

        with self.assertRaises(oracle.ChandrasekharError):
            oracle._inv_2x2_exact_iv([[1, 2], [2, 4]])
        # Picard box symmetry: z_iv=(0,0) forces b_th contained while b_z is not (kills DEL 1),
        # and th_iv=(0,0) forces b_z contained while b_th is not (kills DEL 0)
        _, _, _b_th_p, b_z_p = oracle._le3_picard_remainder(
            Fraction(1, 1),
            Fraction(1, 8),
            (oracle._IV_ONE, oracle._IV_ONE),
            (0, 0),
            4,
        )
        self.assertLess(b_z_p[0], 0)
        _, _, b_th_p2, _b_z_p2 = oracle._le3_picard_remainder(
            Fraction(1, 1),
            Fraction(1, 8),
            (0, 0),
            (-oracle._IV_ONE, -oracle._IV_ONE),
            4,
        )
        self.assertLess(b_th_p2[0], 0)
        with self.assertRaises(oracle.ChandrasekharError):
            oracle._le3_picard_remainder(
                Fraction(1, 2),
                Fraction(100, 1),
                (oracle._IV_ONE, oracle._IV_ONE),
                (-oracle._IV_ONE, -oracle._IV_ONE),
                4,
            )

    def test_03_strict_json_and_validate_certificate_payload_matrix(self) -> None:
        # Strict JSON parser checks (including exact MAX_INT_DIGITS & MAX_JSON_BYTES boundaries)
        self.assertEqual(oracle.parse_strict_json_text("[1,true,null]", require_object=False), [1, True, None])
        self.assertEqual(oracle.parse_strict_json_text('{"a": ' + ("9" * 1000) + "}")["a"], int("9" * 1000))
        exact_cap_json = '{"a":"' + ("x" * (oracle.MAX_JSON_BYTES - 8)) + '"}'
        self.assertEqual(len(exact_cap_json.encode("utf-8")), oracle.MAX_JSON_BYTES)
        self.assertEqual(len(oracle.parse_strict_json_text(exact_cap_json)["a"]), oracle.MAX_JSON_BYTES - 8)
        over_cap_json = '{"a":"' + ("x" * (oracle.MAX_JSON_BYTES - 7)) + '"}'
        with self.assertRaises(oracle.ChandrasekharError) as cap_ctx:
            oracle.parse_strict_json_text(over_cap_json)
        self.assertEqual(cap_ctx.exception.code, "JSON_TOO_LARGE")

        with self.assertRaises(oracle.ChandrasekharError):
            oracle.parse_strict_json_text("[1,2]", require_object=True)
        with self.assertRaises(oracle.ChandrasekharError):
            oracle.parse_strict_json_text('{"x": 1.5}')
        with self.assertRaises(oracle.ChandrasekharError):
            oracle.parse_strict_json_text('{"x": NaN}')
        with self.assertRaises(oracle.ChandrasekharError):
            oracle.parse_strict_json_text('{"a": 1, "\\u0061": 2}')
        with self.assertRaises(oracle.ChandrasekharError) as big_int_ctx:
            oracle.parse_strict_json_text('{"a": ' + ("9" * 5000) + "}")
        self.assertEqual(big_int_ctx.exception.code, "INT_DIGITS_EXCEEDED")
        with self.assertRaises(oracle.ChandrasekharError):
            oracle.parse_strict_json_text("{bad}")
        with self.assertRaises(oracle.ChandrasekharError):
            oracle.parse_strict_json_text("[" * 70 + "]" * 70, require_object=False)

        # Iterative tree depth (exact boundary max_depth=1 passes, depth 2 fails) & forbidden types
        oracle.validate_json_tree_iterative({"a": 1}, max_depth=1)
        with self.assertRaises(oracle.ChandrasekharError):
            oracle.validate_json_tree_iterative({"a": {"b": 1}}, max_depth=1)
        with self.assertRaises(oracle.ChandrasekharError):
            oracle.validate_json_tree_iterative({1: "a"})
        with self.assertRaises(oracle.ChandrasekharError):
            oracle.validate_json_tree_iterative({"x": Fraction(1, 2)})
        with self.assertRaises(oracle.ChandrasekharError):
            oracle.validate_json_tree_iterative({"x": (1, 2)})

        # Valid replay and non-replay validation
        ok_res = oracle.validate_certificate_payload(self.cert, full_replay=True)
        self.assertTrue(ok_res["valid"])

        # Hostile cert rejections (re-signed with full_replay=False to kill each guard independently!)
        with self.assertRaises(oracle.ChandrasekharError):
            oracle.validate_certificate_payload(self.cert, full_replay=1)  # type: ignore[arg-type]
        with self.assertRaises(oracle.ChandrasekharError):
            oracle.validate_certificate_payload([1, 2])
        with self.assertRaises(oracle.ChandrasekharError):
            oracle.validate_certificate_payload(_DictSub(self.cert))

        extra_keys = dict(self.cert, extra=1)
        with self.assertRaises(oracle.ChandrasekharError):
            oracle.validate_certificate_payload(extra_keys)

        bad_schema = _resign(dict(self.cert, schema="wrong"))
        with self.assertRaises(oracle.ChandrasekharError) as sc_ctx:
            oracle.validate_certificate_payload(bad_schema, full_replay=False)
        self.assertEqual(sc_ctx.exception.code, "SCHEMA_MISMATCH")

        bad_track = _resign(dict(self.cert, track_id="wrong"))
        with self.assertRaises(oracle.ChandrasekharError) as tr_ctx:
            oracle.validate_certificate_payload(bad_track, full_replay=False)
        self.assertEqual(tr_ctx.exception.code, "TRACK_ID_MISMATCH")

        bad_payload_type = _resign(dict(self.cert, payload=[1, 2]))
        with self.assertRaises(oracle.ChandrasekharError) as pt_ctx:
            oracle.validate_certificate_payload(bad_payload_type, full_replay=False)
        self.assertEqual(pt_ctx.exception.code, "INVALID_PAYLOAD_TYPE")

        # Outer-resigned mismatched payload_sha256 kills payload_sha guard independently of cert_sha guard
        bad_psha = copy.deepcopy(self.cert)
        bad_psha["payload_sha256"] = "0" * 64
        bad_psha["certificate_sha256"] = oracle.canonical_sha256(
            {
                "schema": bad_psha["schema"],
                "track_id": bad_psha["track_id"],
                "payload_sha256": bad_psha["payload_sha256"],
                "payload": bad_psha["payload"],
            }
        )
        with self.assertRaises(oracle.ChandrasekharError) as ps_ctx:
            oracle.validate_certificate_payload(bad_psha, full_replay=False)
        self.assertEqual(ps_ctx.exception.code, "PAYLOAD_SHA_MISMATCH")

        bad_csha = dict(self.cert, certificate_sha256="0" * 64)
        with self.assertRaises(oracle.ChandrasekharError) as cs_ctx:
            oracle.validate_certificate_payload(bad_csha, full_replay=False)
        self.assertEqual(cs_ctx.exception.code, "CERT_SHA_MISMATCH")

        # Re-signed tampered payload passes full_replay=False, fails full_replay=True
        tampered = copy.deepcopy(self.cert)
        tampered["payload"]["novelty_tier"] = "N9"
        resigned = _resign(tampered)
        self.assertTrue(oracle.validate_certificate_payload(resigned, full_replay=False)["valid"])
        with self.assertRaises(oracle.ChandrasekharError):
            oracle.validate_certificate_payload(resigned, full_replay=True)

    def test_04_independent_semantic_audit_kills_every_tamper(self) -> None:
        ok_ind = audit.independent_audit_payload(self.cert["payload"])
        self.assertTrue(ok_ind["independent_audit_passed"])
        self.assertEqual(ok_ind["multipoles_checked"], 3)
        self.assertEqual(ok_ind["critical_points_checked"], 4)
        self.assertEqual(ok_ind["albedo_cases_checked"], 4)

        def mutate_and_expect_fail(mutator, expected_code: str | None = None) -> None:
            p = copy.deepcopy(self.cert["payload"])
            mutator(p)
            with self.assertRaises(oracle.ChandrasekharError) as ctx:
                audit.independent_audit_payload(p)
            if expected_code is not None:
                self.assertEqual(ctx.exception.code, expected_code)

        # Pillar 1 tampers
        mutate_and_expect_fail(lambda p: p["theorem1_black_hole_darboux"].__setitem__("zerilli_superpotential_identity_exact", False))
        mutate_and_expect_fail(lambda p: p["theorem1_black_hole_darboux"]["multipoles"][0].__setitem__("lambda", "99"))
        mutate_and_expect_fail(lambda p: p["theorem1_black_hole_darboux"]["multipoles"][0].__setitem__("lambda", "²"), "INVALID_RATIONAL")
        mutate_and_expect_fail(lambda p: p["theorem1_black_hole_darboux"]["multipoles"][0].__setitem__("omega_as_times_M", "99"))
        mutate_and_expect_fail(lambda p: p["theorem1_black_hole_darboux"]["multipoles"][0].__setitem__("v_rw_at_r5M", "1/2"))
        mutate_and_expect_fail(lambda p: p["theorem1_black_hole_darboux"]["multipoles"][0].__setitem__("v_zerilli_at_r5M", "1/2"))

        # Pillar 2 tampers
        mutate_and_expect_fail(lambda p: p["theorem2_magnetoconvection_sos"].__setitem__("sos_identity_exact", False))
        mutate_and_expect_fail(lambda p: p["theorem2_magnetoconvection_sos"]["critical_points"][0].__setitem__("Q_over_pi2", "1"))
        mutate_and_expect_fail(lambda p: p["theorem2_magnetoconvection_sos"]["critical_points"][0].__setitem__("R_c_over_pi4", "1"))
        mutate_and_expect_fail(lambda p: p["theorem2_magnetoconvection_sos"]["critical_points"][0].__setitem__("supercritical_margin_at_delta_1e_3", "0"))

        # Pillar 3 tampers (independently killing mismatch, <=0, >=tol, and range checks)
        mutate_and_expect_fail(lambda p: p["theorem3_lane_emden_polytropes"].__setitem__("n0_closed_form_exact", False))
        mutate_and_expect_fail(lambda p: p["theorem3_lane_emden_polytropes"]["n3_series_prefix"].__setitem__(1, "-1/5"))
        mutate_and_expect_fail(lambda p: p["theorem3_lane_emden_polytropes"].__setitem__("xi1_width", "1/1000000000"))
        mutate_and_expect_fail(
            lambda p: (
                p["theorem3_lane_emden_polytropes"].__setitem__("xi1_hi", p["theorem3_lane_emden_polytropes"]["xi1_lo"]),
                p["theorem3_lane_emden_polytropes"].__setitem__("xi1_width", "0"),
            )
        )
        mutate_and_expect_fail(
            lambda p: (
                p["theorem3_lane_emden_polytropes"].__setitem__("xi1_lo", "68968481/10000000"),
                p["theorem3_lane_emden_polytropes"].__setitem__("xi1_hi", "68968482/10000000"),
                p["theorem3_lane_emden_polytropes"].__setitem__("xi1_width", "1/10000000"),
            )
        )
        mutate_and_expect_fail(lambda p: p["theorem3_lane_emden_polytropes"].__setitem__("omega3_width", "1/1000000000"))
        mutate_and_expect_fail(
            lambda p: (
                p["theorem3_lane_emden_polytropes"].__setitem__("omega3_hi", p["theorem3_lane_emden_polytropes"]["omega3_lo"]),
                p["theorem3_lane_emden_polytropes"].__setitem__("omega3_width", "0"),
            )
        )
        mutate_and_expect_fail(
            lambda p: (
                p["theorem3_lane_emden_polytropes"].__setitem__("omega3_lo", "20182351/10000000"),
                p["theorem3_lane_emden_polytropes"].__setitem__("omega3_hi", "20182352/10000000"),
                p["theorem3_lane_emden_polytropes"].__setitem__("omega3_width", "1/10000000"),
            )
        )
        # Out-of-window endpoints
        mutate_and_expect_fail(
            lambda p: (
                p["theorem3_lane_emden_polytropes"].__setitem__("xi1_lo", "6896848/1000000"),
                p["theorem3_lane_emden_polytropes"].__setitem__("xi1_hi", "68968480001/10000000000"),
                p["theorem3_lane_emden_polytropes"].__setitem__("xi1_width", "1/10000000000"),
            )
        )
        mutate_and_expect_fail(
            lambda p: (
                p["theorem3_lane_emden_polytropes"].__setitem__("xi1_lo", "68968489999/10000000000"),
                p["theorem3_lane_emden_polytropes"].__setitem__("xi1_hi", "6896849/1000000"),
                p["theorem3_lane_emden_polytropes"].__setitem__("xi1_width", "1/10000000000"),
            )
        )
        mutate_and_expect_fail(
            lambda p: (
                p["theorem3_lane_emden_polytropes"].__setitem__("omega3_lo", "2018235/1000000"),
                p["theorem3_lane_emden_polytropes"].__setitem__("omega3_hi", "20182350001/10000000000"),
                p["theorem3_lane_emden_polytropes"].__setitem__("omega3_width", "1/10000000000"),
            )
        )
        mutate_and_expect_fail(
            lambda p: (
                p["theorem3_lane_emden_polytropes"].__setitem__("omega3_lo", "20182359999/10000000000"),
                p["theorem3_lane_emden_polytropes"].__setitem__("omega3_hi", "2018236/1000000"),
                p["theorem3_lane_emden_polytropes"].__setitem__("omega3_width", "1/10000000000"),
            )
        )

        # Pillar 4 tampers (independently killing m_vol <= 0 vs s_flx + m_vol != l_vol)
        mutate_and_expect_fail(lambda p: p["theorem4_chandrasekhar_fermi_virial"].__setitem__("gauss_virial_balance_zero", False))
        mutate_and_expect_fail(
            lambda p: (
                p["theorem4_chandrasekhar_fermi_virial"].__setitem__("cube_magnetic_energy_M", "0"),
                p["theorem4_chandrasekhar_fermi_virial"].__setitem__(
                    "cube_surface_stress_flux", p["theorem4_chandrasekhar_fermi_virial"]["cube_lorentz_virial_int"]
                ),
            )
        )
        mutate_and_expect_fail(lambda p: p["theorem4_chandrasekhar_fermi_virial"].__setitem__("cube_surface_stress_flux", "0"))

        # Pillar 5 tampers (killing QUAD_LAW, ALBEDO, and ALPHA0 spurious-branch guards independently)
        mutate_and_expect_fail(lambda p: p["theorem5_radiative_transfer_riccati"].__setitem__("alpha0_algebraic_law_exact_Q_q", False))
        mutate_and_expect_fail(
            lambda p: p["theorem5_radiative_transfer_riccati"]["albedo_cases"][0].__setitem__("alpha0_exact", "1"),
            expected_code="AUDIT_T5_QUAD_LAW",
        )
        mutate_and_expect_fail(
            lambda p: p["theorem5_radiative_transfer_riccati"]["albedo_cases"][0].__setitem__("alpha0_exact", "4"),
            expected_code="AUDIT_T5_ALPHA0",
        )
        mutate_and_expect_fail(
            lambda p: p["theorem5_radiative_transfer_riccati"]["albedo_cases"][0].__setitem__("q", "1/3"),
            expected_code="AUDIT_T5_ALBEDO",
        )
        mutate_and_expect_fail(lambda p: p["theorem5_radiative_transfer_riccati"]["albedo_cases"][0].__setitem__("quad4_max_residual_lt_1e_18", False))

    def test_05_zone_b_file_io_and_cli_hardening(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            cert_path = root / "cert.json"

            # Path type and NUL/empty guards
            with self.assertRaises(oracle.ChandrasekharError):
                audit.require_safe_path(str(cert_path))
            with self.assertRaises(oracle.ChandrasekharError):
                audit.require_safe_path(_PathSub(str(cert_path)))
            with self.assertRaises(oracle.ChandrasekharError):
                audit.require_safe_path(Path("bad\x00name"))
            with self.assertRaises(oracle.ChandrasekharError):
                audit.require_safe_path(Path("\ud800"))
            with self.assertRaises(oracle.ChandrasekharError):
                audit.write_regular_file_bytes(cert_path, "not-bytes")  # type: ignore[arg-type]

            # Write and check valid cert
            w_res = audit.write_certificate_file(cert_path)
            self.assertTrue(w_res["written"])
            c_res = audit.check_certificate_file(cert_path)
            self.assertTrue(c_res["valid"])
            self.assertTrue(c_res["independent_audit"]["independent_audit_passed"])

            # Symlink target, symlink ancestor, file-as-dir, raw sym/../ok traversal, and symlinked/stale PWD
            sym_target = root / "sym_cert.json"
            os.symlink(cert_path, sym_target)
            with self.assertRaises(oracle.ChandrasekharError) as sym_r_ctx:
                audit.read_regular_file_bytes(sym_target)
            self.assertEqual(sym_r_ctx.exception.code, "SYMLINK_FORBIDDEN")
            with self.assertRaises(oracle.ChandrasekharError) as sym_w_ctx:
                audit.write_regular_file_bytes(sym_target, b"x\n")
            self.assertEqual(sym_w_ctx.exception.code, "SYMLINK_FORBIDDEN")
            with self.assertRaises(oracle.ChandrasekharError) as sym_p_ctx:
                audit.require_safe_path(sym_target)
            self.assertEqual(sym_p_ctx.exception.code, "SYMLINK_FORBIDDEN")

            # File used as parent directory triggers ENOTDIR -> SYMLINK_FORBIDDEN
            with self.assertRaises(oracle.ChandrasekharError) as notdir_ctx:
                audit.require_safe_path(cert_path / "child.json")
            self.assertEqual(notdir_ctx.exception.code, "SYMLINK_FORBIDDEN")

            # Empty parts (Path(".") / Path("/")) allowed in require_safe_path, rejected as NON_REGULAR_FILE on read/write
            self.assertEqual(audit.require_safe_path(Path("/")), Path("/"))
            with self.assertRaises(oracle.ChandrasekharError) as root_r_ctx:
                audit.read_regular_file_bytes(Path("/"))
            self.assertEqual(root_r_ctx.exception.code, "NON_REGULAR_FILE")
            with self.assertRaises(oracle.ChandrasekharError) as root_w_ctx:
                audit.write_regular_file_bytes(Path("."), b"x\n")
            self.assertEqual(root_w_ctx.exception.code, "NON_REGULAR_FILE")

            real_sub = root / "real_sub"
            real_sub.mkdir()
            sym_dir = root / "sym_dir"
            os.symlink(real_sub, sym_dir)
            with self.assertRaises(oracle.ChandrasekharError) as sym_anc_ctx:
                audit.require_safe_path(sym_dir / ".." / "cert.json")
            self.assertEqual(sym_anc_ctx.exception.code, "SYMLINK_FORBIDDEN")

            orig_cwd = os.getcwd()
            orig_pwd = os.environ.get("PWD")
            try:
                os.chdir(real_sub)
                os.environ["PWD"] = str(sym_dir)
                with self.assertRaises(oracle.ChandrasekharError) as pwd_sym_ctx:
                    audit.require_safe_path(Path("rel.json"))
                self.assertEqual(pwd_sym_ctx.exception.code, "SYMLINK_FORBIDDEN")
                os.environ["PWD"] = str(root / "nonexistent_stale_pwd_dir")
                rel_p = Path("./local.json")
                self.assertEqual(audit.require_safe_path(rel_p), rel_p)
                os.environ["PWD"] = str(real_sub)
                self.assertEqual(audit.require_safe_path(rel_p), rel_p)
                os.environ.pop("PWD", None)
                self.assertEqual(audit.require_safe_path(rel_p), rel_p)
                with mock.patch.object(Path, "cwd", side_effect=FileNotFoundError("deleted cwd")):
                    with self.assertRaises(oracle.ChandrasekharError) as cwd_ctx:
                        audit.require_safe_path(rel_p)
                    self.assertEqual(cwd_ctx.exception.code, "CWD_UNAVAILABLE")
            finally:
                os.chdir(orig_cwd)
                if orig_pwd is None:
                    os.environ.pop("PWD", None)
                else:
                    os.environ["PWD"] = orig_pwd

            # Overwriting an existing regular file with st_nlink == 1 succeeds via atomic O_EXCL + os.replace
            # Pre-create temp attempt 0 to verify deterministic collision retry on attempt 1
            overwrite_p = root / "atomic_target.json"
            overwrite_p.write_bytes(b"old-content-longer-than-new\n")
            collide0 = root / f".{overwrite_p.name}.s24tmp.{os.getpid()}.0"
            collide0.write_bytes(b"stale-collision\n")
            audit.write_regular_file_bytes(overwrite_p, b"new\n")
            self.assertEqual(overwrite_p.read_bytes(), b"new\n")
            collide0.unlink()

            # Exhausting all 16 O_EXCL attempts raises FILE_WRITE_ERROR
            real_open = os.open

            def _always_eexist(p_arg, flags_arg, *args_arg, **kwargs_arg):
                if flags_arg & os.O_EXCL:
                    raise FileExistsError("simulated collision")
                return real_open(p_arg, flags_arg, *args_arg, **kwargs_arg)

            with mock.patch.object(os, "open", side_effect=_always_eexist):
                with self.assertRaises(oracle.ChandrasekharError) as coll_ctx:
                    audit.write_regular_file_bytes(overwrite_p, b"fail\n")
            self.assertEqual(coll_ctx.exception.code, "FILE_WRITE_ERROR")

            # Failure during os.replace cleans up temp file and preserves original bytes
            with mock.patch.object(os, "replace", side_effect=PermissionError("blocked")):
                with self.assertRaises(oracle.ChandrasekharError) as rep_ctx:
                    audit.write_regular_file_bytes(overwrite_p, b"fail2\n")
            self.assertEqual(rep_ctx.exception.code, "FILE_WRITE_ERROR")
            self.assertEqual(overwrite_p.read_bytes(), b"new\n")
            self.assertEqual(list(root.glob(f".{overwrite_p.name}.s24tmp.*")), [])

            # Hardlink write refused BEFORE any mutation (original content preserved bit-for-bit!)
            orig_bytes = cert_path.read_bytes()
            hl_path = root / "hardlink_cert.json"
            os.link(cert_path, hl_path)
            with self.assertRaises(oracle.ChandrasekharError) as hl_ctx:
                audit.write_regular_file_bytes(hl_path, b"clobbered\n")
            self.assertEqual(hl_ctx.exception.code, "HARDLINK_FORBIDDEN")
            self.assertEqual(cert_path.read_bytes(), orig_bytes)
            hl_path.unlink()

            # FIFO (non-regular, non-blocking!), /dev/null, directory, missing, chmod 000, oversized
            fifo_path = root / "pipe.fifo"
            os.mkfifo(fifo_path)
            with self.assertRaises(oracle.ChandrasekharError):
                audit.read_regular_file_bytes(fifo_path)
            with self.assertRaises(oracle.ChandrasekharError) as fifo_w_ctx:
                audit.write_regular_file_bytes(fifo_path, b"x\n")
            self.assertEqual(fifo_w_ctx.exception.code, "NON_REGULAR_FILE")
            with self.assertRaises(oracle.ChandrasekharError):
                audit.read_regular_file_bytes(Path("/dev/null"))
            if hasattr(os, "mkfifo"):
                nonreg_fifo = root / "nonreg_fifo"
                os.mkfifo(nonreg_fifo)
                with self.assertRaises(oracle.ChandrasekharError) as nonreg_ctx:
                    audit.write_regular_file_bytes(nonreg_fifo, b"x\n")
                self.assertEqual(nonreg_ctx.exception.code, "NON_REGULAR_FILE")
            with self.assertRaises(oracle.ChandrasekharError):
                audit.read_regular_file_bytes(root)
            with self.assertRaises(oracle.ChandrasekharError):
                audit.read_regular_file_bytes(root / "missing.json")
            with self.assertRaises(oracle.ChandrasekharError) as nodir_ctx:
                audit.write_regular_file_bytes(root / "no_such_dir" / "x.json", b"x\n")
            self.assertEqual(nodir_ctx.exception.code, "PATH_NOT_FOUND")

            exact_file = root / "exact_cap.bin"
            exact_file.write_bytes(b"a" * oracle.MAX_JSON_BYTES)
            self.assertEqual(len(audit.read_regular_file_bytes(exact_file)), oracle.MAX_JSON_BYTES)

            big_file = root / "big.json"
            big_file.write_bytes(b"a" * (oracle.MAX_JSON_BYTES + 1))
            with self.assertRaises(oracle.ChandrasekharError) as big_ctx:
                audit.read_regular_file_bytes(big_file)
            self.assertEqual(big_ctx.exception.code, "FILE_TOO_LARGE")

            no_perm = root / "noperm.json"
            no_perm.write_bytes(b"{}\n")
            os.chmod(no_perm, 0o000)
            try:
                if os.geteuid() != 0:
                    with self.assertRaises(oracle.ChandrasekharError):
                        audit.read_regular_file_bytes(no_perm)
            finally:
                os.chmod(no_perm, 0o600)

            # CRLF, missing LF, invalid UTF-8, non-canonical JSON (assert exact error codes!)
            crlf_p = root / "crlf.json"
            crlf_p.write_bytes(orig_bytes[:-1] + b"\r\n")
            with self.assertRaises(oracle.ChandrasekharError) as crlf_ctx:
                audit.check_certificate_file(crlf_p)
            self.assertEqual(crlf_ctx.exception.code, "CRLF_FORBIDDEN")

            nolf_p = root / "nolf.json"
            nolf_p.write_bytes(orig_bytes[:-1])
            with self.assertRaises(oracle.ChandrasekharError) as nolf_ctx:
                audit.check_certificate_file(nolf_p)
            self.assertEqual(nolf_ctx.exception.code, "MISSING_TRAILING_LF")

            bad_utf8_p = root / "bad_utf8.json"
            bad_utf8_p.write_bytes(b"\xff\xfe\n")
            with self.assertRaises(oracle.ChandrasekharError):
                audit.check_certificate_file(bad_utf8_p)

            noncanon_p = root / "noncanon.json"
            noncanon_p.write_bytes(b" " + orig_bytes)
            with self.assertRaises(oracle.ChandrasekharError):
                audit.check_certificate_file(noncanon_p)

            # CLI parser & main() roundtrips and error codes
            stderr_nonlist = io.StringIO()
            with mock.patch.object(sys, "stderr", stderr_nonlist):
                rc_nl = audit.main("not-a-list")  # type: ignore[arg-type]
            self.assertEqual(rc_nl, 2)
            self.assertEqual(json.loads(stderr_nonlist.getvalue())["error_code"], "INVALID_ARGV")

            for bad_path_argv in (["--check", ""], ["--check", "--json"], ["--write", "--json"]):
                stderr_bp = io.StringIO()
                with mock.patch.object(sys, "stderr", stderr_bp):
                    rc_bp = audit.main(bad_path_argv)
                self.assertEqual(rc_bp, 2)
                self.assertEqual(json.loads(stderr_bp.getvalue())["error_code"], "INVALID_PATH_ARG")

            for bad_argv in (
                [123],
                [_StrSub("--standalone")],
                ["\ud800"],
                ["--json", "--json"],
                ["--standalone", "--standalone"],
                ["--standalone", "--check", str(cert_path)],
                ["--check"],
                ["--check=--json"],
                ["--write=--json"],
                ["--unknown"],
            ):
                stderr_buf = io.StringIO()
                with mock.patch.object(sys, "stderr", stderr_buf):
                    rc = audit.main(bad_argv)  # type: ignore[arg-type]
                self.assertEqual(rc, 2, msg=f"expected rc=2 for argv={bad_argv!r}")
                err_obj = json.loads(stderr_buf.getvalue())
                self.assertFalse(err_obj["valid"])

            # Valid CLI modes: default standalone, --standalone --json, --write, --check --json
            out_path = root / "cli_out.json"
            for argv in (
                [],
                ["--standalone", "--json"],
                ["--write", str(out_path)],
                ["--check", str(out_path), "--json"],
            ):
                stdout_buf = io.StringIO()
                with mock.patch.object(sys, "stdout", stdout_buf):
                    rc = audit.main(argv)
                self.assertEqual(rc, 0, msg=f"expected rc=0 for argv={argv!r}")
                self.assertTrue(stdout_buf.getvalue().endswith("\n"))


if __name__ == "__main__":
    unittest.main()
