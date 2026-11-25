#!/usr/bin/env python3
"""Adversarial & Mutation-Killing Test Suite: 4 Mathematical/Physical Pillars,
Exported-Helper Soundness, 100% Mutation/BoolOp Killers & Strict I/O Security.

Pure Python 3 standard library: zero AST floats, zero bare asserts, zero mathematical RNG.
"""
from __future__ import annotations

import ast
import copy
from fractions import Fraction
import hashlib
import io
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import threading
import unittest
from unittest import mock

_THIS_DIR = Path(__file__).resolve().parent
if str(_THIS_DIR) not in sys.path:
    sys.path.insert(0, str(_THIS_DIR))

import tectonics_relu_regions_oracle as oracle
import tectonics_relu_regions_audit as audit

Err = oracle.TectonicsReluError


class _SubInt(int):
    pass


class _SubStr(str):
    pass


class _SubFrac(Fraction):
    pass


class _SubPath(type(Path("."))):
    pass


class _SubList(list):
    pass


def _resign_cert(cert: dict[str, object]) -> dict[str, object]:
    """Recompute payload_sha256 and certificate_sha256 after tampering payload (tests full_replay=False)."""
    payload = cert["payload"]
    p_sha = hashlib.sha256(oracle.canonical_json_bytes(payload)).hexdigest()
    cert["payload_sha256"] = p_sha
    pre = {
        "schema": cert["schema"],
        "track_id": cert["track_id"],
        "payload_sha256": p_sha,
        "payload": payload,
    }
    cert["certificate_sha256"] = hashlib.sha256(oracle.canonical_json_bytes(pre)).hexdigest()
    return cert


class TestTrackS43TectonicsReluRegionsR5(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.cert = oracle.build_standalone_certificate()
        cls.payload = cls.cert["payload"]

    # -----------------------------------------------------------------------
    # 0. AST Purity Gate (Zero Floats, Zero Bare Asserts, Zero islink/isdigit/min/max)
    # -----------------------------------------------------------------------

    def test_00_ast_purity_zero_floats_asserts_min_max(self) -> None:
        for fname in (
            "tectonics_relu_regions_oracle.py",
            "tectonics_relu_regions_audit.py",
            "test_tectonics_relu_regions_r5.py",
        ):
            src = (_THIS_DIR / fname).read_text(encoding="utf-8")
            tree = ast.parse(src)
            for node in ast.walk(tree):
                self.assertNotIsInstance(node, ast.Assert, f"bare assert in {fname}")
                if isinstance(node, ast.Constant):
                    self.assertNotIsInstance(node.value, float, f"float literal in {fname}")
                if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                    self.assertNotIn(node.func.id, ("float", "min", "max"), f"forbidden {node.func.id}() in {fname}")
                if isinstance(node, ast.Attribute):
                    self.assertNotIn(node.attr, ("islink", "isdigit"), f"forbidden .{node.attr} in {fname}")

    # -----------------------------------------------------------------------
    # 1. Four Mathematical & Physical Pillars
    # -----------------------------------------------------------------------

    def test_01_pillar1_bingham_relu_and_poiseuille(self) -> None:
        self.assertEqual(self.payload["novelty_tier"], "N1")
        self.assertEqual(self.payload["individual_domains_novelty"], "N0")
        self.assertEqual(self.payload["oracle_class"], "exact")
        self.assertIs(self.payload["measured_live_mantle_convection_gcm"], False)
        self.assertIs(self.payload["measured_live_deep_network_training_runs"], False)
        self.assertIs(self.payload["zero_trust_path_floats"], True)
        self.assertIs(self.payload["zero_bare_asserts"], True)
        self.assertIs(self.payload["zero_mathematical_rng"], True)

        p1 = self.payload["pillar1_bingham_relu_poiseuille"]
        vp = p1["variational_proximal_identity"]
        self.assertEqual(vp["grid_points"], 41)
        self.assertEqual(vp["plug_points"], 17)
        self.assertEqual(vp["positive_shear_points"], 12)
        self.assertEqual(vp["negative_shear_points"], 12)
        self.assertIs(vp["kkt_subdifferential_all_exact"], True)
        self.assertIs(vp["variational_dominance_all_strict"], True)
        self.assertEqual(len(vp["sample_witnesses"]), 5)
        self.assertEqual(vp["sample_witnesses"][0]["e_star"], "-1")
        self.assertEqual(vp["sample_witnesses"][2]["e_star"], "0")
        self.assertEqual(vp["sample_witnesses"][4]["e_star"], "1")

        ch = p1["poiseuille_plug_shear_channel"]
        self.assertEqual(ch["yield_number_y"], "1/2")
        self.assertEqual(ch["y_plug"], "1")
        self.assertEqual(ch["u_plug"], "2")
        self.assertEqual(ch["q_half"], "10/3")
        self.assertEqual(ch["q_full"], "20/3")
        self.assertEqual(ch["d_visc_half"], "16/3")
        self.assertEqual(ch["d_yield_half"], "8")
        self.assertEqual(ch["power_in_half"], "40/3")
        self.assertIs(ch["dissipation_balance_exact"], True)
        self.assertIs(ch["no_slip_walls_exact"], True)
        self.assertIs(ch["two_neuron_relu_matches_bingham_all"], True)
        self.assertIs(ch["rigid_plug_zero_strain_all"], True)
        self.assertEqual(len(ch["channel_probes"]), 9)

    def test_02_pillar2_yield_phase_diagram_and_2d_relu(self) -> None:
        p2 = self.payload["pillar2_yield_phase_and_2d_relu"]
        pd = p2["yield_phase_diagram"]
        self.assertEqual(pd["yield_points_count"], 8)
        self.assertEqual(pd["newtonian_count"], 1)
        self.assertEqual(pd["mobile_lid_count"], 4)
        self.assertEqual(pd["stagnant_lid_count"], 3)
        self.assertIs(pd["flux_strictly_decreasing_to_y1"], True)
        self.assertIs(pd["stagnant_lid_exact_zero_flux"], True)
        self.assertIs(pd["all_dissipation_balances_exact"], True)
        self.assertEqual(
            [row["q_half"] for row in pd["sweep"]],
            ["32/3", "833/96", "27/4", "10/3", "11/12", "0", "0", "0"],
        )
        self.assertEqual(pd["sweep"][0]["tectonic_regime"], "newtonian_magma_ocean")
        self.assertEqual(pd["sweep"][3]["tectonic_regime"], "mobile_lid_plate_tectonics")
        self.assertEqual(pd["sweep"][5]["tectonic_regime"], "stagnant_lid")

        r2 = p2["shallow_2d_relu_regions"]
        self.assertEqual(r2["neuron_count"], 3)
        self.assertEqual(r2["linear_region_count"], 7)
        self.assertEqual(r2["impossible_pattern"], [0, 0, 1])
        self.assertEqual(r2["codim1_wall_count"], 9)
        self.assertIs(r2["piecewise_constant_jacobian_all_regions"], True)
        self.assertIs(r2["all_walls_exact_rank1_jump"], True)
        self.assertIs(r2["all_walls_continuous"], True)

    def test_03_pillar3_triple_junction_tropical_and_rtf_contrast(self) -> None:
        p3 = self.payload["pillar3_triple_junction_tropical_rtf"]
        rtf = p3["rtf_triple_junction_cocycle"]
        self.assertIs(rtf["omega_cocycle_zero"], True)
        self.assertIs(rtf["velocity_cocycle_zero"], True)
        self.assertIs(rtf["all_velocities_tangent_to_s2"], True)
        self.assertEqual([w["normal_opening"] for w in rtf["walls"]], ["1", "-2", "0"])
        self.assertEqual([w["tangential_shear"] for w in rtf["walls"]], ["0", "0", "-1"])
        self.assertEqual(
            [w["classification"] for w in rtf["walls"]],
            ["divergent_ridge", "convergent_subduction_trench", "transform_fault"],
        )

        tr = p3["tropical_3region_relu_hinge"]
        self.assertIs(tr["gradient_jump_cocycle_zero"], True)
        self.assertIs(tr["weighted_tropical_balancing_zero"], True)
        self.assertIs(tr["unweighted_ray_sum_nonzero"], True)
        self.assertIs(tr["two_layer_relu_equals_max_all_probes"], True)
        self.assertIs(tr["interior_gradients_exact"], True)
        self.assertEqual(tr["tropical_weights"], {"AB": 2, "BC": 1, "CA": 1})

        jc = p3["relu_2d_rtf_jacobian_contrast"]
        self.assertIs(jc["dead_subduction_collision_exact"], True)
        self.assertEqual([c["det_j_plus"] for c in jc["cases"]], ["3", "1/2", "0", "1"])

    def test_04_pillar4_s2_cube_hodge_and_three_obstructions(self) -> None:
        p4 = self.payload["pillar4_s2_hodge_obstructions"]
        cube = p4["discrete_s2_cube_hodge_complex"]
        self.assertEqual((cube["vertices"], cube["edges"], cube["faces"], cube["euler_characteristic"]), (8, 12, 6, 2))
        self.assertEqual((cube["rank_d0"], cube["rank_d1"], cube["betti_numbers"]), (7, 5, [1, 0, 1]))
        self.assertIs(cube["d1_d0_identically_zero"], True)
        self.assertIs(cube["closed_oriented_s2_boundary_zero"], True)
        self.assertIs(cube["betti_euler_matches"], True)

        oa = p4["obstruction_a_toroidal_curl_zero"]
        self.assertEqual((oa["e_pol"], oa["e_tor"], oa["e_eq_combined"], oa["hodge_inner_product"], oa["equipartition_ratio"]), (4, 4, 8, 0, "1"))
        self.assertIs(oa["poloidal_curl_identically_zero"], True)
        self.assertIs(oa["toroidal_div_identically_zero"], True)
        self.assertIs(oa["hodge_pythagorean_exact"], True)

        ob = p4["obstruction_b_gauss_stokes_vs_relu"]
        self.assertIs(ob["outward_div_edge_sign_exact"], True)
        self.assertEqual(ob["s2_basis_fluxes_zero_sum_count"], 12)
        self.assertIs(ob["s2_gauss_stokes_universal_exact"], True)
        self.assertEqual(ob["asym_flux_u"], [-3, 1, -2, 0, -1, 2, -4, 0, 3, -2, -1, 1])
        self.assertEqual(ob["asym_outward_div"], [-1, 3, 1, -2, -9, 4, 5, -1])
        self.assertEqual((ob["asym_ridge_creation_sum"], ob["asym_trench_subduction_sum"], ob["asym_global_net_div"]), (13, -13, 0))
        self.assertEqual((ob["unconstrained_relu_area_ratio"], ob["unconstrained_relu_global_div"]), ("1/4", -4))
        self.assertIs(ob["unconstrained_relu_violates_gauss_stokes"], True)

        # Explicit outward discrete divergence (DEC codifferential delta_1 = -d0^T) sign-convention test:
        # unit flux directed OUT of tail vertex u and INTO head vertex v contributes +1 at u and -1 at v.
        d0, _ = oracle._build_s2_cube_operators()
        for e_i, (tail_v, head_v) in enumerate(oracle._S2_CUBE_EDGES):
            unit_flux = [1 if k == e_i else 0 for k in range(12)]
            div_e = oracle.discrete_outward_div_s2(d0, unit_flux)
            self.assertEqual(div_e[tail_v], 1)
            self.assertEqual(div_e[head_v], -1)
            for w in range(8):
                if w not in (tail_v, head_v):
                    self.assertEqual(div_e[w], 0)
            self.assertEqual(sum(div_e), 0)
            neg_div_e = oracle.discrete_outward_div_s2(d0, [-x for x in unit_flux])
            self.assertEqual(neg_div_e[tail_v], -1)
            self.assertEqual(neg_div_e[head_v], 1)
        recomp_div = oracle.discrete_outward_div_s2(d0, ob["asym_flux_u"])
        self.assertEqual(recomp_div, ob["asym_outward_div"])
        self.assertEqual(sum(x for x in recomp_div if x > 0), 13)
        self.assertEqual(sum(x for x in recomp_div if x < 0), -13)
        self.assertEqual(sum(recomp_div), 0)

        oc = p4["obstruction_c_static_feedforward_vs_gdn2_advection"]
        self.assertIs(oc["static_inference_frozen"], True)
        self.assertEqual(oc["gdn2_delta_rank"], 1)
        self.assertIs(oc["gdn2_key_overwrite_exact"], True)
        self.assertEqual((oc["gdn2_wall_x_t0"], oc["gdn2_wall_x_t1"], oc["gdn2_wall_displacement"]), ("1", "4", "3"))
        self.assertEqual((oc["gdn2_pre_t0"], oc["gdn2_pre_t1"], oc["gdn2_relu_t0"], oc["gdn2_relu_t1"]), ("1/2", "-5/8", "1/2", "0"))
        self.assertIs(oc["gdn2_inference_region_flip_zero_weight_update"], True)

    # -----------------------------------------------------------------------
    # 2. Exported Oracle Primitives & Math Helper Soundness (100% Boundary/BoolOp Killers)
    # -----------------------------------------------------------------------

    def test_05_oracle_primitives_boundaries_and_rejections(self) -> None:
        self.assertEqual(oracle.require_exact_int(5, "x", min_val=5, max_val=5), 5)
        for bad in (True, _SubInt(5), "5"):
            with self.assertRaises(Err) as cm:
                oracle.require_exact_int(bad, "x")
            self.assertEqual(cm.exception.code, "INVALID_INT")
        with self.assertRaises(Err) as cm:
            oracle.require_exact_int(4, "x", min_val=5)
        self.assertEqual(cm.exception.code, "INT_BELOW_MIN")
        with self.assertRaises(Err) as cm:
            oracle.require_exact_int(6, "x", max_val=5)
        self.assertEqual(cm.exception.code, "INT_ABOVE_MAX")

        self.assertIs(oracle.require_exact_bool(True, "b"), True)
        with self.assertRaises(Err) as cm:
            oracle.require_exact_bool(1, "b")
        self.assertEqual(cm.exception.code, "INVALID_BOOL")

        self.assertEqual(oracle.require_exact_str("", "s", non_empty=False), "")
        with self.assertRaises(Err) as cm:
            oracle.require_exact_str(_SubStr("a"), "s")
        self.assertEqual(cm.exception.code, "INVALID_STR")
        with self.assertRaises(Err) as cm:
            oracle.require_exact_str("", "s")
        self.assertEqual(cm.exception.code, "EMPTY_STR")
        with self.assertRaises(Err) as cm:
            oracle.require_exact_str("bad\ud800", "s")
        self.assertEqual(cm.exception.code, "INVALID_UTF8_STR")

        self.assertEqual(oracle.require_exact_fraction(Fraction(0, 1), "q", non_negative=True), Fraction(0, 1))
        self.assertEqual(oracle.require_exact_fraction(Fraction(1, 2), "q", positive=True), Fraction(1, 2))
        with self.assertRaises(Err) as cm:
            oracle.require_exact_fraction(_SubFrac(1, 2), "q")
        self.assertEqual(cm.exception.code, "INVALID_FRACTION")
        with self.assertRaises(Err) as cm:
            oracle.require_exact_fraction(Fraction(0, 1), "q", positive=True)
        self.assertEqual(cm.exception.code, "FRACTION_NOT_POSITIVE")
        with self.assertRaises(Err) as cm:
            oracle.require_exact_fraction(Fraction(-1, 2), "q", non_negative=True)
        self.assertEqual(cm.exception.code, "FRACTION_NEGATIVE")

        good_hex = "a" * 64
        self.assertEqual(oracle.require_sha256_hex(good_hex, "h"), good_hex)
        for bad_hex in ("a" * 63, "a" * 65, "A" * 64, "g" * 64):
            with self.assertRaises(Err) as cm:
                oracle.require_sha256_hex(bad_hex, "h")
            self.assertEqual(cm.exception.code, "INVALID_SHA256")

        # Symmetric MAX_INT_BITS = 3321 <-> MAX_INT_DIGITS = 1000
        max_bit_int = (1 << oracle.MAX_INT_BITS) - 1
        max_bit_str = str(max_bit_int)
        self.assertEqual(len(max_bit_str), oracle.MAX_INT_DIGITS)
        self.assertEqual(oracle.parse_exact_int_ascii(max_bit_str, "n"), max_bit_int)
        self.assertEqual(oracle.parse_exact_int_ascii("-" + max_bit_str, "n"), -max_bit_int)
        self.assertEqual(oracle.parse_exact_int_ascii("0", "n"), 0)
        for tok, code in (
            ("-", "INVALID_INT_TOKEN"),
            ("9" * (oracle.MAX_INT_DIGITS + 1), "INT_TOKEN_TOO_LONG"),
            ("01", "LEADING_ZERO_INT"),
            ("1\u0662", "NON_ASCII_DIGIT"),
            ("-0", "NEGATIVE_ZERO_INT"),
            (str(1 << oracle.MAX_INT_BITS), "INT_TOO_LARGE"),
        ):
            with self.assertRaises(Err) as cm:
                oracle.parse_exact_int_ascii(tok, "n")
            self.assertEqual(cm.exception.code, code)

        # Rational parsing & formatting
        self.assertEqual(oracle.parse_exact_rational("-3/4", "r"), Fraction(-3, 4))
        self.assertEqual(oracle.parse_exact_rational("7", "r"), Fraction(7, 1))
        for bad_r, code in (
            ("1/2/3", "INVALID_RATIONAL"),
            ("3/1", "NON_CANONICAL_DEN"),
            ("3/0", "NON_CANONICAL_DEN"),
            ("2/4", "UNREDUCED_RATIONAL"),
        ):
            with self.assertRaises(Err) as cm:
                oracle.parse_exact_rational(bad_r, "r")
            self.assertEqual(cm.exception.code, code)

        self.assertEqual(oracle.format_exact_rational(Fraction(5, 1)), "5")
        self.assertEqual(oracle.format_exact_rational(Fraction(-5, 3)), "-5/3")
        with self.assertRaises(Err):
            oracle.format_exact_rational(Fraction(1 << oracle.MAX_INT_BITS, 1))
        self.assertEqual(oracle.format_decimal_trunc(Fraction(-1, 1000), 2), "0.00")
        self.assertEqual(oracle.format_decimal_trunc(Fraction(-1, 1000), 0), "0")
        self.assertEqual(oracle.format_decimal_trunc(Fraction(-7, 2), 2), "-3.50")
        self.assertEqual(oracle.format_decimal_trunc(Fraction(7, 2), 0), "3")
        self.assertEqual(oracle.format_decimal_trunc(Fraction(1, 3), 18), "0.333333333333333333")
        with self.assertRaises(Err):
            oracle.format_decimal_trunc(Fraction(1, 3), 19)

        # JSON tree depth=32 pass vs depth=33 fail, forbidden types, byte caps, float/const/dup-key
        ok_nested: object = 1
        for _ in range(oracle.MAX_JSON_DEPTH):
            ok_nested = [ok_nested]
        oracle.validate_json_tree_iterative(ok_nested)
        with self.assertRaises(Err) as cm:
            oracle.validate_json_tree_iterative([ok_nested])
        self.assertEqual(cm.exception.code, "JSON_TOO_DEEP")
        oracle.validate_json_tree_iterative({"ok": [True, None, max_bit_int, "s"]})
        with self.assertRaises(Err) as cm:
            oracle.validate_json_tree_iterative({"bad": (1, 2)})
        self.assertEqual(cm.exception.code, "FORBIDDEN_JSON_TYPE")

        big_s = "a" * (oracle.MAX_JSON_BYTES - 2)
        self.assertEqual(len(oracle.canonical_json_bytes(big_s)), oracle.MAX_JSON_BYTES)
        with self.assertRaises(Err) as cm:
            oracle.canonical_json_bytes("a" * (oracle.MAX_JSON_BYTES - 1))
        self.assertEqual(cm.exception.code, "JSON_TOO_LARGE")

        big_json_ok = '{"a":"' + ("x" * (oracle.MAX_JSON_BYTES - 8)) + '"}'
        self.assertEqual(len(big_json_ok.encode("utf-8")), oracle.MAX_JSON_BYTES)
        self.assertEqual(type(oracle.parse_strict_json_text(big_json_ok)), dict)
        with self.assertRaises(Err) as cm:
            oracle.parse_strict_json_text(big_json_ok + " ")
        self.assertEqual(cm.exception.code, "JSON_TOO_LARGE")
        self.assertEqual(oracle.parse_strict_json_text("[1,2]", require_object=False), [1, 2])
        for bad_j, code in (
            ('{"x":1.5}', "FLOAT_FORBIDDEN"),
            ('{"x":1e2}', "FLOAT_FORBIDDEN"),
            ('{"x":NaN}', "NON_FINITE_FORBIDDEN"),
            ('{"a":1,"a":2}', "DUPLICATE_JSON_KEY"),
            ('{"a":', "INVALID_JSON"),
            ("[1,2]", "JSON_ROOT_NOT_OBJECT"),
            ('{"n":' + "9" * 4300 + "}", "INT_TOKEN_TOO_LONG"),
        ):
            with self.assertRaises(Err) as cm:
                oracle.parse_strict_json_text(bad_j)
            self.assertEqual(cm.exception.code, code)

    def test_06_domain_math_helpers_soundness_and_boundaries(self) -> None:
        self.assertEqual(oracle.q_relu(Fraction(0, 1)), Fraction(0, 1))
        self.assertEqual(oracle.q_relu(Fraction(-3, 2)), Fraction(0, 1))
        self.assertEqual(oracle.q_relu(Fraction(3, 2)), Fraction(3, 2))
        self.assertEqual(oracle.bingham_strain_rate_relu(Fraction(2, 1), Fraction(2, 1), Fraction(1, 1)), Fraction(0, 1))
        self.assertEqual(oracle.bingham_strain_rate_relu(Fraction(5, 1), Fraction(2, 1), Fraction(3, 2)), Fraction(1, 1))
        self.assertEqual(oracle.bingham_strain_rate_relu(Fraction(-5, 1), Fraction(2, 1), Fraction(3, 2)), Fraction(-1, 1))
        self.assertEqual(
            oracle.bingham_dissipation_objective(Fraction(-1, 1), Fraction(-5, 1), Fraction(2, 1), Fraction(3, 2)),
            Fraction(-3, 2),
        )

        # bingham_channel_profile boundary |y| == H passes, |y| > H fails, stagnant lid y_plug == H
        p_edge = oracle.bingham_channel_profile(Fraction(-2, 1), Fraction(4, 1), Fraction(2, 1), Fraction(10, 1), Fraction(1, 1))
        self.assertEqual(p_edge["y_plug"], Fraction(2, 1))
        self.assertEqual(p_edge["u"], Fraction(0, 1))
        with self.assertRaises(Err) as cm:
            oracle.bingham_channel_profile(Fraction(5, 2), Fraction(4, 1), Fraction(2, 1), Fraction(4, 1), Fraction(1, 1))
        self.assertEqual(cm.exception.code, "Y_OUT_OF_CHANNEL")

        # bingham_yield_regime exact Y=0, Y=1/2, Y=1
        self.assertEqual(oracle.bingham_yield_regime(Fraction(0, 1), Fraction(4, 1), Fraction(2, 1), Fraction(1, 1))["active_shear_walls"], 0)
        self.assertEqual(oracle.bingham_yield_regime(Fraction(1, 1), Fraction(4, 1), Fraction(2, 1), Fraction(1, 1))["u_plug"], "0")

        # cross3_q / dot3_q / eval_tropical_hinge_relu / eval_shallow_relu_2d invalid inputs
        for bad_v in (
            (Fraction(1, 1), Fraction(2, 1)),
            "abc",
            (1, 2, 3),
            _SubList([Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)]),
        ):
            with self.assertRaises(Err):
                oracle.cross3_q(bad_v, (Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)))
            with self.assertRaises(Err):
                oracle.dot3_q((Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)), bad_v)
        self.assertEqual(oracle.eval_tropical_hinge_relu(Fraction(0, 1), Fraction(0, 1)), Fraction(0, 1))
        self.assertEqual(oracle.eval_shallow_relu_2d(Fraction(0, 1), Fraction(0, 1)), (Fraction(0, 1), Fraction(0, 1)))

        # matrix_rank_q validation & zero-column handling
        self.assertEqual(oracle.matrix_rank_q([[0, 0], [0, 0]]), 0)
        self.assertEqual(oracle.matrix_rank_q([[Fraction(1, 2), Fraction(1, 1)], [Fraction(1, 1), Fraction(2, 1)]]), 1)
        for bad_m in (
            [],
            "not_mat",
            _SubList([[1, 0], [0, 1]]),
            [[]],
            [123],
            ["row"],
            [_SubList([1, 0]), [0, 1]],
            [[1, 2], [3]],
            [[1, 0], _SubList([0, 1])],
            [[1, "x"]],
        ):
            with self.assertRaises(Err):
                oracle.matrix_rank_q(bad_m)

        # gdn2_rank1_state_step validation & boundaries (alpha == 1 passes, alpha > 1 fails)
        s_id = [[Fraction(1, 1), Fraction(0, 1)], [Fraction(0, 1), Fraction(1, 1)]]
        s_out, d_out = oracle.gdn2_rank1_state_step(
            s_id, Fraction(1, 1), Fraction(1, 1), (Fraction(1, 1), Fraction(0, 1)), (Fraction(2, 1), Fraction(0, 1))
        )
        self.assertEqual(s_out[0][0], Fraction(2, 1))
        self.assertEqual(d_out[0][0], Fraction(1, 1))
        for bad_args in (
            ("not_mat", Fraction(1, 2), Fraction(1, 1), (Fraction(1, 1), Fraction(0, 1)), (Fraction(1, 1), Fraction(0, 1))),
            (_SubList(s_id), Fraction(1, 2), Fraction(1, 1), (Fraction(1, 1), Fraction(0, 1)), (Fraction(1, 1), Fraction(0, 1))),
            ([s_id[0], s_id[1], s_id[0]], Fraction(1, 2), Fraction(1, 1), (Fraction(1, 1), Fraction(0, 1)), (Fraction(1, 1), Fraction(0, 1))),
            ([[Fraction(1, 1)], [Fraction(0, 1)]], Fraction(1, 2), Fraction(1, 1), (Fraction(1, 1), Fraction(0, 1)), (Fraction(1, 1), Fraction(0, 1))),
            ([_SubList(s_id[0]), s_id[1]], Fraction(1, 2), Fraction(1, 1), (Fraction(1, 1), Fraction(0, 1)), (Fraction(1, 1), Fraction(0, 1))),
            (s_id, Fraction(3, 2), Fraction(1, 1), (Fraction(1, 1), Fraction(0, 1)), (Fraction(1, 1), Fraction(0, 1))),
            (s_id, Fraction(1, 2), Fraction(1, 1), (Fraction(1, 1),), (Fraction(1, 1), Fraction(0, 1))),
            (s_id, Fraction(1, 2), Fraction(1, 1), _SubList([Fraction(1, 1), Fraction(0, 1)]), (Fraction(1, 1), Fraction(0, 1))),
            (s_id, Fraction(1, 2), Fraction(1, 1), (Fraction(1, 1), Fraction(0, 1)), (Fraction(1, 1),)),
            (s_id, Fraction(1, 2), Fraction(1, 1), (Fraction(1, 1), Fraction(0, 1)), _SubList([Fraction(1, 1), Fraction(0, 1)])),
        ):
            with self.assertRaises(Err):
                oracle.gdn2_rank1_state_step(*bad_args)

        # discrete_outward_div_s2 strict input validation (no TypeError/IndexError, no bool/float/subclass acceptance)
        d0_ok, _ = oracle._build_s2_cube_operators()
        flux_ok = [0] * 12
        half_flt = int(1) / int(2)
        for bad_d0, bad_flux, exp_code in (
            ("bad", flux_ok, "INVALID_D0_MATRIX"),
            (_SubList(d0_ok), flux_ok, "INVALID_D0_MATRIX"),
            (tuple(d0_ok), flux_ok, "INVALID_D0_MATRIX"),
            (d0_ok[:11], flux_ok, "INVALID_D0_MATRIX"),
            (["bad"] + d0_ok[1:], flux_ok, "INVALID_D0_MATRIX"),
            ([_SubList(d0_ok[0])] + d0_ok[1:], flux_ok, "INVALID_D0_MATRIX"),
            ([d0_ok[0][:7]] + d0_ok[1:], flux_ok, "INVALID_D0_MATRIX"),
            ([[True] + [0] * 7] + d0_ok[1:], flux_ok, "INVALID_INT"),
            ([[half_flt] + [0] * 7] + d0_ok[1:], flux_ok, "INVALID_INT"),
            ([["0"] + [0] * 7] + d0_ok[1:], flux_ok, "INVALID_INT"),
            (d0_ok, "bad", "INVALID_FLUX_VEC"),
            (d0_ok, _SubList(flux_ok), "INVALID_FLUX_VEC"),
            (d0_ok, tuple(flux_ok), "INVALID_FLUX_VEC"),
            (d0_ok, [0] * 11, "INVALID_FLUX_VEC"),
            (d0_ok, [True] + [0] * 11, "INVALID_INT"),
            (d0_ok, [half_flt] + [0] * 11, "INVALID_INT"),
            (d0_ok, ["0"] + [0] * 11, "INVALID_INT"),
        ):
            with self.assertRaises(Err) as cm_div:
                oracle.discrete_outward_div_s2(bad_d0, bad_flux)
            self.assertEqual(cm_div.exception.code, exp_code)

    # -----------------------------------------------------------------------
    # 3. Certificate Validation & 30+ Re-Signed Tamper Kills Under full_replay=False
    # -----------------------------------------------------------------------

    def test_07_certificate_envelope_and_resigned_secondary_audit_kills(self) -> None:
        res_full = audit.verify_certificate_dict(copy.deepcopy(self.cert), full_replay=True)
        self.assertIs(res_full["valid"], True)
        self.assertIs(res_full["full_replay_matched"], True)
        self.assertIs(res_full["secondary_audit"]["secondary_audit_passed"], True)

        res_sec = audit.verify_certificate_dict(copy.deepcopy(self.cert), full_replay=False)
        self.assertIs(res_sec["valid"], True)
        self.assertIs(res_sec["full_replay_matched"], False)

        # Top-level envelope rejections
        with self.assertRaises(Err) as cm:
            oracle.validate_certificate_payload([])
        self.assertEqual(cm.exception.code, "INVALID_CERT_TYPE")

        c = copy.deepcopy(self.cert); c["extra"] = 1
        with self.assertRaises(Err) as cm:
            oracle.validate_certificate_payload(c)
        self.assertEqual(cm.exception.code, "INVALID_CERT_KEYS")

        c = copy.deepcopy(self.cert); c["schema"] = "wrong"
        with self.assertRaises(Err) as cm:
            oracle.validate_certificate_payload(c)
        self.assertEqual(cm.exception.code, "SCHEMA_MISMATCH")

        c = copy.deepcopy(self.cert); c["track_id"] = "wrong"
        with self.assertRaises(Err) as cm:
            oracle.validate_certificate_payload(c)
        self.assertEqual(cm.exception.code, "TRACK_ID_MISMATCH")

        c = copy.deepcopy(self.cert); c["payload"] = []
        with self.assertRaises(Err) as cm:
            oracle.validate_certificate_payload(c)
        self.assertEqual(cm.exception.code, "INVALID_PAYLOAD_KEYS")

        c = copy.deepcopy(self.cert); c["payload"] = {"only": 1}
        with self.assertRaises(Err) as cm:
            oracle.validate_certificate_payload(c)
        self.assertEqual(cm.exception.code, "INVALID_PAYLOAD_KEYS")

        c = copy.deepcopy(self.cert); c["payload_sha256"] = "0" * 64
        with self.assertRaises(Err) as cm:
            oracle.validate_certificate_payload(c)
        self.assertEqual(cm.exception.code, "PAYLOAD_SHA256_MISMATCH")

        c = copy.deepcopy(self.cert); c["certificate_sha256"] = "0" * 64
        with self.assertRaises(Err) as cm:
            oracle.validate_certificate_payload(c)
        self.assertEqual(cm.exception.code, "CERTIFICATE_SHA256_MISMATCH")

        # secondary_audit_payload & internal vector/list helper type/length guards
        with self.assertRaises(Err) as cm:
            audit.secondary_audit_payload([])
        self.assertEqual(cm.exception.code, "AUDIT_INVALID_PAYLOAD")
        with self.assertRaises(Err) as cm:
            audit.secondary_audit_payload({"only": 1})
        self.assertEqual(cm.exception.code, "AUDIT_INVALID_PAYLOAD")
        with self.assertRaises(Err) as cm:
            audit._require_list_len({"k": (1, 2)}, "k", 2, "BAD_LIST_TYPE")
        self.assertEqual(cm.exception.code, "BAD_LIST_TYPE")
        with self.assertRaises(Err) as cm:
            audit._parse_q_vec(["0", "0"], 3, "v", "BAD_Q_LEN")
        self.assertEqual(cm.exception.code, "BAD_Q_LEN")
        with self.assertRaises(Err) as cm:
            audit._parse_q_vec(("0", "0", "1"), 3, "v", "BAD_Q_TYPE")
        self.assertEqual(cm.exception.code, "BAD_Q_TYPE")
        with self.assertRaises(Err) as cm:
            audit._parse_int_vec([0, 0], 3, "v", "BAD_I_LEN")
        self.assertEqual(cm.exception.code, "BAD_I_LEN")
        with self.assertRaises(Err) as cm:
            audit._parse_int_vec((0, 0, 1), 3, "v", "BAD_I_TYPE")
        self.assertEqual(cm.exception.code, "BAD_I_TYPE")

        # Bijective bool/non-bool leaf separation directly in validate_certificate_payload(full_replay=False)
        for mut_bool, exp_bcode in (
            (lambda p: p["pillar1_bingham_relu_poiseuille"]["poiseuille_plug_shear_channel"]["channel_probes"][0].__setitem__("in_plug", 1), "NON_BOOL_IN_BOOL_FIELD"),
            (lambda p: p["pillar4_s2_hodge_obstructions"]["discrete_s2_cube_hodge_complex"].__setitem__("vertices", True), "BOOL_IN_NON_BOOL_FIELD"),
            (lambda p: p["pillar4_s2_hodge_obstructions"]["discrete_s2_cube_hodge_complex"]["betti_numbers"].__setitem__(0, True), "BOOL_IN_LIST"),
        ):
            bc = copy.deepcopy(self.cert)
            mut_bool(bc["payload"])
            _resign_cert(bc)
            with self.assertRaises(Err) as cm_b:
                oracle.validate_certificate_payload(bc, full_replay=False)
            self.assertEqual(cm_b.exception.code, exp_bcode)

        # Re-signed payload tampers: EVERY SINGLE ONE must fail BOTH full_replay=True AND full_replay=False!
        def _tamper(mutator, expected_code: str) -> None:
            tc = copy.deepcopy(self.cert)
            mutator(tc["payload"])
            _resign_cert(tc)
            with self.assertRaises(Err) as cm_t:
                audit.verify_certificate_dict(tc, full_replay=True)
            self.assertEqual(cm_t.exception.code, "FULL_REPLAY_MISMATCH")
            with self.assertRaises(Err) as cm_f:
                audit.verify_certificate_dict(tc, full_replay=False)
            self.assertEqual(cm_f.exception.code, expected_code)

        # Scope & top-level pillar keyset tampers
        _tamper(lambda p: p.__setitem__("novelty_tier", "N2"), "AUDIT_SCOPE_META")
        _tamper(lambda p: p.__setitem__("measured_live_mantle_convection_gcm", True), "AUDIT_MEASURED_FLAG")
        _tamper(lambda p: p.__setitem__("zero_trust_path_floats", False), "AUDIT_ZERO_FLAG")
        _tamper(lambda p: p.__setitem__("pillar1_bingham_relu_poiseuille", []), "AUDIT_P1")
        _tamper(lambda p: p.__setitem__("pillar1_bingham_relu_poiseuille", {"x": 1}), "AUDIT_P1")

        # Pillar 1 tampers
        _tamper(lambda p: p["pillar1_bingham_relu_poiseuille"]["variational_proximal_identity"].__setitem__("kkt_subdifferential_all_exact", False), "AUDIT_P1_VP_FLAG")
        _tamper(lambda p: p["pillar1_bingham_relu_poiseuille"]["variational_proximal_identity"].__setitem__("plug_points", 16), "AUDIT_P1_VP_VAL")
        _tamper(lambda p: p["pillar1_bingham_relu_poiseuille"]["variational_proximal_identity"].__setitem__("sample_witnesses", []), "AUDIT_P1_WIT")
        _tamper(lambda p: p["pillar1_bingham_relu_poiseuille"]["variational_proximal_identity"].__setitem__("sample_witnesses", "bad"), "AUDIT_P1_WIT")
        _tamper(lambda p: p["pillar1_bingham_relu_poiseuille"]["variational_proximal_identity"]["sample_witnesses"].__setitem__(0, []), "AUDIT_P1_WIT")
        _tamper(lambda p: p["pillar1_bingham_relu_poiseuille"]["variational_proximal_identity"]["sample_witnesses"].__setitem__(0, {"x": 1}), "AUDIT_P1_WIT")
        _tamper(lambda p: p["pillar1_bingham_relu_poiseuille"]["variational_proximal_identity"]["sample_witnesses"][0].__setitem__("e_star", "0"), "AUDIT_P1_WIT_VAL")
        _tamper(lambda p: p["pillar1_bingham_relu_poiseuille"]["poiseuille_plug_shear_channel"].__setitem__("dissipation_balance_exact", False), "AUDIT_P1_CH_FLAG")
        _tamper(lambda p: p["pillar1_bingham_relu_poiseuille"]["poiseuille_plug_shear_channel"].__setitem__("q_half", "3"), "AUDIT_P1_CH_VAL")
        # Zero-denominator cross-multiplication regressions (never raise raw ZeroDivisionError on either surface!)
        for zero_field in ("g_grad", "h_half", "eta0"):
            _tamper(
                lambda p, zf=zero_field: p["pillar1_bingham_relu_poiseuille"]["poiseuille_plug_shear_channel"].__setitem__(zf, "0"),
                "AUDIT_P1_CH_VAL",
            )
            pm_z = copy.deepcopy(self.payload)
            pm_z["pillar1_bingham_relu_poiseuille"]["poiseuille_plug_shear_channel"][zero_field] = "0"
            with self.assertRaises(Err) as cm_zsec:
                audit.secondary_audit_payload(pm_z)
            self.assertEqual(cm_zsec.exception.code, "AUDIT_P1_CH_VAL")
        for zero_vp in ("eta0", "tau_y"):
            _tamper(
                lambda p, zv=zero_vp: p["pillar1_bingham_relu_poiseuille"]["variational_proximal_identity"].__setitem__(zv, "0"),
                "AUDIT_P1_VP_VAL",
            )
            pm_zv = copy.deepcopy(self.payload)
            pm_zv["pillar1_bingham_relu_poiseuille"]["variational_proximal_identity"][zero_vp] = "0"
            with self.assertRaises(Err) as cm_zvsec:
                audit.secondary_audit_payload(pm_zv)
            self.assertEqual(cm_zvsec.exception.code, "AUDIT_P1_VP_VAL")
        for zero_pd in ("g_grad", "h_half", "eta0"):
            _tamper(
                lambda p, zp=zero_pd: p["pillar2_yield_phase_and_2d_relu"]["yield_phase_diagram"].__setitem__(zp, "0"),
                "AUDIT_P2_PD_VAL",
            )
            pm_zp = copy.deepcopy(self.payload)
            pm_zp["pillar2_yield_phase_and_2d_relu"]["yield_phase_diagram"][zero_pd] = "0"
            with self.assertRaises(Err) as cm_zpsec:
                audit.secondary_audit_payload(pm_zp)
            self.assertEqual(cm_zpsec.exception.code, "AUDIT_P2_PD_VAL")
        _tamper(lambda p: p["pillar1_bingham_relu_poiseuille"]["poiseuille_plug_shear_channel"]["channel_probes"].__setitem__(0, []), "AUDIT_P1_PROBE")
        _tamper(lambda p: p["pillar1_bingham_relu_poiseuille"]["poiseuille_plug_shear_channel"]["channel_probes"].__setitem__(0, {"x": 1}), "AUDIT_P1_PROBE")
        _tamper(lambda p: p["pillar1_bingham_relu_poiseuille"]["poiseuille_plug_shear_channel"]["channel_probes"][4].__setitem__("u", "1"), "AUDIT_P1_PROBE_VAL")

        # Pillar 2 tampers
        _tamper(lambda p: p["pillar2_yield_phase_and_2d_relu"]["yield_phase_diagram"].__setitem__("stagnant_lid_exact_zero_flux", False), "AUDIT_P2_PD_FLAG")
        _tamper(lambda p: p["pillar2_yield_phase_and_2d_relu"]["yield_phase_diagram"].__setitem__("mobile_lid_count", 3), "AUDIT_P2_PD_VAL")
        _tamper(lambda p: p["pillar2_yield_phase_and_2d_relu"]["yield_phase_diagram"]["sweep"].__setitem__(0, []), "AUDIT_P2_SWEEP")
        _tamper(lambda p: p["pillar2_yield_phase_and_2d_relu"]["yield_phase_diagram"]["sweep"].__setitem__(0, {"x": 1}), "AUDIT_P2_SWEEP")
        _tamper(lambda p: p["pillar2_yield_phase_and_2d_relu"]["yield_phase_diagram"]["sweep"][3].__setitem__("q_half", "4"), "AUDIT_P2_SWEEP_VAL")
        _tamper(lambda p: p["pillar2_yield_phase_and_2d_relu"]["shallow_2d_relu_regions"].__setitem__("all_walls_exact_rank1_jump", False), "AUDIT_P2_R2_FLAG")
        _tamper(lambda p: p["pillar2_yield_phase_and_2d_relu"]["shallow_2d_relu_regions"].__setitem__("codim1_wall_count", 8), "AUDIT_P2_R2_VAL")
        _tamper(lambda p: p["pillar2_yield_phase_and_2d_relu"]["shallow_2d_relu_regions"].__setitem__("impossible_pattern", [0, 0]), "AUDIT_P2_R2_VAL")
        _tamper(lambda p: p["pillar2_yield_phase_and_2d_relu"]["shallow_2d_relu_regions"].__setitem__("impossible_pattern", "bad"), "AUDIT_P2_R2_VAL")
        _tamper(lambda p: p["pillar2_yield_phase_and_2d_relu"]["shallow_2d_relu_regions"]["regions"].__setitem__(0, []), "AUDIT_P2_REGS")
        _tamper(lambda p: p["pillar2_yield_phase_and_2d_relu"]["shallow_2d_relu_regions"]["regions"].__setitem__(0, {"x": 1}), "AUDIT_P2_REGS")
        _tamper(lambda p: p["pillar2_yield_phase_and_2d_relu"]["shallow_2d_relu_regions"]["regions"][5].__setitem__("det_j", 12), "AUDIT_P2_REG_VAL")

        # Pillar 3 tampers
        _tamper(lambda p: p["pillar3_triple_junction_tropical_rtf"]["rtf_triple_junction_cocycle"].__setitem__("omega_cocycle_zero", False), "AUDIT_P3_RTF_FLAG")
        _tamper(lambda p: p["pillar3_triple_junction_tropical_rtf"]["rtf_triple_junction_cocycle"].__setitem__("point_p", ["0", "0"]), "AUDIT_P3_RTF_VAL")
        _tamper(lambda p: p["pillar3_triple_junction_tropical_rtf"]["rtf_triple_junction_cocycle"].__setitem__("point_p", "bad"), "AUDIT_P3_RTF_VAL")
        _tamper(lambda p: p["pillar3_triple_junction_tropical_rtf"]["rtf_triple_junction_cocycle"].__setitem__("omega_a", ["1", "0", "0"]), "AUDIT_P3_RTF_VAL")
        _tamper(lambda p: p["pillar3_triple_junction_tropical_rtf"]["rtf_triple_junction_cocycle"]["walls"].__setitem__(0, []), "AUDIT_P3_WALLS")
        _tamper(lambda p: p["pillar3_triple_junction_tropical_rtf"]["rtf_triple_junction_cocycle"]["walls"].__setitem__(0, {"x": 1}), "AUDIT_P3_WALLS")
        _tamper(lambda p: p["pillar3_triple_junction_tropical_rtf"]["rtf_triple_junction_cocycle"]["walls"][1].__setitem__("normal_opening", "-1"), "AUDIT_P3_WALL_VAL")
        _tamper(lambda p: p["pillar3_triple_junction_tropical_rtf"]["tropical_3region_relu_hinge"].__setitem__("weighted_tropical_balancing_zero", False), "AUDIT_P3_TROP_FLAG")
        _tamper(lambda p: p["pillar3_triple_junction_tropical_rtf"]["tropical_3region_relu_hinge"]["tropical_weights"].__setitem__("AB", 1), "AUDIT_P3_TROP_VAL")
        _tamper(lambda p: p["pillar3_triple_junction_tropical_rtf"]["relu_2d_rtf_jacobian_contrast"].__setitem__("dead_subduction_collision_exact", False), "AUDIT_P3_JC_FLAG")
        _tamper(lambda p: p["pillar3_triple_junction_tropical_rtf"]["relu_2d_rtf_jacobian_contrast"]["cases"].__setitem__(0, []), "AUDIT_P3_JCASES")
        _tamper(lambda p: p["pillar3_triple_junction_tropical_rtf"]["relu_2d_rtf_jacobian_contrast"]["cases"].__setitem__(0, {"x": 1}), "AUDIT_P3_JCASES")
        _tamper(lambda p: p["pillar3_triple_junction_tropical_rtf"]["relu_2d_rtf_jacobian_contrast"]["cases"][2].__setitem__("det_j_plus", "1"), "AUDIT_P3_JC_VAL")

        # Pillar 4 tampers
        _tamper(lambda p: p["pillar4_s2_hodge_obstructions"]["discrete_s2_cube_hodge_complex"].__setitem__("d1_d0_identically_zero", False), "AUDIT_P4_CUBE_FLAG")
        _tamper(lambda p: p["pillar4_s2_hodge_obstructions"]["discrete_s2_cube_hodge_complex"].__setitem__("rank_d0", 6), "AUDIT_P4_CUBE_VAL")
        _tamper(lambda p: p["pillar4_s2_hodge_obstructions"]["obstruction_a_toroidal_curl_zero"].__setitem__("hodge_pythagorean_exact", False), "AUDIT_P4_OA_FLAG")
        _tamper(lambda p: p["pillar4_s2_hodge_obstructions"]["obstruction_a_toroidal_curl_zero"].__setitem__("equipartition_ratio", "2"), "AUDIT_P4_OA_VAL")
        _tamper(lambda p: p["pillar4_s2_hodge_obstructions"]["obstruction_b_gauss_stokes_vs_relu"].__setitem__("outward_div_edge_sign_exact", False), "AUDIT_P4_OB_FLAG")
        _tamper(lambda p: p["pillar4_s2_hodge_obstructions"]["obstruction_b_gauss_stokes_vs_relu"].__setitem__("s2_gauss_stokes_universal_exact", False), "AUDIT_P4_OB_FLAG")
        _tamper(lambda p: p["pillar4_s2_hodge_obstructions"]["obstruction_b_gauss_stokes_vs_relu"].__setitem__("asym_flux_u", [3, -1, 2, 0, 1, -2, 4, 0, -3, 2, 1, -1]), "AUDIT_P4_OB_VAL")
        _tamper(lambda p: p["pillar4_s2_hodge_obstructions"]["obstruction_b_gauss_stokes_vs_relu"].__setitem__("asym_outward_div", [1, -3, -1, 2, 9, -4, -5, 1]), "AUDIT_P4_OB_VAL")
        _tamper(lambda p: p["pillar4_s2_hodge_obstructions"]["obstruction_b_gauss_stokes_vs_relu"].__setitem__("unconstrained_relu_global_div", 0), "AUDIT_P4_OB_VAL")
        _tamper(lambda p: p["pillar4_s2_hodge_obstructions"]["obstruction_c_static_feedforward_vs_gdn2_advection"].__setitem__("gdn2_key_overwrite_exact", False), "AUDIT_P4_OC_FLAG")
        _tamper(lambda p: p["pillar4_s2_hodge_obstructions"]["obstruction_c_static_feedforward_vs_gdn2_advection"].__setitem__("gdn2_wall_displacement", "0"), "AUDIT_P4_OC_VAL")

    # -----------------------------------------------------------------------
    # 4. Strict File I/O, Symlinks, Hardlinks, Streaming & Concurrency
    # -----------------------------------------------------------------------

    def test_08_zone_b_io_symlinks_hardlinks_streaming_and_16t(self) -> None:
        with tempfile.TemporaryDirectory(prefix="s43_zb_") as td:
            tdp = Path(td)
            cert_file = tdp / "cert.json"

            w_res = audit.write_certificate_file(cert_file)
            self.assertIs(w_res["written"], True)
            self.assertEqual(stat.S_IMODE(cert_file.stat().st_mode), 0o600)
            c_res = audit.check_certificate_file(cert_file)
            self.assertIs(c_res["valid"], True)
            # Overwrite existing single-link file (st_nlink == 1) succeeds
            audit.write_certificate_file(cert_file)

            # CRLF, missing trailing LF, bad UTF-8, non-canonical formatting
            raw_ok = cert_file.read_bytes()
            for fname, bad_b, code in (
                ("crlf.json", raw_ok.replace(b"\n", b"\r\n"), "CRLF_FORBIDDEN"),
                ("nolf.json", raw_ok[:-1], "MISSING_TRAILING_LF"),
                ("badutf8.json", b"\xff\xfe\n", "INVALID_UTF8"),
                ("noncanon.json", b" " + raw_ok, "NON_CANONICAL_BYTES"),
            ):
                p = tdp / fname
                p.write_bytes(bad_b)
                with self.assertRaises(Err) as cm:
                    audit.check_certificate_file(p)
                self.assertEqual(cm.exception.code, code)

            # Path type, NUL, lone surrogate, root directory, non-bytes write
            for bad_p, code in (
                (_SubPath(cert_file), "INVALID_PATH_TYPE"),
                (str(cert_file), "INVALID_PATH_TYPE"),
                (Path(f"{td}/a\x00b.json"), "INVALID_PATH"),
                (Path(f"{td}/a\ud800b.json"), "INVALID_UTF8_STR"),
            ):
                with self.assertRaises(Err) as cm:
                    audit.require_safe_path(bad_p)
                self.assertEqual(cm.exception.code, code)
            self.assertEqual(audit.require_safe_path(Path("/")), Path("/"))
            self.assertEqual(audit.require_safe_path(tdp / "nonexistent.json"), tdp / "nonexistent.json")
            with self.assertRaises(Err) as cm:
                audit.read_regular_bytes_capped(Path("/"))
            self.assertEqual(cm.exception.code, "NON_REGULAR_FILE")
            with self.assertRaises(Err) as cm:
                audit.write_regular_file_bytes(Path("/"), b"x")
            self.assertEqual(cm.exception.code, "NON_REGULAR_FILE")
            with self.assertRaises(Err) as cm:
                audit.write_regular_file_bytes(tdp / "nb.json", "not_bytes")  # type: ignore[arg-type]
            self.assertEqual(cm.exception.code, "INVALID_WRITE_DATA")

            # Missing dir, missing file, directory target, FIFO target
            with self.assertRaises(Err) as cm:
                audit.read_regular_bytes_capped(tdp / "no_dir" / "x.json")
            self.assertEqual(cm.exception.code, "PATH_NOT_FOUND")
            with self.assertRaises(Err) as cm:
                audit.read_regular_bytes_capped(tdp / "missing.json")
            self.assertEqual(cm.exception.code, "FILE_READ_ERROR")
            sub_dir = tdp / "adir"
            sub_dir.mkdir()
            with self.assertRaises(Err) as cm:
                audit.read_regular_bytes_capped(sub_dir)
            self.assertEqual(cm.exception.code, "NON_REGULAR_FILE")
            with self.assertRaises(Err) as cm:
                audit.write_regular_file_bytes(sub_dir, b"x")
            self.assertEqual(cm.exception.code, "NON_REGULAR_FILE")
            if hasattr(os, "mkfifo"):
                fifo = tdp / "pipe.json"
                os.mkfifo(fifo)
                with self.assertRaises(Err) as cm:
                    audit.read_regular_bytes_capped(fifo)
                self.assertEqual(cm.exception.code, "NON_REGULAR_FILE")
                with self.assertRaises(Err) as cm:
                    audit.write_regular_file_bytes(fifo, b"x")
                self.assertEqual(cm.exception.code, "NON_REGULAR_FILE")

            # Symlinks: leaf, parent, deep, dotdot, symlinked PWD, stale missing PWD, relative PWD
            sym_leaf = tdp / "sym_leaf.json"
            os.symlink(cert_file, sym_leaf)
            for fn in (
                lambda: audit.require_safe_path(sym_leaf),
                lambda: audit.read_regular_bytes_capped(sym_leaf),
                lambda: audit.write_regular_file_bytes(sym_leaf, b"x"),
            ):
                with self.assertRaises(Err) as cm:
                    fn()
                self.assertEqual(cm.exception.code, "SYMLINK_FORBIDDEN")

            real_sub = tdp / "real_sub" / "deep"
            real_sub.mkdir(parents=True)
            (real_sub / "ok.json").write_bytes(raw_ok)
            sym_parent = tdp / "sym_parent"
            os.symlink(tdp / "real_sub", sym_parent)
            for p_bad in (
                sym_parent / "deep" / "ok.json",
                sym_parent / ".." / "real_sub" / "deep" / "ok.json",
            ):
                with self.assertRaises(Err) as cm:
                    audit.read_regular_bytes_capped(p_bad)
                self.assertEqual(cm.exception.code, "SYMLINK_FORBIDDEN")

            orig_cwd = os.getcwd()
            orig_pwd = os.environ.get("PWD")
            try:
                os.chdir(real_sub)
                os.environ["PWD"] = str(sym_parent / "deep")
                with self.assertRaises(Err) as cm:
                    audit.read_regular_bytes_capped(Path("ok.json"))
                self.assertEqual(cm.exception.code, "SYMLINK_FORBIDDEN")
                os.environ["PWD"] = str(tdp / "stale_missing_dir")
                self.assertEqual(audit.read_regular_bytes_capped(Path("ok.json")), raw_ok)
                os.environ["PWD"] = "relative/pwd"
                self.assertEqual(audit.read_regular_bytes_capped(Path("ok.json")), raw_ok)
                os.environ["PWD"] = str(real_sub)
                self.assertEqual(audit.read_regular_bytes_capped(Path("ok.json")), raw_ok)
                os.environ.pop("PWD", None)
                self.assertEqual(audit.read_regular_bytes_capped(Path("ok.json")), raw_ok)
            finally:
                os.chdir(orig_cwd)
                if orig_pwd is None:
                    os.environ.pop("PWD", None)
                else:
                    os.environ["PWD"] = orig_pwd

            # Hardlink target refusal (st_nlink > 1 -> HARDLINK_FORBIDDEN without clobber)
            hl_alias = tdp / "hl_alias.json"
            os.link(cert_file, hl_alias)
            with self.assertRaises(Err) as cm:
                audit.write_regular_file_bytes(hl_alias, b"tampered\n")
            self.assertEqual(cm.exception.code, "HARDLINK_FORBIDDEN")
            self.assertEqual(cert_file.read_bytes(), raw_ok)
            os.unlink(hl_alias)

            # Streaming > 64 KiB read + exact boundary cap
            stream_p = tdp / "stream140k.bin"
            blob140 = b"x" * 140_000
            stream_p.write_bytes(blob140)
            self.assertEqual(audit.read_regular_bytes_capped(stream_p, max_bytes=140_000), blob140)
            with self.assertRaises(Err) as cm:
                audit.read_regular_bytes_capped(stream_p, max_bytes=139_999)
            self.assertEqual(cm.exception.code, "FILE_TOO_LARGE")
            with self.assertRaises(Err) as cm:
                audit.read_regular_bytes_capped(stream_p, max_bytes=0)
            self.assertEqual(cm.exception.code, "INT_BELOW_MIN")
            with self.assertRaises(Err) as cm:
                audit.read_regular_bytes_capped(stream_p, max_bytes=audit.MAX_ALLOWED_CAP_BYTES + 1)
            self.assertEqual(cm.exception.code, "INT_ABOVE_MAX")

            # Monotonic counter, EEXIST retry + 32-attempt exhaustion, pre-replace temp st_nlink != 1
            tn1 = audit._next_tmp_name("col.json")
            tn2 = audit._next_tmp_name("col.json")
            self.assertNotEqual(tn1, tn2)
            self.assertEqual(
                oracle.parse_exact_int_ascii(tn2.split(".")[-2], "s2"),
                oracle.parse_exact_int_ascii(tn1.split(".")[-2], "s1") + 1,
            )
            col_target = tdp / "col.json"
            (tdp / ".col.json.s43tmp.fixed0").write_bytes(b"occ")
            with mock.patch.object(audit, "_next_tmp_name", side_effect=[".col.json.s43tmp.fixed0", ".col.json.s43tmp.fixed1"]):
                audit.write_regular_file_bytes(col_target, b"ok\n")
            self.assertEqual(col_target.read_bytes(), b"ok\n")

            (tdp / ".col2.json.s43tmp.occ").write_bytes(b"occ")
            with mock.patch.object(audit, "_next_tmp_name", return_value=".col2.json.s43tmp.occ"):
                with self.assertRaises(Err) as cm:
                    audit.write_regular_file_bytes(tdp / "col2.json", b"ok\n")
            self.assertEqual(cm.exception.code, "TEMP_RETRY_EXHAUSTED")

            real_fstat = os.fstat

            def _fake_fstat(fd: int) -> os.stat_result:
                st = real_fstat(fd)
                return os.stat_result((st.st_mode, st.st_ino, st.st_dev, 2, st.st_uid, st.st_gid, st.st_size, st.st_atime, st.st_mtime, st.st_ctime))

            with mock.patch.object(audit.os, "fstat", side_effect=_fake_fstat):
                with self.assertRaises(Err) as cm:
                    audit.write_regular_file_bytes(tdp / "hltmp.json", b"ok\n")
            self.assertEqual(cm.exception.code, "HARDLINK_FORBIDDEN")
            self.assertEqual(list(tdp.glob(".hltmp.json.s43tmp.*")), [])

            # Live 16-thread same-target concurrent write stress
            conc_target = tdp / "conc.json"
            conc_errs: list[str] = []
            conc_lock = threading.Lock()
            conc_ok = 0

            def _cw(tid: int) -> None:
                nonlocal conc_ok
                data_b = f'{{"tid":{tid}}}\n'.encode("ascii")
                try:
                    audit.write_regular_file_bytes(conc_target, data_b)
                    with conc_lock:
                        conc_ok += 1
                except Exception as exc:  # pragma: no cover
                    with conc_lock:
                        conc_errs.append(f"{tid}:{exc}")

            ths = [threading.Thread(target=_cw, args=(i,)) for i in range(16)]
            for th in ths:
                th.start()
            for th in ths:
                th.join()
            self.assertEqual(conc_errs, [])
            self.assertEqual(conc_ok, 16)
            self.assertEqual(list(tdp.glob(".conc.json.s43tmp.*")), [])

            # Unreadable file & directory permissions + /proc/kallsyms streaming refusal
            if os.geteuid() != 0:
                unr = tdp / "unr.json"
                unr.write_bytes(b"{}\n")
                os.chmod(unr, 0o000)
                try:
                    with self.assertRaises(Err):
                        audit.read_regular_bytes_capped(unr)
                finally:
                    os.chmod(unr, 0o600)
                unr_d = tdp / "unr_d"
                unr_d.mkdir()
                os.chmod(unr_d, 0o000)
                try:
                    with self.assertRaises(Err):
                        audit.read_regular_bytes_capped(unr_d / "x.json")
                    with self.assertRaises(Err):
                        audit.write_regular_file_bytes(unr_d / "x.json", b"{}\n")
                finally:
                    os.chmod(unr_d, 0o700)

            kallsyms = Path("/proc/kallsyms")
            if kallsyms.exists():
                with self.assertRaises(Err) as cm:
                    audit.read_regular_bytes_capped(kallsyms)
                self.assertEqual(cm.exception.code, "FILE_TOO_LARGE")

            # Mocked macOS Darwin root-owned system symlink prefix normalization
            root_lnk = os.stat_result((stat.S_IFLNK | 0o777, 1, 1, 1, 0, 0, 11, 0, 0, 0))
            user_lnk = os.stat_result((stat.S_IFLNK | 0o777, 1, 1, 1, 1000, 1000, 11, 0, 0, 0))
            root_dir = os.stat_result((stat.S_IFDIR | 0o755, 1, 1, 2, 0, 0, 0, 0, 0, 0))
            with (
                mock.patch.object(audit.sys, "platform", "linux"),
                mock.patch.object(audit.os, "lstat", return_value=root_lnk),
                mock.patch.object(audit.os, "readlink", return_value="private/tmp"),
            ):
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/tmp/a.json")), Path("/tmp/a.json"))
            with (
                mock.patch.object(audit.sys, "platform", "darwin"),
                mock.patch.object(audit.os, "lstat", return_value=root_lnk),
                mock.patch.object(audit.os, "readlink", side_effect=lambda p: f"private/{p.lstrip('/')}"),
            ):
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("a/var/x")), Path("a/var/x"))
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/")), Path("/"))
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/usr/bin")), Path("/usr/bin"))
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/tmp")), Path("/tmp"))
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/tmp"), allow_exact=True), Path("/private/tmp"))
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/var/folders/x/c.json")), Path("/private/var/folders/x/c.json"))
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/etc/hosts")), Path("/private/etc/hosts"))
                self.assertEqual(audit._validate_path_and_split(Path("/var/x/c.json")), ("/", ["private", "var", "x", "c.json"]))
                seen_pwd: list[tuple[str, list[str]]] = []

                def _fake_open_dir(anchor: str, parts: object) -> int:
                    seen_pwd.append((anchor, list(parts)))  # type: ignore[arg-type]
                    raise Err("PATH_NOT_FOUND", "probe")

                with (
                    mock.patch.dict(os.environ, {"PWD": "/tmp"}),
                    mock.patch.object(audit, "_open_dir_chain", side_effect=_fake_open_dir),
                ):
                    audit._check_pwd_no_symlinks()
                self.assertEqual(seen_pwd, [("/", ["private", "tmp"])])
            with (
                mock.patch.object(audit.sys, "platform", "darwin"),
                mock.patch.object(audit.os, "lstat", return_value=user_lnk),
                mock.patch.object(audit.os, "readlink", return_value="private/tmp"),
            ):
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/tmp/a.json")), Path("/tmp/a.json"))
            with (
                mock.patch.object(audit.sys, "platform", "darwin"),
                mock.patch.object(audit.os, "lstat", return_value=root_dir),
                mock.patch.object(audit.os, "readlink", return_value="private/tmp"),
            ):
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/tmp/a.json")), Path("/tmp/a.json"))
            with (
                mock.patch.object(audit.sys, "platform", "darwin"),
                mock.patch.object(audit.os, "lstat", return_value=root_lnk),
                mock.patch.object(audit.os, "readlink", return_value="other/tmp"),
            ):
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/tmp/a.json")), Path("/tmp/a.json"))
            with (
                mock.patch.object(audit.sys, "platform", "darwin"),
                mock.patch.object(audit.os, "lstat", side_effect=OSError("noent")),
            ):
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/tmp/a.json")), Path("/tmp/a.json"))

    # -----------------------------------------------------------------------
    # 5. Strict CLI Parsing, Abbreviation/Flag Traps, Deleted CWD & Disk Cert
    # -----------------------------------------------------------------------

    def test_09_cli_parsing_flag_traps_deleted_cwd_and_disk_cert(self) -> None:
        with tempfile.TemporaryDirectory(prefix="s43_cli_") as td:
            tdp = Path(td)
            out_path = tdp / "cli_cert.json"

            for argv_ok in (
                [],
                ["--standalone"],
                ["--standalone", "--json"],
                ["--write", str(out_path), "--json"],
                ["--check", str(out_path)],
                ["--check", str(out_path), "--json"],
            ):
                buf_out, buf_err = io.StringIO(), io.StringIO()
                old_out, old_err = sys.stdout, sys.stderr
                try:
                    sys.stdout, sys.stderr = buf_out, buf_err
                    rc = audit.main(argv_ok)
                finally:
                    sys.stdout, sys.stderr = old_out, old_err
                self.assertEqual(rc, 0)
                self.assertEqual(buf_err.getvalue(), "")

            bad_argvs: list[tuple[object, str]] = [
                (["--write", "--json"], "INVALID_PATH_ARG"),
                (["--check", "--json"], "INVALID_PATH_ARG"),
                (["--write", ""], "INVALID_PATH_ARG"),
                (["--write=--json"], "UNKNOWN_FLAG"),
                (["--check=--json"], "UNKNOWN_FLAG"),
                (["--st"], "UNKNOWN_FLAG"),
                (["--wr", str(out_path)], "UNKNOWN_FLAG"),
                (["--ch", str(out_path)], "UNKNOWN_FLAG"),
                (["--js"], "UNKNOWN_FLAG"),
                (["--json", "--json"], "DUPLICATE_FLAG"),
                (["--standalone", "--standalone"], "CONFLICTING_MODE"),
                (["--standalone", "--check", str(out_path)], "CONFLICTING_MODE"),
                (["--write"], "MISSING_PATH_ARG"),
                (["--check"], "MISSING_PATH_ARG"),
                (["--write", "bad\ud800.json"], "INVALID_UTF8_STR"),
                ("not_a_list", "INVALID_ARGV"),
            ]
            for bad, exp_code in bad_argvs:
                buf_out, buf_err = io.StringIO(), io.StringIO()
                old_out, old_err = sys.stdout, sys.stderr
                try:
                    sys.stdout, sys.stderr = buf_out, buf_err
                    rc = audit.main(bad)  # type: ignore[arg-type]
                finally:
                    sys.stdout, sys.stderr = old_out, old_err
                self.assertEqual(rc, 2)
                err_obj = json.loads(buf_err.getvalue())
                self.assertIs(err_obj["valid"], False)
                self.assertEqual(err_obj["error_code"], exp_code)
            self.assertFalse(Path("--json").exists())

            # Deleted-CWD fail-closed check
            del_dir = tdp / "vanishing"
            del_dir.mkdir()
            script = (
                "import os, sys; "
                f"sys.path.insert(0, {str(_THIS_DIR)!r}); "
                "import tectonics_relu_regions_audit as a; "
                f"os.chdir({str(del_dir)!r}); os.rmdir({str(del_dir)!r}); "
                "raise SystemExit(a.main(['--check', 'rel.json']))"
            )
            proc = subprocess.run([sys.executable, "-B", "-c", script], capture_output=True, text=True, timeout=15)
            self.assertEqual(proc.returncode, 2)
            self.assertIn("CWD_UNAVAILABLE", proc.stderr)

        disk_cert = _THIS_DIR / "tectonics_relu_regions_certificate.json"
        if disk_cert.exists():
            res = audit.check_certificate_file(disk_cert)
            self.assertIs(res["valid"], True)
            self.assertEqual(res["payload_sha256"], self.cert["payload_sha256"])
            self.assertEqual(res["certificate_sha256"], self.cert["certificate_sha256"])


if __name__ == "__main__":
    unittest.main()
