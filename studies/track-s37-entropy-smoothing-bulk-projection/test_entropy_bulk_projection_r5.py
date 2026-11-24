#!/usr/bin/env python3
"""Entropy Smoothing & Off-Brane Continuum Projection Test Suite: 4 Mathematical/Physical
Pillars, Exported-Helper Soundness, Mutation/BoolOp Killers & Fail-Closed I/O Security.

Pure Python 3 standard library: zero AST floats, zero bare asserts, zero mathematical RNG.
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
import threading
import unittest
from unittest import mock

_THIS_DIR = Path(__file__).resolve().parent
if str(_THIS_DIR) not in sys.path:
    sys.path.insert(0, str(_THIS_DIR))

import entropy_bulk_projection_oracle as oracle
import entropy_bulk_projection_audit as audit

Err = oracle.EntropyBulkProjectionError


class _SubInt(int):
    pass


class _SubStr(str):
    pass


class _SubFrac(Fraction):
    pass


class _SubPath(type(Path("."))):
    pass


class TestTrackS37EntropyBulkProjectionR5(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.cert = oracle.build_standalone_certificate()
        cls.payload = cls.cert["payload"]

    # -----------------------------------------------------------------------
    # 1. Four Mathematical & Physical Pillars
    # -----------------------------------------------------------------------

    def test_01_pillar1_entropy_smoothing_catmap_and_maxent(self) -> None:
        self.assertEqual(self.payload["novelty_tier"], "N1")
        self.assertEqual(self.payload["oracle_class"], "exact")
        self.assertIs(self.payload["measured_live_cosmological_nbody_fits"], False)
        self.assertIs(self.payload["measured_eht_shadow_tidal_charge_detection"], False)
        self.assertIs(self.payload["measured_laboratory_worthington_piv_velocimetry"], False)
        self.assertIs(self.payload["zero_trust_path_floats"], True)
        self.assertIs(self.payload["zero_bare_asserts"], True)
        self.assertIs(self.payload["zero_mathematical_rng"], True)

        p1 = self.payload["pillar1_entropy_smoothing_catmap_maxent"]
        q3 = p1["q3_jko_diffusion"]
        self.assertEqual(q3["vertices"], 8)
        self.assertEqual(q3["collision_energy_t0"], "1")
        self.assertEqual(q3["collision_energy_t1"], "1/3")
        self.assertEqual(q3["dirichlet_roughness_t0"], "3")
        self.assertIs(q3["doubly_stochastic"], True)
        self.assertIs(q3["collision_energy_strictly_decreasing"], True)
        self.assertIs(q3["dirichlet_roughness_strictly_decreasing"], True)
        self.assertIs(q3["spectral_gap_contraction_certified"], True)

        c8 = p1["c8_jko_diffusion"]
        self.assertEqual(c8["vertices"], 8)
        self.assertIs(c8["collision_energy_strictly_decreasing"], True)
        self.assertIs(c8["dirichlet_roughness_strictly_decreasing"], True)

        cat = p1["arnold_cat_map_filament_arc"]
        self.assertEqual(cat["torus_n"], 16)
        self.assertEqual(cat["matrix_det"], 1)
        self.assertEqual(cat["matrix_trace"], 3)
        self.assertEqual(cat["hyperbolic_discriminant"], 5)
        self.assertEqual(cat["poincare_recurrence_period"], 12)
        self.assertIs(cat["all_12_steps_micro_reversible"], True)
        self.assertIs(cat["poincare_recurrence_t12_exact"], True)
        self.assertIs(cat["coarse_entropy_strictly_increasing_t0_to_t3"], True)
        self.assertIs(cat["coarse_variance_collapses_to_exact_zero_t3"], True)
        self.assertIs(cat["micro_perimeter_hits_theoretical_max_256_t3"], True)
        self.assertIs(cat["non_monotonic_macro_levels_peak_t2"], True)
        self.assertIs(cat["non_monotonic_macro_edges_peak"], True)
        arc = cat["arc_t0_to_t3"]
        self.assertEqual([a["micro_perimeter"] for a in arc], [32, 74, 166, 256])
        self.assertEqual([a["distinct_macro_levels"] for a in arc], [2, 6, 7, 1])
        self.assertEqual([a["coarse_block_variance"] for a in arc], ["48", "17", "3", "0"])
        self.assertEqual([a["coarse_collision_energy"] for a in arc], ["1/4", "33/256", "19/256", "1/16"])

        me = p1["jaynes_maxent_missing_vectors"]
        self.assertEqual(me["missing_ker_dim"], 6)
        self.assertEqual(me["p_star"], ["5/32", "5/32", "5/32", "5/32", "3/32", "3/32", "3/32", "3/32"])
        self.assertEqual(me["gibbs_stratum_ratio"], "5/3")
        self.assertIs(me["ker_basis_rank_6_certified"], True)
        self.assertIs(me["all_6_missing_vectors_zero_bias"], True)
        self.assertIs(me["pythagorean_optimality_exact"], True)
        self.assertIs(me["shannon_gibbs_exact_coincidence"], True)

    def test_02_pillar2_worthington_unruh_and_gravity_bifurcation(self) -> None:
        p2 = self.payload["pillar2_worthington_unruh_gravity_bifurcation"]
        worth = p2["worthington_incompressible_focusing"]
        self.assertEqual(worth["alpha"], "3/2")
        self.assertEqual(worth["beta_forced_2alpha"], "3")
        self.assertEqual(worth["divergence_residual"], "0")
        self.assertEqual(worth["rayleigh_plesset_self_similar_coeff"], "1/8")
        self.assertIs(worth["incompressibility_exact"], True)
        self.assertIs(worth["control_volume_flux_conserved"], True)
        self.assertIs(worth["euler_bernoulli_stagnation_exact"], True)
        self.assertIs(worth["streamline_k4_focusing_exact"], True)
        self.assertEqual(
            [w["axial_ke_amplification"] for w in worth["streamline_k4_focusing_witnesses"]],
            ["16", "81"],
        )

        unruh = p2["unruh_analogue_sonic_horizon"]
        self.assertEqual(unruh["f_ac_at_horizon"], "0")
        self.assertEqual(unruh["surface_gravity_kappa"], "9/2")
        self.assertEqual(unruh["normalized_killing_kappa"], "1/2")
        self.assertIs(unruh["horizon_sign_separation_exact"], True)
        self.assertIs(unruh["kappa_velocity_gradient_matches"], True)
        self.assertIs(unruh["normalized_killing_matches_inv_rh"], True)

        grav = p2["gravitational_negative_heat_capacity_jeans"]
        self.assertEqual(grav["cv_ideal_gas"], "15")
        self.assertEqual(grav["cv_grav_virial"], "-15")
        self.assertIs(grav["virial_identity_exact"], True)
        self.assertIs(grav["heat_capacity_opposite_sign"], True)
        self.assertIs(grav["jeans_critical_zero_exact"], True)
        self.assertIs(grav["jeans_sign_flip_certified"], True)
        self.assertEqual(
            [pr["omega_sq"] for pr in grav["jeans_dispersion_probes"]],
            ["-32", "-20", "0", "28", "64"],
        )

    def test_03_pillar3_offbrane_plummer_and_schur_dark_source(self) -> None:
        p3 = self.payload["pillar3_offbrane_plummer_schur_dark_source"]
        plum = p3["offbrane_plummer_core_theorem"]
        self.assertIs(plum["all_triplets_exact"], True)
        self.assertIs(plum["central_density_finite_zero_cusp"], True)
        self.assertIs(plum["vc_peak_sign_change_exact"], True)
        self.assertIs(plum["total_mass_conserved_certified"], True)
        self.assertEqual(plum["peak_condition_r_sq_over_y0_sq"], 2)
        self.assertEqual(plum["vc_max_fourth_over_gm_sq_y0_1"], "4/27")
        self.assertEqual(
            [t["m_enc_over_m"] for t in plum["pythagorean_triplets"]],
            ["27/125", "125/2197", "512/4913"],
        )

        self.assertIs(p3["all_schur_dark_projections_certified"], True)
        for sk, exp_n in (("schur_dark_gravity_2x2", 2), ("schur_dark_gravity_4x4", 4), ("schur_dark_gravity_6x6", 6)):
            sd = p3[sk]
            self.assertEqual(sd["n_total"], exp_n)
            self.assertIs(sd["full_pd"], True)
            self.assertIs(sd["schur_so_pd"], True)
            self.assertIs(sd["schur_det_identity_exact"], True)
            self.assertIs(sd["j_dark_all_strictly_positive"], True)
            self.assertIs(sd["phi_o_all_strictly_positive"], True)
            self.assertIs(sd["schur_matches_full_solve_exact"], True)
            self.assertIs(sd["energy_decomposition_exact"], True)
            self.assertIs(sd["dark_shadow_strictly_positive"], True)

    def test_04_pillar4_bounce_dmpr_pell_and_observational_gates(self) -> None:
        p4 = self.payload["pillar4_bounce_dmpr_pell_observational_gates"]
        bnc = p4["shtanov_sahni_timelike_bounce"]
        self.assertEqual(bnc["ss_h2_at_rhoc"], "0")
        self.assertEqual(bnc["ss_dh2_dx_at_rhoc"], "-1")
        self.assertEqual(bnc["ss_bounce_hdot_radiation"], "2")
        self.assertEqual(bnc["ss_bounce_hdot_dust"], "3/2")
        self.assertIs(bnc["ss_regular_bounce_certified"], True)
        self.assertIs(bnc["rs2_no_bounce_singular_certified"], True)

        dmpr = p4["dmpr_pell_tidal_charge_shadows"]
        self.assertIs(dmpr["pell_rational_parametrization_verified"], True)
        self.assertIs(dmpr["shadow_chain_strictly_increasing"], True)
        self.assertIs(dmpr["all_pell_witnesses_valid"], True)
        self.assertIs(dmpr["q_neg1_bracket_certified"], True)
        self.assertEqual(dmpr["witness_q_pos1"]["b_crit_sq_over_m2"], "16")
        self.assertEqual(dmpr["witness_q_zero_schwarzschild"]["b_crit_sq_over_m2"], "27")
        self.assertEqual(dmpr["witness_q_neg_495_289_pell"]["b_crit_sq_over_m2"], "574992/14161")
        self.assertEqual(dmpr["witness_q_neg2"]["b_crit_sq_over_m2"], "128/3")
        self.assertEqual(dmpr["witness_q_neg35_pell"]["b_crit_sq_over_m2"], "2000/9")
        self.assertEqual(dmpr["q_neg1_b_crit_sq_lo"], "141/4")
        self.assertEqual(dmpr["q_neg1_b_crit_sq_hi"], "71/2")

        obs = p4["gw170817_cmb_observational_gates"]
        self.assertEqual(obs["gw170817_d_lo"], "98/25")
        self.assertEqual(obs["gw170817_d_hi"], "409/100")
        self.assertIs(obs["d_4_inside_gw170817"], True)
        self.assertIs(obs["flat_d_5_excluded_by_gw170817"], True)
        self.assertEqual(obs["flat_d_5_exclusion_margin"], "91/100")
        self.assertEqual(obs["cmb_redshift_z"], 1100)
        self.assertEqual(obs["dm_to_baryon_ratio"], "12000/2237")
        self.assertIs(obs["dm_to_baryon_in_5_to_6"], True)
        self.assertIs(obs["post_stellar_only_bh_ruled_out_at_cmb"], True)

    # -----------------------------------------------------------------------
    # 2. Exported Primitives, Parsers, Formatters & Canonical JSON Guards
    # -----------------------------------------------------------------------

    def test_05_primitive_parsers_formatters_and_int_bounds(self) -> None:
        # require_exact_int exact boundaries & bool/float/subclass rejection
        self.assertEqual(oracle.require_exact_int(5, "x", min_val=5, max_val=5), 5)
        for bad in (True, False, int(5) / int(2), "5", None, _SubInt(5)):
            with self.assertRaises(Err):
                oracle.require_exact_int(bad, "x")
        with self.assertRaises(Err):
            oracle.require_exact_int(4, "x", min_val=5)
        with self.assertRaises(Err):
            oracle.require_exact_int(6, "x", max_val=5)

        # require_exact_bool, require_exact_str, require_sha256_hex
        self.assertIs(oracle.require_exact_bool(True, "b"), True)
        with self.assertRaises(Err):
            oracle.require_exact_bool(1, "b")
        self.assertEqual(oracle.require_exact_str("", "s", non_empty=False), "")
        with self.assertRaises(Err):
            oracle.require_exact_str("", "s", non_empty=True)
        with self.assertRaises(Err):
            oracle.require_exact_str(_SubStr("a"), "s")
        with self.assertRaises(Err):
            oracle.require_exact_str("bad\ud800sur", "s")
        self.assertEqual(oracle.require_sha256_hex("a" * 64, "h"), "a" * 64)
        for bad_hex in ("a" * 63, "A" * 64, "g" * 64, "\u00e9" * 64):
            with self.assertRaises(Err):
                oracle.require_sha256_hex(bad_hex, "h")

        # require_exact_fraction
        self.assertEqual(oracle.require_exact_fraction(Fraction(0, 1), "q", non_negative=True), Fraction(0, 1))
        self.assertEqual(oracle.require_exact_fraction(Fraction(1, 2), "q", positive=True), Fraction(1, 2))
        for bad in (1, True, int(1) / int(2), "1/2", None, _SubFrac(1, 2)):
            with self.assertRaises(Err):
                oracle.require_exact_fraction(bad, "q")
        with self.assertRaises(Err):
            oracle.require_exact_fraction(Fraction(0, 1), "q", positive=True)
        with self.assertRaises(Err):
            oracle.require_exact_fraction(Fraction(-1, 3), "q", non_negative=True)

        # parse_exact_int_ascii (no .isdigit(), no -0, no leading zero, bounded digits & bits symmetric!)
        self.assertEqual(oracle.parse_exact_int_ascii("0", "n"), 0)
        self.assertEqual(oracle.parse_exact_int_ascii("-42", "n"), -42)
        max_ok = (1 << oracle.MAX_INT_BITS) - 1
        too_big = 1 << oracle.MAX_INT_BITS
        self.assertEqual(len(str(max_ok)), oracle.MAX_INT_DIGITS)
        self.assertEqual(oracle.parse_exact_int_ascii(str(max_ok), "n"), max_ok)
        self.assertEqual(oracle.parse_exact_int_ascii(str(-max_ok), "n"), -max_ok)
        self.assertEqual(oracle.parse_exact_rational(oracle.format_exact_rational(Fraction(max_ok, 1)), "r"), Fraction(max_ok, 1))
        self.assertEqual(oracle.parse_exact_rational(oracle.format_exact_rational(Fraction(-max_ok, max_ok - 1)), "r"), Fraction(-max_ok, max_ok - 1))
        self.assertEqual(
            oracle.parse_strict_json_text(oracle.canonical_json_bytes({"k": max_ok}).decode("ascii"), require_object=True),
            {"k": max_ok},
        )
        for bad in ("", "-", "-0", "00", "007", "-01", "+5", " 5", "1_0", "\u00b2", "\u0661", str(too_big), "9" * oracle.MAX_INT_DIGITS, "9" * (oracle.MAX_INT_DIGITS + 1)):
            with self.assertRaises(Err):
                oracle.parse_exact_int_ascii(bad, "n")

        # parse_exact_rational & formatters (incl. -0.00/-0 normalization & MAX_INT_BITS boundary)
        self.assertEqual(oracle.parse_exact_rational("7", "r"), Fraction(7, 1))
        self.assertEqual(oracle.parse_exact_rational("-3/4", "r"), Fraction(-3, 4))
        for bad in ("1/2/3", "3/1", "3/0", "3/-2", "2/4", "1/\u0662"):
            with self.assertRaises(Err):
                oracle.parse_exact_rational(bad, "r")
        self.assertEqual(oracle.format_exact_rational(Fraction(5, 1)), "5")
        self.assertEqual(oracle.format_exact_rational(Fraction(-5, 3)), "-5/3")
        self.assertEqual(oracle.format_decimal_trunc(Fraction(-7, 4), 2), "-1.75")
        self.assertEqual(oracle.format_decimal_trunc(Fraction(7, 4), 2), "1.75")
        self.assertEqual(oracle.format_decimal_trunc(Fraction(7, 4), 0), "1")
        self.assertEqual(oracle.format_decimal_trunc(Fraction(-1, 1000), 2), "0.00")
        self.assertEqual(oracle.format_decimal_trunc(Fraction(-1, 1000), 0), "0")
        self.assertEqual(oracle.format_decimal_trunc(Fraction(1, 3), 18), "0.333333333333333333")
        with self.assertRaises(Err):
            oracle.format_decimal_trunc(Fraction(1, 2), 19)

        self.assertEqual(oracle.format_exact_rational(Fraction(max_ok, 1)), str(max_ok))
        self.assertEqual(oracle.format_decimal_trunc(Fraction(max_ok, 1), 0), str(max_ok))
        for bad_q in (Fraction(too_big, 1), Fraction(1, too_big), Fraction(10 ** 4500, 1), Fraction(1, 10 ** 4500)):
            with self.assertRaises(Err) as cm_r:
                oracle.format_exact_rational(bad_q)
            self.assertEqual(cm_r.exception.code, "INT_TOO_LARGE")
            with self.assertRaises(Err) as cm_d:
                oracle.format_decimal_trunc(bad_q, 2)
            self.assertEqual(cm_d.exception.code, "INT_TOO_LARGE")

    def test_06_json_canonicalization_cycles_and_strict_parser(self) -> None:
        raw = oracle.canonical_json_bytes({"b": [1, True, None, "x"], "a": 0})
        self.assertEqual(raw, b'{"a":0,"b":[1,true,null,"x"]}')
        with self.assertRaises(Err):
            oracle.canonical_json_bytes({"f": Fraction(1, 2)})
        with self.assertRaises(Err):
            oracle.canonical_json_bytes({"f": int(3) / int(2)})
        # Cyclic dict rejected cleanly via MAX_JSON_DEPTH (no RecursionError!)
        cyc: dict[str, object] = {}
        cyc["self"] = cyc
        with self.assertRaises(Err) as cm_cyc:
            oracle.canonical_json_bytes(cyc)
        self.assertEqual(cm_cyc.exception.code, "JSON_TOO_DEEP")
        # Bounded int boundary in canonical_json_bytes & parse_strict_json_text
        max_ok = (1 << oracle.MAX_INT_BITS) - 1
        self.assertIn(str(max_ok).encode("ascii"), oracle.canonical_json_bytes({"ok": max_ok}))
        for huge in (1 << oracle.MAX_INT_BITS, -(1 << oracle.MAX_INT_BITS), 10 ** 4300):
            with self.assertRaises(Err) as cm_hi:
                oracle.canonical_json_bytes({"big": huge})
            self.assertEqual(cm_hi.exception.code, "INT_TOO_LARGE")
        with self.assertRaises(Err) as cm_hj:
            oracle.parse_strict_json_text('{"big":' + "9" * 4500 + "}", require_object=True)
        self.assertEqual(cm_hj.exception.code, "INT_TOKEN_TOO_LONG")
        # Depth boundary: 32 nested lists OK, 33 rejected
        nested_ok: object = 0
        for _ in range(oracle.MAX_JSON_DEPTH):
            nested_ok = [nested_ok]
        oracle.canonical_json_bytes(nested_ok)
        with self.assertRaises(Err):
            oracle.canonical_json_bytes([nested_ok])
        # Size boundary: exact MAX_JSON_BYTES OK, MAX_JSON_BYTES+1 rejected
        exact_payload = {"s": "a" * (oracle.MAX_JSON_BYTES - 8)}
        exact_raw = oracle.canonical_json_bytes(exact_payload)
        self.assertEqual(len(exact_raw), oracle.MAX_JSON_BYTES)
        self.assertEqual(oracle.parse_strict_json_text(exact_raw.decode("ascii"), require_object=True), exact_payload)
        with self.assertRaises(Err) as cm_j1:
            oracle.canonical_json_bytes({"s": "a" * oracle.MAX_JSON_BYTES})
        self.assertEqual(cm_j1.exception.code, "JSON_TOO_LARGE")
        with self.assertRaises(Err) as cm_j2:
            oracle.parse_strict_json_text('{"s":"' + "a" * oracle.MAX_JSON_BYTES + '"}')
        self.assertEqual(cm_j2.exception.code, "JSON_TOO_LARGE")
        for bad_json in ('{"a":1.5}', '{"a":NaN}', '{"a":1,"a":2}', "[1,2]", "{bad"):
            with self.assertRaises(Err):
                oracle.parse_strict_json_text(bad_json, require_object=True)
        self.assertEqual(oracle.parse_strict_json_text("[1,2]", require_object=False), [1, 2])

    def test_07_linear_algebra_catmap_and_pell_helper_boundaries(self) -> None:
        # bareiss_det_exact, certify_sylvester_pd_exact, solve_linear_system_exact
        swap_m = [[Fraction(0, 1), Fraction(1, 1)], [Fraction(1, 1), Fraction(0, 1)]]
        self.assertEqual(oracle.bareiss_det_exact(swap_m), Fraction(-1, 1))
        self.assertEqual(oracle.solve_linear_system_exact(swap_m, [Fraction(3, 1), Fraction(5, 1)]), [Fraction(5, 1), Fraction(3, 1)])
        sing_m = [[Fraction(1, 1), Fraction(1, 1)], [Fraction(1, 1), Fraction(1, 1)]]
        self.assertEqual(oracle.bareiss_det_exact(sing_m), Fraction(0, 1))
        self.assertIs(oracle.certify_sylvester_pd_exact(sing_m), False)
        with self.assertRaises(Err) as cm_sing:
            oracle.solve_linear_system_exact(sing_m, [Fraction(1, 1), Fraction(1, 1)])
        self.assertEqual(cm_sing.exception.code, "SINGULAR_MATRIX")
        # Matrix validation boundaries: 16x16 OK, 17x17 rejected, empty, non-seq, non-square, non-symmetric
        id16 = [[Fraction(1, 1) if i == j else Fraction(0, 1) for j in range(16)] for i in range(16)]
        self.assertEqual(oracle.bareiss_det_exact(id16), Fraction(1, 1))
        id17 = [[Fraction(1, 1) if i == j else Fraction(0, 1) for j in range(17)] for i in range(17)]
        for bad_mat, exp_code in (
            ("not_mat", "INVALID_MATRIX"),
            ([], "INVALID_MATRIX"),
            (id17, "INVALID_MATRIX"),
            ([[Fraction(1, 1), Fraction(2, 1)]], "NON_SQUARE_MATRIX"),
            (["a"], "NON_SQUARE_MATRIX"),
        ):
            with self.assertRaises(Err) as cm_m:
                oracle.bareiss_det_exact(bad_mat)
            self.assertEqual(cm_m.exception.code, exp_code)
        with self.assertRaises(Err) as cm_ns:
            oracle.certify_sylvester_pd_exact([[Fraction(1, 1), Fraction(2, 1)], [Fraction(0, 1), Fraction(1, 1)]])
        self.assertEqual(cm_ns.exception.code, "NON_SYMMETRIC_MATRIX")
        with self.assertRaises(Err) as cm_vb1:
            oracle.solve_linear_system_exact(swap_m, "12")
        self.assertEqual(cm_vb1.exception.code, "INVALID_VECTOR")
        with self.assertRaises(Err) as cm_vb2:
            oracle.solve_linear_system_exact(swap_m, [Fraction(1, 1)])
        self.assertEqual(cm_vb2.exception.code, "INVALID_VECTOR")

        # Strict Fraction & dimension validation in dot_exact, mat_vec_exact, quad_form_exact
        self.assertEqual(oracle.dot_exact([Fraction(1, 2), Fraction(3, 1)], [Fraction(4, 1), Fraction(1, 3)]), Fraction(3, 1))
        self.assertEqual(oracle.mat_vec_exact([[Fraction(1, 1), Fraction(2, 1)]], [Fraction(3, 1), Fraction(4, 1)]), [Fraction(11, 1)])
        self.assertEqual(oracle.quad_form_exact([[Fraction(2, 1)]], [Fraction(3, 1)]), Fraction(18, 1))
        f_val = int(3) / int(2)
        for u_bad, v_bad, exp_c in (
            ("ab", [Fraction(1, 1), Fraction(2, 1)], "INVALID_VECTOR"),
            ([Fraction(1, 1), Fraction(2, 1)], "ab", "INVALID_VECTOR"),
            ([Fraction(1, 1), Fraction(2, 1)], [Fraction(3, 1)], "VECTOR_LENGTH_MISMATCH"),
            ([f_val], [f_val], "INVALID_FRACTION"),
            ([True], [1], "INVALID_FRACTION"),
            ([Fraction(1, 1)], [1], "INVALID_FRACTION"),
        ):
            with self.assertRaises(Err) as cm_dot:
                oracle.dot_exact(u_bad, v_bad)
            self.assertEqual(cm_dot.exception.code, exp_c)
        for m_bad, v_bad, exp_c in (
            ("not_m", [Fraction(1, 1)], "INVALID_MATRIX"),
            ([], [Fraction(1, 1)], "INVALID_MATRIX"),
            ([[Fraction(1, 1)]], "not_v", "INVALID_VECTOR"),
            ([[Fraction(1, 1)]], [], "INVALID_VECTOR"),
            (["x"], [Fraction(1, 1)], "MATRIX_VECTOR_MISMATCH"),
            ([[Fraction(1, 1), Fraction(2, 1)]], [Fraction(1, 1)], "MATRIX_VECTOR_MISMATCH"),
            ([[f_val]], [f_val], "INVALID_FRACTION"),
            ([[Fraction(1, 1)]], [True], "INVALID_FRACTION"),
            ([[1]], [Fraction(1, 1)], "INVALID_FRACTION"),
        ):
            with self.assertRaises(Err) as cm_mv:
                oracle.mat_vec_exact(m_bad, v_bad)
            self.assertEqual(cm_mv.exception.code, exp_c)
        for m_bad, v_bad, exp_c in (
            ([[1]], [1], "INVALID_FRACTION"),
            ([[Fraction(1, 1), Fraction(2, 1)]], [Fraction(1, 1), Fraction(2, 1)], "NON_SQUARE_MATRIX"),
            ([[Fraction(1, 1)]], [Fraction(1, 1), Fraction(2, 1)], "INVALID_VECTOR"),
            ([[Fraction(1, 1)]], [True], "INVALID_FRACTION"),
        ):
            with self.assertRaises(Err) as cm_qf:
                oracle.quad_form_exact(m_bad, v_bad)
            self.assertEqual(cm_qf.exception.code, exp_c)

        # arnold_cat_step_mod_n & inverse validation boundaries
        self.assertEqual(oracle.arnold_cat_inverse_step_mod_n(oracle.arnold_cat_step_mod_n([(1, 1)], 2), 2), ((1, 1),))
        self.assertEqual(oracle.arnold_cat_step_mod_n([(0, 0)], 64), ((0, 0),))
        for bad_pts, exp_code in (
            ("bad", "INVALID_POINT_SET"),
            ([], "INVALID_POINT_SET"),
            (["ab"], "INVALID_POINT"),
            ([(0, 1, 2)], "INVALID_POINT"),
        ):
            with self.assertRaises(Err) as cm_p:
                oracle.arnold_cat_step_mod_n(bad_pts, 4)  # type: ignore[arg-type]
            self.assertEqual(cm_p.exception.code, exp_code)
        with self.assertRaises(Err):
            oracle.arnold_cat_step_mod_n([(4, 0)], 4)

        # dmpr_pell_witness rejection on non-Pell pair
        with self.assertRaises(Err) as cm_pell:
            oracle.dmpr_pell_witness(Fraction(1, 1), Fraction(2, 1))
        self.assertEqual(cm_pell.exception.code, "PELL_EQUATION_VIOLATED")

    # -----------------------------------------------------------------------
    # 3. Certificate Validation, Non-Replay Schema & Secondary Audit Killers
    # -----------------------------------------------------------------------

    def test_08_certificate_validation_nonreplay_and_secondary_audit_killers(self) -> None:
        res_ok = audit.verify_certificate_dict(self.cert, full_replay=True)
        self.assertIs(res_ok["valid"], True)
        self.assertIs(res_ok["secondary_audit"]["secondary_audit_passed"], True)
        res_nr = audit.verify_certificate_dict(self.cert, full_replay=False)
        self.assertIs(res_nr["full_replay"], False)

        for bad_flag in ("yes", 1, 0, None):
            with self.assertRaises(Err) as cm_bf:
                oracle.validate_certificate_payload(self.cert, full_replay=bad_flag)  # type: ignore[arg-type]
            self.assertEqual(cm_bf.exception.code, "INVALID_BOOL")

        with self.assertRaises(Err) as cm_c0:
            oracle.validate_certificate_payload("not_dict")
        self.assertEqual(cm_c0.exception.code, "CERT_NOT_OBJECT")
        c_extra = copy.deepcopy(self.cert)
        c_extra["extra"] = 1
        with self.assertRaises(Err) as cm_ck:
            oracle.validate_certificate_payload(c_extra)
        self.assertEqual(cm_ck.exception.code, "INVALID_CERT_KEYS")
        for field, bad_val, exp_code in (
            ("schema", "wrong", "INVALID_SCHEMA"),
            ("track_id", "wrong", "INVALID_TRACK_ID"),
            ("payload", [], "PAYLOAD_NOT_OBJECT"),
            ("payload_sha256", "0" * 64, "PAYLOAD_SHA_MISMATCH"),
            ("certificate_sha256", "0" * 64, "CERT_SHA_MISMATCH"),
        ):
            c_bad = copy.deepcopy(self.cert)
            c_bad[field] = bad_val
            with self.assertRaises(Err) as cm_f:
                oracle.validate_certificate_payload(c_bad, full_replay=False)
            self.assertEqual(cm_f.exception.code, exp_code)

        def _resign(payload_mut: dict[str, object]) -> dict[str, object]:
            p_sha = oracle.hashlib.sha256(oracle.canonical_json_bytes(payload_mut)).hexdigest()
            core = {"schema": oracle.SCHEMA_VERSION, "track_id": oracle.TRACK_ID, "payload_sha256": p_sha, "payload": payload_mut}
            c_sha = oracle.hashlib.sha256(oracle.canonical_json_bytes(core)).hexdigest()
            return {"schema": oracle.SCHEMA_VERSION, "track_id": oracle.TRACK_ID, "payload_sha256": p_sha, "certificate_sha256": c_sha, "payload": payload_mut}

        # Re-signed tampered payload passes non-replay schema if valid types, MUST FAIL full_replay=True!
        p_tamp_replay = copy.deepcopy(self.payload)
        p_tamp_replay["pillar1_entropy_smoothing_catmap_maxent"]["q3_jko_diffusion"]["vertices"] = 9
        with self.assertRaises(Err) as cm_rep:
            oracle.validate_certificate_payload(_resign(p_tamp_replay), full_replay=True)
        self.assertEqual(cm_rep.exception.code, "REPLAY_MISMATCH")

        # Non-replay schema killers (including ZB05 bool-for-int & ZB13 hollow payload & metadata)
        nonreplay_mutators = [
            lambda p: p.clear(),
            lambda p: p.__setitem__("novelty_tier", "N0"),
            lambda p: p.__setitem__("oracle_class", "approx"),
            lambda p: p.__setitem__("measured_live_cosmological_nbody_fits", True),
            lambda p: p.__setitem__("zero_mathematical_rng", False),
            lambda p: p.__setitem__("pillar1_entropy_smoothing_catmap_maxent", []),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["arnold_cat_map_filament_arc"].__setitem__("matrix_det", True),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["arnold_cat_map_filament_arc"].__setitem__("arc_t0_to_t3", None),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["arnold_cat_map_filament_arc"].__setitem__("arc_t0_to_t3", p["pillar1_entropy_smoothing_catmap_maxent"]["arnold_cat_map_filament_arc"]["arc_t0_to_t3"][:3]),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["arnold_cat_map_filament_arc"]["arc_t0_to_t3"].__setitem__(0, []),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["arnold_cat_map_filament_arc"]["arc_t0_to_t3"][0].__setitem__("t", False),
        ]
        for fn in nonreplay_mutators:
            pm = copy.deepcopy(self.payload)
            fn(pm)
            with self.assertRaises(Err):
                oracle.validate_certificate_payload(_resign(pm), full_replay=False)

        # Tuple-vs-list killer on _require_payload_dict_list (kills type(val) is not list drop)
        pm_tup = copy.deepcopy(self.payload)
        pm_tup["pillar1_entropy_smoothing_catmap_maxent"]["arnold_cat_map_filament_arc"]["arc_t0_to_t3"] = tuple(
            pm_tup["pillar1_entropy_smoothing_catmap_maxent"]["arnold_cat_map_filament_arc"]["arc_t0_to_t3"]
        )
        with self.assertRaises(Err):
            oracle._validate_payload_nonreplay_schema(pm_tup)

        # Secondary audit killers (every single numeric, boundary, type & BoolOp branch!)
        with self.assertRaises(Err):
            audit.secondary_audit_payload("not_dict")
        with self.assertRaises(Err):
            audit.secondary_audit_payload({})
        with self.assertRaises(Err) as cm_rlen:
            audit._require_rational_list(["1/2"], "x", 2, "ERR_LEN")
        self.assertEqual(cm_rlen.exception.code, "ERR_LEN")
        with self.assertRaises(Err) as cm_rtype:
            audit._require_rational_list("12", "x", 2, "ERR_LEN")
        self.assertEqual(cm_rtype.exception.code, "ERR_LEN")

        sec_mutators = [
            lambda p: p.__setitem__("extra_top", 1),
            lambda p: p.__setitem__("novelty_tier", "N0"),
            lambda p: p.__setitem__("measured_live_cosmological_nbody_fits", True),
            lambda p: p.__setitem__("zero_trust_path_floats", False),
            lambda p: p.pop("pillar1_entropy_smoothing_catmap_maxent"),
            lambda p: p.__setitem__("pillar1_entropy_smoothing_catmap_maxent", []),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"].__setitem__("extra", 1),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["q3_jko_diffusion"].__setitem__("extra", 1),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["q3_jko_diffusion"].__setitem__("vertices", 7),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["q3_jko_diffusion"].__setitem__("steps", 7),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["q3_jko_diffusion"].__setitem__("doubly_stochastic", False),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["q3_jko_diffusion"].__setitem__("collision_energy_t_end", "1/8"),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["c8_jko_diffusion"].__setitem__("dirichlet_roughness_t0", "3"),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["arnold_cat_map_filament_arc"].__setitem__("matrix_det", 2),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["arnold_cat_map_filament_arc"].__setitem__("poincare_recurrence_period", 11),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["arnold_cat_map_filament_arc"].__setitem__("poincare_recurrence_t12_exact", False),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["arnold_cat_map_filament_arc"].__setitem__("arc_t0_to_t3", None),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["arnold_cat_map_filament_arc"].__setitem__("arc_t0_to_t3", "abcd"),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["arnold_cat_map_filament_arc"].__setitem__("arc_t0_to_t3", p["pillar1_entropy_smoothing_catmap_maxent"]["arnold_cat_map_filament_arc"]["arc_t0_to_t3"][:3]),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["arnold_cat_map_filament_arc"]["arc_t0_to_t3"].__setitem__(0, []),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["arnold_cat_map_filament_arc"]["arc_t0_to_t3"][0].__setitem__("extra", 1),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["arnold_cat_map_filament_arc"]["arc_t0_to_t3"][3].__setitem__("micro_perimeter", 0),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["arnold_cat_map_filament_arc"]["arc_t0_to_t3"][3].__setitem__("coarse_block_variance", "999"),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["jaynes_maxent_missing_vectors"].__setitem__("missing_ker_dim", 5),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["jaynes_maxent_missing_vectors"].__setitem__("all_6_missing_vectors_zero_bias", False),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["jaynes_maxent_missing_vectors"].__setitem__("p_star", []),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["jaynes_maxent_missing_vectors"].__setitem__("p_star", "12345678"),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["jaynes_maxent_missing_vectors"].__setitem__("ker_basis_gram_det", "0"),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["jaynes_maxent_missing_vectors"].__setitem__("p_pert_collision_energy", "0"),
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["worthington_incompressible_focusing"].__setitem__("divergence_residual", "1"),
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["worthington_incompressible_focusing"].__setitem__("incompressibility_exact", False),
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["worthington_incompressible_focusing"].__setitem__("streamline_k4_focusing_witnesses", None),
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["worthington_incompressible_focusing"].__setitem__("streamline_k4_focusing_witnesses", "ab"),
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["worthington_incompressible_focusing"].__setitem__("streamline_k4_focusing_witnesses", p["pillar2_worthington_unruh_gravity_bifurcation"]["worthington_incompressible_focusing"]["streamline_k4_focusing_witnesses"][:1]),
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["worthington_incompressible_focusing"]["streamline_k4_focusing_witnesses"].__setitem__(0, []),
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["worthington_incompressible_focusing"]["streamline_k4_focusing_witnesses"][0].__setitem__("extra", 1),
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["worthington_incompressible_focusing"]["streamline_k4_focusing_witnesses"][0].__setitem__("axial_ke_amplification", "99"),
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["unruh_analogue_sonic_horizon"].__setitem__("surface_gravity_kappa", "1/999"),
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["unruh_analogue_sonic_horizon"].__setitem__("f_ac_at_horizon", "999"),
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["unruh_analogue_sonic_horizon"].__setitem__("normalized_killing_kappa", "-5"),
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["unruh_analogue_sonic_horizon"].__setitem__("horizon_sign_separation_exact", False),
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["gravitational_negative_heat_capacity_jeans"].__setitem__("cv_grav_virial", "0"),
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["gravitational_negative_heat_capacity_jeans"].__setitem__("jeans_sign_flip_certified", False),
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["gravitational_negative_heat_capacity_jeans"].__setitem__("jeans_dispersion_probes", None),
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["gravitational_negative_heat_capacity_jeans"].__setitem__("jeans_dispersion_probes", "abcde"),
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["gravitational_negative_heat_capacity_jeans"].__setitem__("jeans_dispersion_probes", p["pillar2_worthington_unruh_gravity_bifurcation"]["gravitational_negative_heat_capacity_jeans"]["jeans_dispersion_probes"][:4]),
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["gravitational_negative_heat_capacity_jeans"]["jeans_dispersion_probes"].__setitem__(0, []),
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["gravitational_negative_heat_capacity_jeans"]["jeans_dispersion_probes"][0].__setitem__("extra", 1),
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["gravitational_negative_heat_capacity_jeans"]["jeans_dispersion_probes"][0].__setitem__("omega_sq", "999"),
            lambda p: p["pillar3_offbrane_plummer_schur_dark_source"]["offbrane_plummer_core_theorem"].__setitem__("peak_condition_r_sq_over_y0_sq", 3),
            lambda p: p["pillar3_offbrane_plummer_schur_dark_source"]["offbrane_plummer_core_theorem"].__setitem__("all_triplets_exact", False),
            lambda p: p["pillar3_offbrane_plummer_schur_dark_source"]["offbrane_plummer_core_theorem"].__setitem__("pythagorean_triplets", None),
            lambda p: p["pillar3_offbrane_plummer_schur_dark_source"]["offbrane_plummer_core_theorem"].__setitem__("pythagorean_triplets", "abc"),
            lambda p: p["pillar3_offbrane_plummer_schur_dark_source"]["offbrane_plummer_core_theorem"].__setitem__("pythagorean_triplets", p["pillar3_offbrane_plummer_schur_dark_source"]["offbrane_plummer_core_theorem"]["pythagorean_triplets"][:2]),
            lambda p: p["pillar3_offbrane_plummer_schur_dark_source"]["offbrane_plummer_core_theorem"]["pythagorean_triplets"].__setitem__(0, []),
            lambda p: p["pillar3_offbrane_plummer_schur_dark_source"]["offbrane_plummer_core_theorem"]["pythagorean_triplets"][0].__setitem__("extra", 1),
            lambda p: p["pillar3_offbrane_plummer_schur_dark_source"]["offbrane_plummer_core_theorem"]["pythagorean_triplets"][0].__setitem__("m_enc_over_m", "1/2"),
            lambda p: p["pillar3_offbrane_plummer_schur_dark_source"].__setitem__("all_schur_dark_projections_certified", False),
            lambda p: p["pillar3_offbrane_plummer_schur_dark_source"]["schur_dark_gravity_2x2"].__setitem__("n_total", 3),
            lambda p: p["pillar3_offbrane_plummer_schur_dark_source"]["schur_dark_gravity_2x2"].__setitem__("full_pd", False),
            lambda p: p["pillar3_offbrane_plummer_schur_dark_source"]["schur_dark_gravity_2x2"].__setitem__("j_dark", []),
            lambda p: p["pillar3_offbrane_plummer_schur_dark_source"]["schur_dark_gravity_2x2"].__setitem__("det_m", "999"),
            lambda p: p["pillar3_offbrane_plummer_schur_dark_source"]["schur_dark_gravity_2x2"].__setitem__("dark_shadow_energy_deficit", "0"),
            lambda p: p["pillar4_bounce_dmpr_pell_observational_gates"]["shtanov_sahni_timelike_bounce"].__setitem__("ss_h2_at_rhoc", "1"),
            lambda p: p["pillar4_bounce_dmpr_pell_observational_gates"]["shtanov_sahni_timelike_bounce"].__setitem__("ss_regular_bounce_certified", False),
            lambda p: p["pillar4_bounce_dmpr_pell_observational_gates"]["dmpr_pell_tidal_charge_shadows"].__setitem__("q_neg1_exact_radicand_17_cubed", 4912),
            lambda p: p["pillar4_bounce_dmpr_pell_observational_gates"]["dmpr_pell_tidal_charge_shadows"].__setitem__("q_neg1_b_crit_sq_lo", "1"),
            lambda p: p["pillar4_bounce_dmpr_pell_observational_gates"]["dmpr_pell_tidal_charge_shadows"].__setitem__("shadow_chain_strictly_increasing", False),
            lambda p: p["pillar4_bounce_dmpr_pell_observational_gates"]["dmpr_pell_tidal_charge_shadows"]["witness_q_pos1"].__setitem__("horizon_root_exact", False),
            lambda p: p["pillar4_bounce_dmpr_pell_observational_gates"]["dmpr_pell_tidal_charge_shadows"]["witness_q_pos1"].__setitem__("pell_residual", "999"),
            lambda p: p["pillar4_bounce_dmpr_pell_observational_gates"]["dmpr_pell_tidal_charge_shadows"]["witness_q_pos1"].__setitem__("b_crit_sq_over_m2", "17"),
            lambda p: p["pillar4_bounce_dmpr_pell_observational_gates"]["dmpr_pell_tidal_charge_shadows"]["witness_q_neg2"].__setitem__("photon_sphere_root_exact", False),
            lambda p: p["pillar4_bounce_dmpr_pell_observational_gates"]["dmpr_pell_tidal_charge_shadows"]["witness_q_neg2"].__setitem__("b_crit_sq_over_m2", "1"),
            lambda p: p["pillar4_bounce_dmpr_pell_observational_gates"]["gw170817_cmb_observational_gates"].__setitem__("cmb_redshift_z", 1099),
            lambda p: p["pillar4_bounce_dmpr_pell_observational_gates"]["gw170817_cmb_observational_gates"].__setitem__("dm_to_baryon_ratio", "1"),
            lambda p: p["pillar4_bounce_dmpr_pell_observational_gates"]["gw170817_cmb_observational_gates"].__setitem__("gw170817_d_hi", "100"),
            lambda p: p["pillar4_bounce_dmpr_pell_observational_gates"]["gw170817_cmb_observational_gates"].__setitem__("flat_d_5_excluded_by_gw170817", False),
        ]
        for fn in sec_mutators:
            pm = copy.deepcopy(self.payload)
            fn(pm)
            with self.assertRaises(Err):
                audit.secondary_audit_payload(pm)

        # Re-signed full_replay=False contradiction & hollow-table tampers MUST fail closed
        def _tamp_schur(p: dict[str, object]) -> None:
            s2 = p["pillar3_offbrane_plummer_schur_dark_source"]["schur_dark_gravity_2x2"]  # type: ignore[index]
            s2["full_pd"] = False  # type: ignore[index]
            s2["schur_matches_full_solve_exact"] = False  # type: ignore[index]
            s2["j_dark"] = []  # type: ignore[index]
            s2["det_m"] = "999"  # type: ignore[index]

        def _tamp_arc3(p: dict[str, object]) -> None:
            a3 = p["pillar1_entropy_smoothing_catmap_maxent"]["arnold_cat_map_filament_arc"]["arc_t0_to_t3"][3]  # type: ignore[index]
            a3["micro_perimeter"] = 0  # type: ignore[index]
            a3["coarse_block_variance"] = "999"  # type: ignore[index]
            a3["coarse_collision_energy"] = "999"  # type: ignore[index]

        def _tamp_jaynes(p: dict[str, object]) -> None:
            jm = p["pillar1_entropy_smoothing_catmap_maxent"]["jaynes_maxent_missing_vectors"]  # type: ignore[index]
            jm["p_star"] = []  # type: ignore[index]
            jm["ker_basis_gram_det"] = "0"  # type: ignore[index]
            jm["p_pert_collision_energy"] = "0"  # type: ignore[index]

        def _tamp_unruh(p: dict[str, object]) -> None:
            un = p["pillar2_worthington_unruh_gravity_bifurcation"]["unruh_analogue_sonic_horizon"]  # type: ignore[index]
            un["f_ac_at_horizon"] = "999"  # type: ignore[index]
            un["surface_gravity_kappa"] = "1/999"  # type: ignore[index]
            un["normalized_killing_kappa"] = "-5"  # type: ignore[index]

        def _tamp_jeans(p: dict[str, object]) -> None:
            for pr in p["pillar2_worthington_unruh_gravity_bifurcation"]["gravitational_negative_heat_capacity_jeans"]["jeans_dispersion_probes"]:  # type: ignore[index]
                pr["omega_sq"] = "999"

        def _tamp_dmpr(p: dict[str, object]) -> None:
            dm = p["pillar4_bounce_dmpr_pell_observational_gates"]["dmpr_pell_tidal_charge_shadows"]  # type: ignore[index]
            dm["q_neg1_b_crit_sq_lo"] = "1"  # type: ignore[index]
            dm["q_neg1_b_crit_sq_hi"] = "2"  # type: ignore[index]
            dm["witness_q_pos1"]["pell_residual"] = "999"  # type: ignore[index]

        def _tamp_obs(p: dict[str, object]) -> None:
            ob = p["pillar4_bounce_dmpr_pell_observational_gates"]["gw170817_cmb_observational_gates"]  # type: ignore[index]
            ob["dm_to_baryon_ratio"] = "1"  # type: ignore[index]
            ob["gw170817_d_hi"] = "100"  # type: ignore[index]

        for fn_resigned in (_tamp_schur, _tamp_arc3, _tamp_jaynes, _tamp_unruh, _tamp_jeans, _tamp_dmpr, _tamp_obs):
            pm = copy.deepcopy(self.payload)
            fn_resigned(pm)
            with self.assertRaises(Err):
                audit.verify_certificate_dict(_resign(pm), full_replay=False)

        # Division-free zero-denominator regression across all 10 denominator leaves (FR=False & secondary_audit_payload)
        zero_denom_mutators = [
            lambda p: p["pillar2_worthington_unruh_gravity_bifurcation"]["unruh_analogue_sonic_horizon"].__setitem__("sonic_horizon_r_h", "0"),
            lambda p: p["pillar4_bounce_dmpr_pell_observational_gates"]["gw170817_cmb_observational_gates"].__setitem__("omega_b_h2", "0"),
        ]
        for wk in (
            "witness_q_pos1",
            "witness_q_zero_schwarzschild",
            "witness_q_neg_495_289_pell",
            "witness_q_neg35_pell",
        ):
            zero_denom_mutators.append(
                lambda p, key=wk: p["pillar4_bounce_dmpr_pell_observational_gates"]["dmpr_pell_tidal_charge_shadows"][key].__setitem__("r_ph_over_m", "0")
            )
            zero_denom_mutators.append(
                lambda p, key=wk: p["pillar4_bounce_dmpr_pell_observational_gates"]["dmpr_pell_tidal_charge_shadows"][key].__setitem__("f_at_r_ph", "0")
            )
        self.assertEqual(len(zero_denom_mutators), 10)
        for zmut in zero_denom_mutators:
            pm_z = copy.deepcopy(self.payload)
            zmut(pm_z)
            with self.assertRaises(Err):
                audit.secondary_audit_payload(pm_z)
            with self.assertRaises(Err):
                audit.verify_certificate_dict(_resign(pm_z), full_replay=False)

        # Direct secondary_audit_payload JSON-tree subclass & runtime float rejection
        for sub_mut in (
            lambda p: p.__setitem__("novelty_tier", _SubStr("N1")),
            lambda p: p.__setitem__("oracle_class", _SubStr("exact")),
            lambda p: p["pillar1_entropy_smoothing_catmap_maxent"]["q3_jko_diffusion"].__setitem__("vertices", _SubInt(8)),
            lambda p: p.__setitem__("novelty_tier", int(3) / int(2)),
        ):
            pm_s = copy.deepcopy(self.payload)
            sub_mut(pm_s)
            with self.assertRaises(Err):
                audit.secondary_audit_payload(pm_s)

    # -----------------------------------------------------------------------
    # 4. Fail-Closed File I/O Security, Concurrency & CLI Traps
    # -----------------------------------------------------------------------

    def test_09_zone_b_io_hardening_streaming_hardlinks_and_concurrency(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tdp = Path(td)
            cert_path = tdp / "cert.json"

            # Write (0o600 mode), overwrite existing single-link file (st_nlink == 1), check & safe path
            wres = audit.write_certificate_file(cert_path)
            self.assertIs(wres["written"], True)
            self.assertEqual(stat.S_IMODE(cert_path.stat().st_mode), 0o600)
            wres2 = audit.write_certificate_file(cert_path)
            self.assertIs(wres2["written"], True)
            self.assertEqual(audit.require_safe_path(cert_path), cert_path)
            self.assertEqual(audit.require_safe_path(tdp / "nonexistent.json"), tdp / "nonexistent.json")
            self.assertEqual(audit.require_safe_path(Path("/")), Path("/"))
            cres = audit.check_certificate_file(cert_path)
            self.assertIs(cres["valid"], True)
            self.assertIs(cres["secondary_audit"]["secondary_audit_passed"], True)

            # Relative path + atomic dir_fd PWD symlink check
            old_cwd = os.getcwd()
            old_pwd = os.environ.get("PWD")
            try:
                os.chdir(td)
                os.environ["PWD"] = td
                self.assertEqual(audit.require_safe_path(Path("cert.json")), Path("cert.json"))
                sym_dir = tdp / "symdir"
                os.symlink(tdp, sym_dir)
                os.environ["PWD"] = str(sym_dir)
                with self.assertRaises(Err):
                    audit.require_safe_path(Path("cert.json"))
                os.environ["PWD"] = str(tdp / "no_such_dir")
                self.assertEqual(audit.require_safe_path(Path("cert.json")), Path("cert.json"))
            finally:
                os.chdir(old_cwd)
                if old_pwd is None:
                    os.environ.pop("PWD", None)
                else:
                    os.environ["PWD"] = old_pwd

            # Path/data type, NUL, directory, symlink, hardlink, FIFO rejections
            with self.assertRaises(Err):
                audit.require_safe_path("cert.json")
            with self.assertRaises(Err):
                audit.require_safe_path(_SubPath(cert_path))
            with self.assertRaises(Err):
                audit.require_safe_path(Path(f"{td}/a\x00b"))
            for bad_data in ("not_bytes", bytearray(b"x")):
                with self.assertRaises(Err) as cm_wd:
                    audit.write_regular_file_bytes(tdp / "missing_dir" / "out.json", bad_data)  # type: ignore[arg-type]
                self.assertEqual(cm_wd.exception.code, "INVALID_WRITE_DATA")
            with self.assertRaises(Err):
                audit.read_regular_bytes_capped(Path("/"))
            with self.assertRaises(Err):
                audit.write_regular_file_bytes(Path("/"), b"{}")
            with self.assertRaises(Err):
                audit.read_regular_bytes_capped(tdp)
            with self.assertRaises(Err):
                audit.write_regular_file_bytes(tdp, b"{}")

            leaf_sym = tdp / "leaf_sym.json"
            os.symlink(cert_path, leaf_sym)
            for fn_call in (
                lambda: audit.require_safe_path(leaf_sym),
                lambda: audit.read_regular_bytes_capped(leaf_sym),
                lambda: audit.write_regular_file_bytes(leaf_sym, b"{}\n"),
            ):
                with self.assertRaises(Err) as cm_s:
                    fn_call()
                self.assertEqual(cm_s.exception.code, "SYMLINK_FORBIDDEN")
            with self.assertRaises(Err) as cm_noent:
                audit.read_regular_bytes_capped(tdp / "missing.json")
            self.assertEqual(cm_noent.exception.code, "FILE_READ_ERROR")
            inter_sym = tdp / "inter_sym"
            os.symlink(tdp, inter_sym)
            with self.assertRaises(Err) as cm_is:
                audit.read_regular_bytes_capped(inter_sym / "cert.json")
            self.assertEqual(cm_is.exception.code, "SYMLINK_FORBIDDEN")
            with self.assertRaises(Err) as cm_md:
                audit.read_regular_bytes_capped(tdp / "no_dir" / "cert.json")
            self.assertEqual(cm_md.exception.code, "PATH_NOT_FOUND")

            hl_target = tdp / "hl.json"
            os.link(cert_path, hl_target)
            with self.assertRaises(Err) as cm_hl:
                audit.write_regular_file_bytes(hl_target, b"{}\n")
            self.assertEqual(cm_hl.exception.code, "HARDLINK_FORBIDDEN")
            os.unlink(hl_target)

            fifo_p = tdp / "p.fifo"
            os.mkfifo(fifo_p)
            with self.assertRaises(Err):
                audit.read_regular_bytes_capped(fifo_p)
            with self.assertRaises(Err):
                audit.write_regular_file_bytes(fifo_p, b"{}\n")

            # Streaming 64 KiB+ read (140 KiB > 2x 65536), exact max_bytes boundary & 1<<100 cap rejection
            stream_p = tdp / "stream140k.bin"
            blob140 = b"z" * 140_000
            stream_p.write_bytes(blob140)
            self.assertEqual(audit.read_regular_bytes_capped(stream_p, 140_000), blob140)
            with self.assertRaises(Err) as cm_sz:
                audit.read_regular_bytes_capped(stream_p, 139_999)
            self.assertEqual(cm_sz.exception.code, "FILE_TOO_LARGE")
            with self.assertRaises(Err) as cm_cap:
                audit.read_regular_bytes_capped(stream_p, 1 << 100)
            self.assertEqual(cm_cap.exception.code, "INT_ABOVE_MAX")
            with self.assertRaises(Err):
                audit.read_regular_bytes_capped(stream_p, 0)

            # CRLF, missing trailing LF, invalid UTF-8, non-canonical JSON spacing
            for name, raw_b, exp_code in (
                ("crlf.json", cert_path.read_bytes().replace(b"\n", b"\r\n"), "CRLF_FORBIDDEN"),
                ("nolf.json", cert_path.read_bytes().rstrip(b"\n"), "MISSING_TRAILING_LF"),
                ("badutf.json", b"\xff\xfe\n", "INVALID_UTF8"),
                ("noncan.json", b" " + cert_path.read_bytes(), "NON_CANONICAL_BYTES"),
            ):
                p = tdp / name
                p.write_bytes(raw_b)
                with self.assertRaises(Err) as cm_c:
                    audit.check_certificate_file(p)
                self.assertEqual(cm_c.exception.code, exp_code)

            # Monotonic counter & uniqueness of _next_tmp_name + mocked EEXIST retry & 32-attempt exhaustion
            tn1 = audit._next_tmp_name("col.json")
            tn2 = audit._next_tmp_name("col.json")
            self.assertNotEqual(tn1, tn2)
            seq1 = oracle.parse_exact_int_ascii(tn1.split(".")[-2], "seq1")
            seq2 = oracle.parse_exact_int_ascii(tn2.split(".")[-2], "seq2")
            self.assertEqual(seq2, seq1 + 1)

            col_target = tdp / "col.json"
            (tdp / ".col.json.s37tmp.fixed0").write_bytes(b"occupy")
            with mock.patch.object(audit, "_next_tmp_name", side_effect=[".col.json.s37tmp.fixed0", ".col.json.s37tmp.fixed1"]):
                audit.write_regular_file_bytes(col_target, b"ok\n")
            self.assertEqual(col_target.read_bytes(), b"ok\n")

            (tdp / ".col2.json.s37tmp.occ").write_bytes(b"x")
            with mock.patch.object(audit, "_next_tmp_name", return_value=".col2.json.s37tmp.occ"):
                with self.assertRaises(Err) as cm_col2:
                    audit.write_regular_file_bytes(tdp / "col2.json", b"ok\n")
            self.assertEqual(cm_col2.exception.code, "TEMP_RETRY_EXHAUSTED")

            # Pre-replace temp hardlink guard (st_nlink != 1 -> HARDLINK_FORBIDDEN + temp cleanup)
            hl_tmp_target = tdp / "hl_tmp.json"
            real_fstat = os.fstat

            def _fake_fstat(fd: int) -> os.stat_result:
                st = real_fstat(fd)
                return os.stat_result((st.st_mode, st.st_ino, st.st_dev, 2, st.st_uid, st.st_gid, st.st_size, st.st_atime, st.st_mtime, st.st_ctime))

            with mock.patch.object(audit.os, "fstat", side_effect=_fake_fstat):
                with self.assertRaises(Err) as cm_ht:
                    audit.write_regular_file_bytes(hl_tmp_target, b"ok\n")
            self.assertEqual(cm_ht.exception.code, "HARDLINK_FORBIDDEN")
            self.assertEqual(list(tdp.glob(".hl_tmp.json.s37tmp.*")), [])

            # Live 16-thread concurrent same-target write contention inside unit suite
            conc_target = tdp / "conc.json"
            conc_errs: list[str] = []
            conc_lock = threading.Lock()
            conc_ok = 0

            def _w(tid: int) -> None:
                nonlocal conc_ok
                data_b = f'{{"tid":{tid}}}\n'.encode("ascii")
                for _ in range(2):
                    try:
                        audit.write_regular_file_bytes(conc_target, data_b)
                        with conc_lock:
                            conc_ok += 1
                    except Exception as exc:  # pragma: no cover
                        with conc_lock:
                            conc_errs.append(f"{tid}:{type(exc).__name__}:{exc}")

            ths = [threading.Thread(target=_w, args=(i,)) for i in range(16)]
            for th in ths:
                th.start()
            for th in ths:
                th.join()
            self.assertEqual(conc_errs, [])
            self.assertEqual(conc_ok, 32)
            self.assertEqual(list(tdp.glob(".conc.json.s37tmp.*")), [])

            # Unreadable file & directory permissions
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

    def test_10_cli_parsing_deleted_cwd_and_flag_traps(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tdp = Path(td)
            out_path = tdp / "cli_cert.json"

            for argv_ok in ([], ["--standalone"], ["--standalone", "--json"], ["--write", str(out_path), "--json"], ["--check", str(out_path)], ["--check", str(out_path), "--json"]):
                buf_out = io.StringIO()
                buf_err = io.StringIO()
                old_out, old_err = sys.stdout, sys.stderr
                try:
                    sys.stdout, sys.stderr = buf_out, buf_err
                    rc = audit.main(argv_ok)
                finally:
                    sys.stdout, sys.stderr = old_out, old_err
                self.assertEqual(rc, 0)
                self.assertEqual(buf_err.getvalue(), "")

            bad_argvs: list[object] = [
                ["--write", "--json"],
                ["--write=--json"],
                ["--check=--json"],
                ["--check", "--json"],
                ["--json", "--json"],
                ["--standalone", "--standalone"],
                ["--standalone", "--check", str(out_path)],
                ["--write"],
                ["--check"],
                ["--write", ""],
                ["--unknown"],
                ["--write", "bad\ud800.json"],
                "not_a_list",
            ]
            for bad in bad_argvs:
                buf_out = io.StringIO()
                buf_err = io.StringIO()
                old_out, old_err = sys.stdout, sys.stderr
                try:
                    sys.stdout, sys.stderr = buf_out, buf_err
                    rc = audit.main(bad)  # type: ignore[arg-type]
                finally:
                    sys.stdout, sys.stderr = old_out, old_err
                self.assertEqual(rc, 2)
                err_obj = json.loads(buf_err.getvalue())
                self.assertIs(err_obj["valid"], False)
                if bad == "not_a_list":
                    self.assertEqual(err_obj["error_code"], "INVALID_ARGV")
                if bad == ["--write", ""]:
                    self.assertEqual(err_obj["error_code"], "INVALID_PATH_ARG")
            self.assertFalse(Path("--json").exists())

            # Deleted-CWD fail-closed check
            del_dir = tdp / "vanishing"
            del_dir.mkdir()
            script = (
                "import os, sys; "
                f"sys.path.insert(0, {str(_THIS_DIR)!r}); "
                "import entropy_bulk_projection_audit as a; "
                f"os.chdir({str(del_dir)!r}); os.rmdir({str(del_dir)!r}); "
                "raise SystemExit(a.main(['--check', 'rel.json']))"
            )
            proc = subprocess.run([sys.executable, "-B", "-c", script], capture_output=True, text=True, timeout=15)
            self.assertEqual(proc.returncode, 2)
            self.assertIn("CWD_UNAVAILABLE", proc.stderr)

            kallsyms = Path("/proc/kallsyms")
            if kallsyms.exists():
                with self.assertRaises(Err) as cm_proc:
                    audit.read_regular_bytes_capped(kallsyms)
                self.assertEqual(cm_proc.exception.code, "FILE_TOO_LARGE")

            # Mocked macOS Darwin /var, /tmp, /etc root-owned system alias normalization
            _fake_root_lnk = os.stat_result((stat.S_IFLNK | 0o777, 0, 0, 1, 0, 0, 0, 0, 0, 0))
            _fake_nonroot_lnk = os.stat_result((stat.S_IFLNK | 0o777, 0, 0, 1, 1000, 0, 0, 0, 0, 0))
            _fake_root_dir = os.stat_result((stat.S_IFDIR | 0o755, 0, 0, 2, 0, 0, 0, 0, 0, 0))
            with mock.patch.object(audit.sys, "platform", "linux"), mock.patch.object(audit.os, "lstat", return_value=_fake_root_lnk), mock.patch.object(audit.os, "readlink", return_value="private/var"):
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/var/folders/x")), Path("/var/folders/x"))
            with mock.patch.object(audit.sys, "platform", "darwin"):
                with mock.patch.object(audit.os, "lstat", return_value=_fake_root_lnk), mock.patch.object(audit.os, "readlink", return_value="private/var"):
                    self.assertEqual(audit._normalize_darwin_system_prefix(Path("var/folders/x")), Path("var/folders/x"))
                    self.assertEqual(audit._normalize_darwin_system_prefix(Path("a/var/x")), Path("a/var/x"))
                    self.assertEqual(audit._normalize_darwin_system_prefix(Path("/var")), Path("/var"))
                    self.assertEqual(audit._normalize_darwin_system_prefix(Path("/var"), allow_exact=True), Path("/private/var"))
                    self.assertEqual(audit._normalize_darwin_system_prefix(Path("/var/../etc/x")), Path("/var/../etc/x"))
                    self.assertEqual(audit._normalize_darwin_system_prefix(Path("/usr/local/x")), Path("/usr/local/x"))
                    self.assertEqual(audit._normalize_darwin_system_prefix(Path("/var/folders/x")), Path("/private/var/folders/x"))
                with mock.patch.object(audit.os, "lstat", return_value=_fake_root_lnk), mock.patch.object(audit.os, "readlink", return_value="/private/tmp"):
                    self.assertEqual(audit._normalize_darwin_system_prefix(Path("/tmp/a/b")), Path("/private/tmp/a/b"))
                with mock.patch.object(audit.os, "lstat", return_value=_fake_root_lnk), mock.patch.object(audit.os, "readlink", return_value="/evil"):
                    self.assertEqual(audit._normalize_darwin_system_prefix(Path("/var/folders/x")), Path("/var/folders/x"))
                with mock.patch.object(audit.os, "lstat", return_value=_fake_nonroot_lnk), mock.patch.object(audit.os, "readlink", return_value="private/var"):
                    self.assertEqual(audit._normalize_darwin_system_prefix(Path("/var/folders/x")), Path("/var/folders/x"))
                with mock.patch.object(audit.os, "lstat", return_value=_fake_root_dir), mock.patch.object(audit.os, "readlink", return_value="private/var"):
                    self.assertEqual(audit._normalize_darwin_system_prefix(Path("/var/folders/x")), Path("/var/folders/x"))
                with mock.patch.object(audit.os, "lstat", side_effect=OSError("no lstat")):
                    self.assertEqual(audit._normalize_darwin_system_prefix(Path("/var/folders/x")), Path("/var/folders/x"))

    def test_11_disk_certificate_matches_standalone(self) -> None:
        disk_cert = _THIS_DIR / "entropy_bulk_projection_certificate.json"
        if disk_cert.exists():
            res = audit.check_certificate_file(disk_cert)
            self.assertIs(res["valid"], True)
            self.assertEqual(res["payload_sha256"], self.cert["payload_sha256"])
            self.assertEqual(res["certificate_sha256"], self.cert["certificate_sha256"])


if __name__ == "__main__":
    unittest.main()
