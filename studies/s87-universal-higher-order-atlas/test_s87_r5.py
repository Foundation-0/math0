#!/usr/bin/env python3
"""
Track S87 Assertion-Free R5 Hardened Unit Test Suite.

Covers all 4 Deep 3rd/4th-Order Meta-Convergences, Law-5 non-commutativity obstructions,
exact-Q oracle boundaries, Zone-B fail-closed I/O & JSON attacks, 4-surface API (CLI/FR1/FR0/SEC),
(0o600, 0o644) committed disk-cert parity + strict 0o600 --write, scratch os.mkfifo probes,
hardlinks, symlinks, read-only directories, --verify-upstream manifest checks, all R10+ static
Lean 4 bypasses, AND 0-skip Lean-less CI dual-mode compatibility (ALETHEIA_REQUIRE_LEAN=1).
"""
from __future__ import annotations

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
import unittest
from unittest import mock

_SCRIPT_DIR = Path(__file__).resolve().parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))

import s87_higher_order_atlas_oracle as s87
import verify_s87_higher_order_atlas as ver


def _resign(cert: dict) -> dict:
    p_sha = hashlib.sha256(s87.canonical_json_bytes(cert["payload"])).hexdigest()
    env = {
        "schema": cert["schema"],
        "track_id": cert["track_id"],
        "payload_sha256": p_sha,
        "payload": cert["payload"],
    }
    c_sha = hashlib.sha256(s87.canonical_json_bytes(env)).hexdigest()
    return {
        "schema": cert["schema"],
        "track_id": cert["track_id"],
        "payload_sha256": p_sha,
        "certificate_sha256": c_sha,
        "payload": cert["payload"],
    }


class TestS87OraclePrimitives(unittest.TestCase):
    def test_error_guards_and_formatters(self) -> None:
        err = s87.S87Error("E_CODE", "e msg")
        self.assertEqual(err.code, "E_CODE")
        self.assertEqual(err.message, "e msg")
        self.assertEqual(str(err), "[E_CODE] e msg")

        s87.require_ok(True, "OK", "ok")
        for bad in (False, 1, "yes", None):
            with self.assertRaises(s87.S87Error) as ctx:
                s87.require_ok(bad, "BAD_COND", "bad")  # type: ignore[arg-type]
            self.assertEqual(ctx.exception.code, "BAD_COND")

        self.assertEqual(s87.q_obj(Fraction(-6, 4)), {"num": -3, "den": 2})
        with self.assertRaises(s87.S87Error) as cq:
            s87.q_obj(3)  # type: ignore[arg-type]
        self.assertEqual(cq.exception.code, "INVALID_FRACTION")

        self.assertEqual(s87.frac_to_dec_str(Fraction(1, 4), 1), "0.2")
        self.assertEqual(s87.frac_to_dec_str(Fraction(1, 8), 3), "0.125")
        self.assertEqual(s87.frac_to_dec_str(Fraction(1, 2), 12), "0.500000000000")
        with self.assertRaises(s87.S87Error):
            s87.frac_to_dec_str(1, 2)  # type: ignore[arg-type]
        for bad_pl in (0, 13, True):
            with self.assertRaises(s87.S87Error) as cpl:
                s87.frac_to_dec_str(Fraction(1, 2), bad_pl)  # type: ignore[arg-type]
            self.assertEqual(cpl.exception.code, "INVALID_PLACES")

        self.assertEqual(s87._check_exact_int(7, "x"), 7)
        with self.assertRaises(s87.S87Error):
            s87._check_exact_int(True, "x")
        self.assertEqual(s87._check_exact_frac(Fraction(2, 3), "f"), Fraction(2, 3))
        with self.assertRaises(s87.S87Error):
            s87._check_exact_frac(2, "f")  # type: ignore[arg-type]

    def test_exact_det_sylvester_and_potential_flip(self) -> None:
        self.assertEqual(s87.exact_det_q([[Fraction(5)]]), Fraction(5))
        self.assertEqual(
            s87.exact_det_q([[Fraction(0), Fraction(1)], [Fraction(1), Fraction(0)]]),
            Fraction(-1),
        )
        self.assertEqual(
            s87.exact_det_q([[Fraction(1), Fraction(2)], [Fraction(2), Fraction(4)]]),
            Fraction(0),
        )
        self.assertEqual(
            s87.exact_det_q(
                [
                    [Fraction(2), Fraction(1), Fraction(0)],
                    [Fraction(1), Fraction(3), Fraction(1)],
                    [Fraction(0), Fraction(1), Fraction(2)],
                ]
            ),
            Fraction(8),
        )
        for bad_m in (
            [],
            "notlist",
            ([Fraction(1)],),
            [(Fraction(1),)],
            [[Fraction(1)], "bad"],
            [[Fraction(1), Fraction(2)]],
        ):
            with self.assertRaises(s87.S87Error):
                s87.exact_det_q(bad_m)  # type: ignore[arg-type]
        with self.assertRaises(s87.S87Error):
            s87.exact_det_q([[1]])  # type: ignore[list-item]

        r_pos = s87.classify_2x2_sylvester(Fraction(2), Fraction(1), Fraction(2))
        self.assertEqual(r_pos["regime"], "strictly_euclidean_posdef")
        self.assertEqual(r_pos["inertia_pos_zero_neg"], [2, 0, 0])
        self.assertEqual(r_pos["det_q"], {"num": 3, "den": 1})
        self.assertTrue(r_pos["sylvester_identity_exact"])

        r_deg = s87.classify_2x2_sylvester(Fraction(1), Fraction(1), Fraction(1))
        self.assertEqual(r_deg["regime"], "degenerate_rank1_fold")
        self.assertEqual(r_deg["inertia_pos_zero_neg"], [1, 1, 0])
        self.assertEqual(r_deg["witness_quadform_q"], {"num": 0, "den": 1})

        r_cat = s87.classify_2x2_sylvester(Fraction(1), Fraction(3, 2), Fraction(2))
        self.assertEqual(r_cat["regime"], "strictly_cat0_indefinite")
        self.assertEqual(r_cat["inertia_pos_zero_neg"], [1, 0, 1])
        self.assertEqual(r_cat["det_q"], {"num": -1, "den": 4})
        self.assertEqual(r_cat["witness_quadform_q"], {"num": -1, "den": 4})

        for bad_p in (Fraction(0), Fraction(-1)):
            with self.assertRaises(s87.S87Error) as cp:
                s87.classify_2x2_sylvester(bad_p, Fraction(0), Fraction(1))
            self.assertEqual(cp.exception.code, "NONPOS_PIVOT")

        # Competing potential flip: test all 4 sign combinations (kills BoolOp)
        f_tt = s87.competing_potential_flip(Fraction(2), Fraction(10), Fraction(8), Fraction(12))
        self.assertTrue(f_tt["sign_flip_exact"])
        self.assertEqual(f_tt["v_lo_q"], {"num": 4, "den": 1})
        self.assertEqual(f_tt["v_hi_q"], {"num": -4, "den": 1})
        self.assertFalse(
            s87.competing_potential_flip(Fraction(2), Fraction(10), Fraction(10), Fraction(12))["sign_flip_exact"]
        )
        self.assertFalse(
            s87.competing_potential_flip(Fraction(2), Fraction(10), Fraction(8), Fraction(10))["sign_flip_exact"]
        )
        self.assertFalse(
            s87.competing_potential_flip(Fraction(2), Fraction(10), Fraction(12), Fraction(8))["sign_flip_exact"]
        )
        with self.assertRaises(s87.S87Error):
            s87.competing_potential_flip(Fraction(0), Fraction(10), Fraction(8), Fraction(12))

        # Frozen Track S71 exact quartic potential difference & barrier flip
        self.assertEqual(s87.s71_quartic_delta_pot(11), 5260)
        self.assertEqual(s87.s71_quartic_delta_pot(12), -12500)
        self.assertEqual(s87.s71_quartic_delta_pot(0, 1, 1, 0), 0)
        for bad_q in ((-1, 10, 60, 1), (1, 0, 60, 1), (1, 10, 0, 1), (1, 10, 60, -1)):
            with self.assertRaises(s87.S87Error) as cq:
                s87.s71_quartic_delta_pot(*bad_q)
            self.assertEqual(cq.exception.code, "INVALID_S71_PARAM")
        self.assertTrue(s87.eval_s71_quartic_barrier_flip(11, 12)["sign_flip_exact"])
        self.assertFalse(s87.eval_s71_quartic_barrier_flip(12, 12)["sign_flip_exact"])
        self.assertFalse(s87.eval_s71_quartic_barrier_flip(11, 11)["sign_flip_exact"])
        self.assertFalse(s87.eval_s71_quartic_barrier_flip(12, 11)["sign_flip_exact"])

    def test_grafting_ppv_carry_cs21_and_ceer_primitives(self) -> None:
        lift = s87.ambient_lift_orthogonality([Fraction(3), Fraction(4)], Fraction(5))
        self.assertEqual(lift["base_dim"], 2)
        self.assertEqual(lift["lifted_dim"], 3)
        self.assertEqual(lift["inner_product_q"], {"num": 0, "den": 1})
        self.assertEqual(lift["base_norm_sq_q"], {"num": 25, "den": 1})
        self.assertEqual(lift["graft_norm_sq_q"], {"num": 25, "den": 1})
        self.assertEqual(lift["combined_norm_sq_q"], {"num": 50, "den": 1})
        self.assertTrue(lift["exact_orthogonality"])
        self.assertTrue(lift["pythagorean_exact"])
        for bad_u in ([], (Fraction(1),)):
            with self.assertRaises(s87.S87Error):
                s87.ambient_lift_orthogonality(bad_u, Fraction(1))  # type: ignore[arg-type]
        with self.assertRaises(s87.S87Error):
            s87.ambient_lift_orthogonality([Fraction(1)], Fraction(0))

        ppv = s87.dual_oracle_bayes_ppv(
            Fraction(1, 20), Fraction(19, 20), Fraction(4, 5), Fraction(1, 5), Fraction(4, 5), Fraction(1, 10)
        )
        self.assertEqual(ppv["single_ppv_q"], {"num": 4, "den": 23})
        self.assertEqual(ppv["dual_ppv_q"], {"num": 32, "den": 51})
        self.assertEqual(ppv["ppv_gain_q"], {"num": 532, "den": 1173})
        self.assertEqual(ppv["ppv_amplification_ratio_q"], {"num": 184, "den": 51})
        self.assertEqual(ppv["ppv_amplification_dec"], "3.6078")
        self.assertTrue(ppv["strict_amplification"])
        ppv_eq = s87.dual_oracle_bayes_ppv(
            Fraction(1, 2), Fraction(1, 2), Fraction(1), Fraction(1), Fraction(1, 2), Fraction(1, 2)
        )
        self.assertFalse(ppv_eq["strict_amplification"])
        with self.assertRaises(s87.S87Error):
            s87.dual_oracle_bayes_ppv(
                Fraction(0), Fraction(1), Fraction(1), Fraction(1), Fraction(1), Fraction(1)
            )

        c_act = s87.f2_to_z_carry_defect(13, 7)
        self.assertEqual((c_act["f2_xor_sum"], c_act["carry_bits"], c_act["z_integer_sum"], c_act["carry_defect"]), (10, 5, 20, 10))
        self.assertTrue(c_act["carry_wall_active"])
        c_zero = s87.f2_to_z_carry_defect(0, 0)
        self.assertFalse(c_zero["carry_wall_active"])
        with self.assertRaises(s87.S87Error):
            s87.f2_to_z_carry_defect(-1, 2)
        with self.assertRaises(s87.S87Error):
            s87.f2_to_z_carry_defect(2, -1)

        # CS-21 boundary accounting: all 4 (t_b < t_a, tot_b > tot_a) combos + t_a == 0 + zero-total guards
        m_tt = s87.cs21_boundary_accounting(400, 1, 100, 500)
        self.assertTrue(m_tt["mirage_detected"])
        self.assertFalse(m_tt["genuine_net_improvement"])
        self.assertEqual(m_tt["true_net_ratio_q"], {"num": 600, "den": 401})
        self.assertEqual(m_tt["candidate_hidden_share_q"], {"num": 5, "den": 6})
        m_tf = s87.cs21_boundary_accounting(400, 1, 100, 2)
        self.assertFalse(m_tf["mirage_detected"])
        self.assertTrue(m_tf["genuine_net_improvement"])
        m_ft = s87.cs21_boundary_accounting(100, 1, 400, 500)
        self.assertFalse(m_ft["mirage_detected"])
        m_ff = s87.cs21_boundary_accounting(100, 1, 100, 1)
        self.assertFalse(m_ff["mirage_detected"])
        self.assertFalse(m_ff["genuine_net_improvement"])
        m_ta0 = s87.cs21_boundary_accounting(0, 5, 1, 2)
        self.assertEqual(m_ta0["apparent_ratio_q"], {"num": 0, "den": 1})
        for bad_cs in ((-1, 5, 1, 1), (-1, 1, 1, 1), (0, 0, 1, 1), (1, 1, 0, 0)):
            with self.assertRaises(s87.S87Error):
                s87.cs21_boundary_accounting(*bad_cs)

        # CEER 5-gate step: all pass, all fail, boundary params
        ok_step = s87.evaluate_ceer_five_gate_step(
            rho=Fraction(1, 2),
            firewall_leak=Fraction(0),
            goodhart_drift=Fraction(0),
            dual_kernel_leaks=0,
            net_cost_ratio=Fraction(1, 2),
            steps=1,
        )
        self.assertTrue(ok_step["all_five_gates_pass"])
        self.assertEqual(ok_step["error_after_steps_q"], {"num": 1, "den": 2})
        fail_all = s87.evaluate_ceer_five_gate_step(
            rho=Fraction(1),
            firewall_leak=Fraction(1),
            goodhart_drift=Fraction(1),
            dual_kernel_leaks=2,
            net_cost_ratio=Fraction(1),
            steps=2,
        )
        self.assertFalse(fail_all["all_five_gates_pass"])
        self.assertFalse(fail_all["gate1_loop_schur_contractive"])
        self.assertFalse(fail_all["gate5_cs21_net_gain"])
        for bad_kw in (
            {"rho": Fraction(0), "firewall_leak": Fraction(0), "goodhart_drift": Fraction(0), "dual_kernel_leaks": 0, "net_cost_ratio": Fraction(1, 2), "steps": 1},
            {"rho": Fraction(1, 2), "firewall_leak": Fraction(0), "goodhart_drift": Fraction(0), "dual_kernel_leaks": 0, "net_cost_ratio": Fraction(0), "steps": 1},
            {"rho": Fraction(1, 2), "firewall_leak": Fraction(0), "goodhart_drift": Fraction(0), "dual_kernel_leaks": 0, "net_cost_ratio": Fraction(1, 2), "steps": 0},
            {"rho": Fraction(1, 2), "firewall_leak": Fraction(-1), "goodhart_drift": Fraction(0), "dual_kernel_leaks": 0, "net_cost_ratio": Fraction(1, 2), "steps": 1},
            {"rho": Fraction(1, 2), "firewall_leak": Fraction(0), "goodhart_drift": Fraction(-1), "dual_kernel_leaks": 0, "net_cost_ratio": Fraction(1, 2), "steps": 1},
            {"rho": Fraction(1, 2), "firewall_leak": Fraction(0), "goodhart_drift": Fraction(0), "dual_kernel_leaks": -1, "net_cost_ratio": Fraction(1, 2), "steps": 1},
        ):
            with self.assertRaises(s87.S87Error):
                s87.evaluate_ceer_five_gate_step(**bad_kw)  # type: ignore[arg-type]

    def test_five_pillars_certificate_values(self) -> None:
        cert = s87.build_certificate()
        ver.audit_certificate_object(cert)
        self.assertEqual(cert["schema"], s87.CERT_SCHEMA)
        self.assertEqual(cert["track_id"], s87.CERT_TRACK_ID)
        p = cert["payload"]

        # Pillar 1: Meta-Convergence A
        p1 = p["pillar1_meta_a_competing_potential"]
        self.assertTrue(p1["pillar_verified"])
        self.assertEqual(p1["s71_mesi_repulsion_dec"], "16.973")
        self.assertEqual(p1["s71_read_fusion_dec"], "2.681")
        self.assertEqual(p1["s71_quartic_barrier_flip"]["delta_pot_r_below"], 5260)
        self.assertEqual(p1["s71_quartic_barrier_flip"]["delta_pot_r_at_barrier"], -12500)
        self.assertEqual(p1["universal_linear_threshold_model"]["v_lo_q"], {"num": 1, "den": 1})
        self.assertEqual(p1["universal_linear_threshold_model"]["v_hi_q"], {"num": -1, "den": 1})
        self.assertEqual(p1["s59_opposite_sign_anisotropy_inversion_q"], {"num": 8, "den": 1})
        self.assertEqual(p1["s59_e8_regime_delta_q"], {"num": 135, "den": 8})
        self.assertEqual(p1["s59_a16_regime_delta_q"], {"num": -30, "den": 1})
        self.assertEqual(p1["s59_a16_matched_kl_ratio_q"], {"num": 293, "den": 77})
        self.assertEqual(p1["s73_vs_s73b_lowbit_amplification_dec"], "2.70")
        self.assertEqual(p1["s28_adm_null_witness_q"], {"num": -13489, "den": 512})
        self.assertEqual(p1["s33_hopf_inertia_flip"]["before"], [4, 0, 0])
        self.assertEqual(p1["s33_hopf_inertia_flip"]["after"], [2, 0, 2])
        self.assertEqual(p1["s34_rosen_cusp_roots"], {"positive_a_root_count": 1, "negative_a_root_count": 3})
        l5a = p1["law5_three_regime_obstruction"]
        self.assertEqual(l5a["strictly_euclidean_2x2"]["det_q"], {"num": 3, "den": 1})
        self.assertEqual(l5a["degenerate_rank1_2x2"]["det_q"], {"num": 0, "den": 1})
        self.assertEqual(l5a["strictly_cat0_s75_2x2"]["det_q"], {"num": -1, "den": 4})
        self.assertEqual(l5a["s81_r3_gram4_det_q"], {"num": 0, "den": 1})
        self.assertEqual(l5a["s81_r3_gram3_minor_det_q"], {"num": 1, "den": 1})
        self.assertTrue(l5a["naive_isometry_blocked"])

        # Pillar 2: Meta-Convergence B
        p2 = p["pillar2_meta_b_grafting_proxy_blindness"]
        self.assertTrue(p2["pillar_verified"])
        self.assertEqual(p2["ambient_dimension_lift"]["combined_norm_sq_q"], {"num": 15, "den": 1})
        self.assertEqual(p2["s31_iso_mdl_concentration_q"], {"num": 75968, "den": 1})
        self.assertEqual(p2["s31_selective_omission_ratio_q"], {"num": 116686848, "den": 1133})
        self.assertEqual(p2["s50_zero_dw_transport"]["margin_delta_q"], {"num": -133, "den": 25})
        self.assertEqual(p2["s50_zero_dw_transport"]["delta_s_frob_norm_sq_q"], {"num": 212, "den": 5})
        self.assertEqual(p2["s50_zero_dw_transport"]["yield_wall_advection_after"], 4)
        self.assertEqual(p2["s77_mellin_granite_gamma_nl_sq_q"], {"num": 128, "den": 185})
        self.assertEqual(p2["s77_mellin_active_push_exact"], 10710)
        self.assertEqual(p2["s77_wsp_cs08_all_delta_q"], {"num": 31, "den": 422})
        self.assertEqual(p2["s77_wsp_cs08_finished_delta_q"], {"num": -43, "den": 327})
        self.assertEqual(p2["s81_portal77_kyfan_ppl_width_wall_q"], {"num": 8714, "den": 5})
        self.assertEqual(p2["s81_motifbench_group3"]["k3_holonomy_dof"], 12)
        self.assertEqual(p2["s81_motifbench_group3"]["orphan_drop_dec"], "9.4223")
        s81_ppv = p2["s81_motifbench_group3"]["dual_oracle_bayes_ppv"]
        self.assertEqual(s81_ppv["single_ppv_q"], {"num": 4, "den": 23})
        self.assertEqual(s81_ppv["dual_ppv_q"], {"num": 32, "den": 51})
        self.assertEqual(s81_ppv["ppv_gain_q"], {"num": 532, "den": 1173})
        self.assertEqual(s81_ppv["ppv_amplification_ratio_q"], {"num": 184, "den": 51})
        self.assertFalse(p2["law5_redundant_oracle_obstruction"]["collinear_second_oracle"]["strict_amplification"])

        # Pillar 3: Meta-Convergence C
        p3 = p["pillar3_meta_c_f2_three_wall_fracture"]
        self.assertTrue(p3["pillar_verified"])
        self.assertEqual(p3["wall1_carry_obstruction"]["s22c_f2x_odd_polys_deg2_to_24"], 8388607)
        self.assertEqual(p3["wall1_carry_obstruction"]["s41_polya_valid_sign_flips"], 0)
        self.assertEqual(p3["wall1_carry_obstruction"]["s41_praxis_sos_det_q"], {"num": 68, "den": 1})
        w2 = p3["wall2_non_orthogonality_obstruction"]
        self.assertEqual(w2["s82_cnot_circuits_verified"], 184)
        self.assertEqual(w2["shear_gram_trace_q"], {"num": 3, "den": 1})
        self.assertLess(w2["charpoly_at_lo_q"]["num"], 0)
        self.assertGreater(w2["charpoly_at_hi_q"]["num"], 0)
        self.assertTrue(w2["s59_hadamard_q4_exact_orthogonal"])
        w3 = p3["wall3_boundary_offload_obstruction"]
        self.assertTrue(w3["s54_cs21_mirage"]["mirage_detected"])
        self.assertEqual(w3["s54_cs21_mirage"]["true_net_ratio_q"], {"num": 600, "den": 401})
        self.assertTrue(w3["s54_cs21_genuine_uncompute"]["genuine_net_improvement"])
        self.assertEqual(w3["s54_cs21_genuine_uncompute"]["true_net_ratio_q"], {"num": 102, "den": 401})

        # Pillar 4: Meta-Convergence D
        p4 = p["pillar4_meta_d_ceer_closed_loop_fixed_point"]
        self.assertTrue(p4["pillar_verified"])
        self.assertEqual(p4["s76_g_loop_det_q"], {"num": 599, "den": 360})
        self.assertEqual(p4["s83_edge_retention_q"], {"num": 3, "den": 4})
        self.assertEqual(p4["s83_triangle_retention_q"], {"num": 5, "den": 8})
        self.assertEqual(p4["s80_songe_20night_fwer_dec"], "0.8715")
        self.assertTrue(p4["certified_five_gate_fixed_point"]["all_five_gates_pass"])
        self.assertEqual(p4["certified_five_gate_fixed_point"]["error_after_steps_q"], {"num": 1, "den": 256})
        self.assertTrue(p4["all_five_ablations_rejected"])
        self.assertEqual(len(p4["borromean_five_gate_ablations"]), 5)
        for ab in p4["borromean_five_gate_ablations"].values():
            self.assertFalse(ab["all_five_gates_pass"])

        # Pillar 5: Provenance & Lean 4
        p5 = p["pillar5_corpus_provenance_and_lean4"]
        self.assertEqual(p5["upstream_corpus_count"], 24)
        self.assertEqual(len(p5["upstream_cert_manifest"]), 24)
        self.assertEqual(p5["lean4_certificate"]["theorem_count"], 20)
        self.assertEqual(p5["lean4_certificate"]["sha256"], s87.LEAN_FILE_SHA256)
        self.assertEqual(p5["novelty_honesty_law4"]["novelty_tier"], "N1")
        self.assertEqual(p5["novelty_honesty_law4"]["n2_claims"], 0)


class TestS87VerifierZoneBAndIO(unittest.TestCase):
    def test_json_tree_and_parser_hardening(self) -> None:
        ver.validate_json_tree_iterative({"a": [1, True, None, "ok", (1 << 2048) - 1]}, max_depth=256)
        ver.validate_json_tree_iterative(1, max_depth=1)
        ver.validate_json_tree_iterative([[1]], max_depth=2)
        for bad_depth in (0, 257, True):
            with self.assertRaises(s87.S87Error) as cd:
                ver.validate_json_tree_iterative({}, max_depth=bad_depth)  # type: ignore[arg-type]
            self.assertEqual(cd.exception.code, "INVALID_MAX_DEPTH")
        with self.assertRaises(s87.S87Error) as cdep:
            ver.validate_json_tree_iterative([[[1]]], max_depth=2)
        self.assertEqual(cdep.exception.code, "JSON_DEPTH_EXCEEDED")
        with self.assertRaises(s87.S87Error) as cnk:
            ver.validate_json_tree_iterative({1: "a"})
        self.assertEqual(cnk.exception.code, "NON_STR_KEY")
        with self.assertRaises(s87.S87Error) as csk:
            ver.validate_json_tree_iterative({"\ud800": "a"})
        self.assertEqual(csk.exception.code, "INVALID_UNICODE_STR")
        with self.assertRaises(s87.S87Error) as csv:
            ver.validate_json_tree_iterative({"a": "\ud800"})
        self.assertEqual(csv.exception.code, "INVALID_UNICODE_STR")
        with self.assertRaises(s87.S87Error) as cbi:
            ver.validate_json_tree_iterative(1 << 2048)
        self.assertEqual(cbi.exception.code, "INT_BIT_LIMIT")
        with self.assertRaises(s87.S87Error) as cft:
            ver.validate_json_tree_iterative((1, 2))
        self.assertEqual(cft.exception.code, "FORBIDDEN_JSON_TYPE")

        class IntSub(int):
            pass

        with self.assertRaises(s87.S87Error) as cis:
            ver.validate_json_tree_iterative(IntSub(5))
        self.assertEqual(cis.exception.code, "FORBIDDEN_JSON_TYPE")

        max_2048 = (1 << 2048) - 1
        self.assertEqual(len(str(max_2048)), ver.MAX_INT_DIGITS)
        self.assertEqual(ver._parse_capped_int_token(str(max_2048)), max_2048)
        with self.assertRaises(s87.S87Error) as tok_bit:
            ver._parse_capped_int_token(str(1 << 2048))
        self.assertEqual(tok_bit.exception.code, "INT_BIT_LIMIT")
        with self.assertRaises(s87.S87Error) as tok_dig:
            ver._parse_capped_int_token("9" * (ver.MAX_INT_DIGITS + 1))
        self.assertEqual(tok_dig.exception.code, "INT_DIGIT_LIMIT")

        self.assertEqual(ver.parse_strict_json('{"x":-42,"y":[true,null,"z"]}'), {"x": -42, "y": [True, None, "z"]})
        exact_max_json = '"' + ("a" * (ver.MAX_JSON_BYTES - 2)) + '"'
        self.assertEqual(len(ver.parse_strict_json(exact_max_json)), ver.MAX_JSON_BYTES - 2)
        with self.assertRaises(s87.S87Error) as cp1:
            ver.parse_strict_json(b"{}")  # type: ignore[arg-type]
        self.assertEqual(cp1.exception.code, "INVALID_JSON_TEXT")
        with self.assertRaises(s87.S87Error) as cp2:
            ver.parse_strict_json('"\ud800"')
        self.assertEqual(cp2.exception.code, "INVALID_UNICODE_STR")
        with self.assertRaises(s87.S87Error) as cp3:
            ver.parse_strict_json('"' + ("a" * (ver.MAX_JSON_BYTES + 1)) + '"')
        self.assertEqual(cp3.exception.code, "JSON_TOO_LARGE")
        with self.assertRaises(s87.S87Error) as cp4:
            ver.parse_strict_json('{"a":1,"\\u0061":2}')
        self.assertEqual(cp4.exception.code, "DUPLICATE_JSON_KEY")
        with self.assertRaises(s87.S87Error) as cp5:
            ver.parse_strict_json('{"a":1.0}')
        self.assertEqual(cp5.exception.code, "FLOAT_FORBIDDEN")
        with self.assertRaises(s87.S87Error) as cp6:
            ver.parse_strict_json('{"a":NaN}')
        self.assertEqual(cp6.exception.code, "NONFINITE_CONSTANT")
        with self.assertRaises(s87.S87Error) as cp7:
            ver.parse_strict_json('{"a":' + ("9" * 5001) + "}")
        self.assertEqual(cp7.exception.code, "INT_DIGIT_LIMIT")
        with self.assertRaises(s87.S87Error) as cp7b:
            ver.parse_strict_json('{"a":-' + ("9" * (ver.MAX_INT_DIGITS + 1)) + "}")
        self.assertEqual(cp7b.exception.code, "INT_DIGIT_LIMIT")
        with self.assertRaises(s87.S87Error) as cp8:
            ver.parse_strict_json('{"a":' + str(1 << 2048) + "}")
        self.assertEqual(cp8.exception.code, "INT_BIT_LIMIT")
        with self.assertRaises(s87.S87Error) as cp9:
            ver.parse_strict_json("{broken")
        self.assertEqual(cp9.exception.code, "JSON_DECODE_ERROR")
        with self.assertRaises(s87.S87Error) as cp10:
            ver.parse_strict_json("[" * 500 + "]" * 500)
        self.assertIn(cp10.exception.code, ("JSON_DEPTH_EXCEEDED", "JSON_DECODE_ERROR"))

    def test_digest_exact_equal_and_four_surfaces(self) -> None:
        good_h = "0123456789abcdef" * 4
        self.assertEqual(ver.require_sha256_hex(good_h, "h"), good_h)
        with self.assertRaises(s87.S87Error) as d1:
            ver.require_sha256_hex(123, "h")
        self.assertEqual(d1.exception.code, "INVALID_DIGEST_TYPE")
        with self.assertRaises(s87.S87Error) as d2:
            ver.require_sha256_hex("a" * 63, "h")
        self.assertEqual(d2.exception.code, "INVALID_DIGEST_LEN")
        with self.assertRaises(s87.S87Error) as d3:
            ver.require_sha256_hex("A" * 64, "h")
        self.assertEqual(d3.exception.code, "INVALID_DIGEST_HEX")
        with self.assertRaises(s87.S87Error) as d4:
            ver.require_sha256_hex("\u00e9" * 64, "h")
        self.assertEqual(d4.exception.code, "INVALID_DIGEST_HEX")

        self.assertTrue(ver.exact_typed_equal({"a": [1, True, None]}, {"a": [1, True, None]}))
        self.assertFalse(ver.exact_typed_equal(1, True))
        self.assertFalse(ver.exact_typed_equal({"a": 1}, {"a": 1, "b": 2}))
        self.assertFalse(ver.exact_typed_equal({"a": 1}, {"b": 1}))
        self.assertFalse(ver.exact_typed_equal([1, 2], [1]))
        self.assertFalse(ver.exact_typed_equal([1, 2], [1, 3]))
        self.assertFalse(ver.exact_typed_equal("x", "y"))

        cert = s87.build_certificate()
        self.assertEqual(ver.audit_certificate_object(cert)["certificate_sha256"], cert["certificate_sha256"])

        with self.assertRaises(s87.S87Error) as a0:
            ver.audit_certificate_object([1, 2])
        self.assertEqual(a0.exception.code, "NON_OBJECT_ROOT")
        c_keys = copy.deepcopy(cert)
        c_keys["extra"] = 1
        with self.assertRaises(s87.S87Error) as a1:
            ver.audit_certificate_object(c_keys)
        self.assertEqual(a1.exception.code, "BAD_CERT_KEYS")
        c_sch = copy.deepcopy(cert)
        c_sch["schema"] = "wrong"
        with self.assertRaises(s87.S87Error) as a2:
            ver.audit_certificate_object(c_sch)
        self.assertEqual(a2.exception.code, "BAD_SCHEMA")
        c_tid = copy.deepcopy(cert)
        c_tid["track_id"] = "wrong"
        with self.assertRaises(s87.S87Error) as a3:
            ver.audit_certificate_object(c_tid)
        self.assertEqual(a3.exception.code, "BAD_TRACK_ID")
        c_pt = copy.deepcopy(cert)
        c_pt["payload"] = []
        with self.assertRaises(s87.S87Error) as a4:
            ver.audit_certificate_object(c_pt)
        self.assertEqual(a4.exception.code, "BAD_PAYLOAD_TYPE")
        c_psha = copy.deepcopy(cert)
        c_psha["payload_sha256"] = "0" * 64
        with self.assertRaises(s87.S87Error) as a5:
            ver.audit_certificate_object(c_psha)
        self.assertEqual(a5.exception.code, "PAYLOAD_SHA_MISMATCH")
        c_csha = copy.deepcopy(cert)
        c_csha["certificate_sha256"] = "0" * 64
        with self.assertRaises(s87.S87Error) as a6:
            ver.audit_certificate_object(c_csha)
        self.assertEqual(a6.exception.code, "CERT_SHA_MISMATCH")

        # Direct verify_certificate_dict FR1/FR0 and secondary_audit_payload tests
        self.assertEqual(ver.verify_certificate_dict(cert, full_replay=False)["certificate_sha256"], cert["certificate_sha256"])
        with self.assertRaises(s87.S87Error) as fr_bad:
            ver.verify_certificate_dict(cert, full_replay=1)  # type: ignore[arg-type]
        self.assertEqual(fr_bad.exception.code, "INVALID_FULL_REPLAY")
        self.assertIs(ver.secondary_audit_payload(cert["payload"]), cert["payload"])
        with self.assertRaises(s87.S87Error) as sec_nd:
            ver.secondary_audit_payload([1, 2])
        self.assertEqual(sec_nd.exception.code, "BAD_PAYLOAD_TYPE")

        # Strict rational dict rejections (incl. AUDIT-187 S87-F1 extra-key / missing-key smuggle)
        for bad_rat in (
            123,
            {"num": 0, "den": 0, "extra": 1},
            {"num": 0, "other": 1},
            {"other": 0, "den": 1},
            {"num": True, "den": 1},
            {"num": 1, "den": True},
            {"num": 1, "den": 0},
            {"num": 1, "den": -1},
            {"num": 4, "den": 2},
        ):
            with self.assertRaises(s87.S87Error) as e_rat:
                ver._parse_rat_dict(bad_rat)
            self.assertEqual(e_rat.exception.code, "BAD_RATIONAL_DICT")
            for target_pillar, target_field in (
                ("pillar1_meta_a_competing_potential", "s59_e8_regime_delta_q"),
                ("pillar2_meta_b_grafting_proxy_blindness", "s31_iso_mdl_concentration_q"),
            ):
                if target_field == "s31_iso_mdl_concentration_q" and bad_rat == 123:
                    continue
                c_rat = copy.deepcopy(cert)
                c_rat["payload"][target_pillar][target_field] = bad_rat
                for surface_fn in (
                    lambda c: ver.secondary_audit_payload(c["payload"]),
                    lambda c: ver.verify_certificate_dict(_resign(c), full_replay=False),
                    lambda c: ver.verify_certificate_dict(_resign(c), full_replay=True),
                ):
                    with self.assertRaises(s87.S87Error) as e_r2:
                        surface_fn(c_rat)
                    self.assertIn(e_r2.exception.code, ("BAD_RATIONAL_DICT", "UNEXPECTED_BOOL_FIELD"))

        c_bool_fld = copy.deepcopy(cert)
        c_bool_fld["payload"]["pillar3_meta_c_f2_three_wall_fracture"]["wall1_carry_obstruction"]["s22c_odd_perfects_found"] = True
        with self.assertRaises(s87.S87Error) as a7f:
            ver.secondary_audit_payload(c_bool_fld["payload"])
        self.assertEqual(a7f.exception.code, "UNEXPECTED_BOOL_FIELD")
        c_bool_lst = copy.deepcopy(cert)
        c_bool_lst["payload"]["pillar1_meta_a_competing_potential"]["s33_hopf_inertia_flip"]["before"][0] = True
        with self.assertRaises(s87.S87Error) as a7l:
            ver.secondary_audit_payload(c_bool_lst["payload"])
        self.assertEqual(a7l.exception.code, "UNEXPECTED_BOOL_ITEM")
        c_bad_pin = copy.deepcopy(cert)
        c_bad_pin["payload"]["pillar5_corpus_provenance_and_lean4"]["upstream_cert_manifest"][0]["sha256"] = "Z" * 64
        with self.assertRaises(s87.S87Error) as a7s:
            ver.secondary_audit_payload(c_bad_pin["payload"])
        self.assertEqual(a7s.exception.code, "INVALID_DIGEST_HEX")

        # Direct _req_int, _req_dict, _audit_sylvester_entry vec boundary probes
        with self.assertRaises(s87.S87Error):
            ver._req_int("not_int", "BAD_INT")
        with self.assertRaises(s87.S87Error):
            ver._req_dict([], frozenset({"a"}), "BAD_D")
        with self.assertRaises(s87.S87Error):
            ver._req_dict({"b": 1}, frozenset({"a"}), "BAD_D")
        for bad_vec in ("notlist", "ab", [{"num": 1, "den": 1}]):
            cand_v = copy.deepcopy(cert["payload"])
            cand_v["pillar1_meta_a_competing_potential"]["law5_three_regime_obstruction"]["strictly_euclidean_2x2"]["witness_vec_q"] = bad_vec
            with self.assertRaises(s87.S87Error) as e_sv:
                ver.secondary_audit_payload(cand_v)
            self.assertEqual(e_sv.exception.code, "BAD_SYLVESTER_VEC")

        # AUDIT-187 S87-F1: ALL 7/7 live re-signed semantic forgeries MUST FAIL on SEC, FR0, AND FR1!
        semantic_tampers: list[tuple[str, Any, str]] = [
            (
                "empty_pillars_1_to_4",
                lambda d: d.update(
                    {
                        "pillar1_meta_a_competing_potential": {},
                        "pillar2_meta_b_grafting_proxy_blindness": {},
                        "pillar3_meta_c_f2_three_wall_fracture": {},
                        "pillar4_meta_d_ceer_closed_loop_fixed_point": {},
                    }
                ),
                "BAD_P1_SCHEMA",
            ),
            (
                "hollow_p1_non_dict",
                lambda d: d.__setitem__("pillar1_meta_a_competing_potential", "HOLLOWED"),
                "BAD_P1_SCHEMA",
            ),
            (
                "flipped_p1_verified",
                lambda d: d["pillar1_meta_a_competing_potential"].__setitem__("pillar_verified", False),
                "BAD_P1_INV",
            ),
            (
                "flipped_p2_verified",
                lambda d: d["pillar2_meta_b_grafting_proxy_blindness"].__setitem__("pillar_verified", False),
                "BAD_P2_INV",
            ),
            (
                "flipped_p3_verified",
                lambda d: d["pillar3_meta_c_f2_three_wall_fracture"].__setitem__("pillar_verified", False),
                "BAD_P3_INV",
            ),
            (
                "flipped_p4_gates_and_ablations",
                lambda d: (
                    d["pillar4_meta_d_ceer_closed_loop_fixed_point"].__setitem__("all_five_ablations_rejected", False),
                    d["pillar4_meta_d_ceer_closed_loop_fixed_point"]["certified_five_gate_fixed_point"].__setitem__("all_five_gates_pass", False),
                ),
                "BAD_P4_INV",
            ),
            (
                "falsified_cat0_det",
                lambda d: d["pillar1_meta_a_competing_potential"]["law5_three_regime_obstruction"]["strictly_cat0_s75_2x2"].__setitem__("det_q", {"num": 999, "den": 1}),
                "BAD_SYLVESTER_INV",
            ),
            (
                "falsified_ppv_amp",
                lambda d: d["pillar2_meta_b_grafting_proxy_blindness"]["s81_motifbench_group3"]["dual_oracle_bayes_ppv"].__setitem__("ppv_amplification_ratio_q", {"num": 1, "den": 1}),
                "BAD_PPV_INV",
            ),
            (
                "falsified_carry_sum",
                lambda d: d["pillar3_meta_c_f2_three_wall_fracture"]["wall1_carry_obstruction"]["active_carry_witness"].__setitem__("z_integer_sum", 10),
                "BAD_CARRY_INV",
            ),
            (
                "falsified_cs21_mirage",
                lambda d: d["pillar3_meta_c_f2_three_wall_fracture"]["wall3_boundary_offload_obstruction"]["s54_cs21_mirage"].__setitem__("mirage_detected", False),
                "BAD_CS21_INV",
            ),
            (
                "falsified_ablation_target",
                lambda d: d["pillar4_meta_d_ceer_closed_loop_fixed_point"]["borromean_five_gate_ablations"]["ablate_g1_contraction_s76"].__setitem__("gate1_loop_schur_contractive", True),
                "BAD_P4_INV",
            ),
            (
                "corrupt_upstream_manifest_ints",
                lambda d: d["pillar5_corpus_provenance_and_lean4"].__setitem__("upstream_cert_manifest", list(range(24))),
                "BAD_MANIFEST_ENTRY",
            ),
            (
                "bad_manifest_pin_sha",
                lambda d: d["pillar5_corpus_provenance_and_lean4"]["upstream_cert_manifest"][0].__setitem__("sha256", "0" * 64),
                "BAD_MANIFEST_PIN",
            ),
            (
                "bad_corpus_count",
                lambda d: d["pillar5_corpus_provenance_and_lean4"].__setitem__("upstream_corpus_count", 23),
                "BAD_CORPUS_COUNT",
            ),
            (
                "bad_manifest_non_list",
                lambda d: d["pillar5_corpus_provenance_and_lean4"].__setitem__("upstream_cert_manifest", "x" * 24),
                "BAD_MANIFEST_LIST",
            ),
            (
                "bad_manifest_len",
                lambda d: d["pillar5_corpus_provenance_and_lean4"]["upstream_cert_manifest"].pop(),
                "BAD_MANIFEST_LIST",
            ),
            (
                "falsified_novelty_tier_N2",
                lambda d: (
                    d["pillar5_corpus_provenance_and_lean4"]["novelty_honesty_law4"].__setitem__("novelty_tier", "N2"),
                    d["pillar5_corpus_provenance_and_lean4"]["novelty_honesty_law4"].__setitem__("n1_exact_synthesis_verified", False),
                ),
                "BAD_NOVELTY_CLAIMS",
            ),
            (
                "corrupt_lean4_theorems_and_axioms",
                lambda d: (
                    d["pillar5_corpus_provenance_and_lean4"]["lean4_certificate"].__setitem__("theorems", []),
                    d["pillar5_corpus_provenance_and_lean4"]["lean4_certificate"].__setitem__("allowed_axioms", ["sorryAx"]),
                ),
                "BAD_THEOREM_LIST",
            ),
            (
                "corrupt_lean4_axioms_only",
                lambda d: d["pillar5_corpus_provenance_and_lean4"]["lean4_certificate"].__setitem__("allowed_axioms", ["sorryAx"]),
                "BAD_ALLOWED_AXIOMS",
            ),
            (
                "bad_lean4_cert_type",
                lambda d: d["pillar5_corpus_provenance_and_lean4"].__setitem__("lean4_certificate", []),
                "BAD_LEAN_CERT_SCHEMA",
            ),
            (
                "bad_lean4_thm_count",
                lambda d: d["pillar5_corpus_provenance_and_lean4"]["lean4_certificate"].__setitem__("theorem_count", 19),
                "BAD_THEOREM_COUNT",
            ),
            (
                "bad_lean4_sha",
                lambda d: d["pillar5_corpus_provenance_and_lean4"]["lean4_certificate"].__setitem__("sha256", "0" * 64),
                "BAD_LEAN_PIN",
            ),
            (
                "bad_novelty_schema",
                lambda d: d["pillar5_corpus_provenance_and_lean4"].__setitem__("novelty_honesty_law4", []),
                "BAD_NOVELTY_SCHEMA",
            ),
            (
                "bad_n2_claims",
                lambda d: d["pillar5_corpus_provenance_and_lean4"]["novelty_honesty_law4"].__setitem__("n2_claims", 1),
                "BAD_NOVELTY_CLAIMS",
            ),
        ]
        for label, mut_fn, exp_code in semantic_tampers:
            cand_c = copy.deepcopy(cert)
            mut_fn(cand_c["payload"])
            with self.assertRaises(s87.S87Error, msg=f"SEC must reject {label}") as e_s:
                ver.secondary_audit_payload(cand_c["payload"])
            self.assertEqual(e_s.exception.code, exp_code, f"SEC code for {label}")
            resigned = _resign(cand_c)
            with self.assertRaises(s87.S87Error, msg=f"FR0 must reject {label}") as e_f0:
                ver.verify_certificate_dict(resigned, full_replay=False)
            self.assertEqual(e_f0.exception.code, exp_code, f"FR0 code for {label}")
            with self.assertRaises(s87.S87Error, msg=f"FR1 must reject {label}") as e_f1:
                ver.verify_certificate_dict(resigned, full_replay=True)
            self.assertEqual(e_f1.exception.code, exp_code, f"FR1 code for {label}")

        c_hollow = copy.deepcopy(cert)
        c_hollow["payload"] = {}
        with self.assertRaises(s87.S87Error) as a8:
            ver.audit_certificate_object(_resign(c_hollow))
        self.assertEqual(a8.exception.code, "BAD_PAYLOAD_KEYS")

        # Re-signed valid-schema tampered value passes FR0 but fails FR1 oracle replay
        c_tamp = copy.deepcopy(cert)
        c_tamp["payload"]["pillar4_meta_d_ceer_closed_loop_fixed_point"]["s80_ratchet_clean_outside_accepts"] = 6
        c_tamp_signed = _resign(c_tamp)
        self.assertEqual(
            ver.verify_certificate_dict(c_tamp_signed, full_replay=False)["certificate_sha256"],
            c_tamp_signed["certificate_sha256"],
        )
        with self.assertRaises(s87.S87Error) as a8r:
            ver.verify_certificate_dict(c_tamp_signed, full_replay=True)
        self.assertEqual(a8r.exception.code, "PAYLOAD_ORACLE_MISMATCH")

        fake_exp = copy.deepcopy(cert)
        fake_exp["certificate_sha256"] = "f" * 64
        with mock.patch.object(ver, "build_certificate", return_value=fake_exp):
            with self.assertRaises(s87.S87Error) as a9:
                ver.audit_certificate_object(cert)
            self.assertEqual(a9.exception.code, "ORACLE_CERT_SHA_MISMATCH")

    def test_committed_disk_cert_upstream_manifest_and_hardened_io(self) -> None:
        disk_cert = _SCRIPT_DIR / "s87_higher_order_atlas_certificate.json"
        mode = stat.S_IMODE(disk_cert.stat().st_mode)
        self.assertIn(mode, (0o600, 0o644))
        checked = ver.check_certificate_file(disk_cert)

        out_buf = io.BytesIO()
        with mock.patch.object(sys, "stdout", type("FakeOut", (), {"buffer": out_buf})()):
            rc = ver.main(["--standalone", "--json"])
        self.assertEqual(rc, 0)
        self.assertEqual(out_buf.getvalue(), disk_cert.read_bytes())
        out_buf2 = io.BytesIO()
        with mock.patch.object(sys, "stdout", type("FakeOut", (), {"buffer": out_buf2})()):
            rc2 = ver.main([])
        self.assertEqual(rc2, 0)
        self.assertEqual(out_buf2.getvalue(), disk_cert.read_bytes())

        chk_buf = io.BytesIO()
        with mock.patch.object(sys, "stdout", type("FakeOut", (), {"buffer": chk_buf})()):
            rc = ver.main(["--check", str(disk_cert), "--json"])
        self.assertEqual(rc, 0)
        self.assertEqual(json.loads(chk_buf.getvalue().decode("utf-8"))["status"], "PASS")
        self.assertEqual(ver.main(["--check", str(disk_cert)]), 0)

        with tempfile.TemporaryDirectory(prefix="s87_io_") as td:
            tdir = Path(td).resolve()
            out_p = tdir / "cert_out.json"
            old_umask = os.umask(0o022)
            try:
                w_buf = io.BytesIO()
                with mock.patch.object(sys, "stdout", type("FakeOut", (), {"buffer": w_buf})()):
                    rc_w = ver.main(["--write", str(out_p), "--json"])
                self.assertEqual(rc_w, 0)
                self.assertEqual(json.loads(w_buf.getvalue().decode("utf-8"))["status"], "WRITTEN")
                self.assertEqual(stat.S_IMODE(out_p.stat().st_mode), 0o600)
                self.assertEqual(ver.main(["--write", str(out_p)]), 0)
                self.assertEqual(out_p.read_bytes(), disk_cert.read_bytes())
            finally:
                os.umask(old_umask)

            # Verify --verify-upstream with synthetic matching & tampered roots (works in isolated CI!)
            fake_root = tdir / "exp_root"
            fake_root.mkdir()
            fake_bytes = b'{"ok":true}\n'
            fake_sha = hashlib.sha256(fake_bytes).hexdigest()
            fake_manifest = (("S1", "t1/c1.json", fake_sha),)
            (fake_root / "t1").mkdir()
            (fake_root / "t1" / "c1.json").write_bytes(fake_bytes)
            with mock.patch.object(ver, "UPSTREAM_CERT_MANIFEST", fake_manifest):
                up_buf = io.BytesIO()
                with mock.patch.object(sys, "stdout", type("FakeOut", (), {"buffer": up_buf})()):
                    rc_u = ver.main(["--verify-upstream", str(fake_root), "--json"])
                self.assertEqual(rc_u, 0)
                self.assertEqual(json.loads(up_buf.getvalue().decode("utf-8"))["tracks_verified"], 1)
                self.assertEqual(ver.main(["--verify-upstream", str(fake_root)]), 0)
                (fake_root / "t1" / "c1.json").write_bytes(b'{"ok":false}\n')
                with self.assertRaises(s87.S87Error) as e_up:
                    ver.verify_upstream_manifest(fake_root)
                self.assertEqual(e_up.exception.code, "UPSTREAM_SHA_MISMATCH")

            # Reject bad path types, surrogate, NUL, root/.. paths
            with self.assertRaises(s87.S87Error) as p0:
                ver.read_regular_file_bytes("not_a_path")  # type: ignore[arg-type]
            self.assertEqual(p0.exception.code, "INVALID_PATH_TYPE")
            with self.assertRaises(s87.S87Error) as p1:
                ver.read_regular_file_bytes(Path(str(tdir) + "/\ud800"))
            self.assertEqual(p1.exception.code, "INVALID_UNICODE_STR")
            with self.assertRaises(s87.S87Error) as p2:
                ver.read_regular_file_bytes(Path(str(tdir) + "/a\x00b"))
            self.assertEqual(p2.exception.code, "INVALID_PATH_NUL")
            with self.assertRaises(s87.S87Error) as p3:
                ver.read_regular_file_bytes(Path("/"))
            self.assertEqual(p3.exception.code, "INVALID_PATH")
            with self.assertRaises(s87.S87Error) as p4:
                ver.read_regular_file_bytes(tdir / "..")
            self.assertEqual(p4.exception.code, "INVALID_PATH")

            with self.assertRaises(s87.S87Error) as p5:
                ver.check_certificate_file(tdir / "no_dir" / "x.json")
            self.assertEqual(p5.exception.code, "PARENT_DIR_ERROR")
            with self.assertRaises(s87.S87Error) as p6:
                ver.check_certificate_file(tdir / "missing.json")
            self.assertEqual(p6.exception.code, "FILE_READ_ERROR")
            with self.assertRaises(s87.S87Error) as p7:
                ver.check_certificate_file(tdir)
            self.assertEqual(p7.exception.code, "NOT_REGULAR_FILE")

            sym_f = tdir / "sym.json"
            sym_f.symlink_to(out_p)
            with self.assertRaises(s87.S87Error) as p8:
                ver.check_certificate_file(sym_f)
            self.assertEqual(p8.exception.code, "SYMLINK_FORBIDDEN")
            with self.assertRaises(s87.S87Error) as p8w:
                ver.write_atomic_0600_bytes(sym_f, b"{}\n")
            self.assertEqual(p8w.exception.code, "SYMLINK_FORBIDDEN")

            sub_d = tdir / "real_sub"
            sub_d.mkdir()
            (sub_d / "c.json").write_bytes(disk_cert.read_bytes())
            sym_d = tdir / "sym_sub"
            sym_d.symlink_to(sub_d)
            with self.assertRaises(s87.S87Error) as p9:
                ver.check_certificate_file(sym_d / "c.json")
            self.assertEqual(p9.exception.code, "SYMLINK_ANCESTOR_FORBIDDEN")

            with mock.patch.object(ver.os, "environ", {}):
                ver._check_pwd_no_symlinks()
            with mock.patch.object(ver.os, "environ", {"PWD": "x" + str(sym_d)}):
                ver._check_pwd_no_symlinks()
            with mock.patch.object(ver.os, "environ", {"PWD": str(sym_d)}):
                with self.assertRaises(s87.S87Error) as p9p:
                    ver._check_pwd_no_symlinks()
                self.assertEqual(p9p.exception.code, "SYMLINK_ANCESTOR_FORBIDDEN")
            with mock.patch.object(ver.os, "environ", {"PWD": "/tmp/\ud800"}):
                with self.assertRaises(s87.S87Error) as p9s:
                    ver.read_regular_file_bytes(Path("c.json"))
                self.assertEqual(p9s.exception.code, "INVALID_UNICODE_STR")
            with mock.patch.dict(os.environ, {"PWD": "/nonexistent_s87_pwd_xyz"}):
                with self.assertRaises(s87.S87Error):
                    ver.read_regular_file_bytes(Path("definitely_missing_s87_rel.json"))

            fifo_p = tdir / "pipe.fifo"
            os.mkfifo(fifo_p)
            with self.assertRaises(s87.S87Error) as pf:
                ver.check_certificate_file(fifo_p)
            self.assertEqual(pf.exception.code, "NOT_REGULAR_FILE")
            with self.assertRaises(s87.S87Error) as pfw:
                ver.write_atomic_0600_bytes(fifo_p, b"{}\n")
            self.assertEqual(pfw.exception.code, "NOT_REGULAR_FILE")

            hl_p = tdir / "hardlink.json"
            os.link(out_p, hl_p)
            with self.assertRaises(s87.S87Error) as ph1:
                ver.check_certificate_file(hl_p)
            self.assertEqual(ph1.exception.code, "HARDLINK_FORBIDDEN")
            with self.assertRaises(s87.S87Error) as ph2:
                ver.write_atomic_0600_bytes(hl_p, b"{}\n")
            self.assertEqual(ph2.exception.code, "HARDLINK_FORBIDDEN")
            hl_p.unlink()

            ro_dir = tdir / "ro_dir"
            ro_dir.mkdir()
            ro_dir.chmod(0o500)
            try:
                with self.assertRaises(s87.S87Error) as pro:
                    ver.write_atomic_0600_bytes(ro_dir / "x.json", b"{}\n")
                self.assertEqual(pro.exception.code, "FILE_WRITE_ERROR")
            finally:
                ro_dir.chmod(0o700)

            crlf_p = tdir / "crlf.json"
            crlf_p.write_bytes(disk_cert.read_bytes().replace(b"\n", b"\r\n"))
            with self.assertRaises(s87.S87Error) as pcrlf:
                ver.check_certificate_file(crlf_p)
            self.assertEqual(pcrlf.exception.code, "CRLF_FORBIDDEN")

            badu_p = tdir / "badutf8.json"
            badu_p.write_bytes(b"\xff\xfe")
            with self.assertRaises(s87.S87Error) as pbu:
                ver.check_certificate_file(badu_p)
            self.assertEqual(pbu.exception.code, "INVALID_UTF8")

            pretty_p = tdir / "pretty.json"
            pretty_p.write_text(json.dumps(checked, indent=2) + "\n", encoding="utf-8")
            with self.assertRaises(s87.S87Error) as ppr:
                ver.check_certificate_file(pretty_p)
            self.assertEqual(ppr.exception.code, "NONCANONICAL_BYTES")

            dfd_chk = os.open(tdir, os.O_RDONLY | os.O_DIRECTORY)
            try:
                self.assertIs(ver._is_symlink_at(dfd_chk, "no_such_entry"), False)
                self.assertIs(ver._is_symlink_at(dfd_chk, "sym.json"), True)
            finally:
                os.close(dfd_chk)

            big_p = tdir / "big.json"
            big_p.write_bytes(b"a" * 32)
            self.assertEqual(ver.read_regular_file_bytes(big_p, max_bytes=32), b"a" * 32)
            big_p.write_bytes(b"a" * 64)
            with mock.patch.object(os, "read", return_value=b""):
                with self.assertRaises(s87.S87Error) as pbig:
                    ver.read_regular_file_bytes(big_p, max_bytes=32)
                self.assertEqual(pbig.exception.code, "FILE_TOO_LARGE")

            empty_p = tdir / "empty.json"
            empty_p.write_bytes(b"")
            with mock.patch.object(os, "read", side_effect=[b"x" * 20, b"y" * 20, b""]):
                with self.assertRaises(s87.S87Error) as pstr:
                    ver.read_regular_file_bytes(empty_p, max_bytes=32)
                self.assertEqual(pstr.exception.code, "FILE_TOO_LARGE")
            with mock.patch.object(os, "read", side_effect=OSError(5, "EIO")):
                with self.assertRaises(s87.S87Error) as peio:
                    ver.read_regular_file_bytes(out_p)
                self.assertEqual(peio.exception.code, "FILE_READ_ERROR")
            with mock.patch.object(os, "write", side_effect=OSError(5, "EIO")):
                with self.assertRaises(s87.S87Error) as pwe:
                    ver.write_atomic_0600_bytes(tdir / "eio.json", b"hello")
                self.assertEqual(pwe.exception.code, "FILE_WRITE_ERROR")
            with mock.patch.object(os, "write", return_value=0):
                with self.assertRaises(s87.S87Error) as pw0:
                    ver.write_atomic_0600_bytes(tdir / "zwrite.json", b"hello")
                self.assertEqual(pw0.exception.code, "FILE_WRITE_ERROR")
            fake_st = type("St", (), {"st_nlink": 2})()
            with mock.patch.object(os, "fstat", return_value=fake_st):
                with self.assertRaises(s87.S87Error) as ptn:
                    ver.write_atomic_0600_bytes(tdir / "hl_tmp.json", b"hello")
                self.assertEqual(ptn.exception.code, "HARDLINK_FORBIDDEN")
            with mock.patch.object(os, "replace", side_effect=OSError(13, "EACCES")):
                with self.assertRaises(s87.S87Error) as prep:
                    ver.write_atomic_0600_bytes(tdir / "rep_err.json", b"hello")
                self.assertEqual(prep.exception.code, "FILE_WRITE_ERROR")

            err_buf = io.StringIO()
            with mock.patch.object(sys, "stderr", err_buf):
                rc_err = ver.main(["--check", str(crlf_p)])
            self.assertEqual(rc_err, 2)
            self.assertIn("CRLF_FORBIDDEN", err_buf.getvalue())


class TestS87LeanR10AndLiveOrCiVerification(unittest.TestCase):
    def test_r10_static_all_classes_and_clean_cases(self) -> None:
        with self.assertRaises(s87.S87Error):
            ver.audit_lean4_source_r10(123)  # type: ignore[arg-type]

        self.assertIs(ver._is_lean4_ident_prev("a", -1), False)
        self.assertIs(ver._is_lean4_ident_prev("a", 0), True)
        self.assertIs(ver._is_lean4_ident_prev("_", 0), True)
        self.assertIs(ver._is_lean4_ident_prev(" ", 0), False)
        self.assertIs(ver._is_lean4_ident_prev("a!", 1), True)
        self.assertIs(ver._is_lean4_ident_prev("_!", 1), True)
        self.assertIs(ver._is_lean4_ident_prev(" !", 1), False)
        self.assertIs(ver._is_lean4_ident_prev("!", 0), False)
        self.assertEqual(ver._strip_outer_parens(""), "")
        self.assertEqual(ver._strip_outer_parens("("), "(")
        self.assertEqual(ver._strip_outer_parens("(false)"), "false")
        self.assertEqual(ver._strip_outer_parens("(false"), "(false")
        self.assertEqual(ver._strip_outer_parens("false)"), "false)")

        self.assertEqual(ver._match_lean4_char_literal_end("'a'", 0, 3), 3)
        self.assertIsNone(ver._match_lean4_char_literal_end("'a", 0, 2))
        self.assertIsNone(ver._match_lean4_char_literal_end("'ab", 0, 3))
        self.assertIsNone(ver._match_lean4_char_literal_end("'ab'", 0, 4))
        self.assertIsNone(ver._match_lean4_char_literal_end("'\n'", 0, 3))
        self.assertEqual(ver._match_lean4_char_literal_end("'\\''", 0, 4), 4)
        self.assertEqual(ver._match_lean4_char_literal_end("'\\n'", 0, 4), 4)
        self.assertIsNone(ver._match_lean4_char_literal_end("'\\n", 0, 3))
        self.assertIsNone(ver._match_lean4_char_literal_end("'\\\n'", 0, 4))
        self.assertEqual(ver._match_lean4_char_literal_end("'\\x2a'", 0, 6), 6)
        self.assertIsNone(ver._match_lean4_char_literal_end("'\\x2g'", 0, 6))
        self.assertIsNone(ver._match_lean4_char_literal_end("'\\x2a!", 0, 6))
        self.assertIsNone(ver._match_lean4_char_literal_end("'\\x2a", 0, 5))
        self.assertIsNone(ver._match_lean4_char_literal_end("'\\y2a'", 0, 6))
        self.assertEqual(ver._match_lean4_char_literal_end("'\\u002A'", 0, 8), 8)
        self.assertIsNone(ver._match_lean4_char_literal_end("'\\u002g'", 0, 8))
        self.assertIsNone(ver._match_lean4_char_literal_end("'\\u002A!", 0, 8))
        self.assertIsNone(ver._match_lean4_char_literal_end("'\\u002A", 0, 7))
        self.assertIsNone(ver._match_lean4_char_literal_end("'\\v002A'", 0, 8))

        clean_src = "\n".join(
            [
                "-- sorry admit axiom native_decide",
                "/- outer /x a/ sorry -x /- nested -/ still comment -/",
                'def s1 := "sorry \\" native_decide"',
                'def s2 := r#"a " sorry " b"#',
                'def s3 := s! "hello {1 + 1} sorry"',
                'def s4 := !r#"sorry"#',
                'def s5 := panic!"sorry"',
                'def s6 := s!x ++ "sorry"',
                'def s7 := dbg_trace.ok "sorry"',
                'def s8 := _ok_1 "sorry"',
                'def s "a {sorry}"',
                'def bar#"ok"',
                "def foo!r := 1 / 2 - 1",
                "def c1 : Char := '\"'",
                "def c2 : Char := '\\''",
                "def c3 : Char := '\\x22'",
                "def c4 : Char := '\\u0022'",
                "def x' := 1",
                "def x_p := x' + 'a'.toNat",
                "def badCharStart := 'a + 1",
                "def x := rec.partial",
                "theorem t1 : 1 = 1 := by decide (native := false)",
                "theorem t2 : 1 = 1 := by decide (config := ({ native := Bool.false }))",
                "def cfg : DecideConfig := { native := false }",
                "def okGuillemet := «hello» ++ «bad sorry»",
                "@[simp] def attrOk := 1",
                "@[extern",
                "import Init.Data.Nat.Basic",
                "#print axioms t1",
                "theorem t_eof : 1 = 1 := by decide",
            ]
        )
        self.assertEqual(ver.audit_lean4_source_r10(clean_src), [])
        self.assertEqual(ver.audit_lean4_source_r10("-- eof no newline"), [])
        self.assertEqual(ver.audit_lean4_source_r10("r#"), [])
        self.assertEqual(ver.audit_lean4_source_r10("rx"), [])
        self.assertEqual(ver.audit_lean4_source_r10('r"sorry"a'), [])
        self.assertEqual(ver.audit_lean4_source_r10('!"a {sorry}"s'), [])
        self.assertEqual(ver.audit_lean4_source_r10('"ok"a!'), [])
        self.assertEqual(ver.audit_lean4_source_r10(' !"sorry"'), [])
        self.assertEqual(ver.audit_lean4_source_r10("'a'"), [])
        self.assertEqual(ver.audit_lean4_source_r10('def f := a\'"\' sorry "'), [])
        self.assertEqual(ver.audit_lean4_source_r10('def f := _\'"\' sorry "'), [])
        self.assertEqual(ver.audit_lean4_source_r10('def f := foo.s! "a {sorry}"'), [])
        self.assertEqual(ver.audit_lean4_source_r10("s!"), [])
        self.assertEqual(ver.audit_lean4_source_r10('panic!"sorry"'), [])
        self.assertEqual(ver.audit_lean4_source_r10('!panic!"sorry"'), [])
        self.assertEqual(ver.audit_lean4_source_r10("def y := a!\"\""), ["LEAN4_UNKNOWN_BANG_STRING"])
        self.assertEqual(ver.audit_lean4_source_r10("'\x22'\nsorry\ndef q : Char := '\x22'"), ["LEAN4_SORRY"])
        self.assertEqual(ver.audit_lean4_source_r10('def x := foo.r#"ok"; sorry; def z := "#"'), ["LEAN4_SORRY"])
        self.assertEqual(
            ver.audit_lean4_source_r10('def _a : String := s!"x"\naxiom evil : False\ndef _b : Char := \'"\''),
            ["LEAN4_AXIOM"],
        )

        cases: list[tuple[str, str]] = [
            ("theorem t : True := by sorry", "LEAN4_SORRY"),
            ("-- comment\ntheorem t : True := by sorry", "LEAN4_SORRY"),
            ("def x := 1 - 2\ndef y := a - sorry", "LEAN4_SORRY"),
            ("def x := 1-2; sorry", "LEAN4_SORRY"),
            ("theorem t : True := by «sorry»", "LEAN4_SORRY"),
            ("theorem t : True := by admit", "LEAN4_ADMIT"),
            ("axiom bogus : False", "LEAN4_AXIOM"),
            ("unsafe def f : Nat := 0", "LEAN4_UNSAFE"),
            ("theorem t : 1 = 1 := by native_decide", "LEAN4_NATIVE_DECIDE"),
            ("def x := sorryAx", "LEAN4_SORRY_AX"),
            ("def x := Lean.Meta.mkSorry", "LEAN4_MK_SORRY"),
            ("def x := Lean.ofReduceBool", "LEAN4_OF_REDUCE_BOOL"),
            ("def x := Lean.ofReduceNat", "LEAN4_OF_REDUCE_NAT"),
            ("def x := Lean.trustCompiler", "LEAN4_TRUST_COMPILER"),
            ("public\n  import Mathlib.Tactic", "LEAN4_NON_INIT_IMPORT"),
            ("partial\n def loop (n : Nat) : Nat := loop n", "LEAN4_PARTIAL"),
            ("theorem t : 1 = 1 := by decide +native", "LEAN4_DECIDE_NATIVE"),
            (") theorem t : 1 = 1 := by decide (native := true)", "LEAN4_DECIDE_NATIVE"),
            ("theorem t : 1 = 1 := by decide (config := { native := true })", "LEAN4_DECIDE_NATIVE"),
            ("theorem t : 1 = 1 := by decide (config := { native })", "LEAN4_DECIDE_NATIVE"),
            ("theorem t : 1 = 1 := by decide (config := myCfg)", "LEAN4_DECIDE_NATIVE"),
            ("theorem t : 1 = 1 := by decide (config := {foo)", "LEAN4_DECIDE_NATIVE"),
            ("theorem t : 1 = 1 := by decide (config := foo})", "LEAN4_DECIDE_NATIVE"),
            ("theorem t : 1 = 1 := by decide (config := { { })", "LEAN4_DECIDE_NATIVE"),
            ("theorem t : 1 = 1 := by decide (config := { } })", "LEAN4_DECIDE_NATIVE"),
            ("theorem t : 1 = 1 := by decide (config := { c with native := false })", "LEAN4_DECIDE_NATIVE"),
            ("theorem t : 1 = 1 := by decide («native» := true)", "LEAN4_DECIDE_NATIVE"),
            ("def c : DecideConfig := { native := true }", "LEAN4_DECIDE_NATIVE"),
            ("set_option debug.skipKernelTC true", "LEAN4_SKIP_KERNEL_TC"),
            ("set_option debug.byAsSorry true", "LEAN4_SKIP_KERNEL_TC"),
            ("set_option debug.proofAsSorry true", "LEAN4_SKIP_KERNEL_TC"),
            ("set_option debug.terminalTacticsAsSorry true", "LEAN4_SKIP_KERNEL_TC"),
            ("#eval 1 + 1", "LEAN4_EVAL_SPOOF"),
            ("#eval! 1 + 1", "LEAN4_EVAL_SPOOF"),
            ("#reduce 1 + 1", "LEAN4_EVAL_SPOOF"),
            ("#exit", "LEAN4_EVAL_SPOOF"),
            ("#print Nat.add", "LEAN4_EVAL_SPOOF"),
            ("#print axioms theorem", "LEAN4_EVAL_SPOOF"),
            ("run_cmd pure ()", "LEAN4_EVAL_SPOOF"),
            ("initialize x : Nat := pure 0", "LEAN4_EVAL_SPOOF"),
            ("builtin_initialize x : Nat := pure 0", "LEAN4_EVAL_SPOOF"),
            ('] @[extern "c_fn"] def f : Nat := 0', "LEAN4_ATTR_TRUST_ESCAPE"),
            ("attribute [implemented_by g] f", "LEAN4_ATTR_TRUST_ESCAPE"),
            ("@[csimp] theorem csimp_bad : 1 = 1 := rfl", "LEAN4_ATTR_TRUST_ESCAPE"),
            ("attribute [csimp] csimp_bad", "LEAN4_ATTR_TRUST_ESCAPE"),
            ('def x := s! "a {sorry} b"', "LEAN4_SORRY"),
            ('def x := !s!"a {sorry}"', "LEAN4_SORRY"),
            ('def x := dbg_trace "{(fun (_ : 1 = 1) => 0) (by native_decide)}" 0', "LEAN4_NATIVE_DECIDE"),
            ('def x := throwError "{sorry}"', "LEAN4_SORRY"),
            ('def x := foo!"a {sorry}"', "LEAN4_UNKNOWN_BANG_STRING"),
            ('def x := xpanic!"ok"', "LEAN4_UNKNOWN_BANG_STRING"),
            ('syntax "foo!" interpolatedStr(term) : term', "LEAN4_META_SYNTAX_ESCAPE"),
            ("macro_rules | `(1) => `(1)", "LEAN4_META_SYNTAX_ESCAPE"),
            ('elab "e" : term => sorry', "LEAN4_META_SYNTAX_ESCAPE"),
            ('notation "openq\\"" => 0', "LEAN4_META_SYNTAX_ESCAPE"),
            ('def x := s! /- c -/ "{sorry}"', "LEAN4_SORRY"),
            ('def x := s! -- c\n"{sorry}"', "LEAN4_SORRY"),
            ("theorem t : 1 = 1 := by decide -revert +native", "LEAN4_DECIDE_NATIVE"),
            ("theorem t : 1 = 1 := by decide (revert := true) +native", "LEAN4_DECIDE_NATIVE"),
            ("set_option «debug».«skipKernelTC» true", "LEAN4_SKIP_KERNEL_TC"),
            ('def q1 : Char := \'"\'\ntheorem bad : False := by sorry\ndef q2 : Char := \'"\'', "LEAN4_SORRY"),
            ('def q1 : Char := \'"\'\naxiom bad : False\ndef q2 : Char := \'"\'', "LEAN4_AXIOM"),
            ('def q1 : Char := \'"\'\ntheorem bad : 1 = 1 := by native_decide\ndef q2 : Char := \'"\'', "LEAN4_NATIVE_DECIDE"),
            ('def q1 : Char := \'"\'\n#eval IO.println "\'S87.bad\' does not depend on any axioms"\ndef q2 : Char := \'"\'', "LEAN4_EVAL_SPOOF"),
            ("def q1 : Char := '\\''\ndef q2 : Char := '\"'\ntheorem bad : False := by sorry\ndef q3 : Char := '\"'", "LEAN4_SORRY"),
            ("def x := «unterminated", "LEAN4_UNTERMINATED_IDENT"),
            ("/- unterminated comment", "LEAN4_UNTERMINATED_COMMENT"),
            ('def x := "unterminated', "LEAN4_UNTERMINATED_STRING"),
            ('def x := s!"unterminated', "LEAN4_UNTERMINATED_STRING"),
            ('def x := r#"unterminated', "LEAN4_UNTERMINATED_STRING"),
            ('def x := s!"{1', "LEAN4_UNTERMINATED_STRING"),
            ("def x := «axioms»\n#print «axioms» foo", "LEAN4_EVAL_SPOOF"),
            ('def x := s!"{\"{}\"}" ++ s!"{sorry}"', "LEAN4_SORRY"),
        ]
        for snippet, expected_code in cases:
            got = ver.audit_lean4_source_r10(snippet)
            self.assertIn(expected_code, got, f"expected {expected_code} for {snippet!r}, got {got}")

    def test_lean_verification_dual_mode_zero_skips(self) -> None:
        """Runs live Lean 4.36.0 when installed, or 0-skip mocked + fail-closed checks in Lean-less CI."""
        lean_file = _SCRIPT_DIR / s87.LEAN_FILE_NAME
        self.assertEqual(ver.audit_lean4_source_r10(lean_file.read_text(encoding="utf-8")), [])
        self.assertEqual(hashlib.sha256(lean_file.read_bytes()).hexdigest(), s87.LEAN_FILE_SHA256)

        has_lean = True
        try:
            ver._find_lean_binary()
        except s87.S87Error:
            has_lean = False

        if os.environ.get("ALETHEIA_REQUIRE_LEAN") == "1":
            self.assertTrue(has_lean, "ALETHEIA_REQUIRE_LEAN=1 requires live lean binary")

        if has_lean:
            out_buf = io.BytesIO()
            with mock.patch.object(sys, "stdout", type("FakeOut", (), {"buffer": out_buf})()):
                rc = ver.main(["--verify-lean", str(lean_file), "--json"])
            self.assertEqual(rc, 0)
            res = json.loads(out_buf.getvalue().decode("utf-8"))
            self.assertEqual(res["theorems_verified"], 20)
            self.assertEqual(res["r10_findings"], 0)
            self.assertEqual(res["allowed_axioms"], ["propext"])
            self.assertEqual(res["sha256"], s87.LEAN_FILE_SHA256)
            self.assertEqual(ver.main(["--verify-lean", str(lean_file)]), 0)
        else:
            # Lean-less CI: verify CLI fails closed with LEAN_BINARY_NOT_FOUND (rc=2) with 0 skips!
            err_buf = io.StringIO()
            with mock.patch.object(sys, "stderr", err_buf):
                rc_nl = ver.main(["--verify-lean", str(lean_file)])
            self.assertEqual(rc_nl, 2)
            self.assertIn("LEAN_BINARY_NOT_FOUND", err_buf.getvalue())

        with tempfile.TemporaryDirectory(prefix="s87_lean_") as td:
            tdir = Path(td).resolve()

            # AUDIT-187 S87-F3: reject non-bool check_pinned_sha and 0-theorem Lean files
            for bad_flag in (0, 1, "false", None):
                with self.assertRaises(s87.S87Error) as e_flag:
                    ver.verify_lean_file(lean_file, check_pinned_sha=bad_flag)  # type: ignore[arg-type]
                self.assertEqual(e_flag.exception.code, "INVALID_CHECK_PINNED_SHA")

            # CRLF, invalid UTF-8, pinned SHA mismatch, and R10 static findings rejected BEFORE lean binary
            crlf_l = tdir / "c.lean"
            crlf_l.write_bytes(b"theorem t : True := trivial\r\n")
            with self.assertRaises(s87.S87Error) as e1:
                ver.verify_lean_file(crlf_l, check_pinned_sha=False)
            self.assertEqual(e1.exception.code, "CRLF_FORBIDDEN")

            badu_l = tdir / "u.lean"
            badu_l.write_bytes(b"\xff\xfe")
            with self.assertRaises(s87.S87Error) as e2:
                ver.verify_lean_file(badu_l, check_pinned_sha=False)
            self.assertEqual(e2.exception.code, "INVALID_UTF8")

            other_l = tdir / "o.lean"
            other_l.write_text("theorem ok1 : 1 = 1 := rfl\n#print axioms ok1\n", encoding="utf-8")
            with self.assertRaises(s87.S87Error) as e3:
                ver.verify_lean_file(other_l, check_pinned_sha=True)
            self.assertEqual(e3.exception.code, "LEAN_SHA_MISMATCH")

            r10_l = tdir / "r10_bad.lean"
            r10_l.write_text("#eval 1 + 1\n", encoding="utf-8")
            with self.assertRaises(s87.S87Error) as e_r10:
                ver.verify_lean_file(r10_l, check_pinned_sha=False)
            self.assertEqual(e_r10.exception.code, "LEAN_R10_STATIC_FINDING")

            for idx_sp, spoof_src in enumerate(
                (
                    'def q1 : Char := \'"\'\n#eval IO.println "\'S87.bad\' does not depend on any axioms"\ndef q2 : Char := \'"\'\n',
                    'def q1 : Char := \'"\'\ntheorem bad : False := by sorry\ndef q2 : Char := \'"\'\n#print axioms bad\n',
                    'def q1 : Char := \'"\'\naxiom bad : False\ndef q2 : Char := \'"\'\n#print axioms bad\n',
                    'def q1 : Char := \'"\'\ntheorem bad : 1 = 1 := by native_decide\ndef q2 : Char := \'"\'\n#print axioms bad\n',
                    "def q1 : Char := '\\''\ndef q2 : Char := '\"'\ntheorem bad : False := by sorry\ndef q3 : Char := '\"'\n",
                    'syntax "foo!" interpolatedStr(term) : term\nmacro_rules | `(foo! $s:interpolatedStr) => `(s! $s)\ndef x := foo!"a {((by sorry : Nat))}"\n',
                )
            ):
                sp_l = tdir / f"spoof_{idx_sp}.lean"
                sp_l.write_text(spoof_src, encoding="utf-8")
                with self.assertRaises(s87.S87Error) as e_sp:
                    ver.verify_lean_file(sp_l, check_pinned_sha=False)
                self.assertEqual(e_sp.exception.code, "LEAN_R10_STATIC_FINDING")

            # Mocked Lean subprocess checks run cleanly in BOTH live and Lean-less CI!
            with mock.patch.object(ver, "_find_lean_binary", return_value="/usr/bin/lean"):
                wrap_ok = subprocess.CompletedProcess(
                    ["lean"],
                    0,
                    stdout="'ok1' depends on axioms: [\n  propext\n]\n'ok2' does not depend on any axioms\n",
                    stderr="",
                )
                with mock.patch.object(subprocess, "run", return_value=wrap_ok):
                    w_res = ver.verify_lean_file(other_l, check_pinned_sha=False)
                    self.assertEqual(w_res["theorems_verified"], 2)

                wrap_bad = subprocess.CompletedProcess(
                    ["lean"],
                    0,
                    stdout="'ok1' depends on axioms: [\n  propext,\n  Classical.choice\n]\n",
                    stderr="",
                )
                with mock.patch.object(subprocess, "run", return_value=wrap_bad):
                    with self.assertRaises(s87.S87Error) as e_wb:
                        ver.verify_lean_file(other_l, check_pinned_sha=False)
                    self.assertEqual(e_wb.exception.code, "LEAN_FORBIDDEN_AXIOM")

                dup_out = subprocess.CompletedProcess(
                    ["lean"],
                    0,
                    stdout="'ok1' does not depend on any axioms\n'ok1' does not depend on any axioms\n",
                    stderr="",
                )
                with mock.patch.object(subprocess, "run", return_value=dup_out):
                    with self.assertRaises(s87.S87Error) as e_dup:
                        ver.verify_lean_file(other_l, check_pinned_sha=False)
                    self.assertEqual(e_dup.exception.code, "LEAN_DUPLICATE_THEOREM")

                fail_rc = subprocess.CompletedProcess(["lean"], 1, stdout="", stderr="type mismatch")
                with mock.patch.object(subprocess, "run", return_value=fail_rc):
                    with self.assertRaises(s87.S87Error) as e_rc:
                        ver.verify_lean_file(other_l, check_pinned_sha=False)
                    self.assertEqual(e_rc.exception.code, "LEAN_COMPILE_FAILED")

                fake_proc_err = subprocess.CompletedProcess(["lean"], 0, stdout="", stderr="warn")
                with mock.patch.object(subprocess, "run", return_value=fake_proc_err):
                    with self.assertRaises(s87.S87Error) as e6:
                        ver.verify_lean_file(other_l, check_pinned_sha=False)
                    self.assertEqual(e6.exception.code, "LEAN_STDERR_NONEMPTY")

                fake_proc_out = subprocess.CompletedProcess(["lean"], 0, stdout="weird line\n", stderr="")
                with mock.patch.object(subprocess, "run", return_value=fake_proc_out):
                    with self.assertRaises(s87.S87Error) as e7:
                        ver.verify_lean_file(other_l, check_pinned_sha=False)
                    self.assertEqual(e7.exception.code, "LEAN_UNEXPECTED_OUTPUT")

                fake_proc_thm = subprocess.CompletedProcess(
                    ["lean"], 0, stdout="'Wrong.thm' does not depend on any axioms\n", stderr=""
                )
                with mock.patch.object(subprocess, "run", return_value=fake_proc_thm):
                    with self.assertRaises(s87.S87Error) as e8:
                        ver.verify_lean_file(lean_file, check_pinned_sha=True)
                    self.assertEqual(e8.exception.code, "LEAN_THEOREM_SET_MISMATCH")

                empty_out = subprocess.CompletedProcess(["lean"], 0, stdout="", stderr="")
                with mock.patch.object(subprocess, "run", return_value=empty_out):
                    with self.assertRaises(s87.S87Error) as e_zero:
                        ver.verify_lean_file(other_l, check_pinned_sha=False)
                    self.assertEqual(e_zero.exception.code, "LEAN_NO_THEOREMS_VERIFIED")

            if has_lean:
                ok_res = ver.verify_lean_file(other_l, check_pinned_sha=False)
                self.assertEqual(ok_res["theorems_verified"], 1)
                cl_l = tdir / "classical.lean"
                cl_l.write_text(
                    "theorem use_em (p : Prop) : p ∨ ¬ p := Classical.em p\n#print axioms use_em\n",
                    encoding="utf-8",
                )
                with self.assertRaises(s87.S87Error) as e4:
                    ver.verify_lean_file(cl_l, check_pinned_sha=False)
                self.assertEqual(e4.exception.code, "LEAN_FORBIDDEN_AXIOM")

                bad_l = tdir / "bad.lean"
                bad_l.write_text("theorem bad : 1 = 2 := rfl\n", encoding="utf-8")
                with self.assertRaises(s87.S87Error) as e5:
                    ver.verify_lean_file(bad_l, check_pinned_sha=False)
                self.assertEqual(e5.exception.code, "LEAN_COMPILE_FAILED")

            # _find_lean_binary discovery branches (LEAN_BIN valid/invalid, PATH, elan, missing)
            dummy_lean = tdir / "fake_lean"
            dummy_lean.write_text("#!/bin/sh\n", encoding="utf-8")
            with mock.patch.dict(os.environ, {"LEAN_BIN": str(dummy_lean)}):
                self.assertEqual(ver._find_lean_binary(), str(dummy_lean))
            with mock.patch.dict(os.environ, {"LEAN_BIN": str(tdir / "no_such_lean")}):
                with self.assertRaises(s87.S87Error) as e_eb:
                    ver._find_lean_binary()
                self.assertEqual(e_eb.exception.code, "LEAN_BINARY_NOT_FOUND")
            with mock.patch.dict(os.environ, {"LEAN_BIN": ""}):
                with mock.patch.object(ver.shutil, "which", return_value="/mock/lean"):
                    self.assertEqual(ver._find_lean_binary(), "/mock/lean")
                with mock.patch.object(ver.shutil, "which", return_value=None):
                    with mock.patch.object(Path, "is_file", return_value=False):
                        with self.assertRaises(s87.S87Error) as e9:
                            ver._find_lean_binary()
                        self.assertEqual(e9.exception.code, "LEAN_BINARY_NOT_FOUND")
                    with mock.patch.object(Path, "is_file", return_value=True):
                        self.assertTrue(ver._find_lean_binary().endswith("lean"))


if __name__ == "__main__":
    unittest.main()
