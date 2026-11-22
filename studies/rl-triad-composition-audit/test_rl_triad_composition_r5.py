#!/usr/bin/env python3
"""Wave 2 Round 9 — Arm R9-5 (AUDIT-082):
Exhaustive R1-R5 unit, boundary, adversarial red-team, and live+standalone
verification suite for rl_triad_composition_audit.py.

Zero bare asserts; zero floats; isolated -I compatible.
"""

from __future__ import annotations

from fractions import Fraction
import hashlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

_THIS_DIR = str(Path(__file__).resolve().parent)
if _THIS_DIR not in sys.path:
    sys.path.insert(0, _THIS_DIR)

import rl_triad_composition_audit as mod


def _assert_no_floats(tc: unittest.TestCase, obj: object, path: str = "root") -> None:
    tc.assertIsNot(type(obj), float, f"float leaked at {path}")
    if isinstance(obj, dict):
        for k, v in obj.items():
            tc.assertIsNot(type(k), float, f"float key at {path}")
            _assert_no_floats(tc, v, f"{path}.{k}")
    elif isinstance(obj, (list, tuple)):
        for i, item in enumerate(obj):
            _assert_no_floats(tc, item, f"{path}[{i}]")


def _base_valid_spec() -> dict[str, object]:
    q = [Fraction(4, 9), Fraction(4, 9), Fraction(1, 9)]
    p = [Fraction(1, 2), Fraction(7, 18), Fraction(1, 9)]
    return {
        "q": list(q),
        "p_old": list(q),
        "p": list(p),
        "features": [Fraction(1, 1), Fraction(-1, 1), Fraction(0, 1)],
        "tii_flags_aligned": True,
        "max_tim_ratio": Fraction(1, 1),
        "max_tim_chi2": Fraction(0, 1),
        "weighting_mode": "ripo_clamped",
        "centering_mode": "weighted_sc",
        "kl_mode": "exact_bregman",
        "delta": Fraction(1, 25),
        "delta_total": Fraction(1, 10),
        "dual_clip_low": Fraction(1, 2),
        "dual_clip_high": Fraction(10, 1),
        "allow_negative_lower_clip": False,
        "use_true_p_old_for_ripo": True,
        "top_k_indices": [0, 1],
        "max_tail_rho": Fraction(5, 1),
        "max_second_moment": Fraction(2, 1),
        "max_d3_upper": Fraction(1, 5),
        "eta": Fraction(1, 2),
        "step_variance_v": Fraction(1, 1),
    }


class TestPrimitivesAndHelpers(unittest.TestCase):
    def test_frac_to_dict_and_exact_frac(self) -> None:
        self.assertEqual(mod.frac_to_dict(Fraction(3, 5)), {"num": 3, "den": 5})
        self.assertEqual(mod.frac_to_dict(Fraction(-6, 4)), {"num": -3, "den": 2})
        with self.assertRaises(TypeError):
            mod.frac_to_dict(3)  # type: ignore[arg-type]

        self.assertEqual(mod.exact_frac(7, "x"), Fraction(7, 1))
        self.assertEqual(mod.exact_frac(Fraction(2, 3), "x"), Fraction(2, 3))
        for bad in (True, False, 1 / 2, "1/2", None, [1]):
            with self.assertRaises(ValueError):
                mod.exact_frac(bad, "x")

    def test_exact_bool(self) -> None:
        self.assertIs(mod.exact_bool(True, "b"), True)
        self.assertIs(mod.exact_bool(False, "b"), False)
        for bad in (0, 1, "true", None):
            with self.assertRaises(ValueError):
                mod.exact_bool(bad, "b")

    def test_exact_rational_sqrt(self) -> None:
        self.assertEqual(mod.exact_rational_sqrt(Fraction(0, 1), "z"), Fraction(0, 1))
        self.assertEqual(mod.exact_rational_sqrt(Fraction(9, 16), "q"), Fraction(3, 4))
        self.assertEqual(mod.exact_rational_sqrt(Fraction(25, 1), "q"), Fraction(5, 1))
        with self.assertRaises(ValueError):
            mod.exact_rational_sqrt(Fraction(-1, 4), "neg")
        with self.assertRaises(ValueError):
            mod.exact_rational_sqrt(Fraction(2, 9), "non_sq_num")
        with self.assertRaises(ValueError):
            mod.exact_rational_sqrt(Fraction(9, 2), "non_sq_den")

    def test_validate_simplex_and_softmax_scores(self) -> None:
        s = mod.validate_simplex([Fraction(1, 3), Fraction(2, 3)], "p")
        self.assertEqual(s, [Fraction(1, 3), Fraction(2, 3)])
        s_tup = mod.validate_simplex((Fraction(1, 2), Fraction(1, 2)), "p")
        self.assertEqual(len(s_tup), 2)
        for bad in (
            "12",
            [Fraction(1, 1)],
            [Fraction(0, 1), Fraction(1, 1)],
            [Fraction(-1, 2), Fraction(3, 2)],
            [Fraction(1, 2), Fraction(1, 3)],
            [Fraction(1, 2), Fraction(2, 3)],
        ):
            with self.assertRaises(ValueError):
                mod.validate_simplex(bad, "p")

        scores = mod.softmax_scores([Fraction(2, 3), Fraction(1, 3)], [Fraction(3, 1), Fraction(0, 1)])
        self.assertEqual(scores, [Fraction(1, 1), Fraction(-2, 1)])
        self.assertEqual(
            Fraction(2, 3) * scores[0] + Fraction(1, 3) * scores[1], Fraction(0, 1)
        )
        with self.assertRaises(ValueError):
            mod.softmax_scores([Fraction(1, 2), Fraction(1, 2)], [Fraction(1, 1)])

    def test_d3_rational_bounds(self) -> None:
        self.assertEqual(mod.d3_rational_bounds(Fraction(1, 1)), (Fraction(0, 1), Fraction(0, 1)))
        lo_gt, hi_gt = mod.d3_rational_bounds(Fraction(3, 2))
        self.assertEqual(lo_gt, Fraction(1, 12))
        self.assertEqual(hi_gt, Fraction(1, 10))
        lo_lt, hi_lt = mod.d3_rational_bounds(Fraction(1, 2))
        self.assertEqual(lo_lt, Fraction(1, 6))
        self.assertEqual(hi_lt, Fraction(1, 4))
        for bad in (Fraction(0, 1), Fraction(-1, 2)):
            with self.assertRaises(ValueError):
                mod.d3_rational_bounds(bad)

    def test_ripo_bounds_and_clamp(self) -> None:
        # delta = 1/20, base_prob = 1/80 -> eps = 2 -> raw [-1, 3]
        lo_raw, hi_raw, eps = mod.compute_ripo_exact_bound(
            Fraction(1, 80), Fraction(1, 20), Fraction(1, 2), Fraction(10, 1), True
        )
        self.assertEqual((lo_raw, hi_raw, eps), (Fraction(-1, 1), Fraction(3, 1), Fraction(2, 1)))
        # Clamped low to 1/2 and capped high to 2
        lo_c, hi_c, _ = mod.compute_ripo_exact_bound(
            Fraction(1, 80), Fraction(1, 20), Fraction(1, 2), Fraction(2, 1), False
        )
        self.assertEqual((lo_c, hi_c), (Fraction(1, 2), Fraction(2, 1)))
        # Exact membership boundary test
        self.assertTrue(mod.ripo_membership_exact(Fraction(3, 1), Fraction(1, 80), Fraction(1, 20)))
        self.assertFalse(mod.ripo_membership_exact(Fraction(31, 10), Fraction(1, 80), Fraction(1, 20)))

        # Unclipped in-band non-square base_prob passes without needing rational sqrt
        self.assertEqual(
            mod.clamp_ratio_ripo_exact(
                Fraction(11, 10), Fraction(1, 3), Fraction(1, 20), Fraction(1, 2), Fraction(10, 1), False
            ),
            Fraction(11, 10),
        )
        # Dual-clip low binds when ratio < dual_clip_low even if ripo_membership holds
        self.assertEqual(
            mod.clamp_ratio_ripo_exact(
                Fraction(1, 4), Fraction(1, 80), Fraction(1, 20), Fraction(1, 2), Fraction(10, 1), False
            ),
            Fraction(1, 2),
        )
        # Dual-clip high binds when ratio > dual_clip_high
        self.assertEqual(
            mod.clamp_ratio_ripo_exact(
                Fraction(5, 2), Fraction(1, 80), Fraction(1, 20), Fraction(1, 2), Fraction(2, 1), False
            ),
            Fraction(2, 1),
        )
        # allow_negative_lower_clip=True lets ratio < dual_clip_low pass if inside RIPO band
        self.assertEqual(
            mod.clamp_ratio_ripo_exact(
                Fraction(1, 4), Fraction(1, 80), Fraction(1, 20), Fraction(1, 2), Fraction(10, 1), True
            ),
            Fraction(1, 4),
        )
        # Exact upper RIPO clip when ratio > 1 + eps
        self.assertEqual(
            mod.clamp_ratio_ripo_exact(
                Fraction(4, 1), Fraction(1, 80), Fraction(1, 20), Fraction(1, 2), Fraction(10, 1), False
            ),
            Fraction(3, 1),
        )
        # Exact lower RIPO clip when 1 - eps > dual_clip_low and ratio < 1 - eps
        self.assertEqual(
            mod.clamp_ratio_ripo_exact(
                Fraction(3, 5), Fraction(4, 9), Fraction(1, 25), Fraction(1, 10), Fraction(10, 1), False
            ),
            Fraction(7, 10),
        )
        # Boundary ratio == low / high in fallback branch
        self.assertEqual(
            mod.clamp_ratio_ripo_exact(
                Fraction(1, 2), Fraction(1, 80), Fraction(1, 20), Fraction(1, 2), Fraction(2, 1), False
            ),
            Fraction(1, 2),
        )
        # Test exact fallback return ratio when dual_clip_low > dual_clip_high? No, test boundary
        # where ripo_membership is false? No, if ratio in [low, high], ripo_membership was true unless
        # raw_low <= ratio <= raw_high & ratio in [dual_clip_low, dual_clip_high].
        # Specifically: ratio == 3 and dual_clip_high == 3 passes fast path;
        # force fallback with ratio > dual_clip_high -> returns high, ratio < dual_clip_low -> returns low.
        # Non-square dual_clip dominance (TRIAD-BUG-02b): NEVER crashes on valid rational inputs!
        self.assertEqual(
            mod.clamp_ratio_ripo_exact(
                Fraction(1, 50), Fraction(1, 2), Fraction(1, 2), Fraction(1, 2), Fraction(2, 1), False
            ),
            Fraction(1, 2),
        )
        self.assertEqual(
            mod.clamp_ratio_ripo_exact(
                Fraction(147, 25), Fraction(1, 6), Fraction(1, 2), Fraction(1, 2), Fraction(2, 1), False
            ),
            Fraction(2, 1),
        )
        # Boundary ratio == 1 returns 1 cleanly
        self.assertEqual(
            mod.clamp_ratio_ripo_exact(
                Fraction(1, 1), Fraction(1, 3), Fraction(1, 20), Fraction(1, 2), Fraction(2, 1), False
            ),
            Fraction(1, 1),
        )
        # Allow negative lower clip when ratio < raw_low
        self.assertEqual(
            mod.clamp_ratio_ripo_exact(
                Fraction(-2, 1), Fraction(1, 80), Fraction(1, 20), Fraction(1, 2), Fraction(10, 1), True
            ),
            Fraction(-1, 1),
        )


class TestFiveExactPureQTheorems(unittest.TestCase):
    def test_t1_three_axis_factorization(self) -> None:
        t1 = mod.prove_t1_three_axis_factorization()
        self.assertTrue(t1["factorization_exact"])
        self.assertEqual(t1["chi2_tim_unaligned"], {"num": 1, "den": 20})
        self.assertEqual(t1["chi2_tim_aligned"], {"num": 0, "den": 1})

        rz = t1["reinforce_zero_thm1"]
        self.assertEqual(rz["kappa_zero_v0"], {"num": 2, "den": 1})
        self.assertEqual(rz["kappa_zero_eta_max"], {"num": 2, "den": 3})
        self.assertEqual(rz["kappa_zero_rho"], {"num": 22, "den": 25})
        self.assertEqual(rz["kappa_zero_c"], {"num": 9, "den": 250})
        self.assertEqual(rz["kappa_zero_v_inf"], {"num": 3, "den": 10})
        self.assertTrue(rz["kappa_zero_stable"])
        self.assertEqual(rz["kappa_1_5_exp_lo"], {"num": 1301, "den": 1250})
        self.assertEqual(rz["kappa_1_5_a_lo"], {"num": 1317913, "den": 390625})
        self.assertEqual(rz["kappa_1_5_eta_max_hi"], {"num": 781250, "den": 1317913})
        self.assertEqual(rz["kappa_1_5_rho_lo"], {"num": 9908092, "den": 9765625})
        self.assertTrue(rz["kappa_1_5_certified_unstable"])

        fs = t1["fisher_schur_bridge"]
        self.assertEqual(fs["f00"], {"num": 61, "den": 100})
        self.assertEqual(fs["f01"], {"num": 17, "den": 100})
        self.assertEqual(fs["f11"], {"num": 49, "den": 100})
        self.assertEqual(fs["schur_complement_s"], {"num": 27, "den": 49})
        self.assertTrue(fs["schur_strictly_below_f00"])
        self.assertEqual(fs["ripo_half_chi2"], {"num": 9, "den": 3200})
        self.assertEqual(fs["fisher_quad_half"], {"num": 9, "den": 3200})
        self.assertTrue(fs["ripo_equals_wi4_fisher_exact"])

    def test_t2_trap01_naive_sc_ripo(self) -> None:
        t2 = mod.prove_t2_trap01_naive_sc_ripo()
        self.assertEqual(t2["delta"], {"num": 1, "den": 25})
        self.assertEqual(
            t2["weights"],
            [{"num": 13, "den": 10}, {"num": 7, "den": 10}, {"num": 3, "den": 2}],
        )
        self.assertEqual(t2["expected_weight_ew"], {"num": 19, "den": 18})
        self.assertEqual(t2["sampler_mean_score_s_bar_q"], {"num": -1, "den": 2})
        self.assertEqual(t2["uncentered_ripo_drift"], {"num": -47, "den": 180})
        self.assertEqual(t2["naive_sc_ripo_drift"], {"num": 4, "den": 15})
        self.assertEqual(t2["cov_q_w_s"], {"num": 4, "den": 15})
        self.assertTrue(t2["naive_drift_equals_cov_exact"])
        self.assertTrue(t2["naive_sc_sign_reversed"])
        self.assertTrue(t2["naive_sc_worse_magnitude"])
        self.assertEqual(t2["weighted_sc_additive_drift"], {"num": 0, "den": 1})
        self.assertEqual(t2["weighted_sc_normalized_drift"], {"num": 0, "den": 1})
        self.assertTrue(t2["weighted_sc_exact_zero"])

    def test_t3_trap02_topk_ripo_split_tail_and_singularity(self) -> None:
        t3 = mod.prove_t3_trap02_topk_ripo_split_tail_and_singularity()
        pa = t3["part_a_split_tail"]
        self.assertEqual(pa["rho"], {"num": 1, "den": 4})
        self.assertTrue(pa["q_hat_zero_reconstruction_error"])
        self.assertTrue(pa["tail_ratios_identical"])
        self.assertEqual(pa["split_tail_weights"], [{"num": 2, "den": 1}, {"num": 4, "den": 1}])
        self.assertTrue(pa["tail_weights_strictly_split"])
        self.assertEqual(pa["sufficiency_lhs"], {"num": 225, "den": 1936})
        self.assertEqual(pa["sufficiency_rhs_split"], {"num": 25, "den": 1936})
        self.assertTrue(pa["sufficiency_violated_in_split_case"])
        self.assertEqual(pa["true_ews_split"], {"num": -2473, "den": 29282})
        self.assertEqual(
            pa["eq10_scalar_alpha_residuals"],
            {
                "alpha_1_unclipped": {"num": -2425, "den": 29282},
                "alpha_1_2_clipped_t2": {"num": -145, "den": 29282},
                "alpha_1_4_vanilla_rho": {"num": 995, "den": 29282},
            },
        )
        self.assertTrue(pa["all_tested_scalar_alphas_nonzero_drift"])
        self.assertEqual(pa["sufficiency_rhs_pass"], {"num": 225, "den": 1936})
        self.assertTrue(pa["sufficiency_holds_in_pass_case"])
        self.assertEqual(pa["pass_case_eq10_alpha1_residual"], {"num": 0, "den": 1})
        self.assertTrue(pa["pass_case_exact_zero_drift"])

        pb = t3["part_b_tail_singularity_and_loom"]
        self.assertEqual(pb["rho_exact_peaked"], {"num": 2000000, "den": 1})
        self.assertEqual(pb["rho_floored_peaked"], {"num": 20000, "den": 1})
        self.assertEqual(pb["q_hat_sum_under_floor"], {"num": 4901, "den": 5000})
        self.assertTrue(pb["normalization_broken_by_floor"])
        self.assertEqual(pb["alpha_sc_floored"], {"num": 20000, "den": 1})
        self.assertEqual(pb["alpha_tis_floored"], {"num": 1, "den": 1})
        self.assertEqual(pb["alpha_mis_floored"], {"num": 0, "den": 1})
        self.assertTrue(pb["tis_immune_to_rho_blowup"])
        self.assertTrue(pb["mis_drops_entire_tail"])
        self.assertEqual(pb["loom_ir03_rho_exact"], {"num": 0, "den": 1})
        self.assertEqual(pb["loom_ir03_paper_eps_spurious_rho"], {"num": 1, "den": 546875})
        self.assertTrue(pb["loom_ir03_spurious_nonzero_under_eps_floor"])

    def test_t4_trap03_tim_vs_ripo_dead_zone(self) -> None:
        t4 = mod.prove_t4_trap03_tim_vs_ripo_dead_zone()
        st = t4["sync_tim_explosion"]
        self.assertEqual(st["tv_distance"], {"num": 99, "den": 1000})
        self.assertEqual(st["is_second_moment"], {"num": 400, "den": 37})
        self.assertEqual(st["chi2_divergence"], {"num": 363, "den": 37})
        self.assertTrue(st["second_moment_exceeds_10x"])

        dz = t4["ripo_lower_clip_dead_zone"]
        self.assertEqual(dz["eps"], {"num": 2, "den": 1})
        self.assertEqual(dz["raw_lower_bound"], {"num": -1, "den": 1})
        self.assertEqual(dz["raw_upper_bound"], {"num": 3, "den": 1})
        self.assertTrue(dz["raw_lower_negative"])
        self.assertTrue(dz["neg_adv_ratio_unclipped_raw"])
        self.assertEqual(dz["dual_clip_floor"], {"num": 1, "den": 2})
        self.assertEqual(dz["dual_clip_geom_dist"], {"num": 1, "den": 320})
        self.assertEqual(dz["isometry_shrink_factor"], {"num": 16, "den": 1})

        ht = t4["ripo_heteroscedasticity"]
        self.assertEqual(ht["v_q_1_2000"], {"num": 121, "den": 2000})
        self.assertEqual(ht["v_q_4_5"], {"num": 5, "den": 4})
        self.assertEqual(ht["heteroscedasticity_ratio"], {"num": 2500, "den": 121})
        self.assertTrue(ht["exceeds_20x"])

        tc = t4["tim_trust_region_corruption"]
        self.assertEqual(tc["p_admitted"], {"num": 7, "den": 20})
        self.assertEqual(tc["noisy_ripo_dist"], {"num": 1, "den": 25})
        self.assertTrue(tc["noisy_ripo_passes"])
        self.assertEqual(tc["true_learner_dist"], {"num": 289, "den": 25})
        self.assertEqual(tc["overshoot_factor"], {"num": 289, "den": 1})

    def test_t5_trap04_songe_bregman_and_d3_sandwich(self) -> None:
        t5 = mod.prove_t5_trap04_songe_bregman_and_d3_sandwich()
        ck = t5["clipped_kl_reversal"]
        self.assertEqual(ck["dl_dq0_clipped"], {"num": 512, "den": 3969})
        self.assertEqual(ck["dl_dz0_clipped"], {"num": 1, "den": 504})
        self.assertEqual(ck["dl_dq0_bregman"], {"num": -2031616, "den": 3969})
        self.assertEqual(ck["dl_dz0_bregman"], {"num": -496, "den": 63})
        self.assertEqual(ck["dl_dz0_forward_kl"], {"num": -31, "den": 64})
        self.assertTrue(ck["clipped_reverses_gradient_anti_teacher"])
        self.assertTrue(ck["bregman_pulls_toward_teacher"])
        self.assertTrue(ck["forward_kl_pulls_toward_teacher"])

        sd = t5["d3_ripo_sandwich"]
        self.assertEqual(sd["w_3_2_lo"], {"num": 1, "den": 12})
        self.assertEqual(sd["w_3_2_hi"], {"num": 1, "den": 10})
        self.assertEqual(sd["w_3_2_half_sq"], {"num": 1, "den": 8})
        self.assertTrue(sd["w_3_2_ordered"])
        self.assertEqual(sd["w_1_2_lo"], {"num": 1, "den": 6})
        self.assertEqual(sd["w_1_2_hi"], {"num": 1, "den": 4})
        self.assertEqual(sd["w_1_2_half_sq"], {"num": 1, "den": 8})
        self.assertTrue(sd["w_1_2_ordered"])
        self.assertTrue(sd["w_1_vanishes"])


class TestUnifiedRLCertifierAndRedTeam(unittest.TestCase):
    def test_schema_and_type_rejections(self) -> None:
        with self.assertRaises(ValueError):
            mod.certify_unified_rl_step("not-a-dict")

        # Missing key & extra key
        s_miss = _base_valid_spec()
        del s_miss["eta"]
        with self.assertRaises(ValueError):
            mod.certify_unified_rl_step(s_miss)

        s_extra = _base_valid_spec()
        s_extra["extra"] = 1
        with self.assertRaises(ValueError):
            mod.certify_unified_rl_step(s_extra)

        # Length mismatches across q, p_old, p, features
        for field in ("p_old", "p", "features"):
            spec = _base_valid_spec()
            if field == "features":
                spec[field] = [Fraction(1, 1), Fraction(0, 1)]
            else:
                spec[field] = [Fraction(1, 2), Fraction(1, 2)]
            with self.assertRaises(ValueError):
                mod.certify_unified_rl_step(spec)

        # Features not a sequence
        spec_nf = _base_valid_spec()
        spec_nf["features"] = "abc"
        with self.assertRaises(ValueError):
            mod.certify_unified_rl_step(spec_nf)

        # Invalid enum strings and non-str enums
        for field, bad_vals in (
            ("weighting_mode", ("ppo", 1)),
            ("centering_mode", ("magic_sc", None)),
            ("kl_mode", ("reverse_kl", 0)),
        ):
            for bv in bad_vals:
                spec = _base_valid_spec()
                spec[field] = bv
                with self.assertRaises(ValueError):
                    mod.certify_unified_rl_step(spec)

        # Domain range violations on all numeric bounds
        bad_params = [
            ("max_tim_ratio", Fraction(9, 10)),
            ("max_tim_chi2", Fraction(-1, 10)),
            ("delta", Fraction(0, 1)),
            ("delta_total", Fraction(0, 1)),
            ("dual_clip_low", Fraction(0, 1)),
            ("dual_clip_low", Fraction(11, 10)),
            ("dual_clip_high", Fraction(9, 10)),
            ("max_tail_rho", Fraction(9, 10)),
            ("max_second_moment", Fraction(9, 10)),
            ("max_d3_upper", Fraction(-1, 10)),
            ("eta", Fraction(0, 1)),
            ("step_variance_v", Fraction(-1, 10)),
        ]
        for key, val in bad_params:
            spec = _base_valid_spec()
            spec[key] = val
            with self.assertRaises(ValueError, msg=f"{key}={val}"):
                mod.certify_unified_rl_step(spec)

        # Invalid top_k_indices shapes/types/bounds/duplicates (including set/dict & direct parser bounds)
        for bad_tk in (
            "01",
            {0, 1},
            {0: 1},
            [],
            [0, 1, 2],
            [True],
            [-1],
            [3],
            [0, 0],
        ):
            with self.assertRaises(ValueError, msg=f"_parse_topk_indices({bad_tk!r})"):
                mod._parse_topk_indices(bad_tk, 3)
            spec = _base_valid_spec()
            spec["top_k_indices"] = bad_tk
            with self.assertRaises(ValueError, msg=f"top_k={bad_tk!r}"):
                mod.certify_unified_rl_step(spec)

    def test_valid_admitted_across_modes_and_exact_boundaries(self) -> None:
        # 1. Clean RIPO + weighted_sc + exact_bregman + top_k
        spec = _base_valid_spec()
        res = mod.certify_unified_rl_step(spec)
        self.assertTrue(res["admitted"])
        self.assertEqual(res["status"], "ADMITTED_UNIFIED_RL_STEP")
        self.assertEqual(res["reasons"], [])
        self.assertEqual(res["diagnostics"]["residual_drift"], {"num": 0, "den": 1})
        self.assertEqual(res["diagnostics"]["topk_tail_rho"], {"num": 1, "den": 1})

        # 2. Exact boundary equality on every numeric threshold MUST admit (<= vs <)
        spec_b = _base_valid_spec()
        d = res["diagnostics"]
        spec_b["max_tim_ratio"] = Fraction(d["observed_max_tim_ratio"]["num"], d["observed_max_tim_ratio"]["den"])
        spec_b["max_tim_chi2"] = Fraction(d["chi2_tim"]["num"], d["chi2_tim"]["den"])
        spec_b["delta_total"] = Fraction(d["learner_half_chi2"]["num"], d["learner_half_chi2"]["den"])
        spec_b["max_second_moment"] = Fraction(d["is_second_moment"]["num"], d["is_second_moment"]["den"])
        spec_b["max_d3_upper"] = Fraction(d["d3_upper_bound"]["num"], d["d3_upper_bound"]["den"])
        spec_b["max_tail_rho"] = Fraction(1, 1)
        spec_b["dual_clip_low"] = Fraction(1, 1)
        spec_b["dual_clip_high"] = Fraction(1, 1)
        # Keep unclipped ratios at exact 1/1 for dual_clip_low=high=1 boundary
        spec_b["p"] = list(spec_b["q"])
        spec_b["delta_total"] = Fraction(1, 100)
        spec_b["max_second_moment"] = Fraction(1, 1)
        spec_b["max_d3_upper"] = Fraction(0, 1)
        spec_b["step_variance_v"] = Fraction(0, 1)
        spec_b["eta"] = Fraction(1, 1)
        res_b = mod.certify_unified_rl_step(spec_b)
        self.assertTrue(res_b["admitted"])

        # 3. Unclipped IS + none centering + no top_k + chi2_fisher_rao KL
        spec_is = _base_valid_spec()
        spec_is["weighting_mode"] = "unclipped_is"
        spec_is["centering_mode"] = "none"
        spec_is["kl_mode"] = "chi2_fisher_rao"
        spec_is["top_k_indices"] = None
        res_is = mod.certify_unified_rl_step(spec_is)
        self.assertTrue(res_is["admitted"])
        self.assertIsNone(res_is["diagnostics"]["topk_tail_rho"])

        # 4. TIS + weighted_sc + none KL + top_k
        spec_tis = _base_valid_spec()
        spec_tis["weighting_mode"] = "tis"
        spec_tis["dual_clip_high"] = Fraction(10, 9)  # clips p[0]/q[0] = 9/8 > 10/9
        spec_tis["kl_mode"] = "none"
        res_tis = mod.certify_unified_rl_step(spec_tis)
        self.assertTrue(res_tis["admitted"])

    def test_each_individual_gate_refusal_and_exact_boundaries(self) -> None:
        # G1a: TII_KERNEL_FLAGS_UNALIGNED
        s = _base_valid_spec()
        s["tii_flags_aligned"] = False
        r = mod.certify_unified_rl_step(s)
        self.assertFalse(r["admitted"])
        self.assertEqual(r["reasons"], ["TII_KERNEL_FLAGS_UNALIGNED"])

        # G1b & G1c: TII_RATIO_EXCEEDS_BOUND and TII_CHI2_EXCEEDS_BOUND (test both p_old>q and p_old<q)
        s = _base_valid_spec()
        s["p_old"] = [Fraction(1, 2), Fraction(7, 18), Fraction(1, 9)]
        s["max_tim_ratio"] = Fraction(10, 9)  # observed 9/8 = 1.125 > 10/9
        s["max_tim_chi2"] = Fraction(1, 100)  # observed 1/72 > 1/100
        r = mod.certify_unified_rl_step(s)
        self.assertIn("TII_RATIO_EXCEEDS_BOUND", r["reasons"])
        self.assertIn("TII_CHI2_EXCEEDS_BOUND", r["reasons"])
        # Exact boundary equality admits:
        s["max_tim_ratio"] = Fraction(8, 7)  # max(9/8, 8/7) == 8/7
        s["max_tim_chi2"] = Fraction(1, 72)
        self.assertTrue(mod.certify_unified_rl_step(s)["admitted"])

        # G2a: IS_SECOND_MOMENT_EXCEEDED (exact > boundary)
        s = _base_valid_spec()
        obs_m2 = mod.certify_unified_rl_step(s)["diagnostics"]["is_second_moment"]
        m2_f = Fraction(obs_m2["num"], obs_m2["den"])
        s["max_second_moment"] = m2_f
        self.assertTrue(mod.certify_unified_rl_step(s)["admitted"])
        s["max_second_moment"] = m2_f - Fraction(1, 10000)
        self.assertEqual(mod.certify_unified_rl_step(s)["reasons"], ["IS_SECOND_MOMENT_EXCEEDED"])

        # G2b: D3_DIAGNOSTIC_EXCEEDED (exact > boundary)
        s = _base_valid_spec()
        obs_d3 = mod.certify_unified_rl_step(s)["diagnostics"]["d3_upper_bound"]
        d3_f = Fraction(obs_d3["num"], obs_d3["den"])
        s["max_d3_upper"] = d3_f
        self.assertTrue(mod.certify_unified_rl_step(s)["admitted"])
        s["max_d3_upper"] = d3_f - Fraction(1, 10000)
        self.assertEqual(mod.certify_unified_rl_step(s)["reasons"], ["D3_DIAGNOSTIC_EXCEEDED"])

        # G2c: STEP_SIZE_STABILITY_VIOLATED (exact rho_step == 1 MUST reject!)
        s = _base_valid_spec()
        s["p"] = list(s["q"])  # second_moment == 1
        s["step_variance_v"] = Fraction(1, 1)  # v_eff == 1 -> eta_max == 2/(1+1) == 1
        s["eta"] = Fraction(1, 1)  # rho_step == 0 + 1 == 1 -> REJECT!
        self.assertEqual(mod.certify_unified_rl_step(s)["reasons"], ["STEP_SIZE_STABILITY_VIOLATED"])
        s["eta"] = Fraction(99, 100)  # rho_step < 1 -> ADMIT!
        self.assertTrue(mod.certify_unified_rl_step(s)["admitted"])

        # G3a: NAIVE_SC_POLICY_UNSOUND even with constant degenerate features!
        s = _base_valid_spec()
        s["centering_mode"] = "naive_sc"
        s["features"] = [Fraction(1, 1), Fraction(1, 1), Fraction(1, 1)]
        self.assertEqual(mod.certify_unified_rl_step(s)["reasons"], ["NAIVE_SC_POLICY_UNSOUND"])

        # G3b: SCORE_CENTERING_RESIDUAL_DRIFT_NONZERO on uncentered TIS AND constant-feature spoof (TRIAD-BUG-01)
        s = _base_valid_spec()
        s["weighting_mode"] = "tis"
        s["dual_clip_high"] = Fraction(10, 9)  # clips token 0 -> non-zero drift
        s["centering_mode"] = "none"
        self.assertEqual(
            mod.certify_unified_rl_step(s)["reasons"],
            ["SCORE_CENTERING_RESIDUAL_DRIFT_NONZERO"],
        )
        # Constant features [1, 1, 1] with centering_mode="none" + biased RIPO/TIS MUST STILL REJECT!
        s_cf = _base_valid_spec()
        s_cf["q"] = [Fraction(4, 9), Fraction(4, 9), Fraction(1, 9)]
        s_cf["p_old"] = list(s_cf["q"])
        s_cf["p"] = [Fraction(2, 3), Fraction(1, 6), Fraction(1, 6)]
        s_cf["features"] = [Fraction(1, 1), Fraction(1, 1), Fraction(1, 1)]
        s_cf["centering_mode"] = "none"
        s_cf["top_k_indices"] = None
        s_cf["delta_total"] = Fraction(5, 1)
        s_cf["max_second_moment"] = Fraction(5, 1)
        s_cf["max_d3_upper"] = Fraction(5, 1)
        s_cf["eta"] = Fraction(1, 5)
        self.assertEqual(
            mod.certify_unified_rl_step(s_cf)["reasons"],
            ["SCORE_CENTERING_RESIDUAL_DRIFT_NONZERO"],
        )
        s_cf["weighting_mode"] = "tis"
        s_cf["dual_clip_high"] = Fraction(5, 4)
        self.assertEqual(
            mod.certify_unified_rl_step(s_cf)["reasons"],
            ["SCORE_CENTERING_RESIDUAL_DRIFT_NONZERO"],
        )

        # G3c: Non-square dual_clip dominance inside certify_unified_rl_step (TRIAD-BUG-02b) MUST NOT crash
        s_nsq = _base_valid_spec()
        s_nsq["q"] = [Fraction(1, 2), Fraction(1, 6), Fraction(1, 3)]
        s_nsq["p_old"] = list(s_nsq["q"])
        s_nsq["p"] = [Fraction(1, 100), Fraction(98, 100), Fraction(1, 100)]
        s_nsq["delta"] = Fraction(1, 2)
        s_nsq["dual_clip_low"] = Fraction(1, 2)
        s_nsq["dual_clip_high"] = Fraction(2, 1)
        s_nsq["top_k_indices"] = None
        res_nsq = mod.certify_unified_rl_step(s_nsq)
        self.assertFalse(res_nsq["admitted"])
        self.assertIn("TRUST_REGION_BUDGET_EXCEEDED", res_nsq["reasons"])

        # G4a: TOPK_HEAD_NOT_DOMINATING_TAIL (red-team bypass: passing rare tokens as top_k!)
        s = _base_valid_spec()
        s["top_k_indices"] = [1, 2]  # q[2]=1/9 < q[0]=4/9!
        self.assertIn("TOPK_HEAD_NOT_DOMINATING_TAIL", mod.certify_unified_rl_step(s)["reasons"])

        # Exact tie at Top-K boundary (min head == max tail) MUST admit!
        s_tie = _base_valid_spec()
        s_tie["q"] = [Fraction(1, 3), Fraction(1, 3), Fraction(1, 3)]
        s_tie["p_old"] = list(s_tie["q"])
        s_tie["p"] = list(s_tie["q"])
        s_tie["top_k_indices"] = [0, 1]
        self.assertTrue(mod.certify_unified_rl_step(s_tie)["admitted"])

        # G4b: TOPK_TAIL_MASS_RATIO_EXCEEDED in BOTH directions (rho > max and 1/rho > max)
        s = _base_valid_spec()
        s["p"] = [Fraction(4, 9), Fraction(17, 36), Fraction(1, 12)]  # rho = (1/9)/(1/12) = 4/3
        s["max_tail_rho"] = Fraction(4, 3)
        self.assertTrue(mod.certify_unified_rl_step(s)["admitted"])
        s["max_tail_rho"] = Fraction(5, 4)
        self.assertIn("TOPK_TAIL_MASS_RATIO_EXCEEDED", mod.certify_unified_rl_step(s)["reasons"])

        # Reverse direction: p_tail > q_tail -> rho = 3/4, 1/rho = 4/3 > 5/4
        s_rev = _base_valid_spec()
        s_rev["p"] = [Fraction(4, 9), Fraction(15, 36), Fraction(5, 36)]  # rho = (4/36)/(5/36)=4/5 -> 1/rho=5/4
        s_rev["max_tail_rho"] = Fraction(5, 4)
        self.assertTrue(mod.certify_unified_rl_step(s_rev)["admitted"])
        s_rev["max_tail_rho"] = Fraction(6, 5)
        self.assertIn("TOPK_TAIL_MASS_RATIO_EXCEEDED", mod.certify_unified_rl_step(s_rev)["reasons"])

        # G4c: TOPK_RIPO_SPLIT_TAIL_VIOLATION (split-tail condition & dual_clip_low/high tail checks)
        s_sp = _base_valid_spec()
        s_sp["q"] = [Fraction(289, 484), Fraction(169, 484), Fraction(25, 484), Fraction(1, 484)]
        s_sp["p_old"] = list(s_sp["q"])
        s_sp["p"] = [Fraction(200, 484), Fraction(180, 484), Fraction(100, 484), Fraction(4, 484)]
        s_sp["features"] = [Fraction(0, 1), Fraction(0, 1), Fraction(1, 1), Fraction(-1, 1)]
        s_sp["delta"] = Fraction(25, 484)
        s_sp["delta_total"] = Fraction(5, 1)
        s_sp["max_second_moment"] = Fraction(10, 1)
        s_sp["max_d3_upper"] = Fraction(5, 1)
        s_sp["eta"] = Fraction(1, 10)
        r_sp = mod.certify_unified_rl_step(s_sp)
        self.assertEqual(r_sp["reasons"], ["TOPK_RIPO_SPLIT_TAIL_VIOLATION"])

        # Exact split-tail equality passes (delta = 225/484)
        s_sp["delta"] = Fraction(225, 484)
        self.assertTrue(mod.certify_unified_rl_step(s_sp)["admitted"])

        # Tail dual_clip_high violation (1/rho = 4 > dual_clip_high = 3)
        s_sp["dual_clip_high"] = Fraction(3, 1)
        self.assertIn("TOPK_RIPO_SPLIT_TAIL_VIOLATION", mod.certify_unified_rl_step(s_sp)["reasons"])

        # Tail dual_clip_low violation (rho = 4/3 -> 1/rho = 3/4 < dual_clip_low = 4/5)
        s_dl = _base_valid_spec()
        s_dl["p"] = [Fraction(4, 9), Fraction(17, 36), Fraction(1, 12)]  # 1/rho = 3/4
        s_dl["dual_clip_low"] = Fraction(4, 5)
        self.assertIn("TOPK_RIPO_SPLIT_TAIL_VIOLATION", mod.certify_unified_rl_step(s_dl)["reasons"])

        # Heterogeneous-tail bypass (TRIAD-BUG-02a): rho == 1 yet actual tail splits w_2=1/2 != 2=w_3!
        s_het = _base_valid_spec()
        s_het["q"] = [Fraction(16, 36), Fraction(15, 36), Fraction(4, 36), Fraction(1, 36)]
        s_het["p_old"] = list(s_het["q"])
        s_het["p"] = [Fraction(16, 36), Fraction(15, 36), Fraction(1, 36), Fraction(4, 36)]
        s_het["features"] = [Fraction(0, 1), Fraction(0, 1), Fraction(1, 1), Fraction(-1, 1)]
        s_het["delta"] = Fraction(1, 36)
        s_het["delta_total"] = Fraction(5, 1)
        s_het["max_second_moment"] = Fraction(5, 1)
        s_het["max_d3_upper"] = Fraction(5, 1)
        s_het["eta"] = Fraction(1, 5)
        s_het["top_k_indices"] = [0, 1]
        self.assertEqual(
            mod.certify_unified_rl_step(s_het)["reasons"],
            ["TOPK_RIPO_SPLIT_TAIL_VIOLATION"],
        )
        # Same heterogeneous tail under TIS (dual_clip_high=2 clips token 3 only -> TOPK_TAIL_WEIGHT_MISMATCH)
        s_het_tis = dict(s_het)
        s_het_tis["weighting_mode"] = "tis"
        s_het_tis["dual_clip_high"] = Fraction(2, 1)
        self.assertEqual(
            mod.certify_unified_rl_step(s_het_tis)["reasons"],
            ["TOPK_TAIL_WEIGHT_MISMATCH"],
        )
        # Modeled split-tail violation even when actual tail tokens are individually unclipped:
        # q_tail=5/16, p_tail=13/64 -> rho=20/13 -> modeled threshold 147/4160 > delta=9/256,
        # while actual tail distances are 1/64 and 9/256 (both <= delta, so actual_tail_mismatch=False).
        s_ms = _base_valid_spec()
        s_ms["q"] = [Fraction(6, 16), Fraction(5, 16), Fraction(4, 16), Fraction(1, 16)]
        s_ms["p_old"] = list(s_ms["q"])
        s_ms["p"] = [Fraction(26, 64), Fraction(25, 64), Fraction(12, 64), Fraction(1, 64)]
        s_ms["features"] = [Fraction(0, 1), Fraction(0, 1), Fraction(1, 1), Fraction(-1, 1)]
        s_ms["delta"] = Fraction(9, 256)
        s_ms["dual_clip_low"] = Fraction(1, 4)
        s_ms["delta_total"] = Fraction(5, 1)
        s_ms["max_second_moment"] = Fraction(5, 1)
        s_ms["max_d3_upper"] = Fraction(5, 1)
        s_ms["eta"] = Fraction(1, 5)
        s_ms["top_k_indices"] = [0, 1]
        self.assertEqual(
            mod.certify_unified_rl_step(s_ms)["reasons"],
            ["TOPK_RIPO_SPLIT_TAIL_VIOLATION"],
        )

        # G5a/b/c: RIPO policy flags & TRUST_REGION_BUDGET_EXCEEDED
        s = _base_valid_spec()
        s["use_true_p_old_for_ripo"] = False
        self.assertEqual(mod.certify_unified_rl_step(s)["reasons"], ["RIPO_NOISY_ROLLOUT_BASIS_POLICY"])

        s = _base_valid_spec()
        s["allow_negative_lower_clip"] = True
        self.assertEqual(mod.certify_unified_rl_step(s)["reasons"], ["RIPO_LOWER_CLIP_DEAD_ZONE_ENABLED"])

        s = _base_valid_spec()
        obs_tr = mod.certify_unified_rl_step(s)["diagnostics"]["learner_half_chi2"]
        tr_f = Fraction(obs_tr["num"], obs_tr["den"])
        s["delta_total"] = tr_f
        self.assertTrue(mod.certify_unified_rl_step(s)["admitted"])
        s["delta_total"] = tr_f - Fraction(1, 10000)
        self.assertEqual(mod.certify_unified_rl_step(s)["reasons"], ["TRUST_REGION_BUDGET_EXCEEDED"])

        # G6: NON_BREGMAN_CLIPPED_KL_REVERSAL
        s = _base_valid_spec()
        s["kl_mode"] = "clipped_ratio_kl"
        self.assertEqual(mod.certify_unified_rl_step(s)["reasons"], ["NON_BREGMAN_CLIPPED_KL_REVERSAL"])

    def test_demo_certifier_cases(self) -> None:
        cases = mod._demo_certifier_cases()
        self.assertTrue(cases["hardened_unified_step"]["admitted"])
        self.assertEqual(cases["hardened_unified_step"]["reasons"], [])
        bad = cases["multi_trap_unaligned_step"]
        self.assertFalse(bad["admitted"])
        expected_reasons = {
            "TII_KERNEL_FLAGS_UNALIGNED",
            "TII_RATIO_EXCEEDS_BOUND",
            "TII_CHI2_EXCEEDS_BOUND",
            "RIPO_NOISY_ROLLOUT_BASIS_POLICY",
            "RIPO_LOWER_CLIP_DEAD_ZONE_ENABLED",
            "TRUST_REGION_BUDGET_EXCEEDED",
            "IS_SECOND_MOMENT_EXCEEDED",
            "D3_DIAGNOSTIC_EXCEEDED",
            "STEP_SIZE_STABILITY_VIOLATED",
            "NAIVE_SC_POLICY_UNSOUND",
            "SCORE_CENTERING_RESIDUAL_DRIFT_NONZERO",
            "TOPK_TAIL_MASS_RATIO_EXCEEDED",
            "TOPK_RIPO_SPLIT_TAIL_VIOLATION",
            "NON_BREGMAN_CLIPPED_KL_REVERSAL",
        }
        self.assertEqual(set(bad["reasons"]), expected_reasons)


class TestAnchorsCertificateAndCLI(unittest.TestCase):
    def test_standalone_certificate_zero_float_and_determinism(self) -> None:
        c1 = mod.build_certificate(standalone=True)
        c2 = mod.build_certificate(standalone=True)
        self.assertEqual(c1, c2)
        self.assertEqual(c1["anchors"]["anchor_mode"], "standalone")
        self.assertIsNone(c1["anchors"]["all_anchors_matched"])
        self.assertEqual(c1["anchors"]["anchors_total"], len(mod.ANCHOR_SPECS))
        _assert_no_floats(self, c1)

        # Verify canonical_sha256 matches exact serialized payload without canonical_sha256
        copy_c = dict(c1)
        obs_hash = copy_c.pop("canonical_sha256")
        raw = json.dumps(copy_c, sort_keys=True, separators=(",", ":")).encode("utf-8")
        self.assertEqual(obs_hash, hashlib.sha256(raw).hexdigest())

    def test_verify_live_anchors_temp_missing_and_tampered(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tdir = Path(tmp)
            # Empty dir -> all missing
            res_empty = mod.verify_live_anchors(tdir)
            self.assertFalse(res_empty["all_file_digests_matched"])
            self.assertFalse(res_empty["all_anchors_matched"])
            self.assertEqual(res_empty["anchors_verified"], 0)

            # Create one file with matching anchor line but wrong SHA-256
            p = tdir / "score-centering/repo/losses.py"
            p.parent.mkdir(parents=True, exist_ok=True)
            lines = [""] * 150
            lines[120] = '        assert not c or c.stat == "ratio", "ok"'
            lines[146] = "            rho = jnp.maximum(q_tail, 0.0) / denom"
            p.write_text("\n".join(lines), encoding="utf-8")
            res_part = mod.verify_live_anchors(tdir)
            self.assertFalse(res_part["all_file_digests_matched"])
            self.assertEqual(res_part["anchors_verified"], 2)
            self.assertFalse(res_part["all_anchors_matched"])

    def test_live_repos_if_present(self) -> None:
        sibling_repos = Path(__file__).resolve().parent.parent / "repos"
        if not sibling_repos.is_dir():
            return
        cert = mod.build_certificate(repos_dir=sibling_repos, standalone=False)
        self.assertTrue(cert["anchors"]["all_file_digests_matched"])
        self.assertTrue(cert["anchors"]["all_anchors_matched"])
        self.assertEqual(cert["anchors"]["anchors_verified"], len(mod.ANCHOR_SPECS))
        _assert_no_floats(self, cert)

    def test_cli_standalone_write_cert_and_live_fail(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out_path = Path(tmp) / "cert.json"
            buf = io.StringIO()
            with mock.patch.object(sys, "stdout", buf):
                rc = mod.main(["--standalone", "--write-cert", str(out_path)])
            self.assertEqual(rc, 0)
            self.assertEqual(buf.getvalue(), "")
            loaded = json.loads(out_path.read_text(encoding="utf-8"))
            self.assertEqual(loaded["audit_id"], "AUDIT-082")
            _assert_no_floats(self, loaded)

            # --json prints stdout even when --write-cert is passed
            buf2 = io.StringIO()
            with mock.patch.object(sys, "stdout", buf2):
                rc2 = mod.main(["--standalone", "--json", "--write-cert", str(out_path)])
            self.assertEqual(rc2, 0)
            self.assertEqual(buf2.getvalue(), out_path.read_text(encoding="utf-8"))

            # Live mode against empty temp dir returns exit code 1
            buf3 = io.StringIO()
            with mock.patch.object(sys, "stdout", buf3):
                rc3 = mod.main(["--repos-dir", tmp, "--json"])
            self.assertEqual(rc3, 1)


if __name__ == "__main__":
    unittest.main(verbosity=2)
