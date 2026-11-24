#!/usr/bin/env python3
"""R1-R5 Verification, Invariance, Adversarial-Bypass & 100% Mutation-Kill Suite
for Wave 2 Round 9 Arm R9-2 (AUDIT-079: RIPO Riemannian RL Tomography).

Zero floats. Zero bare asserts. Zero external dependencies.
"""

from __future__ import annotations

from fractions import Fraction
import hashlib
import io
import json
from pathlib import Path
import sys
import tempfile
from contextlib import redirect_stdout
from typing import Any

for _p in (str(Path.cwd()), str(Path(__file__).resolve().parent)):
    if _p not in sys.path:
        sys.path.append(_p)

import ripo_riemannian_audit as mod


def check(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


def check_raises(
    exc_type: type[BaseException],
    fn: Any,
    *args: Any,
    match: str | None = None,
    **kwargs: Any,
) -> None:
    try:
        fn(*args, **kwargs)
    except exc_type as exc:
        if match is not None and match not in str(exc):
            raise AssertionError(
                f"Expected {match!r} in {exc_type.__name__} message, got {str(exc)!r}"
            )
        return
    raise AssertionError(f"Expected {exc_type.__name__} for {fn.__name__}({args}, {kwargs})")


def check_no_floats(obj: Any, path: str = "$") -> None:
    if isinstance(obj, float):
        raise AssertionError(f"Float detected at {path}: {obj!r}")
    if isinstance(obj, dict):
        for k, v in obj.items():
            check_no_floats(v, f"{path}.{k}")
    elif isinstance(obj, list):
        for idx, v in enumerate(obj):
            check_no_floats(v, f"{path}[{idx}]")


class SubFraction(Fraction):
    pass


def test_group_1_strict_validators_and_brackets() -> None:
    # require / require_int / require_bool / require_rat / require_prob
    mod.require(True, "ok")
    check_raises(ValueError, mod.require, False, "fail")

    check(mod.require_int(5, "n", min_val=5, max_val=5) == 5, "exact bounds int")
    check_raises(ValueError, mod.require_int, True, "n")
    check_raises(ValueError, mod.require_int, 4, "n", min_val=5)
    check_raises(ValueError, mod.require_int, 6, "n", max_val=5)
    check_raises(ValueError, mod.require_int, "5", "n")

    check(mod.require_bool(True, "b") is True, "bool True")
    check(mod.require_bool(False, "b") is False, "bool False")
    check_raises(ValueError, mod.require_bool, 1, "b")
    check_raises(ValueError, mod.require_bool, 0, "b")

    check(mod.require_rat(3, "q") == Fraction(3), "int rat")
    check(mod.require_rat(Fraction(2, 3), "q") == Fraction(2, 3), "frac rat")
    check_raises(ValueError, mod.require_rat, True, "q")
    check_raises(ValueError, mod.require_rat, "1/2", "q")
    check_raises(ValueError, mod.require_rat, SubFraction(1, 2), "q")

    check(mod.require_prob(Fraction(1, 2), "p", open_interval=True) == Fraction(1, 2), "open prob")
    check_raises(ValueError, mod.require_prob, Fraction(0), "p", open_interval=True)
    check_raises(ValueError, mod.require_prob, Fraction(1), "p", open_interval=True)
    check(mod.require_prob(Fraction(0), "p", open_interval=False) == Fraction(0), "closed 0")
    check(mod.require_prob(Fraction(1), "p", open_interval=False) == Fraction(1), "closed 1")
    check_raises(ValueError, mod.require_prob, Fraction(-1, 10), "p", open_interval=False)
    check_raises(ValueError, mod.require_prob, Fraction(11, 10), "p", open_interval=False)

    check(mod.rat_str(Fraction(3, 6)) == "1/2", "rat_str")
    check(mod.bracket_str((Fraction(1, 2), Fraction(3, 4))) == ["1/2", "3/4"], "bracket_str")

    # isqrt_bracket exactness & boundaries
    check(mod.isqrt_bracket(Fraction(0), 1) == (Fraction(0), Fraction(0)), "sqrt(0)")
    check(mod.isqrt_bracket(Fraction(9, 16), 8) == (Fraction(3, 4), Fraction(3, 4)), "exact square")
    lo2, hi2 = mod.isqrt_bracket(Fraction(2), 8)
    check(lo2 == Fraction(181, 128) and hi2 == Fraction(363, 256), "sqrt(2) at 8 bits")
    check(lo2 * lo2 < 2 < hi2 * hi2 and hi2 - lo2 == Fraction(1, 256), "sqrt(2) width")
    lo23, hi23 = mod.isqrt_bracket(Fraction(2, 3), 10)
    check(lo23 * lo23 < Fraction(2, 3) < hi23 * hi23, "sqrt(2/3) bracket")
    check(hi23 - lo23 == Fraction(1, 1024), "sqrt(2/3) width")
    check_raises(ValueError, mod.isqrt_bracket, Fraction(-1, 4), 8, match="must be non-negative")
    check_raises(ValueError, mod.isqrt_bracket, Fraction(2), 0)
    check_raises(ValueError, mod.isqrt_bracket, Fraction(2), 257)

    # ln_bracket exact Mercator & range reduction
    check(mod.ln_bracket(Fraction(1), 1) == (Fraction(0), Fraction(0)), "ln(1)")
    # y = 5/4 in [1, 4/3], terms=1: u = 1/9, lo = 2/9, tail = (2/3)*(1/729)/(80/81) = 1/1080
    l54_lo, l54_hi = mod.ln_bracket(Fraction(5, 4), 1)
    check(l54_lo == Fraction(2, 9) and l54_hi == Fraction(241, 1080), "exact ln(5/4) t=1")
    # y = 4/5 in [2/3, 1), terms=1: negation of ln(5/4)
    l45_lo, l45_hi = mod.ln_bracket(Fraction(4, 5), 1)
    check(l45_lo == -Fraction(241, 1080) and l45_hi == -Fraction(2, 9), "exact ln(4/5) t=1")
    # Exact boundaries 4/3 and 2/3 (exp2 == 0)
    l43_lo, l43_hi = mod.ln_bracket(Fraction(4, 3), 1)
    # u = 1/7 => lo = 2/7, tail = (2/3)*(1/343)/(48/49) = 1/504 => hi = 145/504
    check(l43_lo == Fraction(2, 7) and l43_hi == Fraction(145, 504), "exact ln(4/3) boundary")
    l23_lo, l23_hi = mod.ln_bracket(Fraction(2, 3), 1)
    # 1/(2/3) = 3/2, u = 1/5 => pos_lo = 2/5, tail = (2/3)*(1/125)/(24/25) = 1/180 => pos_hi = 73/180
    check(l23_lo == -Fraction(73, 180) and l23_hi == -Fraction(2, 5), "exact ln(2/3) boundary")
    # ln(2) at terms=2: u=1/3 => lo = 2/3 + 2/81 = 56/81, tail = (2/5)*(1/243)/(8/9) = 1/540
    l2_lo, l2_hi = mod.ln_bracket(Fraction(2), 2)
    check(l2_lo == Fraction(56, 81) and l2_hi == Fraction(1123, 1620), "exact ln(2) t=2")
    # x = 1/2 (exp2 = -1, y = 1) => exact negation of ln(2)
    lh_lo, lh_hi = mod.ln_bracket(Fraction(1, 2), 2)
    check(lh_lo == -l2_hi and lh_hi == -l2_lo, "exact ln(1/2) == -ln(2)")
    # x = 3 (exp2 = 2, y = 3/4 < 1) and x = 1/3 (exp2 = -2, y = 4/3 >= 1)
    l3_lo, l3_hi = mod.ln_bracket(Fraction(3), 12)
    l13_lo, l13_hi = mod.ln_bracket(Fraction(1, 3), 12)
    check(Fraction(10986, 10000) < l3_lo < l3_hi < Fraction(10987, 10000), "ln(3) accuracy")
    check(l13_lo < -Fraction(10986, 10000) and l13_hi > -Fraction(10987, 10000), "ln(1/3) accuracy")
    check_raises(ValueError, mod.ln_bracket, Fraction(0), 5)
    check_raises(ValueError, mod.ln_bracket, Fraction(-2), 5)
    check_raises(ValueError, mod.ln_bracket, Fraction(2), 0)
    check_raises(ValueError, mod.ln_bracket, Fraction(2), 129)

    # bernoulli_divergences_exact
    d_eq = mod.bernoulli_divergences_exact(Fraction(1, 2), Fraction(1, 2), scale_bits=16, ln_terms=8)
    check(d_eq["d_geom_single"] == 0 and d_eq["chi2_pearson_full"] == 0, "zero divergence")
    check(d_eq["h2_bracket"] == (Fraction(0), Fraction(0)), "zero H2")
    check(d_eq["kl_forward_bracket"] == (Fraction(0), Fraction(0)), "zero KL fwd")
    check(d_eq["kl_reverse_bracket"] == (Fraction(0), Fraction(0)), "zero KL rev")

    d_14_12 = mod.bernoulli_divergences_exact(Fraction(1, 4), Fraction(1, 2), scale_bits=20, ln_terms=12)
    check(d_14_12["d_geom_single"] == Fraction(1, 8), "d_geom(1/4, 1/2)")
    check(d_14_12["half_chi2_pearson_full"] == Fraction(1, 6), "half chi2(1/4, 1/2)")
    check(d_14_12["chi2_pearson_full"] == Fraction(1, 3), "chi2_pearson(1/4, 1/2)")
    check(d_14_12["chi2_neyman_full"] == Fraction(1, 4), "chi2_neyman(1/4, 1/2)")
    check(d_14_12["four_h2_bracket"][0] == 4 * d_14_12["h2_bracket"][0], "four_h2 lo")
    check(d_14_12["four_h2_bracket"][1] == 4 * d_14_12["h2_bracket"][1], "four_h2 hi")
    check(d_14_12["kl_forward_bracket"][1] < d_14_12["chi2_neyman_full"], "KL(P||Q) <= chi2(P||Q)")
    check(d_14_12["kl_reverse_bracket"][1] < d_14_12["chi2_pearson_full"], "KL(Q||P) <= chi2(Q||P)")
    check(d_14_12["kl_reverse_bracket"][0] > d_14_12["kl_forward_bracket"][1], "KL asymmetry")


def test_group_2_dual_oracle_linear_algebra() -> None:
    # bareiss_det: 1x1, swap, singular, rational 3x3, multi-pivot 4x4
    check_raises(ValueError, mod.bareiss_det, [])
    check_raises(ValueError, mod.bareiss_det, [[Fraction(1), Fraction(2)]])
    check(mod.bareiss_det([[Fraction(7, 3)]]) == Fraction(7, 3), "1x1 det")
    check(mod.bareiss_det([[Fraction(0), Fraction(1)], [Fraction(1), Fraction(0)]]) == Fraction(-1), "2x2 swap det")
    check(mod.bareiss_det([[Fraction(0), Fraction(1)], [Fraction(0), Fraction(2)]]) == Fraction(0), "zero col det")
    m3 = [
        [Fraction(1, 2), Fraction(1, 3), Fraction(0)],
        [Fraction(1, 3), Fraction(1), Fraction(1, 2)],
        [Fraction(0), Fraction(1, 2), Fraction(2)],
    ]
    # det = (1/2)*(2 - 1/4) - (1/3)*(2/3) = 7/8 - 2/9 = 47/72
    check(mod.bareiss_det(m3) == Fraction(47, 72), "3x3 rational det")
    m4 = [
        [Fraction(2), Fraction(1), Fraction(0), Fraction(3)],
        [Fraction(1), Fraction(3), Fraction(2), Fraction(1)],
        [Fraction(0), Fraction(2), Fraction(4), Fraction(1)],
        [Fraction(3), Fraction(1), Fraction(1), Fraction(5)],
    ]
    # Exact det via cofactor: verify against Faddeev-LeVerrier c_0 (even n => det == c_0)
    d4 = mod.bareiss_det(m4)
    cp4 = mod.faddeev_leverrier_charpoly(m4)
    check(d4 == Fraction(-5) and cp4[0] == Fraction(-5), "4x4 multi-pivot Bareiss == FL == -5")

    # faddeev_leverrier_charpoly errors & exact polynomial (incl. 1x1 boundary!)
    check_raises(ValueError, mod.faddeev_leverrier_charpoly, [])
    check_raises(ValueError, mod.faddeev_leverrier_charpoly, [[Fraction(1), Fraction(2)]])
    check(mod.faddeev_leverrier_charpoly([[Fraction(5)]]) == [Fraction(-5), Fraction(1)], "1x1 charpoly")
    m_indef = [
        [Fraction(1), Fraction(2), Fraction(0)],
        [Fraction(2), Fraction(-1), Fraction(0)],
        [Fraction(0), Fraction(0), Fraction(0)],
    ]
    cp_indef = mod.faddeev_leverrier_charpoly(m_indef)
    check(cp_indef == [Fraction(0), Fraction(-5), Fraction(0), Fraction(1)], "indefinite charpoly")

    # sym_inertia_dual_oracle across all signatures (incl. 1x1 & empty!)
    check_raises(ValueError, mod.sym_inertia_dual_oracle, [], match="sym_matrix: must be non-empty")
    check_raises(
        ValueError,
        mod.sym_inertia_dual_oracle,
        [[Fraction(1), Fraction(2)], [Fraction(0), Fraction(1)]],
        match="must be symmetric",
    )
    check_raises(
        ValueError,
        mod.sym_inertia_dual_oracle,
        [[Fraction(1), Fraction(2)]],
        match="sym_matrix: must be square",
    )
    r_1x1 = mod.sym_inertia_dual_oracle([[Fraction(5)]])
    check(r_1x1["inertia"] == (1, 0, 0) and r_1x1["dual_oracle_det_match"] and r_1x1["inertia_sum_exact"], "1x1 inertia")
    r_indef = mod.sym_inertia_dual_oracle(m_indef)
    check(r_indef["inertia"] == (1, 1, 1) and r_indef["dual_oracle_det_match"] and r_indef["inertia_sum_exact"], "inertia (1,1,1)")
    check(mod.sym_inertia_dual_oracle([[Fraction(-2), Fraction(0)], [Fraction(0), Fraction(-3)]])["inertia"] == (0, 0, 2), "inertia (0,0,2)")
    check(mod.sym_inertia_dual_oracle([[Fraction(3), Fraction(1)], [Fraction(1), Fraction(2)]])["inertia"] == (2, 0, 0), "inertia (2,0,0)")
    check(mod.sym_inertia_dual_oracle([[Fraction(0), Fraction(0)], [Fraction(0), Fraction(0)]])["inertia"] == (0, 2, 0), "inertia (0,2,0)")
    check(mod.sym_inertia_dual_oracle(m3)["inertia"] == (3, 0, 0), "m3 PD inertia (3,0,0)")

    # schur_complement_scalar: k=1 boundary + strict validation + row-swap Gauss-Jordan + singular rejection
    check(
        mod.schur_complement_scalar([[Fraction(2), Fraction(1)], [Fraction(1), Fraction(3)]], [0], 1)
        == Fraction(5, 2),
        "k=1 Schur == 5/2",
    )
    check_raises(ValueError, mod.schur_complement_scalar, [[Fraction(1)]], [0], 0, match="at least 2x2")
    check_raises(
        ValueError,
        mod.schur_complement_scalar,
        [[Fraction(1), Fraction(2)], [Fraction(3)]],
        [0],
        1,
        match="schur_matrix: must be square",
    )
    check_raises(
        ValueError,
        mod.schur_complement_scalar,
        [[Fraction(2), Fraction(1)], [Fraction(1), Fraction(3)]],
        [0],
        0,
        match="must not appear in active",
    )
    check_raises(
        ValueError,
        mod.schur_complement_scalar,
        [[Fraction(2), Fraction(1)], [Fraction(1), Fraction(3)]],
        [0],
        -1,
    )
    check_raises(
        ValueError,
        mod.schur_complement_scalar,
        [[Fraction(2), Fraction(1)], [Fraction(1), Fraction(3)]],
        [0],
        True,
    )
    check_raises(
        ValueError,
        mod.schur_complement_scalar,
        [[Fraction(2), Fraction(1), Fraction(0)], [Fraction(1), Fraction(3), Fraction(0)], [Fraction(0), Fraction(0), Fraction(1)]],
        [0, 0],
        2,
        match="duplicate indices",
    )
    m_swap = [
        [Fraction(0), Fraction(1), Fraction(2)],
        [Fraction(1), Fraction(0), Fraction(3)],
        [Fraction(2), Fraction(3), Fraction(20)],
    ]
    check(mod.schur_complement_scalar(m_swap, [0, 1], 2) == Fraction(8), "non-diag swap Schur == 8")
    m_gj = [
        [Fraction(2), Fraction(1), Fraction(5)],
        [Fraction(1), Fraction(2), Fraction(4)],
        [Fraction(5), Fraction(4), Fraction(20)],
    ]
    # M_AA^-1 * [5, 4] = [2, 1], quad = 5*2 + 4*1 = 14, Schur = 6
    check(mod.schur_complement_scalar(m_gj, [0, 1], 2) == Fraction(6), "general 2x2 Schur == 6")
    check_raises(ValueError, mod.schur_complement_scalar, m_gj, [], 2)
    check_raises(
        ValueError,
        mod.schur_complement_scalar,
        [[Fraction(1), Fraction(1), Fraction(1)], [Fraction(1), Fraction(1), Fraction(1)], [Fraction(1), Fraction(1), Fraction(1)]],
        [0, 1],
        2,
    )


def test_group_3_four_exact_ripo_pillars() -> None:
    cert = mod.build_certificate(standalone=True)
    check_no_floats(cert)
    check(cert["audit_id"] == "AUDIT-079", "audit_id")
    check(cert["honest_novelty"] == "N1", "novelty")
    check(cert["verdict"] == "RIPO_RIEMANNIAN_AUDIT_ALL_VERIFIED", "verdict")

    # Pillar 1: Paper & Zhihu audit
    p1 = cert["pillar_1_paper_and_zhihu_audit"]
    we = p1["worked_example_delta_1_over_50"]
    check(we["delta"] == "1/50", "worked delta")
    check(we["actual_boundary_d_geom_half_delta"] == "1/100", "half delta d_geom")
    check(we["p_0p8_reported_0p92_truncation_defect"] is True, "0.92 truncation defect")
    check(we["p_0p8_d_geom_at_reported_0p92"] == "9/1000", "d_geom at 0.92 == 9/1000")
    check(we["p_0p01_lower_clip_negative"] is True, "worked lower clip negative")
    check(we["non_isometry_full_half_chi2_ratio_exact"] == "99/20", "non-isometry 99/20")
    check(we["non_isometry_trpo_kl_ratio_gt_15"] is True, "KL ratio > 15")
    check(we["non_isometry_four_h2_ratio_gt_11"] is True, "4H^2 ratio > 11")

    t1 = p1["table1_qwen3_8b_base"]
    check(t1["Base"]["exact_avg"] == "807/70", "Base exact avg")
    check(t1["GRPO"]["exact_avg"] == "1997/70", "GRPO exact avg")
    check(t1["DAPO"]["exact_avg"] == "2143/70", "DAPO exact avg")
    check(t1["GSPO"]["exact_avg"] == "1124/35", "GSPO exact avg")
    check(t1["GMPO"]["exact_avg"] == "2469/70", "GMPO exact avg")
    check(t1["DCPO"]["exact_avg"] == "2421/70", "DCPO exact avg")
    check(t1["DCPO"]["avg_error"] == "3/35", "DCPO 8B error 3/35")
    check(t1["DCPO"]["rounding_error_exceeds_half_tenth"] is True, "DCPO 8B exceeds 0.05")
    check(t1["RIPO"]["exact_avg"] == "1346/35", "RIPO exact avg")
    check(t1["RIPO"]["exact_rel_ratio"] == "695/1997", "RIPO exact rel ratio")
    check(t1["RIPO"]["rounded_rel_ratio"] == "20/57", "RIPO rounded rel ratio")
    check(t1["RIPO"]["rounding_error_exceeds_half_tenth"] is False, "RIPO avg rounds cleanly")
    check(p1["table1_qwen3_8b_ripo_vs_grpo_double_rounding_gap"] == "325/113829", "double rounding gap")
    check(p1["table1_qwen3_4b_dcpo_avg_mismatch"]["exact_avg"] == "979/35", "DCPO 4B exact")
    check(p1["table1_qwen3_4b_dcpo_avg_mismatch"]["error"] == "6/35", "DCPO 4B error 6/35")
    check(p1["abstract_aime24_1p7b_rel_gain"] == "70/113", "AIME24 1.7B gain")
    check(p1["abstract_aime24_exceeds_60pct"] is True, "AIME24 > 60%")
    check(p1["table2_label_inversion"]["degraded_cols_with_delta_high_gt_low"] == 0, "T2 high>low == 0")
    check(p1["table2_label_inversion"]["degraded_cols_with_delta_low_gt_high"] == 3, "T2 low>high == 3")
    check(p1["table2_label_inversion"]["contradicts_sec54_prose"] is True, "T2 contradicts prose")
    check(p1["table3_smt25_copy_paste_error"]["exact_delta"] == "123/10", "T3 exact 12.3")
    check(p1["table3_smt25_copy_paste_error"]["error"] == "19/10", "T3 error 1.9")

    # Pillar 2: RIPO-GEO-01 & RIPO-GEO-02
    p2 = cert["pillar_2_boundary_and_divergence_theorems"]
    g1 = p2["RIPO_GEO_01_boundary_pathology"]
    check(g1["default_delta"] == "1/20", "default delta")
    check(g1["upper_simplex_overflow_root"] == "4/5", "upper root 4/5")
    check(g1["upper_root_exact_verified"] is True, "upper root exact")
    check(g1["interior_two_sided_window_width"] == "3/4", "window width 3/4")
    check(g1["witness_p_1_over_80"]["lower_bound"] == "-1/1", "L = -1")
    check(g1["witness_p_1_over_80"]["upper_bound"] == "3/1", "U = 3")
    check(g1["witness_p_1_over_80"]["neg_adv_surrogate_at_r_1_over_100"] == "-1/100", "unclipped -1/100")
    check(g1["witness_p_1_over_80"]["negative_advantage_unclipped"] is True, "neg adv unclipped")
    check(g1["witness_p_1_over_500"]["lower_bound"] == "-4/1", "L = -4")
    check(g1["witness_p_1_over_500"]["upper_bound"] == "6/1", "U = 6")
    check(g1["sec51_dual_clip_lower_isometry_cutoff"] == "1/5", "dual low cutoff 1/5")
    check(g1["sec51_dual_clip_upper_isometry_cutoff"] == "1/1620", "dual high cutoff 1/1620")

    g2 = p2["RIPO_GEO_02_rare_token_divergence_ladder"]
    check(g2["delta"] == "1/25" and g2["m10_d_geom_over_kl_fwd_gt_50"] is True, "ladder m10 > 50x")
    pts = g2["points"]
    check(len(pts) == 4, "4 ladder points")
    check([pt["exact_two_sqrt_diff_sq"] for pt in pts] == ["2/225", "1/200", "1/450", "2/3025"], "exact 2*(sqrt q - sqrt p)^2")
    check([pt["p_old"] for pt in pts] == ["1/225", "1/1600", "1/14400", "1/245025"], "exact ladder p_old")
    check([pt["q_ripo_upper"] for pt in pts] == ["4/225", "9/1600", "1/576", "4/9801"], "exact ladder q_upper")
    check(pts[-1]["d_geom_over_kl_fwd_gt_ratio"] == 51, "m=10 ratio floor 51")

    # Pillar 3: RIPO-GEO-03 variance decomposition
    p3 = cert["pillar_3_variance_decomposition"]
    w3 = p3["witnesses"]
    check(w3["rare_p_1_over_500"]["v_raw_upper"] == "9/125", "rare v_raw 9/125")
    check(w3["rare_p_1_over_500"]["v_centered_exact"] == "1/20", "rare v_centered 1/20")
    check(w3["mid_p_1_over_5"]["v_raw_upper"] == "9/20", "mid v_raw 9/20")
    check(w3["high_p_4_over_5"]["v_raw_upper"] == "5/4", "high v_raw 5/4")
    check(w3["high_p_4_over_5"]["v_raw_lower"] == "9/20", "high v_raw_lower 9/20")
    check(w3["high_p_4_over_5"]["v_raw_over_delta"] == "25/1", "high v_raw 25x delta")
    check(w3["high_p_4_over_5"]["upper_lower_asymmetry_4s"] == "4/5", "asymmetry 4/5")
    check(p3["high_over_rare_v_raw_ratio"] == "625/36", "high/rare ratio 625/36")

    # Pillar 4: RIPO-FS-04 AUDIT-064 WI-4 bridge
    p4 = cert["pillar_4_fisher_schur_bridge_audit064"]
    check(p4["fisher_matrix_diag"] == ["9/4", "49/2", "0/1"], "WI-4 F_p diag")
    check(p4["fisher_krein_inertia"] == [2, 1, 0], "WI-4 inertia")
    check(p4["schur_kernel_curvature"] == "0/1", "WI-4 Schur kernel 0/1")
    check(p4["steps"]["raw"]["dp"] == ["3/4", "-3/8", "-3/8"], "raw dp")
    check(p4["steps"]["raw"]["full_half_chi2"] == "9/8", "raw full 9/8")
    check(p4["steps"]["raw"]["tok0_ripo_d_geom"] == "9/16", "raw tok0 9/16")
    check(p4["steps"]["pre"]["dp"] == ["3/20", "5/8", "-31/40"], "pre dp")
    check(p4["steps"]["pre"]["full_half_chi2"] == "401/200", "pre full 401/200")
    check(p4["steps"]["pre"]["tok0_ripo_d_geom"] == "9/400", "pre tok0 9/400")
    check(p4["steps"]["schur"]["full_half_chi2"] == "0/1", "schur full 0/1")
    check(p4["pre_over_raw_full_kl_inflation"] == "401/225", "KL inflation 401/225")
    check(p4["pre_over_raw_tok0_ripo_shrink"] == "1/25", "tok0 shrink 1/25")
    check(p4["pre_tok0_share_of_full"] == "9/802", "tok0 share 9/802")
    check(
        p4["j_p_conservation_exact"]
        and p4["j_p_pullback_exact"]
        and p4["f_p_matches_audit064_exact"]
        and p4["dual_oracle_det_match"]
        and p4["inertia_sum_exact"]
        and p4["verified"],
        "Pillar 4 boolean proof witnesses",
    )
    check(
        p2["verified"] and p3["verified"] and g1["eps_identities_exact"] and g2["all_d_geom_constant_exact"],
        "Pillars 2-3 boolean proof witnesses",
    )
    check(
        cert["pillar_5_hardened_trust_region_guard"]["upper_overflow_hardened_guard"]["upper_overflow_prevented"] is True,
        "cert upper overflow prevented witness",
    )


def test_group_4_hardened_guards_unseen_and_adversarial() -> None:
    # Unseen-instance global certification of compute_symmetric_chi2_safe_bounds
    for p, d in [
        (Fraction(1, 10000), Fraction(1, 20)),
        (Fraction(1, 80), Fraction(1, 20)),
        (Fraction(1, 2), Fraction(1, 20)),
        (Fraction(9999, 10000), Fraction(1, 20)),
        (Fraction(1, 3), Fraction(1, 2)),
    ]:
        q_lo, q_hi = mod.compute_symmetric_chi2_safe_bounds(p, d, scale_bits=24)
        check(Fraction(0) < q_lo < p < q_hi < Fraction(1), f"strict interior ({p}, {d})")
        for q_end in (q_lo, q_hi):
            diff2 = (q_end - p) ** 2
            check(diff2 <= d * p * (1 - p), "fwd Pearson <= delta")
            check(diff2 <= d * q_end * (1 - q_end), "rev Neyman <= delta")
            divs = mod.bernoulli_divergences_exact(p, q_end, scale_bits=20, ln_terms=14)
            check(divs["kl_forward_bracket"][1] <= d, "global KL(P||Q) <= delta")
            check(divs["kl_reverse_bracket"][1] <= d, "global KL(Q||P) <= delta")

    check_raises(ValueError, mod.compute_symmetric_chi2_safe_bounds, Fraction(1, 2), Fraction(1, 20), scale_bits=3)
    check_raises(ValueError, mod.compute_symmetric_chi2_safe_bounds, Fraction(1, 2), Fraction(1, 20), scale_bits=257)
    # Exact precision-sufficiency boundary kills for s_fwd_lo == 0, q_rev_lo == p, p == q_rev_hi
    check_raises(
        ValueError,
        mod.compute_symmetric_chi2_safe_bounds,
        Fraction(1, 10000),
        Fraction(1, 20),
        scale_bits=4,
        match="forward bracket",
    )
    # p=1/1000, d=125/499, bits=4 => d*(1-2p)=1/4 exact => s_rev_lo=4/16 => q_rev_lo == p!
    # Wait: s_fwd_lo at p=1/1000, d=125/499, bits=4 is isqrt(0.00025*256)/16 = 0;
    # use p=1/100, d=25/98 (d*(1-2p)=1/4 exact), bits=4 => s_fwd=isqrt(0.0025*256)=0;
    # at bits=6: d*(1-2p) = 1/4 = 16/64, sqrt(d*p*(1-p)) = sqrt(0.255*0.0099) ~ 0.0502 => 3/64 > 0!
    # disc = (1/4)^2 + 4*(25/98)*(123/98)*(99/10000) ~ 0.0625 + 0.0127 = 0.0752 => sqrt(disc) ~ 0.274 > 17/64.
    # For bits=6 with q_rev_lo == p and s_fwd_lo > 0: need p small enough that sqrt(disc) - d*(1-2p) < 1/64
    # while sqrt(d*p*(1-p)) >= 1/64: choose p=1/200, d=100/396? Let's use exact p=1/400, d=100/199 (d*(1-2p)=1/2=32/64):
    # sqrt(d*p*(1-p)) ~ sqrt(0.5*0.0025) = 0.0353 >= 2/64 > 0!
    # disc = 1/4 + 4*(100/199)*(299/199)*(399/160000) ~ 0.25 + 0.0075 = 0.2575 => sqrt(disc) ~ 0.5074 < 33/64 = 0.515625!
    check_raises(
        ValueError,
        mod.compute_symmetric_chi2_safe_bounds,
        Fraction(1, 400),
        Fraction(100, 199),
        scale_bits=6,
        match="lower reverse bracket",
    )
    check_raises(
        ValueError,
        mod.compute_symmetric_chi2_safe_bounds,
        Fraction(399, 400),
        Fraction(100, 199),
        scale_bits=6,
        match="upper reverse bracket",
    )

    # Guard mode coverage + exact polynomial boundary check (<= vs <)
    # Exact boundary: p = 1/2, d = 1/16 => d*p*(1-p) = 1/64, sqrt = 1/8 => q = 5/8:
    # fwd: (1/8)^2 == 1/64 == d*p*(1-p), rev: d*q*(1-q) = (1/16)*(15/64) = 15/1024 < 1/64 => CLIP_UPPER_GUARD!
    g_rev_edge = mod.evaluate_ripo_trust_region_hardened(
        Fraction(1, 2), Fraction(5, 8), Fraction(1, 16), Fraction(1)
    )
    check(g_rev_edge["verdict"] == "CLIP_UPPER_GUARD", "reverse chi2 tightens upper edge")
    # Exact fwd+rev interior equality: p = 1/5, q = 3/10, d = 1/16? Wait: (q-p)^2 = 1/100;
    # p*(1-p) = 4/25 => d = (1/100)/(4/25) = 1/16 exact! And q*(1-q) = 21/100 > 4/25 => rev_ok strict!
    g_fwd_eq = mod.evaluate_ripo_trust_region_hardened(
        Fraction(1, 5), Fraction(3, 10), Fraction(1, 16), Fraction(1)
    )
    check(g_fwd_eq["verdict"] == "ALLOW_UNCLIPPED", "exact fwd equality allowed")
    # Exact rev equality with strict fwd: p = 3/10, q = 1/5, d = 1/16 => (q-p)^2 = 1/100 == (1/16)*(4/25) = d*q*(1-q)!
    g_rev_eq = mod.evaluate_ripo_trust_region_hardened(
        Fraction(3, 10), Fraction(1, 5), Fraction(1, 16), Fraction(-1)
    )
    check(g_rev_eq["verdict"] == "ALLOW_UNCLIPPED", "exact rev equality allowed")

    # Lower guard clip when p > d (lower_dead_zone_prevented == False)
    g_low_mid = mod.evaluate_ripo_trust_region_hardened(
        Fraction(1, 2), Fraction(1, 10), Fraction(1, 20), Fraction(-2)
    )
    check(g_low_mid["verdict"] == "CLIP_LOWER_GUARD", "mid lower clipped")
    check(g_low_mid["lower_dead_zone_prevented"] is False, "p > d not dead zone")
    check(g_low_mid["upper_overflow_prevented"] is False, "p=1/2 not overflow")

    # Upper guard clip with upper_overflow_prevented == True (p = 9/10, d = 1/20)
    g_hi_ovf = mod.evaluate_ripo_trust_region_hardened(
        Fraction(9, 10), Fraction(99, 100), Fraction(1, 20), Fraction(1)
    )
    check(g_hi_ovf["verdict"] == "CLIP_UPPER_GUARD", "upper overflow clipped")
    check(g_hi_ovf["upper_overflow_prevented"] is True, "upper overflow prevented")

    # Regression tests for RIPO-BUG-01 & RIPO-BUG-02 (exact p*=4/5 root & scale_bits=4 consistency)
    # (a) Exact root p* = 4/5, d = 1/20 => d*p == (1-p)^2 => BOTH guard and raw flag simplex overflow!
    g_root_guard = mod.evaluate_ripo_trust_region_hardened(
        Fraction(4, 5), Fraction(99, 100), Fraction(1, 20), Fraction(1)
    )
    g_root_raw = mod.evaluate_ripo_trust_region_hardened(
        Fraction(4, 5), Fraction(99, 100), Fraction(1, 20), Fraction(1), mode="ripo_raw", scale_bits=4
    )
    check(g_root_guard["upper_overflow_prevented"] is True, "RIPO-BUG-02: p*=4/5 guard overflow True")
    check(g_root_raw["upper_clip_exceeds_simplex"] is True, "RIPO-BUG-02: p*=4/5 raw overflow True")
    # Just below root p = 4/5 - 1/1000 => BOTH False even at scale_bits=4!
    g_below_root_raw = mod.evaluate_ripo_trust_region_hardened(
        Fraction(4, 5) - Fraction(1, 1000), Fraction(9, 10), Fraction(1, 20), Fraction(1), mode="ripo_raw", scale_bits=4
    )
    g_below_root_guard = mod.evaluate_ripo_trust_region_hardened(
        Fraction(4, 5) - Fraction(1, 1000), Fraction(9, 10), Fraction(1, 20), Fraction(1)
    )
    check(g_below_root_raw["upper_clip_exceeds_simplex"] is False, "below p* raw overflow False")
    check(g_below_root_guard["upper_overflow_prevented"] is False, "below p* guard overflow False")
    # (b) RIPO-BUG-01a: p = 1/20 - 1/1000, q = 1/1000, d = 1/20, adv = -1, scale_bits = 4
    d_b1a = mod.evaluate_ripo_trust_region_hardened(
        Fraction(1, 20) - Fraction(1, 1000),
        Fraction(1, 1000),
        Fraction(1, 20),
        Fraction(-1),
        mode="ripo_raw",
        scale_bits=4,
    )
    check(d_b1a["verdict"] == "DIAGNOSTIC_DEAD_ZONE_UNCLIPPED", "RIPO-BUG-01a dead zone verdict")
    check(d_b1a["lower_clip_negative"] is True and Fraction(d_b1a["lower_bound"]) < 0, "RIPO-BUG-01a lower_bound < 0")
    # (c) RIPO-BUG-01b: p = 4/5 + 1/10000, q = 99/100, d = 1/20, scale_bits = 4
    d_b1b_guard = mod.evaluate_ripo_trust_region_hardened(
        Fraction(4, 5) + Fraction(1, 10000), Fraction(99, 100), Fraction(1, 20), Fraction(1), scale_bits=4
    )
    d_b1b_raw = mod.evaluate_ripo_trust_region_hardened(
        Fraction(4, 5) + Fraction(1, 10000), Fraction(99, 100), Fraction(1, 20), Fraction(1), mode="ripo_raw", scale_bits=4
    )
    check(d_b1b_guard["upper_overflow_prevented"] is True and d_b1b_raw["upper_clip_exceeds_simplex"] is True, "RIPO-BUG-01b consistent overflow")
    # (d) ripo_dual_0p5_10 upper overflow check: at p = 1/20, d = 19/20 => 10*p = 1/2 < 1 so dual caps at 1/2 < 1!
    d_dual_cap_ok = mod.evaluate_ripo_trust_region_hardened(
        Fraction(1, 20), Fraction(2, 5), Fraction(19, 20), Fraction(1), mode="ripo_dual_0p5_10", scale_bits=4
    )
    check(d_dual_cap_ok["upper_clip_exceeds_simplex"] is False, "dual cap 10*p < 1 avoids overflow")
    d_dual_ovf = mod.evaluate_ripo_trust_region_hardened(
        Fraction(4, 5), Fraction(99, 100), Fraction(1, 20), Fraction(1), mode="ripo_dual_0p5_10", scale_bits=4
    )
    check(d_dual_ovf["upper_clip_exceeds_simplex"] is True, "dual at p=4/5 still overflows")

    # Diagnostic modes: ripo_raw & ripo_dual_0p5_10
    d_raw_dead = mod.evaluate_ripo_trust_region_hardened(
        Fraction(1, 80), Fraction(1, 8000), Fraction(1, 20), Fraction(-1), mode="ripo_raw"
    )
    check(d_raw_dead["verdict"] == "DIAGNOSTIC_DEAD_ZONE_UNCLIPPED", "raw dead zone hit")
    check(d_raw_dead["lower_clip_negative"] is True and d_raw_dead["upper_clip_exceeds_simplex"] is False, "raw flags")
    check(d_raw_dead["ratio_clipped"] == "1/100" and d_raw_dead["surrogate_value"] == "-1/100", "raw unclipped")

    d_raw_pos = mod.evaluate_ripo_trust_region_hardened(
        Fraction(1, 80), Fraction(1, 8000), Fraction(1, 20), Fraction(1), mode="ripo_raw"
    )
    check(d_raw_pos["verdict"] == "DIAGNOSTIC_EVALUATED", "adv > 0 not dead zone")
    d_raw_up = mod.evaluate_ripo_trust_region_hardened(
        Fraction(9, 10), Fraction(99, 100), Fraction(1, 20), Fraction(-1), mode="ripo_raw"
    )
    check(d_raw_up["verdict"] == "DIAGNOSTIC_EVALUATED" and d_raw_up["upper_clip_exceeds_simplex"] is True, "raw upper overflow")

    d_dual_lo = mod.evaluate_ripo_trust_region_hardened(
        Fraction(1, 80), Fraction(1, 8000), Fraction(1, 20), Fraction(-1), mode="ripo_dual_0p5_10"
    )
    check(d_dual_lo["verdict"] == "DIAGNOSTIC_EVALUATED", "dual not dead zone")
    check(d_dual_lo["lower_bound"] == "1/2" and d_dual_lo["ratio_clipped"] == "1/2", "dual lower 1/2 clamp")
    check(d_dual_lo["upper_bound"] == "3/1", "dual upper unclamped at 1/80")

    d_dual_hi = mod.evaluate_ripo_trust_region_hardened(
        Fraction(1, 2000), Fraction(1, 100), Fraction(1, 20), Fraction(1), mode="ripo_dual_0p5_10"
    )
    check(d_dual_hi["upper_bound"] == "10/1" and d_dual_hi["ratio_clipped"] == "10/1", "dual upper 10 clamp")
    check(d_dual_hi["surrogate_value"] == "10/1", "dual upper surrogate 10")

    # Reject bad guard arguments (incl. unconditional scale_bits check BEFORE q == 0 early return!)
    check_raises(ValueError, mod.evaluate_ripo_trust_region_hardened, Fraction(1, 2), Fraction(1, 2), Fraction(1, 20), Fraction(1), mode="invalid")
    check_raises(ValueError, mod.evaluate_ripo_trust_region_hardened, Fraction(0), Fraction(1, 2), Fraction(1, 20), Fraction(1))
    check_raises(ValueError, mod.evaluate_ripo_trust_region_hardened, Fraction(1, 2), Fraction(-1, 10), Fraction(1, 20), Fraction(1))
    check_raises(ValueError, mod.evaluate_ripo_trust_region_hardened, Fraction(1, 2), Fraction(1, 2), Fraction(1), Fraction(1))
    check_raises(ValueError, mod.evaluate_ripo_trust_region_hardened, Fraction(1, 2), Fraction(0), Fraction(1, 20), Fraction(-1), scale_bits=True)
    check_raises(ValueError, mod.evaluate_ripo_trust_region_hardened, Fraction(1, 2), Fraction(0), Fraction(1, 20), Fraction(-1), scale_bits=3)
    check_raises(ValueError, mod.evaluate_ripo_trust_region_hardened, Fraction(1, 2), Fraction(0), Fraction(1, 20), Fraction(-1), scale_bits=257)

    # Full-simplex guard tests (all branches!)
    s_pass = mod.verify_simplex_step_hardened(
        [Fraction(1, 2), Fraction(1, 4), Fraction(1, 4)],
        [Fraction(51, 100), Fraction(49, 200), Fraction(49, 200)],
        Fraction(1, 20),
        Fraction(1, 40),
    )
    check(s_pass["verdict"] == "PASS" and s_pass["cauchy_schwarz_verified"] is True, "simplex pass")
    check(s_pass["chi2_pearson"] == "1/2500", "exact chi2_pearson")
    check(s_pass["cauchy_schwarz_lower_bound"] == "1/2500", "exact CS lb equality")
    s_nonprop = mod.verify_simplex_step_hardened(
        [Fraction(1, 2), Fraction(1, 4), Fraction(1, 4)],
        [Fraction(51, 100), Fraction(24, 100), Fraction(25, 100)],
        Fraction(1, 20),
        Fraction(1, 40),
    )
    check(s_nonprop["verdict"] == "PASS" and s_nonprop["cauchy_schwarz_verified"] is True, "nonprop pass")
    check(s_nonprop["chi2_pearson"] == "3/5000", "nonprop chi2 == 3/5000")
    check(s_nonprop["cauchy_schwarz_lower_bound"] == "1/1875", "nonprop CS lb")

    # Fail strictly by Neyman chi2 while Pearson chi2 <= delta & KL <= kl_budget:
    # p_old = [1/2, 1/2], p_new = [4/5, 1/5]:
    # chi2_pearson = 0.09/0.5 + 0.09/0.5 = 9/25 = 0.36
    # chi2_neyman = 0.09/0.8 + 0.09/0.2 = 9/80 + 9/20 = 45/80 = 9/16 = 0.5625
    # KL(P||Q) = 0.5*ln(5/8) + 0.5*ln(5/2) = 0.5*ln(25/16) ~ 0.223 < 1/2
    s_neyman_fail = mod.verify_simplex_step_hardened(
        [Fraction(1, 2), Fraction(1, 2)],
        [Fraction(4, 5), Fraction(1, 5)],
        Fraction(2, 5),  # 0.40 >= 0.36 (Pearson OK), < 0.5625 (Neyman FAILS!)
        Fraction(1, 2),  # 0.50 > 0.223 (KL OK)
    )
    check(s_neyman_fail["verdict"] == "REJECT_TRUST_REGION_EXCEEDED", "Neyman failure caught")

    # Fail strictly by KL budget while BOTH Pearson and Neyman chi2 <= delta:
    s_kl_fail = mod.verify_simplex_step_hardened(
        [Fraction(1, 2), Fraction(1, 2)],
        [Fraction(4, 5), Fraction(1, 5)],
        Fraction(3, 5),  # 0.60 >= 0.5625 (both chi2 OK)
        Fraction(1, 10),  # 0.10 < 0.223 (KL FAILS!)
    )
    check(s_kl_fail["verdict"] == "REJECT_TRUST_REGION_EXCEEDED", "KL budget failure caught")

    # Fail strictly by Pearson chi2 while Neyman <= delta & KL <= budget:
    # p_old = [4/5, 1/5], p_new = [1/2, 1/2]:
    # chi2_pearson = 9/16 = 0.5625, chi2_neyman = 9/25 = 0.36, KL(P||Q) ~ 0.1927
    s_pearson_fail = mod.verify_simplex_step_hardened(
        [Fraction(4, 5), Fraction(1, 5)],
        [Fraction(1, 2), Fraction(1, 2)],
        Fraction(2, 5),  # 0.40 < 0.5625 (Pearson FAILS!), >= 0.36 (Neyman OK)
        Fraction(1, 2),  # KL OK
    )
    check(s_pearson_fail["verdict"] == "REJECT_TRUST_REGION_EXCEEDED", "Pearson failure caught")

    # Support collapse at non-zero index
    s_zero = mod.verify_simplex_step_hardened(
        [Fraction(1, 2), Fraction(1, 4), Fraction(1, 4)],
        [Fraction(3, 4), Fraction(1, 4), Fraction(0)],
        Fraction(1, 20),
        Fraction(1, 40),
    )
    check(s_zero["verdict"] == "REJECT_SUPPORT_COLLAPSE" and s_zero["collapsed_index"] == 2, "support collapse idx 2")

    # Invalid simplex inputs (incl. unconditional ln_terms validation BEFORE support-collapse early return!)
    check_raises(ValueError, mod.verify_simplex_step_hardened, (Fraction(1, 2), Fraction(1, 2)), [Fraction(1, 2), Fraction(1, 2)], Fraction(1, 20), Fraction(1, 40))
    check_raises(ValueError, mod.verify_simplex_step_hardened, [Fraction(1)], [Fraction(1)], Fraction(1, 20), Fraction(1, 40))
    check_raises(ValueError, mod.verify_simplex_step_hardened, [Fraction(1, 2), Fraction(1, 2)], [Fraction(1, 3), Fraction(1, 3), Fraction(1, 3)], Fraction(1, 20), Fraction(1, 40))
    check_raises(ValueError, mod.verify_simplex_step_hardened, [Fraction(1, 2), Fraction(1, 2)], [Fraction(1), Fraction(0)], Fraction(1, 20), Fraction(1, 40), ln_terms=True)
    check_raises(ValueError, mod.verify_simplex_step_hardened, [Fraction(1, 2), Fraction(1, 2)], [Fraction(1), Fraction(0)], Fraction(1, 20), Fraction(1, 40), ln_terms=0)
    check_raises(ValueError, mod.verify_simplex_step_hardened, [Fraction(1, 2), Fraction(1, 2)], [Fraction(1), Fraction(0)], Fraction(1, 20), Fraction(1, 40), ln_terms=129)
    check_raises(
        ValueError,
        mod.verify_simplex_step_hardened,
        [Fraction(1, 2), Fraction(2, 3)],
        [Fraction(1, 2), Fraction(1, 2)],
        Fraction(1, 20),
        Fraction(1, 40),
        match="p_old must sum to 1",
    )
    check_raises(
        ValueError,
        mod.verify_simplex_step_hardened,
        [Fraction(1, 2), Fraction(1, 2)],
        [Fraction(1, 2), Fraction(2, 3)],
        Fraction(1, 20),
        Fraction(1, 40),
        match="p_new must sum to 1",
    )


def test_group_5_anchors_determinism_and_cli() -> None:
    a_standalone = mod.verify_read_only_anchors(
        standalone=True, expected_digests=("0" * 64, "0" * 64, "0" * 64)
    )
    check(
        a_standalone["anchor_mode"] == "standalone"
        and a_standalone["all_digests_verified"] is True
        and a_standalone["arxiv_2607_10169_pdf_sha256"] == mod.PINNED_ARXIV_PDF_SHA256,
        "standalone anchors ignore spoofed expected_digests",
    )
    check_raises(ValueError, mod.verify_read_only_anchors, standalone=1)

    c_sa_1 = mod.build_certificate(standalone=True)
    c_sa_2 = mod.build_certificate(standalone=True)
    check(c_sa_1 == c_sa_2, "standalone determinism")
    check_no_floats(c_sa_1)

    # Multi-chunk _sha256_file (>65536 bytes) + fail-closed mismatch test
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        big_file = root / "big.bin"
        raw_bytes = b"RIPO-AUDIT-079" * 6000
        big_file.write_bytes(raw_bytes)
        check(
            mod._sha256_file(big_file) == hashlib.sha256(raw_bytes).hexdigest(),
            "multi-chunk sha256 exact",
        )
        # Isolated sandbox testing BOTH passing and per-file fail-closed SHA-256 verification
        r9_base = root / "round9"
        (r9_base / "repos" / "ripo").mkdir(parents=True)
        (r9_base / "repos" / "zhihu").mkdir(parents=True)
        (root / "round6" / "arm4-weight-iteration").mkdir(parents=True)
        pdf_p = r9_base / "repos" / "ripo" / "arxiv_2607.10169.pdf"
        zh_p = r9_base / "repos" / "zhihu" / "zhihu_2098101007368640039_ripo.md"
        a064_p = root / "round6" / "arm4-weight-iteration" / "warp_weight_iteration_certificate.json"
        pdf_p.write_bytes(b"pdf-fixture")
        zh_p.write_bytes(b"zhihu-fixture")
        a064_p.write_bytes(b"audit064-fixture")
        h_pdf = hashlib.sha256(b"pdf-fixture").hexdigest()
        h_zh = hashlib.sha256(b"zhihu-fixture").hexdigest()
        h_a064 = hashlib.sha256(b"audit064-fixture").hexdigest()
        a_ok = mod.verify_read_only_anchors(
            standalone=False, anchors_base=r9_base, expected_digests=(h_pdf, h_zh, h_a064)
        )
        check(a_ok["anchor_mode"] == "live_read_only" and a_ok["all_digests_verified"] is True, "sandbox match")
        check_raises(
            ValueError,
            mod.verify_read_only_anchors,
            standalone=False,
            anchors_base=r9_base,
            expected_digests=("0" * 64, h_zh, h_a064),
            match="arXiv PDF SHA-256 mismatch",
        )
        check_raises(
            ValueError,
            mod.verify_read_only_anchors,
            standalone=False,
            anchors_base=r9_base,
            expected_digests=(h_pdf, "0" * 64, h_a064),
            match="Zhihu transcript SHA-256 mismatch",
        )
        check_raises(
            ValueError,
            mod.verify_read_only_anchors,
            standalone=False,
            anchors_base=r9_base,
            expected_digests=(h_pdf, h_zh, "0" * 64),
            match="AUDIT-064 cert SHA-256 mismatch",
        )

        # CLI --write-cert (silent stdout) and --write-cert --json (both)
        buf_w = io.StringIO()
        with redirect_stdout(buf_w):
            rc_w = mod.main(["--standalone", "--write-cert"], out_dir=root)
        check(rc_w == 0 and buf_w.getvalue() == "", "CLI write-cert silent stdout")
        written = (root / "ripo_riemannian_certificate.json").read_text(encoding="utf-8")
        check(written.endswith("\n") and json.loads(written)["canonical_sha256"] == c_sa_1["canonical_sha256"], "written cert matches")

        buf_wj = io.StringIO()
        with redirect_stdout(buf_wj):
            rc_wj = mod.main(["--standalone", "--write-cert", "--json"], out_dir=root)
        check(rc_wj == 0 and buf_wj.getvalue() == written, "CLI write-cert + json matches")

    # Live read-only anchors when running inside full expedition tree
    live_pdf = Path(__file__).resolve().parent.parent / "repos" / "ripo" / "arxiv_2607.10169.pdf"
    if live_pdf.is_file():
        a_live = mod.verify_read_only_anchors(standalone=False)
        check(a_live["anchor_mode"] == "live_read_only" and a_live["all_digests_verified"] is True, "live anchors")
        check(a_live["arxiv_2607_10169_pdf_sha256"] == mod.PINNED_ARXIV_PDF_SHA256, "live pdf sha")
        check(a_live["zhihu_2098101007368640039_md_sha256"] == mod.PINNED_ZHIHU_MD_SHA256, "live zhihu sha")
        check(a_live["audit064_certificate_json_sha256"] == mod.PINNED_AUDIT064_CERT_SHA256, "live audit064 sha")
        buf2 = io.StringIO()
        with redirect_stdout(buf2):
            rc2 = mod.main([])
        check(rc2 == 0, "CLI default live rc == 0")
        parsed2 = json.loads(buf2.getvalue())
        check(parsed2["pinned_read_only_anchors"]["anchor_mode"] == "live_read_only", "CLI live mode")
        check_no_floats(parsed2)

    buf = io.StringIO()
    with redirect_stdout(buf):
        rc = mod.main(["--standalone"])
    check(rc == 0, "CLI standalone rc == 0")
    parsed = json.loads(buf.getvalue())
    check(parsed["pinned_read_only_anchors"]["anchor_mode"] == "standalone", "CLI standalone mode")
    check_raises(ValueError, mod.main, ["--unknown-flag"])


def run_all() -> int:
    test_group_1_strict_validators_and_brackets()
    test_group_2_dual_oracle_linear_algebra()
    test_group_3_four_exact_ripo_pillars()
    test_group_4_hardened_guards_unseen_and_adversarial()
    test_group_5_anchors_determinism_and_cli()
    sys.stdout.write("TEST_R5_RIPO_RIEMANNIAN_ALL_PASS\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(run_all())
