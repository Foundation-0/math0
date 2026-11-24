"""Comprehensive R5 mutation-killing & red-team test suite for AUDIT-083 (BPO).

Covers BOTH bpo_bellman_oracle.py AND bpo_bellman_audit.py under -I -O -B -W error
with zero bare assert statements and zero floats on trust paths.
"""

from __future__ import annotations

import contextlib
from fractions import Fraction
import hashlib
import io
import json
from pathlib import Path
import sys
import tempfile
from typing import Any, Callable

_SCRIPT_DIR = str(Path(__file__).resolve().parent)
if _SCRIPT_DIR not in sys.path:
    sys.path.insert(0, _SCRIPT_DIR)

import bpo_bellman_audit as audit_mod
import bpo_bellman_oracle as oracle


class TestFailure(RuntimeError):
    """Explicit assertion-free test failure."""


def check_eq(actual: Any, expected: Any, label: str) -> None:
    if actual != expected or type(actual) is not type(expected):
        raise TestFailure(f"{label}: expected {expected!r} ({type(expected).__name__}), got {actual!r} ({type(actual).__name__})")


def check_raises(fn: Callable[[], Any], expected_code: str, label: str) -> None:
    try:
        fn()
    except oracle.BpoOracleError as exc:
        if exc.code != expected_code:
            raise TestFailure(f"{label}: expected code {expected_code!r}, got {exc.code!r} ({exc})") from exc
        return
    raise TestFailure(f"{label}: expected BpoOracleError({expected_code!r}) but succeeded")


def test_primitives_and_refusals() -> None:
    oracle.verify_no_floats({"a": [1, (2, "x"), {3}]})
    check_raises(lambda: oracle.verify_no_floats(1.5), "FLOAT_FORBIDDEN", "scalar float")
    check_raises(lambda: oracle.verify_no_floats({1.0: "x"}), "FLOAT_FORBIDDEN", "dict key float")
    check_raises(lambda: oracle.verify_no_floats({"a": [1.0]}), "FLOAT_FORBIDDEN", "nested float")

    check_eq(oracle.require_non_empty_str("  ok ", "f"), "ok", "strip str")
    check_raises(lambda: oracle.require_non_empty_str(1, "f"), "TYPE_ERROR", "non-str")
    check_raises(lambda: oracle.require_non_empty_str("   ", "f"), "EMPTY_STRING", "blank str")

    check_eq(oracle.require_exact_bool(True, "b"), True, "bool True")
    check_raises(lambda: oracle.require_exact_bool(1, "b"), "TYPE_ERROR", "int not bool")

    check_eq(oracle.require_exact_int(3, "i"), 3, "int 3")
    check_raises(lambda: oracle.require_exact_int(False, "i"), "TYPE_ERROR", "bool not int")
    check_raises(lambda: oracle.require_exact_int(3.0, "i"), "TYPE_ERROR", "float not int")

    check_eq(oracle.require_exact_fraction(Fraction(1, 3), "x"), Fraction(1, 3), "Fraction")
    check_eq(oracle.require_exact_fraction(-2, "x"), Fraction(-2, 1), "int")
    check_eq(oracle.require_exact_fraction("0.25", "x"), Fraction(1, 4), "dec str")
    check_eq(oracle.require_exact_fraction("-3/5", "x"), Fraction(-3, 5), "frac str")
    check_raises(lambda: oracle.require_exact_fraction(True, "x"), "TYPE_ERROR", "bool frac")
    check_raises(lambda: oracle.require_exact_fraction(0.25, "x"), "FLOAT_FORBIDDEN", "float frac")
    check_raises(lambda: oracle.require_exact_fraction("1/0", "x"), "ZERO_DENOMINATOR", "div0")
    check_raises(lambda: oracle.require_exact_fraction("1.0\n", "x"), "INVALID_RATIONAL", "newline")
    check_raises(lambda: oracle.require_exact_fraction([], "x"), "TYPE_ERROR", "list frac")

    check_eq(oracle.require_prob_vector(["0", "1"], "p"), (Fraction(0, 1), Fraction(1, 1)), "boundary simplex")
    check_eq(oracle.require_prob_vector(["1/2", "1/2"], "p", require_positive=True), (Fraction(1, 2), Fraction(1, 2)), "pos simplex")
    check_raises(lambda: oracle.require_prob_vector("10", "p"), "TYPE_ERROR", "str not prob vec")
    check_raises(lambda: oracle.require_prob_vector(["1"], "p"), "INVALID_LENGTH", "len < 2")
    check_raises(lambda: oracle.require_prob_vector(["-1/2", "3/2"], "p"), "INVALID_PROBABILITY", "neg prob")
    check_raises(lambda: oracle.require_prob_vector(["2", "-1"], "p"), "INVALID_PROBABILITY", ">1 prob")
    check_raises(lambda: oracle.require_prob_vector(["0", "1"], "p", require_positive=True), "INVALID_PROBABILITY", "0 not positive")
    check_raises(lambda: oracle.require_prob_vector(["1", "0"], "p", require_positive=True), "INVALID_PROBABILITY", "1 not <1")
    check_raises(lambda: oracle.require_prob_vector(["1/3", "1/3"], "p"), "SIMPLEX_SUM_ERROR", "sum != 1")

    check_eq(oracle.frac_str(Fraction(4, 2)), "2/1", "frac_str")
    check_raises(lambda: oracle.frac_str(2), "TYPE_ERROR", "frac_str non-Fraction")
    check_eq(oracle.format_exact_decimal(Fraction(1, 2), 0), "1", "0dp half up")
    check_eq(oracle.format_exact_decimal(Fraction(1, 3), 0), "0", "0dp below half")
    check_eq(oracle.format_exact_decimal(Fraction(-1, 200), 2), "-0.01", "neg half up")
    check_eq(oracle.format_exact_decimal(Fraction(-1, 1000), 2), "0.00", "neg zero no sign")
    check_raises(lambda: oracle.format_exact_decimal(1, 2), "TYPE_ERROR", "format non-Fraction")
    check_raises(lambda: oracle.format_exact_decimal(Fraction(1, 2), -1), "INVALID_RANGE", "neg places")

    check_eq(oracle.canonical_json_bytes({"b": 1, "a": 2}), b'{"a":2,"b":1}', "canonical json")
    check_eq(len(oracle.canonical_sha256({"a": 1})), 64, "sha len")
    check_raises(lambda: oracle.canonical_json_bytes({"a": 1.0}), "FLOAT_FORBIDDEN", "json float")


def test_pillar1_theorem1() -> None:
    rew = {"00": "1", "01": "0", "10": "0", "11": "0"}
    opt = oracle.verify_pmd_bellman_theorem1_exact(rew, ["1/2", "1/2"], ["1/2", "1/2"], ["1/2", "1/2"], 4)
    check_eq(opt["v_root"], "1/4", "v_root 1/4")
    check_eq(opt["v_s0"], "1/2", "v_s0 1/2")
    check_eq(opt["v_s1"], "0/1", "v_s1 0")
    check_eq(opt["telescoping_verified"], True, "telescoping ok")
    check_eq(opt["partition_kl_identity_verified"], True, "partition kl ok")
    check_eq(opt["martingale_identity_verified"], True, "martingale ok")
    check_eq(opt["all_reachable_residuals_zero"], True, "all residuals 1/1")
    check_eq(opt["matches_pi_plus_on_reachable"], True, "matches pi+")
    check_eq(opt["theorem1_iff_verified"], True, "iff verified")
    check_eq(opt["linearized_step1_grad_root_z0_at_pi_plus"], "-1/8", "step1 linearization breaks fixed point")
    check_eq(opt["linearization_destroys_pmd_fixed_point"], True, "fixed point destroyed")

    # Perturbed reachable state breaks trajectory residual
    pert = oracle.verify_pmd_bellman_theorem1_exact(
        rew, ["1/2", "1/2"], ["1/2", "1/2"], ["1/2", "1/2"], 4,
        candidate_policy={"root": ["4/5", "1/5"], "s0": ["1/2", "1/2"], "s1": ["1/2", "1/2"]},
    )
    check_eq(pert["martingale_identity_verified"], True, "martingale still holds for perturbed policy")
    check_eq(pert["all_reachable_residuals_zero"], False, "perturbed fails zero residual")
    check_eq(pert["matches_pi_plus_on_reachable"], False, "perturbed != pi+")
    check_eq(pert["theorem1_iff_verified"], True, "iff holds on perturbed")

    # Unreachable s1 branch (mu_root = [1, 0]) permits arbitrary s1 policy while preserving residual == 1
    unr = oracle.verify_pmd_bellman_theorem1_exact(
        rew, ["1", "0"], ["1/2", "1/2"], ["1/2", "1/2"], 4,
        candidate_policy={"root": ["1", "0"], "s0": ["16/17", "1/17"], "s1": ["9/10", "1/10"]},
    )
    check_eq(unr["trajectory_exp_delta_pow_d"]["10"], "UNREACHABLE", "10 unreachable")
    check_eq(unr["all_reachable_residuals_zero"], True, "reachable residuals zero")
    check_eq(unr["theorem1_iff_verified"], True, "iff holds with unreachable branch")
    check_eq(unr["linearization_destroys_pmd_fixed_point"], False, "degenerate root var=0")

    # Symmetric unreachable s0 branch (mu_root = [0, 1]) + negative reward boundary -1
    rew_neg = {"00": "0", "01": "0", "10": "-1", "11": "1"}
    unr_s0 = oracle.verify_pmd_bellman_theorem1_exact(
        rew_neg, ["0", "1"], ["1/2", "1/2"], ["1/2", "1/2"], 1,
        candidate_policy={"root": ["0", "1"], "s0": ["9/10", "1/10"], "s1": ["1/5", "4/5"]},
    )
    check_eq(unr_s0["trajectory_exp_delta_pow_d"]["00"], "UNREACHABLE", "00 unreachable")
    check_eq(unr_s0["all_reachable_residuals_zero"], True, "s1 branch optimal")

    # Red-team: candidate violating absolute continuity (pi in Pi_mu) MUST fail closed!
    check_raises(
        lambda: oracle.verify_pmd_bellman_theorem1_exact(
            rew, ["1", "0"], ["1/2", "1/2"], ["1/2", "1/2"], 4,
            candidate_policy={"root": ["1/2", "1/2"], "s0": ["16/17", "1/17"], "s1": ["1/2", "1/2"]},
        ),
        "ABSOLUTE_CONTINUITY_VIOLATION",
        "pi outside supp(mu) refused",
    )

    # Red-team: candidate assigning 0 where mu > 0 MUST fail closed (KL = +inf)
    check_raises(
        lambda: oracle.verify_pmd_bellman_theorem1_exact(
            rew, ["1/2", "1/2"], ["1/2", "1/2"], ["1/2", "1/2"], 4,
            candidate_policy={"root": ["1", "0"], "s0": ["16/17", "1/17"], "s1": ["1/2", "1/2"]},
        ),
        "SUPPORT_VIOLATION",
        "pi=0 where mu>0 refused",
    )

    # Schema & range refusals
    check_raises(lambda: oracle.verify_pmd_bellman_theorem1_exact({"00": "1"}, ["1/2", "1/2"], ["1/2", "1/2"], ["1/2", "1/2"], 4), "SCHEMA_ERROR", "bad rewards keys")
    check_raises(lambda: oracle.verify_pmd_bellman_theorem1_exact({"00": "2", "01": "0", "10": "0", "11": "0"}, ["1/2", "1/2"], ["1/2", "1/2"], ["1/2", "1/2"], 4), "INVALID_RANGE", "R > 1")
    check_raises(lambda: oracle.verify_pmd_bellman_theorem1_exact({"00": "-2", "01": "0", "10": "0", "11": "0"}, ["1/2", "1/2"], ["1/2", "1/2"], ["1/2", "1/2"], 4), "INVALID_RANGE", "R < -1")
    check_raises(lambda: oracle.verify_pmd_bellman_theorem1_exact(rew, ["1/3", "1/3", "1/3"], ["1/2", "1/2"], ["1/2", "1/2"], 4), "INVALID_LENGTH", "non-binary mu_root")
    check_raises(lambda: oracle.verify_pmd_bellman_theorem1_exact(rew, ["1/2", "1/2"], ["1/2", "1/2"], ["1/2", "1/2"], 0), "INVALID_RANGE", "eta <= 0")
    check_raises(lambda: oracle.verify_pmd_bellman_theorem1_exact(rew, ["1/2", "1/2"], ["1/2", "1/2"], ["1/2", "1/2"], 1), "NON_INTEGER_EXPONENT", "non-int eta*A")
    check_raises(lambda: oracle.verify_pmd_bellman_theorem1_exact(rew, ["1/2", "1/2"], ["1/2", "1/2"], ["1/2", "1/2"], 200), "INVALID_RANGE", "exponent > 64")
    check_raises(
        lambda: oracle.verify_pmd_bellman_theorem1_exact(rew, ["1/2", "1/2"], ["1/2", "1/2"], ["1/2", "1/2"], 4, candidate_policy={"root": ["1/2", "1/2"]}),
        "SCHEMA_ERROR",
        "bad cand keys",
    )
    check_raises(
        lambda: oracle.verify_pmd_bellman_theorem1_exact(
            rew, ["1/2", "1/2"], ["1/2", "1/2"], ["1/2", "1/2"], 4,
            candidate_policy={"root": ["1/3", "1/3", "1/3"], "s0": ["1/2", "1/2"], "s1": ["1/2", "1/2"]},
        ),
        "INVALID_LENGTH",
        "non-binary cand",
    )


def test_pillar2_duality_and_pillar3_drift() -> None:
    # Rare exploration token (10x IS ratio -> BPO omega = 1099/1090, unclipped)
    rare = oracle.analyze_bpo_complementary_weight_and_duality(
        ["1/100", "49/100", "1/2"], ["1/1000", "499/1000", "1/2"], 0, "1/10", "3", "1/5", "7/25", "1"
    )
    check_eq(rare["importance_ratio_r"], "10/1", "10x IS")
    check_eq(rare["smoothed_weight_omega"], "1099/1090", "BPO omega")
    check_eq(rare["mask_m"], 1, "unclipped mask")
    check_eq(rare["score_centering_top1_duality_exact"], True, "SC Top-1 duality")
    check_eq(rare["jacobian_cancellation_exact"], True, "Jacobian cancel")
    check_eq(rare["unsmoothed_logit_grad_l1"], "999/500", "2*(1-mu)")
    check_eq(rare["cap_active_area_unit_square"], "8/75", "C=3 eps=0.1 area")

    # Mask zeroing branches: adv > 0 & omega > 1 + eps_high, and adv < 0 & omega < 1 - eps_low
    mask_hi = oracle.analyze_bpo_complementary_weight_and_duality(
        ["9/10", "1/10"], ["1/2", "1/2"], 0, "1/10", "3", "1/5", "7/25", "1"
    )
    check_eq(mask_hi["mask_m"], 0, "positive adv masked")
    check_eq(mask_hi["effective_weight"], "0/1", "masked effective weight 0")

    mask_lo = oracle.analyze_bpo_complementary_weight_and_duality(
        ["1/10", "9/10"], ["9/10", "1/10"], 0, "1/10", "3", "1/5", "7/25", "-1"
    )
    check_eq(mask_lo["mask_m"], 0, "negative adv masked")
    check_eq(mask_lo["effective_weight"], "0/1", "neg masked weight 0")

    # Cap globally dead when C >= (1+eps)/eps (BPO-BUG-02b: cap_dead_for_positive_adv MUST also be True!)
    dead_cap = oracle.analyze_bpo_complementary_weight_and_duality(
        ["1/2", "1/2"], ["1/2", "1/2"], 0, "1/2", "3", "1/5", "3", "0"
    )
    check_eq(dead_cap["cap_active_area_unit_square"], "0/1", "eps=1/2 C=3 cap area 0")
    check_eq(dead_cap["cap_mu_max_at_pi1"], "0/1", "mu_max 0")
    check_eq(dead_cap["cap_dead_for_positive_adv"], True, "cap_dead_for_positive_adv True when cap_area==0 (BPO-BUG-02b)")

    # eps == 0 branch (p_y < 1), plus p_y == 1 with eps > 0 (singular unsmoothed but finite smoothed) & q_y == 0
    eps0 = oracle.analyze_bpo_complementary_weight_and_duality(
        ["1/2", "1/2"], ["0", "1"], 0, "0", "2", "1/5", "7/25", "-1"
    )
    check_eq(eps0["importance_ratio_r"], "INF", "q=0 gives INF IS ratio")
    check_eq(eps0["cap_active_area_unit_square"], "1/4", "eps=0 C=2 area 1/(2C)=1/4")
    check_eq(eps0["omega_max_global"], "INF", "eps=0 max INF")

    py1 = oracle.analyze_bpo_complementary_weight_and_duality(
        ["1", "0"], ["1/2", "1/2"], 0, "1/10", "3", "1/5", "7/25", "-1"
    )
    check_eq(py1["unsmoothed_weight_rho_top1"], "SINGULAR", "p=1 singular unsmoothed")
    check_eq(py1["smoothed_weight_omega"], "6/1", "p=1 smoothed 6")
    check_eq(py1["effective_weight"], "3/1", "capped at C=3")
    check_eq(py1["score_centering_top1_duality_exact"], False, "no duality at p=1")

    # Refusals for Pillar 2
    check_raises(lambda: oracle.analyze_bpo_complementary_weight_and_duality(["1", "0"], ["1/2", "1/2"], 0, "0", "3", "1/5", "7/25", "1"), "SINGULAR_COMPLEMENTARY_RATIO", "eps=0 p=1 singular")
    check_raises(lambda: oracle.analyze_bpo_complementary_weight_and_duality(["1/2", "1/2"], ["1/3", "1/3", "1/3"], 0, "1/10", "3", "1/5", "7/25", "1"), "LENGTH_MISMATCH", "len mismatch")
    check_raises(lambda: oracle.analyze_bpo_complementary_weight_and_duality(["1/2", "1/2"], ["1/2", "1/2"], -1, "1/10", "3", "1/5", "7/25", "1"), "INVALID_RANGE", "idx < 0")
    check_raises(lambda: oracle.analyze_bpo_complementary_weight_and_duality(["1/2", "1/2"], ["1/2", "1/2"], 2, "1/10", "3", "1/5", "7/25", "1"), "INVALID_RANGE", "idx >= len")
    check_raises(lambda: oracle.analyze_bpo_complementary_weight_and_duality(["1/2", "1/2"], ["1/2", "1/2"], 0, "-1/10", "3", "1/5", "7/25", "1"), "INVALID_RANGE", "eps < 0")
    check_raises(lambda: oracle.analyze_bpo_complementary_weight_and_duality(["1/2", "1/2"], ["1/2", "1/2"], 0, "1/10", "1", "1/5", "7/25", "1"), "INVALID_RANGE", "cap <= 1")
    check_raises(lambda: oracle.analyze_bpo_complementary_weight_and_duality(["1/2", "1/2"], ["1/2", "1/2"], 0, "1/10", "3", "0", "7/25", "1"), "INVALID_RANGE", "elow <= 0")
    check_raises(lambda: oracle.analyze_bpo_complementary_weight_and_duality(["1/2", "1/2"], ["1/2", "1/2"], 0, "1/10", "3", "1", "7/25", "1"), "INVALID_RANGE", "elow >= 1")
    check_raises(lambda: oracle.analyze_bpo_complementary_weight_and_duality(["1/2", "1/2"], ["1/2", "1/2"], 0, "1/10", "3", "1/5", "0", "1"), "INVALID_RANGE", "ehigh <= 0")

    # Pillar 3: |V|=2 vs |V|=3 drift dichotomy
    d2_0 = oracle.audit_bpo_vs_score_centering_drift_exact(["1/4", "3/4"], ["1/2", "1/2"], "0")
    check_eq(d2_0["bpo_unsmoothed_zero_drift"], True, "binary eps=0 exact zero drift")
    check_eq(d2_0["bpo_smoothed_zero_drift"], True, "binary eps=0 smoothed==unsmoothed")

    d2_1 = oracle.audit_bpo_vs_score_centering_drift_exact(["1/4", "3/4"], ["1/2", "1/2"], "1/10")
    check_eq(d2_1["bpo_smoothed_drift_l1"], "12/119", "binary eps=0.1 non-zero drift")
    check_eq(d2_1["bpo_smoothed_zero_drift"], False, "smoothing breaks binary zero drift")

    d3_0 = oracle.audit_bpo_vs_score_centering_drift_exact(["1/4", "1/2", "1/4"], ["1/2", "1/4", "1/4"], "0")
    check_eq(d3_0["bpo_unsmoothed_drift"], ["3/32", "-5/48", "1/96"], "trinary exact drift vector")
    check_eq(d3_0["bpo_unsmoothed_drift_l1"], "5/24", "trinary drift l1")
    check_eq(d3_0["bpo_unsmoothed_zero_drift"], False, "binary KL breaks zero drift on |V|>=3")
    check_eq(d3_0["full_score_centering_zero_drift"], True, "full SC zero drift")

    check_raises(lambda: oracle.audit_bpo_vs_score_centering_drift_exact(["1/2", "1/2"], ["1/3", "1/3", "1/3"], "0"), "LENGTH_MISMATCH", "drift len mismatch")
    check_raises(lambda: oracle.audit_bpo_vs_score_centering_drift_exact(["1/2", "1/2"], ["1/2", "1/2"], "-1"), "INVALID_RANGE", "drift eps < 0")


def test_pillar4_gate_and_pillar5_tables() -> None:
    # Certified case (binary, canceled eps=0, R3 on, adv <= 0, mask_m=1)
    ok_g = oracle.evaluate_bpo_trust_region_gate("4/5", "1/2", "-1", "0", "3", "1/5", "7/25", 2, True, True)
    check_eq(ok_g["status"], "CERTIFIED", "certified gate")
    check_eq(ok_g["mask_m"], 1, "certified mask_m 1")
    check_eq(ok_g["violation_codes"], [], "0 violations")

    # Boundary tests killing >= / > / <= / < mutants on every violation predicate
    # 1) BPO_SINGULAR_AUTODIFF boundary: p_y == 99/100 triggers, p_y == 98/100 does not
    g_sing_hit = oracle.evaluate_bpo_trust_region_gate("99/100", "99/100", "0", "0", "3", "1/5", "7/25", 2, True, False)
    check_eq(g_sing_hit["violation_codes"], ["BPO_SINGULAR_AUTODIFF"], "p=0.99 triggers singular")
    g_sing_ok = oracle.evaluate_bpo_trust_region_gate("98/100", "98/100", "0", "0", "3", "1/5", "7/25", 2, True, False)
    check_eq(g_sing_ok["status"], "CERTIFIED", "p=0.98 clean")

    # 2) BPO_OVERCONFIDENT_DAMPING boundary: holds iff damping < 1/2 (1 - p_y < eps) for any eps > 0
    g_damp_hit = oracle.evaluate_bpo_trust_region_gate("85/100", "85/100", "-1", "1/5", "3", "1/5", "3", 2, True, False)
    check_eq(g_damp_hit["violation_codes"], ["BPO_OVERCONFIDENT_DAMPING"], "p=0.85 eps=0.2 damping=3/7 < 1/2 triggers")
    g_damp_ok = oracle.evaluate_bpo_trust_region_gate("9/10", "9/10", "-1", "1/10", "3", "1/5", "3", 2, True, False)
    check_eq(g_damp_ok["status"], "CERTIFIED", "p=0.90 eps=0.1 damping=1/2 clean")

    # 3) BPO_CAP_MASK_DEAD_CONFLICT boundary: 1 + ehigh > cap_c clean, 1 + ehigh <= cap_c (incl. ==) triggers
    g_cap_ok = oracle.evaluate_bpo_trust_region_gate("1/2", "1/2", "1", "1/10", "3", "1/5", "3", 2, True, False)
    check_eq(g_cap_ok["status"], "CERTIFIED", "1+ehigh=4 > cap=3 clean")
    g_cap_eq = oracle.evaluate_bpo_trust_region_gate("1/2", "1/2", "1", "1/10", "3", "1/5", "2", 2, True, False)
    check_eq(g_cap_eq["violation_codes"], ["BPO_CAP_MASK_DEAD_CONFLICT"], "1+ehigh == cap=3 still dead for adv>0")
    g_cap_hit = oracle.evaluate_bpo_trust_region_gate("1/2", "1/2", "1", "1/10", "3", "1/5", "7/25", 2, True, False)
    check_eq(g_cap_hit["violation_codes"], ["BPO_CAP_MASK_DEAD_CONFLICT"], "1+ehigh < cap triggers")

    # 4) BPO-BUG-01: binary smoothed off-policy drift triggers BPO_SMOOTHED_BINARY_DRIFT_ACTIVE
    g_bin_drift = oracle.evaluate_bpo_trust_region_gate("1/4", "1/2", "-1", "1/10", "3", "1/2", "3", 2, True, False)
    check_eq(g_bin_drift["violation_codes"], ["BPO_SMOOTHED_BINARY_DRIFT_ACTIVE"], "binary smoothed drift caught (BPO-BUG-01)")

    # 5) BPO-BUG-02a: globally unreachable cap (cap * eps >= 1 + eps) rejected regardless of adv sign
    g_cap_unreach = oracle.evaluate_bpo_trust_region_gate("1/2", "1/2", "-1", "1/2", "3", "1/5", "3/2", 2, True, False)
    check_eq(g_cap_unreach["violation_codes"], ["BPO_CAP_GLOBALLY_UNREACHABLE"], "cap=3 eps=1/2 unreachable (BPO-BUG-02a)")
    g_cap_reach = oracle.evaluate_bpo_trust_region_gate("1/2", "1/2", "-1", "1/2", "2", "1/5", "3/2", 2, True, False)
    check_eq(g_cap_reach["status"], "CERTIFIED", "cap=2 eps=1/2 reachable boundary")

    # 6) BPO-BUG-03a: globally dead lower mask ((1-elow)*(1+eps) <= eps) & globally dead upper mask ((1+ehigh)*eps >= 1+eps)
    g_lo_dead = oracle.evaluate_bpo_trust_region_gate("1/2", "1/2", "-1", "1/2", "2", "2/3", "3/2", 2, True, False)
    check_eq(g_lo_dead["violation_codes"], ["BPO_LOWER_MASK_GLOBALLY_DEAD"], "1-elow == eps/(1+eps) dead boundary")
    g_lo_dead2 = oracle.evaluate_bpo_trust_region_gate("1/2", "1/2", "-1", "1/2", "2", "7/10", "3/2", 2, True, False)
    check_eq(g_lo_dead2["violation_codes"], ["BPO_LOWER_MASK_GLOBALLY_DEAD"], "elow=7/10 eps=1/2 dead (BPO-BUG-03a)")
    g_hi_dead = oracle.evaluate_bpo_trust_region_gate("1/2", "1/2", "-1", "1/2", "2", "1/5", "2", 2, True, False)
    check_eq(g_hi_dead["violation_codes"], ["BPO_UPPER_MASK_GLOBALLY_DEAD"], "1+ehigh == (1+eps)/eps upper dead boundary")

    # 7) BPO-BUG-03b: actively clipped/zeroed tokens (M_t^i == 0) rejected on BOTH negative & positive advantages
    g_clip_neg = oracle.evaluate_bpo_trust_region_gate("1/10", "9/10", "-1", "0", "3", "1/5", "7/25", 2, True, True)
    check_eq(g_clip_neg["mask_m"], 0, "neg adv masked")
    check_eq(g_clip_neg["violation_codes"], ["BPO_TRUST_REGION_CLIPPED"], "neg clip caught (BPO-BUG-03b)")
    g_clip_pos = oracle.evaluate_bpo_trust_region_gate("4/5", "1/2", "1", "0", "6/5", "1/5", "1/4", 2, True, True)
    check_eq(g_clip_pos["mask_m"], 0, "pos adv masked")
    check_eq(g_clip_pos["violation_codes"], ["BPO_TRUST_REGION_CLIPPED"], "pos clip caught (BPO-BUG-03b)")

    # 8) BPO_MULTITOKEN_DRIFT_ACTIVE + BPO_MOE_TIM_UNMITIGATED
    g_multi = oracle.evaluate_bpo_trust_region_gate("1/2", "1/3", "0", "1/10", "3", "1/5", "3", 3, False, False)
    check_eq(g_multi["violation_codes"], ["BPO_MULTITOKEN_DRIFT_ACTIVE", "BPO_MOE_TIM_UNMITIGATED"], "v=3 off-policy + no R3")

    # Gate input refusals
    check_raises(lambda: oracle.evaluate_bpo_trust_region_gate("0", "1/2", "1", "0", "3", "1/5", "1", 2, True, False), "INVALID_PROBABILITY", "pi=0")
    check_raises(lambda: oracle.evaluate_bpo_trust_region_gate("1", "1/2", "1", "0", "3", "1/5", "1", 2, True, False), "INVALID_PROBABILITY", "pi=1")
    check_raises(lambda: oracle.evaluate_bpo_trust_region_gate("1/2", "0", "1", "0", "3", "1/5", "1", 2, True, False), "INVALID_PROBABILITY", "mu=0")
    check_raises(lambda: oracle.evaluate_bpo_trust_region_gate("1/2", "1", "1", "0", "3", "1/5", "1", 2, True, False), "INVALID_PROBABILITY", "mu=1")
    check_raises(lambda: oracle.evaluate_bpo_trust_region_gate("1/2", "1/2", "1", "-1/10", "3", "1/5", "1", 2, True, False), "INVALID_RANGE", "eps<0")
    check_raises(lambda: oracle.evaluate_bpo_trust_region_gate("1/2", "1/2", "1", "0", "1", "1/5", "1", 2, True, False), "INVALID_RANGE", "cap<=1")
    check_raises(lambda: oracle.evaluate_bpo_trust_region_gate("1/2", "1/2", "1", "0", "3", "0", "1", 2, True, False), "INVALID_RANGE", "elow<=0")
    check_raises(lambda: oracle.evaluate_bpo_trust_region_gate("1/2", "1/2", "1", "0", "3", "1", "1", 2, True, False), "INVALID_RANGE", "elow>=1")
    check_raises(lambda: oracle.evaluate_bpo_trust_region_gate("1/2", "1/2", "1", "0", "3", "1/5", "0", 2, True, False), "INVALID_RANGE", "ehigh<=0")
    check_raises(lambda: oracle.evaluate_bpo_trust_region_gate("1/2", "1/2", "1", "0", "3", "1/5", "1", 1, True, False), "INVALID_RANGE", "vocab<2")
    check_raises(lambda: oracle.evaluate_bpo_trust_region_gate("1/2", "1/2", "1", "1/10", "3", "1/5", "1", 2, True, True), "INCONSISTENT_CONFIG", "canceled+eps>0")

    # Pillar 5: Tables audit + bad rounding + boundary scores [0, 100] + duplicates + schema
    t_ok = oracle.audit_bpo_empirical_tables_exact(list(audit_mod.STANDALONE_TABLE_ROWS))
    check_eq(t_ok["row_count"], 14, "14 rows")
    check_eq(t_ok["all_rounding_ok"], True, "all 14 rows round ok")
    check_eq(t_ok["max_abs_diff"], "1/30", "max diff 1/30")

    t_bad = oracle.audit_bpo_empirical_tables_exact(
        [{"table": "T", "method": "M", "aime24": "0", "aime25": "100", "aime26": "50", "reported_avg": "51.0"}]
    )
    check_eq(t_bad["all_rounding_ok"], False, "wrong avg flagged")

    check_raises(lambda: oracle.audit_bpo_empirical_tables_exact([]), "EMPTY_SEQUENCE", "empty rows")
    check_raises(lambda: oracle.audit_bpo_empirical_tables_exact("abc"), "EMPTY_SEQUENCE", "str rows")
    check_raises(lambda: oracle.audit_bpo_empirical_tables_exact([{"bad": 1}]), "SCHEMA_ERROR", "bad row keys")
    row_a = {"table": "T", "method": "M", "aime24": "10", "aime25": "20", "aime26": "30", "reported_avg": "20.0"}
    check_raises(lambda: oracle.audit_bpo_empirical_tables_exact([row_a, row_a]), "DUPLICATE_ID", "dup row")
    check_raises(lambda: oracle.audit_bpo_empirical_tables_exact([dict(row_a, aime24="-1")]), "INVALID_RANGE", "score < 0")
    check_raises(lambda: oracle.audit_bpo_empirical_tables_exact([dict(row_a, aime24="101")]), "INVALID_RANGE", "score > 100")


def test_audit_runner_and_refusals() -> None:
    cert_s = audit_mod.run_audit(standalone=True)
    check_eq(cert_s["verdict"], "VERIFIED", "standalone verified")
    check_eq(cert_s["verbatim_spec_checks"]["bpo_clip_numeric_specified_in_tex"], False, "clip omitted")

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        out_file = tmp_path / "bpo_cert.json"

        buf_j = io.StringIO()
        with contextlib.redirect_stdout(buf_j):
            rc = audit_mod.main(["--standalone", "--json", "--output", str(out_file)])
        check_eq(rc, 0, "cli json rc=0")
        check_eq(out_file.read_text(encoding="ascii"), buf_j.getvalue(), "output file == stdout")

        buf_s = io.StringIO()
        with contextlib.redirect_stdout(buf_s):
            rc2 = audit_mod.main(["--standalone"])
        check_eq(rc2, 0, "cli summary rc=0")
        check_eq(json.loads(buf_s.getvalue())["certificate_sha256"], cert_s["certificate_sha256"], "summary sha matches")

        # Parser & BPO-BUG-04 clip-spec detector tests
        check_raises(lambda: audit_mod._parse_latex_aime_tables("\\label{tab:mainaime}\n\\end{table}\n"), "PARSE_ERROR", "fewer than 14 rows")
        check_eq(audit_mod._has_bpo_clip_numeric_spec("BPO uses $\\epsilon=0.1$ and $C=3.0$."), False, "default spec has no clip bounds")
        check_eq(audit_mod._has_bpo_clip_numeric_spec("Set\n$\\epsilon_{\\mathrm{low}} = 0.2$\nfor mask."), True, "multiline eps_low detected (BPO-BUG-04)")
        check_eq(audit_mod._has_bpo_clip_numeric_spec("BPO uses clipping interval\n$[0.85, 1.25]$."), True, "non-DAPO BPO interval detected (BPO-BUG-04)")

        # Live repo missing file & SHA mismatch refusals
        empty_repo = tmp_path / "empty_bpo"
        empty_repo.mkdir()
        check_raises(lambda: audit_mod.run_audit(standalone=False, repo_dir=empty_repo), "MISSING_FILE", "missing pdf")

        bad_sha_repo = tmp_path / "bad_sha_bpo"
        (bad_sha_repo / "latex_src").mkdir(parents=True)
        (bad_sha_repo / "2609.15987.pdf").write_bytes(b"corrupt")
        check_raises(lambda: audit_mod.run_audit(standalone=False, repo_dir=bad_sha_repo), "SHA_MISMATCH", "corrupt pdf sha")

        # Tampered anchor test (by temporarily overriding PINNED_ARTIFACT_SHA256 in a controlled unit test)
        orig_pins = dict(audit_mod.PINNED_ARTIFACT_SHA256)
        try:
            anch_repo = tmp_path / "anch_bpo"
            (anch_repo / "latex_src").mkdir(parents=True)
            pdf_b = b"pdf"
            txt_b = b"txt"
            tex_b = b"missing anchors"
            (anch_repo / "2609.15987.pdf").write_bytes(pdf_b)
            (anch_repo / "2609.15987.txt").write_bytes(txt_b)
            (anch_repo / "latex_src" / "main.tex").write_bytes(tex_b)
            audit_mod.PINNED_ARTIFACT_SHA256["2609.15987.pdf"] = hashlib.sha256(pdf_b).hexdigest()
            audit_mod.PINNED_ARTIFACT_SHA256["2609.15987.txt"] = hashlib.sha256(txt_b).hexdigest()
            audit_mod.PINNED_ARTIFACT_SHA256["latex_src/main.tex"] = hashlib.sha256(tex_b).hexdigest()
            check_raises(lambda: audit_mod.run_audit(standalone=False, repo_dir=anch_repo), "ANCHOR_MISMATCH", "missing verbatim anchor")

            # Missing required Table 1 method refusal (14 valid rows, none named BPO)
            fake_rows = "\n".join(
                f"M{i} & 50.0 & 50.0 & 50.0 & 50.0 \\\\" for i in range(14)
            )
            tex_bad_t1 = (
                "\\frac{1 + \\eps - \\mu(y^i_t|x, y^i_{<t})}{1 + \\eps - \\pi(y^i_t|x, y^i_{<t})}\n"
                "approximate the full reverse KL divergence using binary KL divergence\n"
                "Computing the full reverse KL divergence in~\\eqref{eq:est2} can be costly.\n"
                "All methods use rollout-router replay (R3)\n"
                "BPO uses the default setting $\\epsilon=0.1$ and $C=3.0$ in the main experiments.\n"
                "\\begin{table}\\label{tab:mainaime}\n" + fake_rows + "\n\\end{table}\n"
            ).encode("utf-8")
            (anch_repo / "latex_src" / "main.tex").write_bytes(tex_bad_t1)
            audit_mod.PINNED_ARTIFACT_SHA256["latex_src/main.tex"] = hashlib.sha256(tex_bad_t1).hexdigest()
            check_raises(lambda: audit_mod.run_audit(standalone=False, repo_dir=anch_repo), "SCHEMA_ERROR", "Table1 missing BPO")
        finally:
            audit_mod.PINNED_ARTIFACT_SHA256.clear()
            audit_mod.PINNED_ARTIFACT_SHA256.update(orig_pins)

    # Default live staged arXiv:2609.15987 directory (when present in workspace)
    default_repo = Path(__file__).resolve().parent.parent / "repos" / "bpo"
    if (default_repo / "latex_src" / "main.tex").is_file():
        cert_live = audit_mod.run_audit(standalone=False)
        check_eq(cert_live["execution_mode"], "live_readonly", "live mode")
        check_eq(cert_live["verdict"], "VERIFIED", "live verified")
        check_eq(cert_live["verbatim_spec_checks"]["reverse_kl_misnomer_anchored"], True, "reverse KL anchored")
        check_eq(cert_live["verbatim_spec_checks"]["bpo_clip_numeric_specified_in_tex"], False, "clip numeric absent")
        buf_live = io.StringIO()
        with contextlib.redirect_stdout(buf_live):
            rc_l = audit_mod.main(["--repo-dir", str(default_repo)])
        check_eq(rc_l, 0, "cli live --repo-dir rc=0")


def main() -> int:
    tests = [
        ("primitives_and_refusals", test_primitives_and_refusals),
        ("pillar1_theorem1", test_pillar1_theorem1),
        ("pillar2_duality_and_pillar3_drift", test_pillar2_duality_and_pillar3_drift),
        ("pillar4_gate_and_pillar5_tables", test_pillar4_gate_and_pillar5_tables),
        ("audit_runner_and_refusals", test_audit_runner_and_refusals),
    ]
    for _name, fn in tests:
        fn()
    sys.stdout.write(json.dumps({"passed": len(tests), "status": "PASS", "suite": "test_bpo_bellman_r5"}, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
