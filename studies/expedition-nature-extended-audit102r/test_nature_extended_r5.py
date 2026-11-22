"""Assertion-free R5 test suite for Track S4b (AUDIT-102): Extended Nature-Inspired Exact Operators.

Run cleanly under:
  python3 -I -O -B -W error symbiosis/stream/track-s4b-nature-extended/test_nature_extended_r5.py

Pure Python 3 stdlib. Zero floats in trust paths. Zero bare assert statements.
"""

import copy
from fractions import Fraction
import hashlib
import io
import json
import os
import sys
import tempfile

_SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
if _SCRIPT_DIR not in sys.path:
    sys.path.insert(0, _SCRIPT_DIR)

import nature_extended_certifier as nec  # noqa: E402
import nature_extended_oracle as neo  # noqa: E402


class _TestFailure(RuntimeError):
    pass


class _SubStr(str):
    pass


class _SubInt(int):
    pass


class _SubList(list):
    pass


def _check(cond: bool, msg: str) -> None:
    if not cond:
        raise _TestFailure(msg)


def _expect_error(fn, expected_code: str, label: str) -> None:
    try:
        fn()
    except neo.NatureExtendedError as exc:
        if exc.code != expected_code:
            raise _TestFailure(f"{label}: expected {expected_code}, got {exc.code} ({exc.detail})")
        return
    raise _TestFailure(f"{label}: expected NatureExtendedError({expected_code}), but succeeded")


def _resign(cert: dict) -> dict:
    unsigned = {k: v for k, v in cert.items() if k != "canonical_sha256"}
    cert["canonical_sha256"] = hashlib.sha256(neo.canonical_json_bytes(unsigned)).hexdigest()
    return cert


def test_group1_core_pure_q_helpers() -> None:
    # frac_dec6 rounding boundaries (including half-to-even & negative zero suppression)
    _check(neo.frac_dec6(Fraction(0, 1)) == "0.000000", "frac_dec6 0")
    _check(neo.frac_dec6(Fraction(1, 4)) == "0.250000", "frac_dec6 1/4")
    _check(neo.frac_dec6(Fraction(-1, 4)) == "-0.250000", "frac_dec6 -1/4")
    _check(neo.frac_dec6(Fraction(1, 2_000_000)) == "0.000000", "half-to-even even tie down")
    _check(neo.frac_dec6(Fraction(3, 2_000_000)) == "0.000002", "half-to-even odd tie up")
    _check(neo.frac_dec6(Fraction(5, 2_000_000)) == "0.000002", "half-to-even even tie stay")
    _check(neo.frac_dec6(Fraction(6, 10_000_000)) == "0.000001", "strictly above half up")
    _check(neo.frac_dec6(Fraction(4, 10_000_000)) == "0.000000", "strictly below half down")
    _check(neo.frac_dec6(Fraction(14, 10_000_000)) == "0.000001", "odd q strictly below half stays down")
    _check(neo.frac_dec6(Fraction(-1, 10_000_000)) == "0.000000", "no -0.000000")

    # round_half_even_exact boundaries
    _check(neo.round_half_even_exact(Fraction(1, 3)) == 0, "rhe < 1/2")
    _check(neo.round_half_even_exact(Fraction(2, 3)) == 1, "rhe > 1/2")
    _check(neo.round_half_even_exact(Fraction(1, 2)) == 0, "rhe 0.5 -> 0")
    _check(neo.round_half_even_exact(Fraction(3, 2)) == 2, "rhe 1.5 -> 2")
    _check(neo.round_half_even_exact(Fraction(5, 2)) == 2, "rhe 2.5 -> 2")
    _check(neo.round_half_even_exact(Fraction(-1, 2)) == 0, "rhe -0.5 -> 0")
    _check(neo.round_half_even_exact(Fraction(-3, 2)) == -2, "rhe -1.5 -> -2")
    _check(neo.round_half_even_exact(Fraction(-5, 4)) == -1, "rhe -1.25 -> -1")
    _check(neo.round_half_even_exact(Fraction(-7, 4)) == -2, "rhe -1.75 -> -2")

    # contains_float recursive check (dict values, dict keys, list, tuple, set, complex)
    _check(neo.contains_float(float("0.5")) is True, "direct float")
    _check(neo.contains_float(complex(1, 0)) is True, "direct complex")
    _check(neo.contains_float({"a": [1, (2, float("1.0"))]}) is True, "nested tuple float")
    _check(neo.contains_float({float("1.5"): "x"}) is True, "dict key float")
    _check(neo.contains_float({float("2.5")}) is True, "set float")
    _check(neo.contains_float({"a": [1, (2, "ok", True, None)]}) is False, "clean nested")

    # solve_linear_exact pivoting, zero-factor skip, and singular/shape rejections
    sol_piv = neo.solve_linear_exact([[0, 1], [2, 3]], [4, 14])
    _check(sol_piv == [Fraction(1, 1), Fraction(4, 1)], f"pivot solve mismatch: {sol_piv}")
    sol_3 = neo.solve_linear_exact([[1, 0, 1], [0, 2, 1], [1, 2, 4]], [3, 5, 11])
    _check(sol_3 == [Fraction(3, 2), Fraction(7, 4), Fraction(3, 2)], f"3x3 solve mismatch: {sol_3}")
    _expect_error(lambda: neo.solve_linear_exact([], []), "ERR_BAD_MATRIX", "empty matrix")
    _expect_error(lambda: neo.solve_linear_exact([[1]], [1, 2]), "ERR_BAD_MATRIX", "rhs mismatch")
    _expect_error(lambda: neo.solve_linear_exact([[1, 2], [3]], [1, 2]), "ERR_BAD_MATRIX", "non-square")
    _expect_error(lambda: neo.solve_linear_exact([[1, 2], [2, 4]], [3, 6]), "ERR_SINGULAR_MATRIX", "singular")
    _expect_error(lambda: neo.solve_linear_exact([[True]], [1]), "ERR_BAD_PARAM", "bool in matrix")
    _expect_error(lambda: neo._require_pos_fraction(0, "x"), "ERR_BAD_PARAM", "zero pos frac")
    _expect_error(lambda: neo._require_pos_fraction(-1, "x"), "ERR_BAD_PARAM", "neg pos frac")
    _expect_error(lambda: neo._to_fraction("1/2", "x"), "ERR_BAD_PARAM", "str frac")
    _expect_error(lambda: neo.canonical_json_bytes(object()), "ERR_CERT_JSON", "non-JSON canonical")


def test_group2_pillar1_kinetic_proofreading() -> None:
    # Independent closed-form verification with distinct w_fwd != v_cat
    dc, dw, kon, wf, vc = Fraction(2, 1), Fraction(10, 1), Fraction(3, 1), Fraction(1, 20), Fraction(1, 50)
    for k in (0, 1, 2, 3):
        res = neo.solve_proofreading_chain_exact(dc, dw, kon, wf, vc, k)
        expected_jc = kon * (vc / (dc + vc)) * ((wf / (dc + wf)) ** k)
        expected_jw = kon * (vc / (dw + vc)) * ((wf / (dw + wf)) ** k)
        expected_f = expected_jw / expected_jc
        _check(Fraction(*res["flux_correct"]) == expected_jc, f"p1 j_c k={k}")
        _check(Fraction(*res["flux_wrong"]) == expected_jw, f"p1 j_w k={k}")
        _check(Fraction(*res["error_ratio"]) == expected_f, f"p1 error_ratio k={k}")
        _check(res["closed_form_residual"] == [0, 1], f"p1 residual k={k}")
        _check(res["above_floor"] is True, f"p1 above_floor k={k}")
        _check(res["beats_f0"] is (k >= 1), f"p1 beats_f0 k={k}")

    # Independent equilibrium detailed-balance verification
    rr = Fraction(1, 10)
    eq = neo.solve_equilibrium_cycle_control_exact(dc, dw, kon, wf, rr, vc)
    alpha_c = (dc + wf) / (dc + wf + rr)
    alpha_w = (dw + wf) / (dw + wf + rr)
    expected_feq = (dc + vc * alpha_c) / (dw + vc * alpha_w)
    _check(Fraction(*eq["error_ratio"]) == expected_feq, "p1 eq closed form")
    _check(eq["cycle_balance_ratio"] == [1, 1], "p1 cycle ratio 1/1")
    _check(eq["strictly_worse_than_f0"] is True, "p1 eq > f0")

    # Coupled gate control exact formula
    cp = neo.solve_coupled_gate_control_exact(dc, dw, kon, wf, vc)
    _check(Fraction(*cp["error_ratio"]) == (dc + wf) / (dw + wf), "p1 coupled closed form")
    _check(cp["strictly_worse_than_f0"] is True, "p1 coupled > f0")

    # Parameter validation boundaries
    _expect_error(lambda: neo.solve_proofreading_chain_exact(5, 5, 1, 1, 1, 1), "ERR_BAD_PARAM", "p1 dw==dc")
    _expect_error(lambda: neo.solve_proofreading_chain_exact(5, 4, 1, 1, 1, 1), "ERR_BAD_PARAM", "p1 dw<dc")
    _expect_error(lambda: neo.solve_proofreading_chain_exact(1, 2, 1, 1, 1, -1), "ERR_BAD_PARAM", "p1 k<0")
    _expect_error(lambda: neo.solve_proofreading_chain_exact(1, 2, 1, 1, 1, True), "ERR_BAD_PARAM", "p1 k bool")
    _expect_error(lambda: neo.solve_equilibrium_cycle_control_exact(5, 5, 1, 1, 1, 1), "ERR_BAD_PARAM", "eq dw<=dc")
    _expect_error(lambda: neo.solve_coupled_gate_control_exact(5, 5, 1, 1, 1, ), "ERR_BAD_PARAM", "cp dw<=dc")


def test_group3_pillar2_immune_negative_selection() -> None:
    # Hand-computed small L=3 exact known-answer oracle: S = {"000", "111"}
    r1 = neo.negative_selection_exhaustive_exact(3, ("000", "111"), 1)
    _check(r1["detector_count"] == 0 and r1["hole_count"] == 6 and r1["first_hole"] == "001", "L=3 r=1")
    r2 = neo.negative_selection_exhaustive_exact(3, ("000", "111"), 2)
    _check(
        r2["detector_count"] == 2
        and r2["detected_count"] == 6
        and r2["hole_count"] == 0
        and r2["first_hole"] is None
        and r2["first_recombinant_hole"] is None
        and r2["false_positive_count"] == 0,
        f"L=3 r=2 mismatch: {r2}",
    )
    r3 = neo.negative_selection_exhaustive_exact(3, ("000", "111"), 3)
    _check(r3["detector_count"] == 6 and r3["detected_count"] == 6 and r3["hole_count"] == 0, "L=3 r=3")
    # Independent brute-force pairwise r_contiguous_match cross-check on L=4, r=2
    s4 = ("0000", "1111", "0011")
    u4 = [format(i, "04b") for i in range(16)]
    bf_det = [d for d in u4 if all(not neo.r_contiguous_match(d, s, 2) for s in s4)]
    bf_ns = [x for x in u4 if x not in s4]
    bf_hit = [x for x in bf_ns if any(neo.r_contiguous_match(d, x, 2) for d in bf_det)]
    ns4 = neo.negative_selection_exhaustive_exact(4, s4, 2)
    _check(ns4["detector_count"] == len(bf_det) and ns4["detected_count"] == len(bf_hit), "L=4 brute-force parity")

    # Full L=8 audit verification
    p2 = neo.audit_immune_negative_selection_exact()
    by_r = {row["r"]: row for row in p2["r_sweep"]}
    _check(by_r[2]["detector_count"] == 0 and by_r[2]["hole_count"] == 248, "L=8 r=2 collapse")
    _check(by_r[3]["detector_count"] == 16 and by_r[3]["hole_count"] == 8 and by_r[3]["recombinant_hole_count"] == 8, "L=8 r=3")
    _check(by_r[4]["detector_count"] == 64 and by_r[4]["hole_count"] == 56 and by_r[4]["recombinant_hole_count"] == 8, "L=8 r=4")
    _check(by_r[6]["hole_count"] == 0 and by_r[8]["detector_count"] == 248, "L=8 r=6,8")
    _check(p2["must_fail_uncensored_control"]["false_positive_count"] == 4, "L=8 uncensored FP=4")
    _check(p2["must_fail_uncensored_control"]["false_positive_rate"] == [1, 2], "L=8 uncensored FP rate 1/2")

    # Direct _validate_binary_string isolation + r_contiguous_match / negative_selection / uncensored rejections
    _expect_error(lambda: neo._validate_binary_string(_SubStr("01"), 2), "ERR_BAD_BITSTRING", "vbs substr")
    _expect_error(lambda: neo._validate_binary_string("010", 2), "ERR_BAD_BITSTRING", "vbs len")
    _expect_error(lambda: neo._validate_binary_string("02", 2), "ERR_BAD_BITSTRING", "vbs non-binary")
    _check(neo.r_contiguous_match("0101", "1100", 2) is True, "rcm match")
    _check(neo.r_contiguous_match("0101", "1010", 2) is False, "rcm non-match")
    _expect_error(lambda: neo.r_contiguous_match(_SubStr("01"), "01", 1), "ERR_BAD_BITSTRING", "rcm substr a")
    _expect_error(lambda: neo.r_contiguous_match("01", _SubStr("01"), 1), "ERR_BAD_BITSTRING", "rcm substr b")
    _expect_error(lambda: neo.r_contiguous_match(12, "01", 1), "ERR_BAD_BITSTRING", "rcm int a")
    _expect_error(lambda: neo.r_contiguous_match("01", 12, 1), "ERR_BAD_BITSTRING", "rcm int b")
    _expect_error(lambda: neo.r_contiguous_match("01", "010", 1), "ERR_BAD_BITSTRING", "rcm len mismatch")
    _expect_error(lambda: neo.r_contiguous_match("", "", 1), "ERR_BAD_BITSTRING", "rcm empty")
    _expect_error(lambda: neo.r_contiguous_match("02", "01", 1), "ERR_BAD_BITSTRING", "rcm non-binary")
    _expect_error(lambda: neo.r_contiguous_match("01", "01", 0), "ERR_BAD_PARAM", "rcm r=0")
    _expect_error(lambda: neo.r_contiguous_match("01", "01", 3), "ERR_BAD_PARAM", "rcm r>len")
    _expect_error(lambda: neo.r_contiguous_match("01", "01", True), "ERR_BAD_PARAM", "rcm r bool")
    _expect_error(lambda: neo.negative_selection_exhaustive_exact(1, ("0",), 1), "ERR_BAD_PARAM", "L<2")
    _expect_error(lambda: neo.negative_selection_exhaustive_exact(11, ("0" * 11, "1" * 11), 1), "ERR_BAD_PARAM", "L>10")
    _expect_error(lambda: neo.negative_selection_exhaustive_exact(_SubInt(3), ("000",), 2), "ERR_BAD_PARAM", "L subint")
    _expect_error(lambda: neo.negative_selection_exhaustive_exact(True, ("01",), 1), "ERR_BAD_PARAM", "L bool")
    _expect_error(lambda: neo.negative_selection_exhaustive_exact(3, ("000",), 0), "ERR_BAD_PARAM", "neg r<1")
    _expect_error(lambda: neo.negative_selection_exhaustive_exact(3, ("000",), 4), "ERR_BAD_PARAM", "neg r>L")
    _expect_error(lambda: neo.negative_selection_exhaustive_exact(3, ("000",), True), "ERR_BAD_PARAM", "neg r bool")
    _expect_error(lambda: neo.negative_selection_exhaustive_exact(3, [], 2), "ERR_BAD_PARAM", "empty self")
    _expect_error(lambda: neo.negative_selection_exhaustive_exact(3, {"000"}, 2), "ERR_BAD_PARAM", "set self")
    _expect_error(lambda: neo.negative_selection_exhaustive_exact(2, ("00", "01", "10", "11"), 1), "ERR_BAD_PARAM", "full self")
    _expect_error(lambda: neo.uncensored_detector_control_exact([], 1, "00"), "ERR_BAD_PARAM", "unc empty")
    _expect_error(lambda: neo.uncensored_detector_control_exact({"00"}, 1, "00"), "ERR_BAD_PARAM", "unc set")
    _expect_error(lambda: neo.uncensored_detector_control_exact(("00",), 1, "000"), "ERR_BAD_BITSTRING", "unc det len")


def test_group4_pillar3_turing_reaction_diffusion() -> None:
    p3 = neo.audit_turing_reaction_diffusion_exact()
    _check(p3["c6_spectrum"]["max_eigenvector_residual"] == [0, 1], "C_6 eig residual")
    wit_modes = {m["eigenvalue"][0]: m for m in p3["turing_witness"]["dispersion"]["modes"]}
    _check(wit_modes[0]["det"] == [2, 1] and wit_modes[0]["unstable"] is False, "mode 0 stable")
    _check(wit_modes[1]["det"] == [-4, 1] and wit_modes[1]["unstable"] is True, "mode 1 unstable")
    _check(wit_modes[3]["det"] == [44, 1] and wit_modes[3]["unstable"] is False, "mode 3 stable")
    _check(wit_modes[4]["det"] == [98, 1] and wit_modes[4]["unstable"] is False, "mode 4 stable")
    _check(p3["turing_witness"]["dispersion"]["s_term"] == [16, 1], "s_term == 16")
    _check(p3["turing_witness"]["dispersion"]["turing_discriminant"] == [176, 1], "disc == 176")

    # Equal diffusion, subthreshold, spectral gap exact numbers
    eq_modes = [m["det"] for m in p3["must_fail_equal_diffusion_control"]["dispersion"]["modes"]]
    _check(eq_modes == [[2, 1], [5, 1], [17, 1], [26, 1]], f"eq dets: {eq_modes}")
    sub_disp = p3["must_fail_subthreshold_ratio_control"]["dispersion"]
    _check(
        sub_disp["s_term"] == [4, 1]
        and sub_disp["turing_discriminant"] == [-16, 1]
        and sub_disp["continuous_turing_unstable"] is False,
        "sub disp",
    )
    # s_term < 0 yet disc > 0 (D_u=10, D_v=1 -> S=-38, S^2 - 80 = +1364): MUST stay stable!
    neg_s = neo.evaluate_turing_dispersion_exact(2, -5, 2, -4, 10, 1, (0, 1))
    _check(
        neg_s["homogeneous_stable"] is True
        and Fraction(*neg_s["s_term"]) < 0
        and Fraction(*neg_s["turing_discriminant"]) > 0
        and neg_s["continuous_turing_unstable"] is False,
        "neg s_term with positive disc must not trigger Turing",
    )
    gap_ctrl = p3["must_fail_discrete_spectral_gap_control"]
    _check(gap_ctrl["continuous_probe_det"] == [-2, 5], "gap probe det -2/5")
    gap_dets = [m["det"] for m in gap_ctrl["dispersion"]["modes"]]
    _check(gap_dets == [[2, 1], [1, 6], [3, 10], [34, 15]], f"gap dets: {gap_dets}")

    # Hand-computed 1-step forward Euler on C_6 homogeneous vector (1,1,1,1,1,1)
    step1 = neo.step_c6_reaction_diffusion_exact(2, -5, 2, -4, 1, 10, 1, 1, (1, 1, 1, 1, 1, 1), Fraction(1, 4), 1)
    _check(step1["initial_norm_sq"] == [12, 1] and step1["norm_sq_ratio"] == [5, 32], f"step1: {step1}")
    _check(step1["decayed"] is True and step1["amplified"] is False, "step1 decayed")

    # Unstable homogeneous edge cases (tr_j >= 0 or det_j <= 0, including det_m < 0 with hom_stable=False)
    bad_tr = neo.evaluate_turing_dispersion_exact(4, -5, 2, -2, 1, 10, (0, 1))
    _check(bad_tr["homogeneous_stable"] is False and bad_tr["continuous_turing_unstable"] is False, "tr>=0")
    bad_det = neo.evaluate_turing_dispersion_exact(1, -1, 1, -2, Fraction(1, 10), Fraction(1, 10), (0, 1))
    _check(
        bad_det["homogeneous_stable"] is False
        and bad_det["discrete_turing_unstable"] is False
        and Fraction(*bad_det["modes"][1]["det"]) < 0
        and bad_det["modes"][1]["unstable"] is False,
        "det<=0 with det_m<0 must stay unstable=False",
    )

    # Bad parameter rejections
    _expect_error(lambda: neo.evaluate_turing_dispersion_exact(2, -5, 2, -4, 1, 10, []), "ERR_BAD_PARAM", "empty lams")
    _expect_error(lambda: neo.evaluate_turing_dispersion_exact(2, -5, 2, -4, 1, 10, {0}), "ERR_BAD_PARAM", "set lams")
    _expect_error(lambda: neo.evaluate_turing_dispersion_exact(2, -5, 2, -4, 1, 10, (-1,)), "ERR_BAD_PARAM", "neg lam")
    _expect_error(
        lambda: neo.step_c6_reaction_diffusion_exact(2, -5, 2, -4, 1, 10, 1, 1, (1, 1, 1, 1, 1, 1), Fraction(1, 4), 0),
        "ERR_BAD_PARAM",
        "steps=0",
    )
    _expect_error(
        lambda: neo.step_c6_reaction_diffusion_exact(2, -5, 2, -4, 1, 10, 1, 1, (1, 1, 1, 1, 1, 1), Fraction(1, 4), True),
        "ERR_BAD_PARAM",
        "steps bool",
    )
    _expect_error(
        lambda: neo.step_c6_reaction_diffusion_exact(2, -5, 2, -4, 1, 10, 1, 1, (1, 1, 1), Fraction(1, 4), 1),
        "ERR_BAD_PARAM",
        "bad mode_vec len",
    )
    _expect_error(
        lambda: neo.step_c6_reaction_diffusion_exact(2, -5, 2, -4, 1, 10, 0, 0, (1, 1, 1, 1, 1, 1), Fraction(1, 4), 1),
        "ERR_BAD_PARAM",
        "zero initial state",
    )


def test_group5_pillar4_starling_topological_flocking() -> None:
    # Hand-computed mini-graph checks (path 0-1-2 and 4-cycle)
    path_edges = [(0, 1), (1, 2)]
    _check(neo.graph_connectivity_and_diameter(3, path_edges) == (1, 2), "path diameter 2")
    _check(neo.graph_connectivity_and_diameter(3, path_edges, omit=1) == (2, None), "path omit cut-vertex")
    _check(neo.exact_kirchhoff_effective_resistance(3, path_edges, 0, 2) == Fraction(2, 1), "path R_eff 2")
    # Unrelated disconnected component must NOT break R_eff between connected endpoints!
    _check(neo.exact_kirchhoff_effective_resistance(4, [(0, 1), (2, 3)], 0, 1) == Fraction(1, 1), "R_eff ignores unrelated component")
    _expect_error(
        lambda: neo.exact_kirchhoff_effective_resistance(3, [(0, 1)], 0, 2),
        "ERR_DISCONNECTED_ENDPOINTS",
        "disconnected R_eff",
    )
    cycle4 = [(0, 1), (1, 2), (2, 3), (0, 3)]
    _check(neo.exact_kirchhoff_effective_resistance(4, cycle4, 0, 2) == Fraction(1, 1), "C4 R_eff 1")
    _check(neo.graph_connectivity_and_diameter(4, cycle4) == (1, 2), "C4 diam 2")

    # Explicit tie counter check on unit square (plus k == n - 1 complete-graph boundary)
    sq_pts = [(0, 0), (1, 0), (0, 1), (1, 1)]
    _, sq_ties = neo.build_topological_knn_graph(sq_pts, 1)
    _check(sq_ties == 4, f"square k=1 ties should be 4, got {sq_ties}")
    sq_full, sq_full_ties = neo.build_topological_knn_graph(sq_pts, 3)
    _check(len(sq_full) == 6 and sq_full_ties == 0, "k == n - 1 complete graph")

    # Full 16-agent flock audit checks
    p4 = neo.audit_starling_topological_flocking_exact()
    _check(p4["k6_boundary_tie_count"] == 0 and p4["k1_boundary_tie_count"] == 0, "zero boundary ties")
    _check(p4["all_scale_edges_identical"] is True and p4["all_scale_reff_identical"] is True, "scale invariance")
    _check(p4["two_vertex_connected"] is True and p4["max_single_node_ablation_components"] == 1, "2-vertex connected")
    _check(p4["must_fail_metric_fragmentation_control"]["fragments_to_singletons"] is True, "metric fragments")
    _check(p4["must_fail_subcritical_k1_control"]["disconnected"] is True, "k=1 disconnected")

    # Bad parameter rejections
    _expect_error(lambda: neo.build_topological_knn_graph(sq_pts, 0), "ERR_BAD_PARAM", "knn k=0")
    _expect_error(lambda: neo.build_topological_knn_graph(sq_pts, 4), "ERR_BAD_PARAM", "knn k>=n")
    _expect_error(lambda: neo.build_topological_knn_graph(sq_pts, True), "ERR_BAD_PARAM", "knn k bool")
    _expect_error(lambda: neo.build_metric_radius_graph(sq_pts, -1), "ERR_BAD_PARAM", "metric r_sq<0")
    _expect_error(lambda: neo.build_metric_radius_graph(sq_pts, True), "ERR_BAD_PARAM", "metric r_sq bool")
    _expect_error(lambda: neo.exact_kirchhoff_effective_resistance(3, path_edges, 1, 1), "ERR_BAD_PARAM", "src==dst")
    _expect_error(lambda: neo.exact_kirchhoff_effective_resistance(3, path_edges, -1, 2), "ERR_BAD_PARAM", "src<0")
    _expect_error(lambda: neo.exact_kirchhoff_effective_resistance(3, path_edges, 0, 3), "ERR_BAD_PARAM", "dst>=n")
    _expect_error(lambda: neo.exact_kirchhoff_effective_resistance(3, path_edges, True, 2), "ERR_BAD_PARAM", "src bool")
    _expect_error(lambda: neo.exact_kirchhoff_effective_resistance(3, path_edges, 0, True), "ERR_BAD_PARAM", "dst bool")


def test_group6_pillar5_synaptic_homeostatic_siliquant() -> None:
    # Known-answer symmetric absmax quantization + commutation
    scale, codes, deq = neo.symmetric_absmax_quantize_exact(neo.P5_WEIGHT_BLOCK, 7)
    _check(scale == Fraction(2, 7), f"scale mismatch: {scale}")
    _check(codes == [0, 1, -3, 4, -7, 6, -2, 5], f"codes mismatch: {codes}")
    _check(deq[0] == Fraction(0, 1) and deq[4] == Fraction(-2, 1), "dequant exact extremes")

    # D8 lattice decoder: exercise even-sum no-flip, odd-sum positive-err flip (+1), odd-sum negative-err flip (-1)
    # 1. Even sum: P5_WEIGHT_BLOCK -> sum(codes) = 4 (even)
    d8_even = neo.d8_absmax_quantize_exact(neo.P5_WEIGHT_BLOCK, 7)
    _check(d8_even == [0, 1, -3, 4, -7, 6, -2, 5] and sum(d8_even) % 2 == 0, "D8 even")
    # 2. Odd sum where largest residual has scaled[i] > q[i] (+1 flip)
    # Use max = 7 so scaled == raw; [0, 0, 0, 0, 0, 0, 7, 1 + 2/5] -> q = [0..0, 7, 1] (sum 8 even);
    # make sum odd: [0, 0, 0, 0, 0, 0, 7, 2/5] -> q = [0..0, 7, 0] (sum 7 odd), scaled[7]=2/5 > 0 -> +1 => [0..0, 7, 1]!
    d8_pos_flip = neo.d8_absmax_quantize_exact([0, 0, 0, 0, 0, 0, 7, Fraction(2, 5)], 7)
    _check(d8_pos_flip == [0, 0, 0, 0, 0, 0, 7, 1], f"D8 pos flip: {d8_pos_flip}")
    # 3. Odd sum where largest residual has scaled[i] < q[i] (-1 flip)
    d8_neg_flip = neo.d8_absmax_quantize_exact([0, 0, 0, 0, 0, 0, 7, Fraction(-2, 5)], 7)
    _check(d8_neg_flip == [0, 0, 0, 0, 0, 0, 7, -1], f"D8 neg flip: {d8_neg_flip}")
    # 4. Exact-integer tie (Claude Code counterexample [0, 1, 0..0], q_max=7): prefers non-zero coord inward -> [0, 6, 0..0]
    d8_tie_pos = neo.d8_absmax_quantize_exact([0, 1, 0, 0, 0, 0, 0, 0], 7)
    _check(d8_tie_pos == [0, 6, 0, 0, 0, 0, 0, 0] and sum(d8_tie_pos) % 2 == 0, f"D8 pos tie: {d8_tie_pos}")
    d8_tie_neg = neo.d8_absmax_quantize_exact([0, -1, 0, 0, 0, 0, 0, 0], 7)
    _check(d8_tie_neg == [0, -6, 0, 0, 0, 0, 0, 0] and sum(d8_tie_neg) % 2 == 0, f"D8 neg tie: {d8_tie_neg}")

    # Full Pillar 5 audit check
    p5 = neo.audit_synaptic_homeostatic_siliquant_exact()
    _check(p5["multiplicative_upscaling"]["absmax_code_flips"] == 0, "up absmax 0 flips")
    _check(p5["multiplicative_upscaling"]["d8_code_flips"] == 0, "up d8 0 flips")
    _check(p5["multiplicative_downscaling"]["absmax_code_flips"] == 0, "dn absmax 0 flips")
    _check(p5["multiplicative_downscaling"]["d8_code_flips"] == 0, "dn d8 0 flips")
    _check(p5["must_fail_additive_shift_control"]["absmax_code_flips"] > 0, "add absmax flips > 0")
    _check(p5["must_fail_additive_shift_control"]["d8_code_flips"] > 0, "add d8 flips > 0")
    _check(p5["must_fail_unstable_gain_control"]["amplified_error"] is True, "unstable gain amplifies")

    # Bad parameter rejections across Pillar 5 helpers
    _expect_error(lambda: neo.symmetric_absmax_quantize_exact([1, 2], 0), "ERR_BAD_PARAM", "sym q_max=0")
    _expect_error(lambda: neo.symmetric_absmax_quantize_exact([1, 2], True), "ERR_BAD_PARAM", "sym q_max bool")
    _expect_error(lambda: neo.symmetric_absmax_quantize_exact([], 7), "ERR_BAD_PARAM", "sym empty")
    _expect_error(lambda: neo.symmetric_absmax_quantize_exact([0, 0], 7), "ERR_BAD_PARAM", "sym zero vec")
    _expect_error(lambda: neo.d8_absmax_quantize_exact([1, 2, 3], 7), "ERR_BAD_PARAM", "d8 bad len")
    _expect_error(lambda: neo.d8_absmax_quantize_exact([1] * 8, 0), "ERR_BAD_PARAM", "d8 q_max=0")
    _expect_error(lambda: neo.d8_absmax_quantize_exact([1] * 8, True), "ERR_BAD_PARAM", "d8 q_max bool")
    _expect_error(lambda: neo.d8_absmax_quantize_exact([0] * 8, 7), "ERR_BAD_PARAM", "d8 zero vec")
    _expect_error(lambda: neo.pairwise_ratio_max_drift_exact([], []), "ERR_BAD_PARAM", "ratio empty")
    _expect_error(lambda: neo.pairwise_ratio_max_drift_exact([1], [1, 2]), "ERR_BAD_PARAM", "ratio len")
    _expect_error(lambda: neo.pairwise_ratio_max_drift_exact([1, 2], [0, 2]), "ERR_ZERO_DENOM", "ratio zero denom")
    _expect_error(lambda: neo.squared_cosine_exact([], []), "ERR_BAD_PARAM", "cos empty")
    _expect_error(lambda: neo.squared_cosine_exact([1], [1, 2]), "ERR_BAD_PARAM", "cos len")
    _expect_error(lambda: neo.squared_cosine_exact([0, 0], [1, 0]), "ERR_ZERO_NORM", "cos zero u")
    _expect_error(lambda: neo.squared_cosine_exact([1, 0], [0, 0]), "ERR_ZERO_NORM", "cos zero v")
    _expect_error(lambda: neo.run_multiplicative_homeostasis_exact(1, 1, 1, 0), "ERR_BAD_PARAM", "hom steps=0")
    _expect_error(lambda: neo.run_multiplicative_homeostasis_exact(1, 1, 1, True), "ERR_BAD_PARAM", "hom steps bool")


def test_group7_certificate_validator_and_cli_fail_closed() -> None:
    cert = neo.build_nature_extended_certificate()
    neo.validate_certificate(cert)

    # Top-level structural, type, float, and digest tamper matrix
    _expect_error(lambda: neo.validate_certificate(["not", "dict"]), "ERR_CERT_TYPE", "non-dict cert")

    def _tamper(mutator, code, label, resign=True):
        c = copy.deepcopy(cert)
        mutator(c)
        if resign:
            _resign(c)
        _expect_error(lambda: neo.validate_certificate(c), code, label)

    _tamper(lambda c: c["summary"].__setitem__("x", float("0.1")), "ERR_CERT_FLOAT", "float inject", resign=False)
    _tamper(lambda c: c.__setitem__("extra_key", 1), "ERR_CERT_KEYS", "extra top key", resign=False)
    _tamper(lambda c: c.pop("summary"), "ERR_CERT_KEYS", "missing top key", resign=False)
    _tamper(lambda c: c.__setitem__("schema", "wrong"), "ERR_CERT_SCHEMA", "bad schema")
    _tamper(lambda c: c.__setitem__("schema", _SubStr(neo.SCHEMA_VERSION)), "ERR_CERT_STR", "substr schema", resign=False)
    _tamper(lambda c: c.__setitem__("schema", "   "), "ERR_CERT_STR", "blank schema")
    _tamper(lambda c: c.__setitem__("audit_id", "AUDIT-999"), "ERR_CERT_AUDIT_ID", "bad audit_id")

    # Governance, Law 4, Law 5, primary_sources tampers
    _expect_error(lambda: neo._req_bool({}, "flag", True, "t"), "ERR_CERT_BOOL", "req_bool missing key")
    _expect_error(lambda: neo._req_nonempty_str({}, "k", "t"), "ERR_CERT_STR", "req_str missing key")
    _expect_error(lambda: neo._req_int_eq({}, "k", 1, "t"), "ERR_CERT_INT", "req_int missing key")
    _tamper(lambda c: c.__setitem__("governance", []), "ERR_CERT_TYPE", "gov non-dict")
    _tamper(lambda c: c["governance"].pop("aletheia_version"), "ERR_CERT_KEYS", "gov missing version")
    _tamper(lambda c: c["governance"].__setitem__("aletheia_version", "1.0.0"), "ERR_CERT_GOV", "gov version")
    _tamper(lambda c: c["governance"].__setitem__("zero_floats", False), "ERR_CERT_BOOL", "gov flag False")
    _tamper(lambda c: c["governance"].__setitem__("zero_floats", 1), "ERR_CERT_BOOL", "gov flag int 1")
    _tamper(lambda c: c["governance"].pop("zero_floats"), "ERR_CERT_KEYS", "gov flag missing")
    _tamper(lambda c: c["law4_novelty"].__setitem__("classical_mechanisms_class", "N2"), "ERR_CERT_LAW4", "law4 N2")
    _tamper(lambda c: c["law4_novelty"].__setitem__("engineering_certifier_class", "N3"), "ERR_CERT_LAW4", "law4 eng")
    _tamper(lambda c: c["law4_novelty"].__setitem__("primary_source_count", 7), "ERR_CERT_INT", "law4 count")
    _tamper(lambda c: c["law4_novelty"].__setitem__("primary_source_count", _SubInt(8)), "ERR_CERT_INT", "law4 count subint", resign=False)
    _tamper(lambda c: c["law4_novelty"].__setitem__("primary_source_count", True), "ERR_CERT_INT", "law4 count bool")
    _tamper(lambda c: c["law4_novelty"].pop("primary_source_count"), "ERR_CERT_KEYS", "law4 count missing")
    _tamper(lambda c: c["law5_discipline"].__setitem__("metaphor_claims_present", True), "ERR_CERT_BOOL", "law5 meta")
    _tamper(lambda c: c.__setitem__("primary_sources", tuple(c["primary_sources"])), "ERR_CERT_SOURCES", "sources tuple", resign=False)
    _tamper(lambda c: c["primary_sources"].pop(), "ERR_CERT_SOURCES", "sources short")
    _tamper(lambda c: c["primary_sources"][0].__setitem__("novelty_class", "N1"), "ERR_CERT_SOURCES", "source N1")
    _tamper(lambda c: c["primary_sources"][0].__setitem__("year", 1949), "ERR_CERT_SOURCES", "source year <1950")
    _tamper(lambda c: c["primary_sources"][0].__setitem__("year", 2027), "ERR_CERT_SOURCES", "source year >2026")
    _tamper(lambda c: c["primary_sources"][0].__setitem__("year", _SubInt(1974)), "ERR_CERT_SOURCES", "source year subint", resign=False)
    _tamper(lambda c: c["primary_sources"][0].__setitem__("year", True), "ERR_CERT_SOURCES", "source year bool")
    _tamper(lambda c: c["primary_sources"][0].__setitem__("id", "NATX-N0-99"), "ERR_CERT_SOURCES", "source id")

    # Pillars key set & _parse_frac_pair tampers
    _tamper(lambda c: c["pillars"].pop("p5_synaptic_homeostatic_siliquant"), "ERR_CERT_PILLARS", "missing pillar")
    _tamper(lambda c: c["pillars"]["p1_kinetic_proofreading"].__setitem__("intrinsic_f0", (1, 10)), "ERR_CERT_FRAC", "frac tuple len2", resign=False)
    _tamper(lambda c: c["pillars"]["p1_kinetic_proofreading"].__setitem__("intrinsic_f0", [1]), "ERR_CERT_FRAC", "frac len1")
    _tamper(lambda c: c["pillars"]["p1_kinetic_proofreading"].__setitem__("intrinsic_f0", [True, 10]), "ERR_CERT_FRAC", "frac bool num")
    _tamper(lambda c: c["pillars"]["p1_kinetic_proofreading"].__setitem__("intrinsic_f0", [1, True]), "ERR_CERT_FRAC", "frac bool den")
    _tamper(lambda c: c["pillars"]["p1_kinetic_proofreading"].__setitem__("intrinsic_f0", [1, 0]), "ERR_CERT_FRAC", "frac zero den")
    _tamper(lambda c: c["pillars"]["p1_kinetic_proofreading"].__setitem__("intrinsic_f0", [2, 20]), "ERR_CERT_FRAC", "frac unreduced")

    # Pillar 1 tampers (isolating each sub-clause of ratios invariant while keeping error_reduction consistent!)
    _tamper(lambda c: c["pillars"]["p1_kinetic_proofreading"].__setitem__("intrinsic_f0", [1, 11]), "ERR_CERT_P1", "p1 f0")
    _tamper(lambda c: c["pillars"]["p1_kinetic_proofreading"].__setitem__("stages", []), "ERR_CERT_P1", "p1 stages len")
    _tamper(lambda c: c["pillars"]["p1_kinetic_proofreading"].__setitem__("stages", "bad"), "ERR_CERT_P1", "p1 stages type")
    _tamper(lambda c: c["pillars"]["p1_kinetic_proofreading"]["stages"][0].__setitem__("closed_form_residual", [1, 10]), "ERR_CERT_P1", "p1 res")

    def _set_p1_ratios(c, r0, r1, r2):
        p1 = c["pillars"]["p1_kinetic_proofreading"]
        p1["stages"][0]["error_ratio"] = neo.frac_pair(r0)
        p1["stages"][1]["error_ratio"] = neo.frac_pair(r1)
        p1["stages"][2]["error_ratio"] = neo.frac_pair(r2)
        p1["error_reduction_k0_to_k1"] = neo.frac_pair(r0 / r1)
        p1["error_reduction_k0_to_k2"] = neo.frac_pair(r0 / r2)

    _tamper(lambda c: _set_p1_ratios(c, Fraction(101, 1001), Fraction(1, 1000), Fraction(1, 500)), "ERR_CERT_P1", "p1 non-monotone")
    _tamper(lambda c: _set_p1_ratios(c, Fraction(1, 2), Fraction(1, 10), Fraction(1, 1000)), "ERR_CERT_P1", "p1 r1>=f0")
    _tamper(lambda c: _set_p1_ratios(c, Fraction(101, 1001), Fraction(1, 50), Fraction(1, 100)), "ERR_CERT_P1", "p1 r2>=f0^2")
    # NATX102-CRASH-01 & NATX102-BYPASS-01: zero & negative error_ratio rejected cleanly (no ZeroDivisionError)
    _tamper(lambda c: c["pillars"]["p1_kinetic_proofreading"]["stages"][2].__setitem__("error_ratio", [0, 1]), "ERR_CERT_P1", "p1 r2==0")
    _tamper(lambda c: _set_p1_ratios(c, Fraction(101, 1001), Fraction(1, 50), Fraction(-1, 100)), "ERR_CERT_P1", "p1 r2<0")
    _tamper(lambda c: c["pillars"]["p1_kinetic_proofreading"]["stages"][0].__setitem__("beats_f0", True), "ERR_CERT_BOOL", "p1 beats_f0")
    _tamper(lambda c: c["pillars"]["p1_kinetic_proofreading"]["stages"][0].__setitem__("above_floor", False), "ERR_CERT_BOOL", "p1 above_floor")
    _tamper(lambda c: c["pillars"]["p1_kinetic_proofreading"].__setitem__("error_reduction_k0_to_k1", [9, 1]), "ERR_CERT_P1", "p1 red k1")
    _tamper(lambda c: c["pillars"]["p1_kinetic_proofreading"].__setitem__("error_reduction_k0_to_k2", [90, 1]), "ERR_CERT_P1", "p1 red k2")
    _tamper(lambda c: c["pillars"]["p1_kinetic_proofreading"]["must_fail_equilibrium_control"].__setitem__("cycle_balance_ratio", [2, 1]), "ERR_CERT_P1", "p1 eq bal")
    _tamper(lambda c: c["pillars"]["p1_kinetic_proofreading"]["must_fail_equilibrium_control"].__setitem__("error_ratio", [1, 10]), "ERR_CERT_P1", "p1 eq <= f0")
    _tamper(lambda c: c["pillars"]["p1_kinetic_proofreading"]["must_fail_coupled_gate_control"].__setitem__("error_ratio", [1, 10]), "ERR_CERT_P1", "p1 cp <= f0")

    # Pillar 2 tampers
    _tamper(lambda c: c["pillars"]["p2_immune_negative_selection"].__setitem__("r_sweep", []), "ERR_CERT_P2", "p2 sweep len")
    _tamper(lambda c: c["pillars"]["p2_immune_negative_selection"].__setitem__("r_sweep", tuple(c["pillars"]["p2_immune_negative_selection"]["r_sweep"])), "ERR_CERT_P2", "p2 sweep tuple", resign=False)
    _tamper(lambda c: c["pillars"]["p2_immune_negative_selection"]["r_sweep"][0].__setitem__("detected_count", True) or c["pillars"]["p2_immune_negative_selection"]["r_sweep"][0].__setitem__("hole_count", 247), "ERR_CERT_P2", "p2 det bool sum248")
    _tamper(lambda c: c["pillars"]["p2_immune_negative_selection"]["r_sweep"][4].__setitem__("detected_count", 247) or c["pillars"]["p2_immune_negative_selection"]["r_sweep"][4].__setitem__("hole_count", True), "ERR_CERT_P2", "p2 hole bool sum248 on r6")
    _tamper(lambda c: c["pillars"]["p2_immune_negative_selection"]["r_sweep"][0].__setitem__("detected_count", -1) or c["pillars"]["p2_immune_negative_selection"]["r_sweep"][0].__setitem__("hole_count", 249), "ERR_CERT_P2", "p2 det<0")
    _tamper(lambda c: c["pillars"]["p2_immune_negative_selection"]["r_sweep"][0].__setitem__("hole_count", 247), "ERR_CERT_P2", "p2 sum!=248")
    _tamper(lambda c: c["pillars"]["p2_immune_negative_selection"]["r_sweep"][1].__setitem__("detector_count", True), "ERR_CERT_P2", "p2 dtr bool")
    _tamper(lambda c: c["pillars"]["p2_immune_negative_selection"]["r_sweep"][1].__setitem__("recombinant_hole_count", True), "ERR_CERT_P2", "p2 rec bool")
    _tamper(lambda c: c["pillars"]["p2_immune_negative_selection"]["r_sweep"][1].__setitem__("detector_count", -1), "ERR_CERT_P2", "p2 dtr<0")
    _tamper(lambda c: c["pillars"]["p2_immune_negative_selection"]["r_sweep"][1].__setitem__("detector_count", 257), "ERR_CERT_P2", "p2 dtr>256")
    _tamper(lambda c: c["pillars"]["p2_immune_negative_selection"]["r_sweep"][1].__setitem__("recombinant_hole_count", -1), "ERR_CERT_P2", "p2 rec<0")
    _tamper(lambda c: c["pillars"]["p2_immune_negative_selection"]["r_sweep"][1].__setitem__("recombinant_hole_count", 9), "ERR_CERT_P2", "p2 rec>hole")
    _tamper(lambda c: c["pillars"]["p2_immune_negative_selection"]["r_sweep"][0].__setitem__("detector_count", 1), "ERR_CERT_P2", "p2 r2 det!=0")
    _tamper(lambda c: c["pillars"]["p2_immune_negative_selection"]["r_sweep"][2].__setitem__("hole_count", 8) or c["pillars"]["p2_immune_negative_selection"]["r_sweep"][2].__setitem__("detected_count", 240), "ERR_CERT_P2", "p2 r4 non-mono")
    _tamper(lambda c: c["pillars"]["p2_immune_negative_selection"]["r_sweep"][6].__setitem__("hole_count", 1) or c["pillars"]["p2_immune_negative_selection"]["r_sweep"][6].__setitem__("detected_count", 247), "ERR_CERT_P2", "p2 r8 hole!=0")
    _tamper(lambda c: c["pillars"]["p2_immune_negative_selection"]["r_sweep"][6].__setitem__("detector_count", 247), "ERR_CERT_P2", "p2 r8 det!=248")
    # NATX102-BYPASS-04: extra forged keys inside nested pillar dicts rejected
    _tamper(lambda c: c["pillars"]["p2_immune_negative_selection"]["r_sweep"][0].__setitem__("extra_forged", "bypass"), "ERR_CERT_KEYS", "p2 extra forged key")
    _tamper(lambda c: c["pillars"]["p2_immune_negative_selection"]["must_fail_uncensored_control"].__setitem__("false_positive_count", 0), "ERR_CERT_P2", "p2 unc fp=0")
    _tamper(lambda c: c["pillars"]["p2_immune_negative_selection"]["must_fail_uncensored_control"].__setitem__("false_positive_count", True), "ERR_CERT_P2", "p2 unc fp bool")

    # Pillar 3 tampers
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["c6_spectrum"].__setitem__("ring_eigenvalues", _SubList([0, 1, 3, 4])), "ERR_CERT_P3", "p3 eigs sublist", resign=False)
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["c6_spectrum"].__setitem__("ring_eigenvalues", [0, 1, 2, 4]), "ERR_CERT_P3", "p3 eigs")
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["c6_spectrum"].__setitem__("ring_eigenvalues", [False, True, 3, 4]), "ERR_CERT_P3", "p3 eigs bool", resign=False)
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["c6_spectrum"].__setitem__("max_eigenvector_residual", [1, 10]), "ERR_CERT_P3", "p3 eig res")
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["turing_witness"]["dispersion"].__setitem__("s_term", [0, 1]), "ERR_CERT_P3", "p3 s<=0")
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["turing_witness"]["dispersion"].__setitem__("turing_discriminant", [0, 1]), "ERR_CERT_P3", "p3 disc<=0")
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["turing_witness"]["dispersion"].__setitem__("modes", tuple(c["pillars"]["p3_turing_reaction_diffusion"]["turing_witness"]["dispersion"]["modes"])), "ERR_CERT_P3", "p3 modes tuple", resign=False)
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["turing_witness"]["dispersion"].__setitem__("modes", []), "ERR_CERT_P3", "p3 modes len")
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["turing_witness"]["dispersion"]["modes"][0].__setitem__("eigenvalue", [2, 1]), "ERR_CERT_P3", "p3 mode lam")
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["turing_witness"]["dispersion"]["modes"][1].__setitem__("det", [0, 1]), "ERR_CERT_P3", "p3 unstable det>=0")
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["turing_witness"]["dispersion"]["modes"][0].__setitem__("det", [0, 1]), "ERR_CERT_P3", "p3 stable det<=0")
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["turing_witness"]["homogeneous_dynamics"].__setitem__("norm_sq_ratio", [1, 1]), "ERR_CERT_P3", "p3 hom>=1")
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["turing_witness"]["homogeneous_dynamics"].__setitem__("norm_sq_ratio", [0, 1]), "ERR_CERT_P3", "p3 hom==0")
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["turing_witness"]["homogeneous_dynamics"].__setitem__("norm_sq_ratio", [-1, 2]), "ERR_CERT_P3", "p3 hom<0")
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["turing_witness"]["mode1_dynamics"].__setitem__("norm_sq_ratio", [1, 1]), "ERR_CERT_P3", "p3 m1<=1")
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["must_fail_equal_diffusion_control"]["mode1_dynamics"].__setitem__("norm_sq_ratio", [1, 1]), "ERR_CERT_P3", "p3 eq>=1")
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["must_fail_equal_diffusion_control"]["mode1_dynamics"].__setitem__("norm_sq_ratio", [0, 1]), "ERR_CERT_P3", "p3 eq==0")
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["must_fail_equal_diffusion_control"]["mode1_dynamics"].__setitem__("norm_sq_ratio", [-1, 2]), "ERR_CERT_P3", "p3 eq<0")
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["must_fail_subthreshold_ratio_control"]["dispersion"].__setitem__("s_term", [0, 1]), "ERR_CERT_P3", "p3 sub s<=0")
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["must_fail_subthreshold_ratio_control"]["dispersion"].__setitem__("turing_discriminant", [0, 1]), "ERR_CERT_P3", "p3 sub disc>=0")
    _tamper(lambda c: c["pillars"]["p3_turing_reaction_diffusion"]["must_fail_discrete_spectral_gap_control"].__setitem__("continuous_probe_det", [0, 1]), "ERR_CERT_P3", "p3 gap probe>=0")

    # Pillar 4 tampers
    _tamper(lambda c: c["pillars"]["p4_starling_topological_flocking"].__setitem__("topological_scaling", tuple(c["pillars"]["p4_starling_topological_flocking"]["topological_scaling"])), "ERR_CERT_P4", "p4 topo tuple", resign=False)
    _tamper(lambda c: c["pillars"]["p4_starling_topological_flocking"].__setitem__("topological_scaling", []), "ERR_CERT_P4", "p4 topo len")

    def _set_all_topo_reff(c, pair):
        for row in c["pillars"]["p4_starling_topological_flocking"]["topological_scaling"]:
            row["reff_0_to_15"] = list(pair)

    _tamper(lambda c: _set_all_topo_reff(c, [0, 1]), "ERR_CERT_P4", "p4 all reff==0")
    _tamper(lambda c: _set_all_topo_reff(c, [-1, 1]), "ERR_CERT_P4", "p4 all reff<0")
    _tamper(lambda c: c["pillars"]["p4_starling_topological_flocking"]["topological_scaling"][0].__setitem__("diameter", 0), "ERR_CERT_P4", "p4 diam<1")
    _tamper(lambda c: c["pillars"]["p4_starling_topological_flocking"]["topological_scaling"][0].__setitem__("diameter", _SubInt(3)), "ERR_CERT_P4", "p4 diam subint", resign=False)
    _tamper(lambda c: c["pillars"]["p4_starling_topological_flocking"]["topological_scaling"][0].__setitem__("diameter", True), "ERR_CERT_P4", "p4 diam bool", resign=False)
    _tamper(lambda c: c["pillars"]["p4_starling_topological_flocking"]["topological_scaling"][1].__setitem__("reff_0_to_15", [1, 1]), "ERR_CERT_P4", "p4 reff drift")
    _tamper(lambda c: c["pillars"]["p4_starling_topological_flocking"]["must_fail_metric_fragmentation_control"].__setitem__("scaling", tuple(c["pillars"]["p4_starling_topological_flocking"]["must_fail_metric_fragmentation_control"]["scaling"])), "ERR_CERT_P4", "p4 met tuple", resign=False)
    _tamper(lambda c: c["pillars"]["p4_starling_topological_flocking"]["must_fail_metric_fragmentation_control"].__setitem__("scaling", []), "ERR_CERT_P4", "p4 met len")
    _tamper(lambda c: c["pillars"]["p4_starling_topological_flocking"]["must_fail_subcritical_k1_control"].__setitem__("components", 1), "ERR_CERT_P4", "p4 k1 comps=1")
    _tamper(lambda c: c["pillars"]["p4_starling_topological_flocking"]["must_fail_subcritical_k1_control"].__setitem__("components", _SubInt(3)), "ERR_CERT_P4", "p4 k1 comps subint", resign=False)
    _tamper(lambda c: c["pillars"]["p4_starling_topological_flocking"]["must_fail_subcritical_k1_control"].__setitem__("components", True), "ERR_CERT_P4", "p4 k1 comps bool")

    # Pillar 5 tampers (including code-vec bounds/parity & NATX102-BYPASS-03 negative errors)
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"].__setitem__("base_d8_codes", tuple(c["pillars"]["p5_synaptic_homeostatic_siliquant"]["base_d8_codes"])), "ERR_CERT_P5", "p5 code tuple", resign=False)
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"].__setitem__("base_d8_codes", [0] * 7), "ERR_CERT_P5", "p5 code len7")
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"].__setitem__("base_d8_codes", [False, 1, -3, 4, -7, 6, -2, 5]), "ERR_CERT_P5", "p5 code bool", resign=False)
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"].__setitem__("base_d8_codes", [-8, 1, -3, 4, -7, 6, -2, 5]), "ERR_CERT_P5", "p5 code <-q_max")
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"].__setitem__("base_d8_codes", [8, 1, -3, 4, -7, 6, -2, 5]), "ERR_CERT_P5", "p5 code >q_max")
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"].__setitem__("base_d8_codes", [1, 1, -3, 4, -7, 6, -2, 5]), "ERR_CERT_P5", "p5 d8 odd parity")
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"]["multiplicative_upscaling"].__setitem__("max_ratio_drift", [1, 10]), "ERR_CERT_P5", "p5 up ratio")
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"]["multiplicative_upscaling"].__setitem__("squared_cosine_drift", [1, 10]), "ERR_CERT_P5", "p5 up cos")
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"]["multiplicative_upscaling"].__setitem__("zero_weight_after", [1, 10]), "ERR_CERT_P5", "p5 up zero")
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"]["damped_homeostatic_control"].__setitem__("final_error", [1, 2]), "ERR_CERT_P5", "p5 damped err>=init")
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"]["damped_homeostatic_control"].__setitem__("final_error", [-1, 10]), "ERR_CERT_P5", "p5 damped err<0")
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"]["damped_homeostatic_control"].__setitem__("max_trajectory_ratio_drift", [1, 10]), "ERR_CERT_P5", "p5 damped ratio")
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"]["deadbeat_homeostatic_control"].__setitem__("post_step_error", [1, 10]), "ERR_CERT_P5", "p5 deadbeat err")
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"]["must_fail_additive_shift_control"].__setitem__("zero_weight_after", [0, 1]), "ERR_CERT_P5", "p5 add zero")
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"]["must_fail_additive_shift_control"].__setitem__("max_ratio_drift", [0, 1]), "ERR_CERT_P5", "p5 add ratio")
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"]["must_fail_additive_shift_control"].__setitem__("squared_cosine_drift", [0, 1]), "ERR_CERT_P5", "p5 add cos")
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"]["must_fail_additive_shift_control"].__setitem__("absmax_code_flips", 0), "ERR_CERT_P5", "p5 add abs flips 0")
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"]["must_fail_additive_shift_control"].__setitem__("absmax_code_flips", True), "ERR_CERT_P5", "p5 add abs flips bool")
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"]["must_fail_additive_shift_control"].__setitem__("d8_code_flips", 0), "ERR_CERT_P5", "p5 add d8 flips 0")
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"]["must_fail_additive_shift_control"].__setitem__("d8_code_flips", True), "ERR_CERT_P5", "p5 add d8 flips bool")
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"]["must_fail_unstable_gain_control"].__setitem__("final_error", [1, 20]), "ERR_CERT_P5", "p5 unstable err<=init")
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"]["must_fail_unstable_gain_control"].__setitem__("initial_error", [0, 1]), "ERR_CERT_P5", "p5 unstable init==0")
    _tamper(lambda c: c["pillars"]["p5_synaptic_homeostatic_siliquant"]["must_fail_unstable_gain_control"].__setitem__("initial_error", [-1, 10]), "ERR_CERT_P5", "p5 unstable init<0")
    _check(cert["summary"]["must_fail_controls_verified"] == 11, "11 dynamic must_fail controls")
    _tamper(lambda c: c["summary"].__setitem__("must_fail_controls_verified", 10), "ERR_CERT_INT", "summary controls count 10!=11")

    # SHA-256 tamper checks (strict str, length 64, lowercase hex, digest mismatch)
    _tamper(lambda c: c.__setitem__("canonical_sha256", _SubStr(c["canonical_sha256"])), "ERR_CERT_SHA", "sha substr", resign=False)
    _tamper(lambda c: c.__setitem__("canonical_sha256", "a" * 63), "ERR_CERT_SHA", "sha len 63", resign=False)
    _tamper(lambda c: c.__setitem__("canonical_sha256", c["canonical_sha256"].upper()), "ERR_CERT_SHA", "sha upper", resign=False)
    _tamper(lambda c: c.__setitem__("canonical_sha256", "g" * 64), "ERR_CERT_SHA", "sha non-hex", resign=False)
    flipped = ("0" if cert["canonical_sha256"][0] != "0" else "1") + cert["canonical_sha256"][1:]
    _tamper(lambda c: c.__setitem__("canonical_sha256", flipped), "ERR_CERT_SHA", "sha mismatch", resign=False)

    # CLI certifier round-trip tests (--output, --check, --check --json, --json, drift detection)
    with tempfile.TemporaryDirectory() as tmpdir:
        out_path = os.path.join(tmpdir, "cert.json")
        orig_stdout = sys.stdout
        try:
            buf = io.StringIO()
            sys.stdout = buf
            rc = nec.main(["--output", out_path])
            _check(rc == 0 and buf.getvalue() == "", "cli --output quiet stdout")

            buf2 = io.StringIO()
            sys.stdout = buf2
            rc2 = nec.main(["--check", out_path])
            _check(rc2 == 0 and "OK AUDIT-102" in buf2.getvalue(), "cli --check summary")

            buf3 = io.StringIO()
            sys.stdout = buf3
            rc3 = nec.main(["--check", out_path, "--json"])
            _check(rc3 == 0 and json.loads(buf3.getvalue()) == cert, "cli --check --json")

            buf4 = io.StringIO()
            sys.stdout = buf4
            rc4 = nec.main(["--json"])
            _check(rc4 == 0 and json.loads(buf4.getvalue()) == cert, "cli --json")

            buf5 = io.StringIO()
            sys.stdout = buf5
            rc5 = nec.main([])
            _check(rc5 == 0 and json.loads(buf5.getvalue()) == cert, "cli default stdout")

            out_path2 = os.path.join(tmpdir, "cert2.json")
            buf6 = io.StringIO()
            sys.stdout = buf6
            rc6 = nec.main(["--output", out_path2, "--json"])
            _check(rc6 == 0 and json.loads(buf6.getvalue()) == cert and os.path.isfile(out_path2), "cli --output --json")
        finally:
            sys.stdout = orig_stdout

        # Drift check: alter a non-validated text field and re-sign -> valid schema but drifts from fresh recomputation
        drifted = copy.deepcopy(cert)
        drifted["law5_discipline"]["operator_scope"] = "modified_scope"
        _resign(drifted)
        drift_path = os.path.join(tmpdir, "drifted.json")
        with open(drift_path, "w", encoding="utf-8", newline="\n") as fh:
            fh.write(nec.format_pretty_json(drifted))
        _expect_error(lambda: nec.check_certificate_file(drift_path), "ERR_CERT_DRIFT", "cli drift detect")

        # Strict JSON file checks: duplicate keys, float literal, NaN constant, malformed JSON, non-canonical bytes
        for fname, content, code in (
            ("dup.json", '{"a": 1, "a": 2}\n', "ERR_CERT_JSON"),
            ("flt.json", '{"a": 1.5}\n', "ERR_CERT_FLOAT"),
            ("nan.json", '{"a": NaN}\n', "ERR_CERT_FLOAT"),
            ("bad.json", "{bad\n", "ERR_CERT_JSON"),
            ("compact.json", json.dumps(cert, sort_keys=True, separators=(",", ":")) + "\n", "ERR_CERT_DRIFT"),
        ):
            p = os.path.join(tmpdir, fname)
            with open(p, "w", encoding="utf-8", newline="\n") as fh:
                fh.write(content)
            _expect_error(lambda path=p: nec.check_certificate_file(path), code, f"cli strict {fname}")


def main() -> int:
    groups = (
        ("group1_core_pure_q_helpers", test_group1_core_pure_q_helpers),
        ("group2_pillar1_kinetic_proofreading", test_group2_pillar1_kinetic_proofreading),
        ("group3_pillar2_immune_negative_selection", test_group3_pillar2_immune_negative_selection),
        ("group4_pillar3_turing_reaction_diffusion", test_group4_pillar3_turing_reaction_diffusion),
        ("group5_pillar4_starling_topological_flocking", test_group5_pillar4_starling_topological_flocking),
        ("group6_pillar5_synaptic_homeostatic_siliquant", test_group6_pillar5_synaptic_homeostatic_siliquant),
        ("group7_certificate_validator_and_cli_fail_closed", test_group7_certificate_validator_and_cli_fail_closed),
    )
    for name, fn in groups:
        fn()
        sys.stdout.write(f"PASS {name}\n")
    sys.stdout.write(f"OK all {len(groups)}/7 R5 groups passed\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
