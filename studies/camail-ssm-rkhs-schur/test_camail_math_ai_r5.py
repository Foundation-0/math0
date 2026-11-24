#!/usr/bin/env python3
"""R1-R5 Verification, Invariance, Unseen-Instance & Mutation-Kill Suite for AUDIT-058.

Pure Python 3 stdlib; zero bare asserts; 100% guard coverage for `aletheia mutate`.
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

import camail_math_ai_symbiosis as cm


def check(cond: bool, msg: str) -> None:
    if not cond:
        raise cm.CamailAuditError(f"[TEST_FAIL] {msg}")


def expect_error(code: str, fn) -> None:
    try:
        fn()
    except cm.CamailAuditError as exc:
        check(f"[{code}]" in str(exc), f"Expected [{code}], got {exc}")
        return
    raise cm.CamailAuditError(f"[TEST_MISSED_ERR] Expected [{code}], got no error")


def assert_no_floats(obj: object, path: str = "root") -> None:
    check(not isinstance(obj, float), f"Float found at {path}: {obj!r}")
    if isinstance(obj, dict):
        for k, v in obj.items():
            assert_no_floats(v, f"{path}.{k}")
    elif isinstance(obj, (list, tuple)):
        for i, v in enumerate(obj):
            assert_no_floats(v, f"{path}[{i}]")


def test_group_1_full_certificate_and_zero_floats() -> None:
    res = cm.run_all()
    assert_no_floats(res)
    check(res["verdict"] == "CAMAIL_MATH_AI_SYMBIOSIS_ALL_VERIFIED", f"Bad verdict: {res['verdict']}")
    p1, p2, p3, p4 = res["pillars"]["P1"], res["pillars"]["P2"], res["pillars"]["P3"], res["pillars"]["P4"]
    check(p1["camail_b1_exact_qi_proof"]["bug_equals_conjugated_observability"] is True, "CAMAIL-B1 failed")
    check(p1["lti_lyapunov_and_schur_spa"]["spa_dc_error"] == "0/1", "SPA DC error nonzero")
    check(p1["lti_lyapunov_and_schur_spa"]["direct_dc_error"] != "0/1", "Direct truncation DC error zero")
    check(p1["stable_rank_r_opt_rh4_hierarchy"]["cs11_rank3_vs_rank4_separation"]["shared_R_opt"] == "8/3", "CS-11 R_opt wrong")
    check(p1["stable_rank_r_opt_rh4_hierarchy"]["cs11_rank3_vs_rank4_separation"]["R_H4_rank3_diag_2_1_1_0"] == "3/1", "CS-11 R_H4 rank3 wrong")
    check(p2["gdn_hadamard_equivariance_exact_Q"]["readout_exact_zero_residual_3steps"] is True, "GDN equivariance failed")
    check(p2["exact_lattice_amplification_laws"]["G_E8_over_G_Z_exact"] == "929/1080", "E8/Z ratio wrong")
    check(p3["camail_b4_exact_krein_refutation"]["gamma_half_buggy_D2"] == "-31/1536", "CAMAIL-B4 buggy D2 wrong")
    check(p3["camail_b4_exact_krein_refutation"]["gamma_half_fixed_D2"] == "1/1536", "CAMAIL-B4 fixed D2 wrong")
    check(p3["camail_b4_exact_krein_refutation"]["gamma_half_buggy_krein"] == [8, 0, 1], "CAMAIL-B4 Krein wrong")
    check(p3["camail_b4_exact_krein_refutation"]["gamma_two_spurious_floor"] == "1/6", "CAMAIL-B4 floor wrong")
    check(p4["qrr_u1_gauge_exact_qi"]["dressed_equals_connection_form"] is True, "QRR dressed identity failed")
    check(p4["discretax_deltanet_wy_inversion"]["exact_inverse_verified"] is True, "WY inversion failed")


def test_group_2_invariance_and_exact_identities() -> None:
    # 1. Permutation invariance of 2D star discrepancy & RKHS Schur-optimal quadrature
    pts = cm.fib_lattice_2d(8, 5, midpoint_shift=True)
    pts_rev = tuple(reversed(pts))
    check(cm.exact_2d_star_discrepancy_linf(pts) == cm.exact_2d_star_discrepancy_linf(pts_rev), "D_inf* not permutation invariant")
    r1 = cm.exact_2d_l2_star_rkhs(pts)
    r2 = cm.exact_2d_l2_star_rkhs(pts_rev)
    check(r1["D2_equal"] == r2["D2_equal"] and r1["D2_schur_opt"] == r2["D2_schur_opt"], "RKHS Schur not permutation invariant")

    # 2. Coordinate swap (x, y) -> (y, x) invariance of 2D D_inf* and L2*
    pts_swap = tuple((y, x) for x, y in pts)
    check(cm.exact_2d_star_discrepancy_linf(pts) == cm.exact_2d_star_discrepancy_linf(pts_swap), "D_inf* not coord-swap invariant")
    check(cm.exact_2d_l2_star_rkhs(pts)["D2_schur_opt"] == cm.exact_2d_l2_star_rkhs(pts_swap)["D2_schur_opt"], "RKHS not coord-swap invariant")

    # 3. Orthogonal similarity invariance of R_opt and R_{H4} via exact rational Hadamard H_4/2
    h4 = cm.sylvester_hadamard_int(4)
    q4 = tuple(tuple(v / 2 for v in row) for row in h4)
    g = cm.qmat([[2, 0, 0, 0], [0, Fraction(4, 3), 0, 0], [0, 0, Fraction(1, 3), 0], [0, 0, 0, Fraction(1, 3)]])
    g_rot = cm.qmul(q4, cm.qmul(g, cm.qtranspose(q4)))
    m1 = cm.spectral_moments_r_opt_rh4(g)
    m2 = cm.spectral_moments_r_opt_rh4(g_rot)
    check(m1["R_opt"] == m2["R_opt"] and m1["R_H4"] == m2["R_H4"], "Moment bounds broke under orthogonal rotation")

    # 4. Exact hyperbolic 2x2 Bunch-Kaufman pivot & Moore-Penrose zero matrix & empty elim Schur
    h2 = cm.qmat([[0, 2, 0], [2, 0, 0], [0, 0, 0]])
    check(cm.op_krein_inertia(h2) == (1, 1, 1), "Hyperbolic 2x2 inertia wrong")
    check(cm.qpinv_sym(cm.qzeros(2, 2)) == cm.qzeros(2, 2), "Zero pinv wrong")
    check(cm.op_schur_pushforward(cm.qeye(2), ()) == cm.qeye(2), "Empty elim Schur wrong")
    check(cm.op_dark_mode_shadow(cm.qeye(2), (1,)) == {"dim_dark": 0, "r_cross": 0}, "Full-rank shadow wrong")

    # 5. Exact Qi division identity
    z1 = cm.Qi(Fraction(3), Fraction(4))
    z2 = cm.Qi(Fraction(1), Fraction(-2))
    check((z1 / z2) * z2 == z1, "Qi division identity failed")


def test_group_3_unseen_instances() -> None:
    # 1. Unseen 1D weighted centered L2 discrepancy at gamma=1/3 on 5 uniform midpoints:
    #    buggy c0 = 1 + 1/108 vs fixed c0 = 1 + 1/36 => exact diff = -1/54, buggy Krein n_- == 1!
    pts5 = tuple(Fraction(2 * k + 1, 10) for k in range(5))
    b = cm.exact_l2_ctr_weighted_gram(pts5, Fraction(1, 3), buggy_sq_c0=True)
    f = cm.exact_l2_ctr_weighted_gram(pts5, Fraction(1, 3), buggy_sq_c0=False)
    check(b["D2_equal"] - f["D2_equal"] == Fraction(-1, 54), "Unseen gamma=1/3 diff wrong")
    check(b["gram_inertia"][2] == 1 and f["gram_inertia"][2] == 0, "Unseen gamma=1/3 Krein wrong")

    # 2. Unseen 2D Fib_5 (5 points) exact D_inf* and Schur-optimal quadrature
    f5 = cm.fib_lattice_2d(5, 3, midpoint_shift=True)
    d5 = cm.exact_2d_star_discrepancy_linf(f5)
    rk5 = cm.exact_2d_l2_star_rkhs(f5)
    check(Fraction(0) < d5 < Fraction(1, 2), "Unseen Fib_5 D_inf* out of range")
    check(rk5["gram_inertia"] == (6, 0, 0) and rk5["D2_schur_opt"] < rk5["D2_equal"], "Unseen Fib_5 RKHS failed")

    # 3. Unseen rank-1 equal-eigenvalue spectrum where det_h == 0 => R_H4 == R_opt == 2!
    g_eq = cm.qmat([[3, 0, 0], [0, 3, 0], [0, 0, 0]])
    m_eq = cm.spectral_moments_r_opt_rh4(g_eq)
    check(m_eq["R_opt"] == Fraction(2) and m_eq["R_H4"] == Fraction(2), "Degenerate det_h=0 R_H4 failed")

    # 4. Exact closed-interval boundary endpoints {0, 1} accepted cleanly by exact_l2_ctr_weighted_gram!
    end_res = cm.exact_l2_ctr_weighted_gram((Fraction(0), Fraction(1)), Fraction(1), buggy_sq_c0=False)
    check(end_res["gram_inertia"][2] == 0 and end_res["D2_equal"] > 0, "Endpoint {0,1} discrepancy failed")


def test_group_4_r5_adversarial_refusal_controls() -> None:
    # Exercise EVERY require() and boundary guard for 100% mutation kill!
    expect_error("BAD_SCALAR", lambda: cm.to_q(True))  # type: ignore[arg-type]
    expect_error("QI_DIV_ZERO", lambda: cm.Qi(Fraction(1), Fraction(0)) / cm.Qi(Fraction(0), Fraction(0)))
    expect_error("EMPTY_MAT", lambda: cm.qmat([]))
    expect_error("EMPTY_COL", lambda: cm.qmat([[]]))
    expect_error("RAGGED_MAT", lambda: cm.qmat([[1, 2], [3]]))
    expect_error("BAD_DIM", lambda: cm.qeye(0))
    expect_error("BAD_DIM", lambda: cm.qeye(True))  # type: ignore[arg-type]

    # Leading-symmetric non-square matrix kills `if n != len(m[0]): -> if False:`
    rect_top_sym = cm.qmat([[1, 2, 3], [2, 5, 6]])
    check(cm.is_symmetric(rect_top_sym) is False, "Non-square top-sym marked symmetric")

    expect_error("SHAPE_ERR", lambda: cm.qadd(cm.qeye(2), cm.qeye(3)))
    expect_error("SHAPE_ERR", lambda: cm.qsub(cm.qeye(2), cm.qeye(3)))
    expect_error("MUL_SHAPE", lambda: cm.qmul(cm.qeye(2), cm.qeye(3)))
    expect_error("TRACE_SQUARE", lambda: cm.qtrace(rect_top_sym))
    expect_error("SOLVE_SHAPE", lambda: cm.qsolve(rect_top_sym, cm.qeye(2)))
    expect_error("SINGULAR_SOLVE", lambda: cm.qsolve(cm.qmat([[1, 1], [1, 1]]), cm.qeye(2)))

    asym = cm.qmat([[1, 2], [0, 1]])
    expect_error("NOT_SYM", lambda: cm.qpinv_sym(asym))
    expect_error("NOT_SYM", lambda: cm.op_krein_inertia(asym))
    expect_error("SCHUR_NOT_SYM", lambda: cm.op_schur_pushforward(asym, (1,)))
    expect_error("SCHUR_BAD_IDX", lambda: cm.op_schur_pushforward(cm.qeye(2), (5,)))
    expect_error("SCHUR_BAD_IDX", lambda: cm.op_schur_pushforward(cm.qeye(2), (0, 0)))
    expect_error("SCHUR_EMPTY_KEEP", lambda: cm.op_schur_pushforward(cm.qeye(2), (0, 1)))
    expect_error("SHADOW_NOT_SYM", lambda: cm.op_dark_mode_shadow(asym, (1,)))
    expect_error("SHADOW_BAD_IDX", lambda: cm.op_dark_mode_shadow(cm.qeye(2), (5,)))

    expect_error("NOT_PSD_MOMENT", lambda: cm.spectral_moments_r_opt_rh4(cm.qmat([[1, 0], [0, -1]])))
    expect_error("ZERO_GRAM", lambda: cm.spectral_moments_r_opt_rh4(cm.qzeros(2, 2)))
    expect_error("LYAP_SHAPE", lambda: cm.solve_discrete_lyapunov_q(rect_top_sym, cm.qeye(2)))
    expect_error("BAD_HAD_N", lambda: cm.sylvester_hadamard_int(3))
    expect_error("BAD_HAD_N", lambda: cm.sylvester_hadamard_int(0))

    expect_error("EMPTY_PTS", lambda: cm.exact_l2_ctr_weighted_gram((), Fraction(1), buggy_sq_c0=False))
    expect_error("BAD_GAMMA", lambda: cm.exact_l2_ctr_weighted_gram((Fraction(1, 2),), Fraction(0), buggy_sq_c0=False))
    expect_error("PT_OOB", lambda: cm.exact_l2_ctr_weighted_gram((Fraction(3, 2),), Fraction(1), buggy_sq_c0=False))
    expect_error("PT_OOB", lambda: cm.exact_l2_ctr_weighted_gram((Fraction(-1, 2),), Fraction(1), buggy_sq_c0=False))
    expect_error("EMPTY_PTS2D", lambda: cm.exact_2d_star_discrepancy_linf(()))
    expect_error("PT2D_OOB", lambda: cm.exact_2d_star_discrepancy_linf(((Fraction(2), Fraction(0)),)))
    expect_error("EMPTY_PTS2D", lambda: cm.exact_2d_l2_star_rkhs(()))


def main() -> int:
    groups = (
        test_group_1_full_certificate_and_zero_floats,
        test_group_2_invariance_and_exact_identities,
        test_group_3_unseen_instances,
        test_group_4_r5_adversarial_refusal_controls,
    )
    for fn in groups:
        fn()
    print(f"ROUND5_CAMAIL_MATH_AI_R5_OK: {len(groups)}/{len(groups)} test groups passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
