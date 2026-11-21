#!/usr/bin/env python3
"""R1-R5 Verification, Invariance & Mutation-Kill Suite for aletheia_calculus.py (AUDIT-051).

Tests:
  G1: Registry integrity & Unicode/ASCII parser precedence + AST parity
  G2: Coordinate/vertex-relabeling & gauge invariance across all 8 operators
  G3: Exact values & structural laws of all 7 compressed expedition theorems
  G4: All 6 commutator/composition discovery probes (C1..C6) + fresh unseen instances
  G5: Adversarial R5 refusal controls (non-symmetric, floats, OOB, boundary twist,
      singular solve, duplicate index, overlapping union, invalid sign, lex/parse errors)

Zero bare asserts; pure Python 3 stdlib.
"""

from __future__ import annotations

from fractions import Fraction
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import aletheia_calculus as ac


def check(cond: bool, msg: str) -> None:
    if not cond:
        raise ac.CalculusError(f"[TEST_FAIL] {msg}")


def expect_error(code: str, fn) -> None:
    try:
        fn()
    except ac.CalculusError as exc:
        check(f"[{code}]" in str(exc), f"Expected [{code}], got {exc}")
        return
    raise ac.CalculusError(f"[TEST_MISSED_ERR] Expected [{code}], no exception raised")


def test_group_1_registry_and_parser() -> None:
    reg = ac.verify_glyph_registry()
    check(reg["glyph_count"] == 8, "Expected 8 glyphs")
    check(reg["all_category_Sm_and_zero_collision"] is True, "Collision flag false")

    # Verify precedence: ⧄ (60) binds tighter than ⟠ (50), ⦺ (70) tighter than ⩩ (30)
    t_u = ac.Parser(ac.tokenize("⦺(A ⧄ B) ⩩ (1, 0, 0)")).parse()
    t_a = ac.Parser(ac.tokenize("(+-0)(A |/| B) =#= (1, 0, 0)")).parse()
    check(t_u == t_a, "Unicode vs ASCII AST mismatch")
    check(t_u[0] == "EXACTEQ" and t_u[1][0] == "INERTIA" and t_u[1][1][0] == "SCHUR", "Precedence mismatch")

    # Verify unary negation & arithmetic & built-ins
    env = {"a": Fraction(3, 2), "b": Fraction(1, 2)}
    check(ac.eval_expr("-a + b ⩩ -1", env) is True, "Unary neg / add failed")
    check(ac.eval_expr("a * b ⩩ 3/4", env) is True, "Scalar mul failed")

    # Verify R5GATE precedence (20 < 30): left-hand side of ⫩
    p_r5 = ac.Parser(ac.tokenize("T ⫩ x")).parse()
    check(p_r5 == ("R5GATE", ("VAR", "T"), ("VAR", "x")), "R5GATE AST mismatch")


def test_group_2_coordinate_and_gauge_invariance() -> None:
    # 1. Vertex-relabeling invariance of ⦺(L ⦷ χ), Φ(L ⦷ χ), Tr(L ⦷ χ), and ⧇(ω)!
    g_orig = ac.make_btz_odd_wormhole()
    chi_orig = ac.CocycleZ2(tuple(-1 if i == 0 else 1 for i in range(len(g_orig.edges))))
    # Apply a non-trivial permutation scrambling boundary and interior vertices
    perm = [9, 3, 7, 1, 5, 0, 8, 2, 6, 4]
    edges_p = tuple((perm[u], perm[v], w) for u, v, w in g_orig.edges)
    b_p = tuple(perm[b] for b in g_orig.boundary)
    g_perm = ac.WeightedGraph(n_verts=10, edges=edges_p, boundary=b_p)

    d_orig = ac.op_holonomy_unmask(g_orig, chi_orig)
    d_perm = ac.op_holonomy_unmask(g_perm, chi_orig)
    check(ac.op_krein_inertia(d_orig) == ac.op_krein_inertia(d_perm), "Krein inertia broke under vertex relabeling")
    check(
        ac.eval_expr("Phi(D1) ⩩ Phi(D2)", {"D1": d_orig, "D2": d_perm}) is True,
        "Monopole flux broke under vertex relabeling",
    )
    check(
        ac.eval_expr("Tr(D1) ⩩ Tr(D2)", {"D1": d_orig, "D2": d_perm}) is True,
        "DtN trace broke under vertex relabeling",
    )

    # 2. Interior coboundary gauge invariance of L ⦷ χ (switch interior vertex 0 NOT touching boundary B!)
    # In g_orig, vertex 0 has edges (0,1), (2,0), (0,3) — NONE touch boundary {6,7,8,9}!
    sw_signs = tuple(
        (-s if (u == 0 or v == 0) else s)
        for (u, v, _w), s in zip(g_orig.edges, chi_orig.signs)
    )
    d_gauge = ac.op_holonomy_unmask(g_orig, ac.CocycleZ2(sw_signs))
    check(ac.op_exact_null_equiv(d_orig, d_gauge) is True, "Interior coboundary gauge changed L ⦷ chi!")

    # 3. Scale invariance & orientation-flip invariance of ⧇(ω)
    om = tuple(Fraction(i + 1) for i in range(len(g_orig.edges)))
    om_scaled = tuple(Fraction(-7, 3) * v for v in om)
    c1 = ac.op_cohom_obstruction(ac.OneCochain(g_orig, om))
    c2 = ac.op_cohom_obstruction(ac.OneCochain(g_orig, om_scaled))
    check(c1 == c2 and Fraction(0) < c1 < Fraction(1), f"Cochain scale invariance failed: {c1} vs {c2}")

    # 4. Idempotence of observer-net equalizer ⟠: (X ⟠ G) ⟠ G ⩩ X ⟠ G
    m = ac.qmat([[5, 1, 2], [1, 7, 3], [2, 3, 9]])
    g3 = ac.ObserverGroup(kind="perm_group", elements=((0, 1, 2), (1, 2, 0), (2, 0, 1)))
    check(ac.eval_expr("(M ⟠ G) ⟠ G ⩩ M ⟠ G", {"M": m, "G": g3}) is True, "Equalizer not idempotent")

    # 5. Bunch-Kaufman 2x2 hyperbolic pivot path (zero diagonal matrix!)
    h2 = ac.qmat([[0, 3, 0, 0], [3, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -5]])
    check(ac.op_krein_inertia(h2) == ac.InertiaTriple(1, 1, 2), "2x2 hyperbolic pivot inertia wrong")

    # 6. Exact Moore-Penrose axioms M M^+ M == M and M^+ M M^+ == M^+ on singular indefinite matrix
    m_indef = ac.qmat([[1, 0, 1], [0, -2, 0], [1, 0, 1]])
    mp = ac.qpinv_sym(m_indef)
    check(ac.qmul(m_indef, ac.qmul(mp, m_indef)) == m_indef, "MP axiom 1 failed")
    check(ac.qmul(mp, ac.qmul(m_indef, mp)) == mp, "MP axiom 2 failed")
    check(ac.qpinv_sym(ac.qzeros(2, 2)) == ac.qzeros(2, 2), "MP zero matrix failed")


def test_group_3_full_engine_and_exact_values() -> None:
    res = ac.run_all()
    check(res["verdict"] == "ALETHEIA_OPERATOR_CALCULUS_ALL_LAWS_VERIFIED", "Bad verdict")
    check(res["compressed_expedition_theorems"]["theorems_verified"] == 13, "Expected 13 compressed theorem checks")
    p = res["commutator_discovery_probes"]
    check(p["C1"]["cases_verified"] == 4, "Expected 4 C1 cases")
    check(p["C1"]["cases"][0]["phi_C"] == "8/5" and p["C1"]["cases"][0]["phi_B"] == "44/35", "C1 depth-2 BTZ values wrong")
    check(p["C1"]["cases"][0]["screening_drop"] == "12/35", "C1 screening drop wrong")
    check(p["C1"]["cases"][1]["inertia_delta_B"] == [1, 0, 2], "C1 K3 asymmetry wrong")
    check(p["C2"]["generalized_indefinite_singular_krein_exact"] == "12/12", "C2 gen Krein count wrong")
    check(p["C2"]["nonsingular_B_nested_shadow_preserved"] == {"dim_dark": 1, "r_cross": 1}, "C2 nested shadow wrong")
    check(p["C2"]["coupled_associator_rank"] >= 1, "C2 associator rank wrong")
    check(p["C3"]["non_invariant_strict_PSD_trials"] == "8/8", "C3 Jensen count wrong")
    check(p["C4"]["cases"][0]["phi_woodbury"] == "11/8", "C4 mouth edge wrong")
    check(p["C4"]["cases"][1]["phi_woodbury"] == "4/3", "C4 cut bridge wrong")
    check(p["C4"]["cases"][2]["phi_woodbury"] == "8628/1607", "C4 asym tri wrong")
    check(p["C4"]["cases"][3]["phi_woodbury"] == "0/1", "C4 dangling bridge wrong")
    check(p["C5"]["exact_kill_ratio"] == "1/1" and p["C5"]["float64_kill_ratio"] == "0/1", "C5 killshot wrong")
    check(p["C6"]["structured_cases"][0]["subadditive_slack"] == "3/4", "C6 odd BTZ slack wrong")
    check(p["C6"]["structured_cases"][1]["subadditive_slack"] == "16/21", "C6 even BTZ slack wrong")
    check(p["C6"]["random_extreme_weight_cases_certified"] == "12/12", "C6 random count wrong")


def test_group_4_unseen_adversarial_instances() -> None:
    # Fresh unseen 5-node interior wheel graph (not in main script!) verifying C4 Woodbury + C6 subadditivity!
    edges_w = (
        (0, 1, Fraction(4)), (1, 2, Fraction(9)), (2, 3, Fraction(6)), (3, 0, Fraction(5)),
        (0, 4, Fraction(2)), (1, 4, Fraction(3)), (2, 4, Fraction(7)), (3, 4, Fraction(11)),
        (0, 5, Fraction(3)), (2, 6, Fraction(5)), (4, 7, Fraction(1)),
    )
    gw = ac.WeightedGraph(n_verts=8, edges=edges_w, boundary=(5, 6, 7))
    c1 = ac.CocycleZ2(tuple(-1 if i == 0 else 1 for i in range(11)))
    c2 = ac.CocycleZ2(tuple(-1 if i == 5 else 1 for i in range(11)))
    phi1 = ac.eval_expr("Phi(L ⦷ c1)", {"L": gw, "c1": c1})
    phi2 = ac.eval_expr("Phi(L ⦷ c2)", {"L": gw, "c2": c2})
    phi12 = ac.eval_expr("Phi(L ⦷ (c1 * c2))", {"L": gw, "c1": c1, "c2": c2})
    check(phi1 > 0 and phi2 > 0 and phi12 > 0 and phi12 <= phi1 + phi2, "Unseen wheel subadditivity failed")

    # Fresh unseen shifted Mellin net MUST FAIL equalization when combined with unshifted observer!
    g_mixed = ac.ObserverGroup(
        kind="mellin_net",
        elements=(
            ((Fraction(1), Fraction(1), Fraction(0)),),
            ((Fraction(1), Fraction(1), Fraction(1)),),  # shifted by alpha=1 -> +5/12 != -1/12!
        ),
    )
    expect_error("NET_NOT_EQUALIZED", lambda: ac.op_observer_equalizer(ac.MellinSeriesProbe(1), g_mixed))

    # Purely shifted Mellin net (alpha=1) equalizes to exact +5/12!
    g_shift = ac.ObserverGroup(kind="mellin_net", elements=(((Fraction(1), Fraction(2), Fraction(1)),),))
    check(ac.op_observer_equalizer(ac.MellinSeriesProbe(1), g_shift) == Fraction(5, 12), "Shifted alpha=1 != 5/12")


def test_group_5_r5_adversarial_refusal_controls() -> None:
    # 1. Scalar & Matrix shape/symmetry guards
    expect_error("NO_FLOATS_IN_EXACTEQ", lambda: ac.op_exact_null_equiv(0.1, 0.1))
    expect_error("BAD_Q_SCALAR", lambda: ac.to_q(True))  # type: ignore[arg-type]
    expect_error("EMPTY_MAT", lambda: ac.qmat([]))
    expect_error("EMPTY_COL", lambda: ac.qmat([[]]))
    expect_error("RAGGED_MAT", lambda: ac.qmat([[1, 2], [3]]))
    rect = ac.qmat([[1, 2, 3], [2, 5, 6]])
    check(ac.is_symmetric(rect) is False, "Non-square matrix marked symmetric")
    expect_error("SHAPE_MISMATCH", lambda: ac.qadd(ac.qeye(2), ac.qeye(3)))
    expect_error("SHAPE_MISMATCH", lambda: ac.qsub(ac.qeye(2), ac.qeye(3)))
    expect_error("MUL_SHAPE", lambda: ac.qmul(ac.qeye(2), ac.qeye(3)))
    expect_error("SOLVE_SHAPE", lambda: ac.qsolve(rect, ac.qeye(2)))

    # 2. Non-symmetric matrix rejected by ⦺, ⧄, ⧅, qpinv_sym
    asym = ac.qmat([[1, 2], [0, 1]])
    expect_error("NOT_SYMMETRIC", lambda: ac.op_krein_inertia(asym))
    expect_error("NOT_SYMMETRIC", lambda: ac.qpinv_sym(asym))
    expect_error("SCHUR_NOT_SYM", lambda: ac.op_schur_pushforward(asym, ac.IndexSet((1,))))
    expect_error("SHADOW_NOT_SYM", lambda: ac.op_dark_mode_shadow(asym, ac.IndexSet((1,))))

    # 3. Graph / Laplacian / Cocycle / Cochain guards (including boundary w=0)
    g_odd = ac.make_btz_odd_wormhole()
    bad_chi = ac.CocycleZ2(tuple(-1 if i == 7 else 1 for i in range(len(g_odd.edges))))
    expect_error("BOUNDARY_TWIST", lambda: ac.op_holonomy_unmask(g_odd, bad_chi))
    expect_error("SIGN_LEN", lambda: g_odd.laplacian((1, 1)))
    expect_error("BAD_SIGN", lambda: g_odd.laplacian((2,) + (1,) * (len(g_odd.edges) - 1)))
    g_zero_w = ac.WeightedGraph(2, ((0, 1, Fraction(0)),), (1,))
    expect_error("NONPOS_WEIGHT", lambda: g_zero_w.laplacian())
    expect_error("COCYCLE_LEN", lambda: ac.CocycleZ2((1, -1)).product(ac.CocycleZ2((1,))))
    expect_error("COCHAIN_LEN", lambda: ac.OneCochain(g_odd, (Fraction(1),)))

    # 4. IndexSet & Schur/Shadow bounds guards
    expect_error("DUP_INDEX", lambda: ac.IndexSet((1, 1)))
    expect_error("OVERLAP_UNION", lambda: ac.IndexSet((0, 1)).union(ac.IndexSet((1, 2))))
    expect_error("SCHUR_OOB", lambda: ac.op_schur_pushforward(ac.qeye(2), ac.IndexSet((5,))))
    expect_error("SCHUR_EMPTY_KEEP", lambda: ac.op_schur_pushforward(ac.qeye(2), ac.IndexSet((0, 1))))
    expect_error("SHADOW_OOB", lambda: ac.op_dark_mode_shadow(ac.qeye(2), ac.IndexSet((5,))))

    # 5. Observer-Net Equalizer guards (perm_group & mellin_net, incl. boundary order=0, lam=0)
    expect_error("EQ_MAT_REQ", lambda: ac.op_observer_equalizer(Fraction(1), ac.ObserverGroup("perm_group", ((0,),))))
    expect_error("EMPTY_GROUP", lambda: ac.op_observer_equalizer(ac.qeye(2), ac.ObserverGroup("perm_group", ())))
    expect_error("BAD_PERM", lambda: ac.op_observer_equalizer(ac.qeye(2), ac.ObserverGroup("perm_group", ((0, 0),))))
    expect_error("EQ_MELLIN_REQ", lambda: ac.op_observer_equalizer(Fraction(1), ac.ObserverGroup("mellin_net", ())))
    expect_error("NET_UNNORMALIZED", lambda: ac.op_observer_equalizer(ac.MellinSeriesProbe(1), ac.ObserverGroup("mellin_net", (((Fraction(2), Fraction(1), Fraction(0)),),))))
    expect_error("BAD_LAM", lambda: ac.op_observer_equalizer(ac.MellinSeriesProbe(1), ac.ObserverGroup("mellin_net", (((Fraction(1), Fraction(0), Fraction(0)),),))))
    expect_error("SHIFT_K1_ONLY", lambda: ac.op_observer_equalizer(ac.MellinSeriesProbe(2), ac.ObserverGroup("mellin_net", (((Fraction(1), Fraction(1), Fraction(1)),),))))

    # 6. Singular linear solve, invalid cocycle, empty mutant family, & screen precondition guards
    expect_error("SINGULAR_SOLVE", lambda: ac.qsolve(ac.qmat([[1, 1], [1, 1]]), ac.qeye(2)))
    expect_error("BAD_COCYCLE", lambda: ac.CocycleZ2((2, 1)))
    expect_error("EMPTY_MUTANTS", lambda: ac.op_r5_gate(ac.R5Spec(lambda _x: True, ()), Fraction(0)))
    g_d2 = ac.make_btz_depth2()
    chi_d2 = ac.CocycleZ2(tuple(-1 if i == 0 else 1 for i in range(len(g_d2.edges))))
    expect_error("C1_PARTITION", lambda: ac.verify_screen_commutator("bad_part", g_d2, (3, 4), (0, 1, 2), chi_d2))
    # Non-separating screen: direct edge from deep node 0 to boundary node 6 (changes BB block -> C1_SEP_BB)
    g_nonsep_bb = ac.WeightedGraph(
        n_verts=5,
        edges=((0, 1, Fraction(1)), (1, 2, Fraction(1)), (2, 0, Fraction(1)), (0, 4, Fraction(1)), (1, 3, Fraction(1)), (3, 4, Fraction(1))),
        boundary=(4,),
    )
    expect_error("C1_NOT_SEPARATING", lambda: ac.verify_screen_commutator("nonsep_bb", g_nonsep_bb, (3,), (0, 1, 2), ac.CocycleZ2((-1, 1, 1, 1, 1, 1))))

    # 7. Lexer / Parser / Eval type errors
    expect_error("LEX_ERR", lambda: ac.tokenize("A @ B"))
    expect_error("PARSE_ERR", lambda: ac.Parser(ac.tokenize("(1 + 2")).parse())
    expect_error("PARSE_ERR", lambda: ac.Parser(ac.tokenize("A ⧄ )")).parse())
    expect_error("TRAILING_TOK", lambda: ac.Parser(ac.tokenize("1 2")).parse())
    expect_error("UNBOUND_VAR", lambda: ac.eval_expr("missing_var", {}))
    expect_error("UNKNOWN_FN", lambda: ac.eval_expr("bogus(1)", {}))
    expect_error("BAD_UNION", lambda: ac.eval_expr("1 | 2", {}))
    expect_error("DIM_REQ_SHADOW", lambda: ac.eval_expr("dim(1)", {}))
    expect_error("KILL_REQ_GATE", lambda: ac.eval_expr("kill(1)", {}))


def main() -> int:
    groups = (
        test_group_1_registry_and_parser,
        test_group_2_coordinate_and_gauge_invariance,
        test_group_3_full_engine_and_exact_values,
        test_group_4_unseen_adversarial_instances,
        test_group_5_r5_adversarial_refusal_controls,
    )
    for fn in groups:
        fn()
    print(f"ROUND4C_ALETHEIA_OPERATOR_CALCULUS_R5_OK: {len(groups)}/{len(groups)} test groups passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
