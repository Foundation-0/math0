#!/usr/bin/env python3
"""R1-R5 Adversarial & Mutation Test Suite for Arm R5-5 (AUDIT-060).

Zero external dependencies. Zero bare asserts.
Safe across all 4 isolated R4 Python modes (-I -B, -I -O -B, -I -B -W error, -I -O -B -W error).
"""
from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import alphaxiv_math_formal_audit as mod


def _req(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


def _must_raise_code(fn, expected_code: str) -> None:
    try:
        fn()
    except mod.AuditError as exc:
        _req(exc.code == expected_code, f"Expected AuditError({expected_code}), got {exc.code}: {exc.message}")
        return
    raise AssertionError(f"Expected AuditError({expected_code}) but call succeeded")


class TestAlphaxivMathFormalR5(unittest.TestCase):
    def test_01_r1_r3_scalar_matrix_and_schur_guards(self) -> None:
        # Scalar R3 guards: bool rejected, float rejected
        _must_raise_code(lambda: mod.to_q(True), "R3_BAD_SCALAR")
        _must_raise_code(lambda: mod.to_q(1.5), "R3_BAD_SCALAR")
        _req(mod.to_q(3) == Fraction(3), "int to_q failed")
        _req(mod.to_q(Fraction(2, 3)) == Fraction(2, 3), "Fraction to_q failed")

        # Matrix shape guards
        _must_raise_code(lambda: mod.qmat([]), "EMPTY_MATRIX")
        _must_raise_code(lambda: mod.qmat([[]]), "EMPTY_COLUMNS")
        _must_raise_code(lambda: mod.qmat([[1, 2], [3]]), "RAGGED_MATRIX")

        # qdet_and_inv guards: non-square, singular
        _must_raise_code(lambda: mod.qdet_and_inv(mod.qmat([[1, 2, 3], [4, 5, 6]])), "NON_SQUARE")
        _must_raise_code(lambda: mod.qdet_and_inv(mod.qmat([[1, 2], [2, 4]])), "SINGULAR_MATRIX")

        # Symmetry & Schur & Inertia guards
        asym = mod.qmat([[1, 2], [0, 1]])
        _req(not mod.is_symmetric(mod.qmat([[1, 2, 3], [2, 4, 5]])), "rectangular matrix must not be symmetric")
        _must_raise_code(lambda: mod.qpinv_sym(asym), "NOT_SYMMETRIC")
        _must_raise_code(lambda: mod.qschur_pushforward(asym, (1,)), "SCHUR_NOT_SYMMETRIC")
        _must_raise_code(lambda: mod.qinertia(asym), "INERTIA_NOT_SYMMETRIC")

        sym = mod.qmat([[2, 1], [1, 2]])
        _must_raise_code(lambda: mod.qschur_pushforward(sym, (0, 0)), "SCHUR_DUP_INDEX")
        _must_raise_code(lambda: mod.qschur_pushforward(sym, (2,)), "SCHUR_OOB_INDEX")
        _must_raise_code(lambda: mod.qschur_pushforward(sym, (-1,)), "SCHUR_OOB_INDEX")
        _must_raise_code(lambda: mod.qschur_pushforward(sym, (0, 1)), "SCHUR_EMPTY_KEEP")
        _req(mod.qschur_pushforward(sym, ()) == sym, "empty elim must return M")

        # Hyperbolic 2x2 zero-diagonal inertia control -> (1, 0, 1)
        hyp = mod.qmat([[0, 3], [3, 0]])
        _req(mod.qinertia(hyp) == (1, 0, 1), f"hyperbolic inertia failed: {mod.qinertia(hyp)}")
        # Zero matrix pinv control
        z2 = mod.qzeros(2, 2)
        _req(mod.qpinv_sym(z2) == z2 and mod.qinertia(z2) == (0, 2, 0), "zero matrix pinv/inertia failed")

    def test_02_feige_extremizer_and_hardened_axiom_log_guards(self) -> None:
        # Must-fail boundary controls on verify_feige_exact_extremizer
        _must_raise_code(lambda: mod.verify_feige_exact_extremizer(15), "FEIGE_BAD_N")
        _must_raise_code(lambda: mod.verify_feige_exact_extremizer(True), "FEIGE_BAD_N")
        res16 = mod.verify_feige_exact_extremizer(16)
        _req(res16["verified"] is True, "Feige n=16 failed")

        # Must-fail controls on verify_feige_axiom_log_strict (closing FEIGE-AUDIT-01!)
        good_log = "'Feige.sharp_unit_slack_feige_complete' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        ok = mod.verify_feige_axiom_log_strict(good_log, ("Feige.sharp_unit_slack_feige_complete",))
        _req(ok["passed"] is True, "good axiom log failed")

        # R1 empty log & empty required decls
        _must_raise_code(lambda: mod.verify_feige_axiom_log_strict("   ", ("Foo",)), "EMPTY_AXIOM_LOG")
        _must_raise_code(lambda: mod.verify_feige_axiom_log_strict(good_log, ()), "EMPTY_REQUIRED_DECLS")
        # Error or sorryAx rejected
        _must_raise_code(
            lambda: mod.verify_feige_axiom_log_strict(good_log + "error: bad\n", ("Feige.sharp_unit_slack_feige_complete",)),
            "AXIOM_LOG_ERROR_OR_SORRY",
        )
        _must_raise_code(
            lambda: mod.verify_feige_axiom_log_strict(
                "'Feige.sharp_unit_slack_feige_complete' depends on axioms: [propext, sorryAx]\n",
                ("Feige.sharp_unit_slack_feige_complete",),
            ),
            "AXIOM_LOG_ERROR_OR_SORRY",
        )
        # FEIGE-AUDIT-01 exploit: log audits True.intro instead of required theorem -> MUST FAIL!
        _must_raise_code(
            lambda: mod.verify_feige_axiom_log_strict(
                "'True.intro' does not depend on any axioms\n",
                ("Feige.sharp_unit_slack_feige_complete",),
            ),
            "MISSING_REQUIRED_DECL",
        )
        # Custom/forbidden axiom Lean.ofReduceBool rejected!
        _must_raise_code(
            lambda: mod.verify_feige_axiom_log_strict(
                "'Feige.sharp_unit_slack_feige_complete' depends on axioms: [propext, Lean.ofReduceBool]\n",
                ("Feige.sharp_unit_slack_feige_complete",),
            ),
            "UNEXPECTED_AXIOMS",
        )

    def test_03_sumset_carry_automaton_and_collatz_wielandt_guards(self) -> None:
        # Must-fail controls on build_diff_carry_automaton & charpoly_3x3_int
        _must_raise_code(lambda: mod.build_diff_carry_automaton((0,), 1), "SUMSET_BAD_BASE")
        _must_raise_code(lambda: mod.build_diff_carry_automaton((0, 0), 12), "SUMSET_BAD_DIGITS")
        _must_raise_code(lambda: mod.build_diff_carry_automaton((0, 12), 12), "SUMSET_DIGIT_RANGE")
        _must_raise_code(lambda: mod.build_diff_carry_automaton((-1, 0), 12), "SUMSET_DIGIT_RANGE")
        _must_raise_code(lambda: mod.charpoly_3x3_int([[1, 0], [0, 1]]), "NOT_3X3")

        # Must-fail controls on collatz_wielandt_certify
        m_imp = [[4, 4, 3], [3, 6, 3], [3, 4, 4]]
        _must_raise_code(
            lambda: mod.collatz_wielandt_certify(m_imp, (Fraction(1), Fraction(1)), Fraction(12)),
            "CW_DIM_MISMATCH",
        )
        _must_raise_code(
            lambda: mod.collatz_wielandt_certify(m_imp, (Fraction(1), Fraction(0), Fraction(1)), Fraction(12)),
            "CW_NONPOS_VEC",
        )
        _must_raise_code(
            lambda: mod.collatz_wielandt_certify([[-1, 0, 0], [0, 1, 0], [0, 0, 1]], (Fraction(1), Fraction(1), Fraction(1)), Fraction(12)),
            "CW_NEG_ENTRY",
        )

        # Positive & negative Collatz-Wielandt certification
        bad_cw = mod.collatz_wielandt_certify(m_imp, (Fraction(1), Fraction(53, 48), Fraction(53, 48)), Fraction(183, 16))
        good_cw = mod.collatz_wielandt_certify(m_imp, (Fraction(1), Fraction(53, 48), Fraction(1)), Fraction(183, 16))
        _req(bad_cw["certified"] is False, "Printed vector should fail CW <= 183/16")
        _req(good_cw["certified"] is True and good_cw["max_ratio"] == "606/53", f"Repaired CW failed: {good_cw}")

    def test_04_hilbert_and_group_guards(self) -> None:
        _must_raise_code(lambda: mod.verify_finite_hilbert_bareiss_and_rh4(1), "HILBERT_BAD_N")
        _must_raise_code(lambda: mod.verify_finite_hilbert_bareiss_and_rh4(11), "HILBERT_BAD_N")
        _must_raise_code(lambda: mod.compute_derived_series_orders(set()), "EMPTY_GROUP")

        # QRR zero-state & non-unit U(1) gauge refusal controls
        zero_vec = ((Fraction(0), Fraction(0)),)
        unit_vec = ((Fraction(1), Fraction(0)),)
        _must_raise_code(lambda: mod.qrr_horizontal_split(zero_vec, unit_vec), "QRR_ZERO_STATE")
        _must_raise_code(
            lambda: mod.apply_u1_gauge_rotation((Fraction(1), Fraction(1)), unit_vec),
            "NOT_UNIT_U1",
        )

        # Offline missing-clone fallback controls (R1 safe unavailable return)
        miss = HERE / "_nonexistent_clone_dir_r5_test"
        r_feige_miss = mod.inspect_feige_clone(miss, HERE)
        r_other_miss = mod.inspect_other_clones(miss, HERE)
        _req(r_feige_miss == {"available": False, "mode": "standalone_offline"}, f"bad feige fallback: {r_feige_miss}")
        _req(r_other_miss == {"available": False, "mode": "standalone_offline"}, f"bad other fallback: {r_other_miss}")

        h4 = mod.verify_finite_hilbert_bareiss_and_rh4(4)
        _req(h4["verified"] is True and len(h4["hilbert_rows"]) == 3, "Hilbert n=4 failed")

    def test_05_full_end_to_end_zero_float_certificate(self) -> None:
        res = mod.run_all(standalone=True)
        _req(res["verdict"] == "ALPHAXIV_MATH_FORMAL_ALL_CHECKS_VERIFIED", f"standalone failed: {res['verdict']}")
        raw = json.dumps(res, sort_keys=True, allow_nan=False)

        # Strictly reject ANY float anywhere in the serialized JSON tree!
        def _reject_float(s: str) -> None:
            raise AssertionError(f"Float literal forbidden in certificate JSON: {s!r}")

        parsed = json.loads(raw, parse_float=_reject_float)
        _req(parsed["module_1_feige_lean_and_exact_extremizer"]["exact_extremizer"]["matches_upstream_summary_sha256"] is True, "Feige SHA mismatch")
        _req(parsed["module_2_sumsets_carry_automaton_and_cw_repair"]["collatz_wielandt_audit_SUMSET_CW_01"]["printed_fails_all_12_perms_and_transposes"] is True, "SUMSET-CW-01 check failed")
        _req(parsed["module_3_hope_hilbert_schur_and_Hn"]["hope_gauge_vs_schur_obstruction"]["schur_incurred_true_error"] == "0/1", "HOPE Schur zero-error failed")
        _req(parsed["module_4_recurrence_and_camail_bridge"]["exact_bridge"]["group_solvability_obstruction"]["A5_perfect_nonsolvable_simple"] is True, "A5 non-solvability failed")


if __name__ == "__main__":
    unittest.main()
