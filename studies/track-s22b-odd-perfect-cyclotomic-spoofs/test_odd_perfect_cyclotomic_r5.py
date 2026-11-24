"""R5 verification, adversarial Zone-B, and mutation-killing test suite for Track S22b.

Zero external dependencies, zero IEEE-754 floats, zero bare asserts, zero RNG.
"""
from __future__ import annotations

import ast
import copy
from fractions import Fraction
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout

ROOT = Path(__file__).resolve().parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import odd_perfect_cyclotomic_audit as audit
import odd_perfect_cyclotomic_oracle as oracle

CERT_PATH = ROOT / audit.DEFAULT_CERT_NAME


def _check(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"S22B_R5_FAILED: {msg}")


def _expect_err(fn, code: str | None = None, label: str = "") -> None:
    try:
        fn()
    except oracle.OddPerfectError as exc:
        if code is not None:
            _check(exc.code == code, f"{label}: expected {code}, got {exc.code} ({exc})")
        return
    raise RuntimeError(f"Expected OddPerfectError({code}) for {label}")


class _EvilPath(type(Path())):
    pass


class _StrSub(str):
    pass


class _IntSub(int):
    pass


class TestTrackS22bOddPerfectCyclotomic(unittest.TestCase):
    def test_01_ast_purity_zero_floats_zero_asserts_and_cert_parity(self) -> None:
        for name in (
            "odd_perfect_cyclotomic_oracle.py",
            "odd_perfect_cyclotomic_audit.py",
            "test_odd_perfect_cyclotomic_r5.py",
        ):
            src = (ROOT / name).read_text(encoding="utf-8")
            tree = ast.parse(src, filename=name)
            asserts = [n.lineno for n in ast.walk(tree) if isinstance(n, ast.Assert)]
            floats = [n.lineno for n in ast.walk(tree) if isinstance(n, ast.Constant) and type(n.value) is float]
            _check(len(asserts) == 0, f"bare asserts in {name}: {asserts}")
            _check(len(floats) == 0, f"float literals in {name}: {floats}")

        res = audit.verify_certificate_file(CERT_PATH)
        _check(res["valid"] is True, "committed certificate invalid")
        cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
        p = cert["payload"]

        # Theorem 1 assertions
        t1 = p["theorem_1_opn_cyclotomic_obstructions"]
        _check(t1["touchard_congruence"]["touchard_theorem_verified"] is True, "Touchard failed")
        _check(t1["touchard_congruence"]["residues_mod_36_when_3_divides_N"] == [9], "Touchard 3|N wrong")
        _check(t1["touchard_congruence"]["residues_mod_36_when_3_nmid_N"] == [1, 13, 25], "Touchard 3 nmid N wrong")
        _check(t1["touchard_congruence"]["rejected_p_mod_36_with_p_eq_2_mod_3"] == [5, 17, 29], "Touchard rejected p wrong")
        _check(t1["cyclotomic_identities"]["pairs_verified"] == 40 and t1["cyclotomic_identities"]["mismatches"] == 0, "cyclotomic id mismatch")
        ceilings = {c["omega"]: (c["strict_upper_bound"], c["below_2"]) for c in t1["three_nmid_rational_ceilings"]}
        _check(ceilings[5] == ("17017/9216", True), f"k=5 ceiling wrong: {ceilings[5]}")
        _check(ceilings[6] == ("323323/165888", True), f"k=6 ceiling wrong: {ceilings[6]}")
        _check(ceilings[7] == ("676039/331776", False), f"k=7 ceiling wrong: {ceilings[7]}")
        _check(all(r["refuted"] for r in t1["unconditional_opn_omega_le_4_refutations"]), "OPN omega<=4 not refuted")
        _check(all(r["refuted"] for r in t1["three_nmid_opn_omega_le_7_refutations"]), "OPN 3 nmid omega<=7 not refuted")
        _check(len(t1["solver_positive_controls"]) == 8 and all(c["recovered"] for c in t1["solver_positive_controls"]), "positive controls missed")

        # Theorem 2 assertions
        t2 = p["theorem_2_odd_spoof_algebra"]
        _check(t2["spoof_count"] == 3 and t2["failure_axes_covered"] == ["distinctness", "positivity", "primality"], "spoof axes incomplete")
        by_name = {s["name"]: s for s in t2["spoofs"]}
        _check(by_name["Descartes_1638"]["spoof_value_N"] == 198585576189, "Descartes N mismatch")
        _check(by_name["Descartes_1638"]["true_abundancy_minus_2"] == "1600/11011", "Descartes defect mismatch")
        _check(by_name["Voight_2003"]["spoof_value_N"] == -22017975903, "Voight N mismatch")
        _check(by_name["Voight_2003"]["true_abundancy_minus_2"] == "2/63", "Voight defect mismatch")
        _check(by_name["Andersen_Byrnes_Nielsen_RepeatedSigned"]["spoof_value_N"] == 101411037, "ABN N mismatch")
        _check(by_name["Andersen_Byrnes_Nielsen_RepeatedSigned"]["true_abs_N_class"] == "deficient", "ABN class mismatch")

        # Theorem 3 assertions
        t3 = p["theorem_3_outlaws_and_solitary10"]
        _check(t3["greening_solitary_le_30"] == [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 21, 23, 25, 27, 29], "Greening <=30 wrong")
        _check(len(t3["friendly_clubs"]) == 5 and all(c["verified"] for c in t3["friendly_clubs"]), "clubs wrong")
        _check(len(t3["unconditional_outlaws_type_A"]) == 8 and len(t3["unconditional_outlaws_type_B_nontrivial"]) == 3, "outlaws count wrong")
        _check(t3["open_frontier_five_thirds_weiner"]["omega_le_3_refutation"]["refuted"] is True, "5/3 k<=3 wrong")
        _check(all(r["refuted"] for r in t3["open_frontier_seven_fifths"]["omega_le_4_refutations"]), "7/5 k<=4 wrong")
        s10 = t3["solitary_10_obstructions"]
        _check(s10["friend_must_be_odd_square"] is True and s10["friend_is_even_square"] is False, "sol10 parity wrong")
        _check(s10["three_cannot_divide_friend"] is True and s10["p_eq_2_mod_3_sigma_even_power_mod_3"] == [1], "sol10 mod3 wrong")
        _check(all(r["refuted"] for r in s10["ward_omega_le_6_refutations"]), "sol10 Ward k<=6 wrong")
        _check(s10["exact_solutions_le_50000"] == [10], "sol10 sieve wrong")

    def test_02_oracle_primitives_boundaries_and_refusal_guards(self) -> None:
        # require_exact_int / require_exact_bool / format_rational boundaries
        _check(oracle.require_exact_int(5, "x", lo=5, hi=5) == 5, "exact boundary lo==hi failed")
        _expect_err(lambda: oracle.require_exact_int(True, "x"), "INVALID_INT", "bool int")
        _expect_err(lambda: oracle.require_exact_int(_IntSub(5), "x"), "INVALID_INT", "int subclass")
        _expect_err(lambda: oracle.require_exact_int(5, "x", lo=True), "INVALID_BOUND", "bool lo")
        _expect_err(lambda: oracle.require_exact_int(5, "x", hi=True), "INVALID_BOUND", "bool hi")
        _expect_err(lambda: oracle.require_exact_int(4, "x", lo=5), "INT_OUT_OF_RANGE", "val < lo")
        _expect_err(lambda: oracle.require_exact_int(6, "x", hi=5), "INT_OUT_OF_RANGE", "val > hi")
        _check(oracle.require_exact_bool(False, "b") is False, "valid bool failed")
        _expect_err(lambda: oracle.require_exact_bool(1, "b"), "INVALID_BOOL", "int as bool")

        # format_rational exact 4000-bit pass vs 4001-bit fail on BOTH num and den!
        ok_big = (1 << oracle.MAX_RATIONAL_BITS) - 1
        too_big = 1 << oracle.MAX_RATIONAL_BITS
        _check(len(oracle.format_rational(Fraction(ok_big, 1))) > 0, "4000-bit num failed")
        _check("/" in oracle.format_rational(Fraction(1, ok_big)), "4000-bit den failed")
        _expect_err(lambda: oracle.format_rational(5), "INVALID_RATIONAL", "int rational")
        _expect_err(lambda: oracle.format_rational(Fraction(too_big, 1)), "RATIONAL_TOO_LARGE", "4001-bit num")
        _expect_err(lambda: oracle.format_rational(Fraction(1, too_big)), "RATIONAL_TOO_LARGE", "4001-bit den")

        # is_prime_exact boundaries (n<2, n==2, small primes, small composites, Carmichael 561, large composite 41*43, strong pseudoprime 341550071728321)
        _check(oracle.is_prime_exact(1) is False and oracle.is_prime_exact(0) is False and oracle.is_prime_exact(-7) is False, "n<2 prime")
        _check(oracle.is_prime_exact(2) is True and oracle.is_prime_exact(3) is True and oracle.is_prime_exact(37) is True, "small primes")
        _check(oracle.is_prime_exact(4) is False and oracle.is_prime_exact(9) is False and oracle.is_prime_exact(49) is False, "small composites")
        _check(oracle.is_prime_exact(41) is True and oracle.is_prime_exact(43) is True, "41/43 prime")
        _check(oracle.is_prime_exact(41 * 43) is False and oracle.is_prime_exact(561) is False, "composite MR")
        _check(oracle.is_prime_exact(341550071728321) is False, "MR pseudoprime 341550071728321")
        _check(oracle.is_prime_exact(22021) is False and oracle.is_prime_exact(127) is True, "22021/127")
        _check(oracle.build_odd_primes(3) == (3,), "build_odd_primes(3) failed")
        _expect_err(lambda: oracle.build_odd_primes(2), "INT_OUT_OF_RANGE", "limit < 3")
        _check(oracle.factorize_exact(1) == {} and oracle.sigma1_exact(1) == 1, "n=1")
        _check(oracle.mobius_exact(1) == 1 and oracle.mobius_exact(4) == 0 and oracle.mobius_exact(6) == 1 and oracle.mobius_exact(30) == -1, "mobius")
        _check(oracle.cyclotomic_eval_exact(1, 3) == 2 and oracle.cyclotomic_eval_exact(3, 3) == 13, "cyclotomic")
        _check(oracle.valuation_exact(24, 2) == 3 and oracle.valuation_exact(9, 2) == 0, "valuation")
        # _strip_and_factor_new_primes with large composite > 5000^2 (triggers unfactored cofactor > 1)
        big_p1, big_p2 = 10007, 10009
        new_ps, cof = oracle._strip_and_factor_new_primes(big_p1 * big_p2, set())
        _check(new_ps == [] and cof == big_p1 * big_p2, "unfactored cofactor failed")
        new_ps2, cof2 = oracle._strip_and_factor_new_primes(5 * big_p1, set())
        _check(new_ps2 == [5, big_p1] and cof2 == 1, "prime remainder extraction failed")

        # solve_abundancy_exact guards & edge cases
        _expect_err(lambda: oracle.solve_abundancy_exact(2, 2), "INVALID_TARGET", "int target")
        _expect_err(lambda: oracle.solve_abundancy_exact(Fraction(1, 1), 2), "INVALID_TARGET", "target == 1")
        _expect_err(lambda: oracle.solve_abundancy_exact(Fraction(2, 1), 0), "INT_OUT_OF_RANGE", "omega=0")
        _expect_err(lambda: oracle.solve_abundancy_exact(Fraction(2, 1), 13), "INT_OUT_OF_RANGE", "omega=13")
        _expect_err(lambda: oracle.solve_abundancy_exact(Fraction(2, 1), 2, need_euler=1), "INVALID_BOOL", "non-bool need_euler")
        _expect_err(lambda: oracle.solve_abundancy_exact(Fraction(2, 1), 2, require_v3_sigma=2, need_euler=False), "INVALID_V3_MODE", "v3 without 3 forbidden")
        _expect_err(lambda: oracle.solve_abundancy_exact(Fraction(2, 1), 2, require_v3_sigma=2, need_euler=True, forbid_primes=frozenset({3})), "INVALID_V3_MODE", "v3 with need_euler=True")
        _expect_err(lambda: oracle.solve_abundancy_exact(Fraction(2, 1), 4, max_nodes=10), "NODE_BUDGET_EXCEEDED", "max_nodes=10")
        _expect_err(lambda: oracle.solve_abundancy_exact(Fraction(2, 1), 2, force_primes=(4,)), "INVALID_FORCED_PRIME", "composite force_prime")
        _expect_err(lambda: oracle.solve_abundancy_exact(Fraction(2, 1), 2, force_primes=(2,)), "INVALID_FORCED_PRIME", "even force_prime 2")
        _expect_err(lambda: oracle.solve_abundancy_exact(Fraction(2, 1), 2, forbid_primes=frozenset({3}), force_primes=(3,)), "INVALID_FORCED_PRIME", "forbidden force_prime")
        # Trigger exact node-budget boundary (nodes == max_nodes passes, nodes > max_nodes fails)
        r_one = oracle.solve_abundancy_exact(Fraction(2, 1), 1, max_nodes=1)
        _check(r_one["nodes_explored"] == 1 and r_one["refuted"] is True, "exact max_nodes==1 failed")
        # Trigger exact target with need_euler=True and force_primes=(5,) to hit init_lb Euler path & 3 nmid N with 3|target.numerator
        r_45 = oracle.solve_abundancy_exact(Fraction(26, 15), 2, need_euler=True, force_primes=(5,))
        _check(any(s["n"] == 45 for s in r_45["solutions_found"]), "forced Euler prime 5 failed")
        # Trigger 3 in forbid_primes AND 3 | target.numerator with need_euler=True (p = 5 ≡ 2 mod 3 IS allowed as Euler prime!)
        # n = 5^1 * 7^2 = 245 -> I(245) = 6/5 * 57/49 = 342/245 (3 | 342!)
        r_245 = oracle.solve_abundancy_exact(Fraction(342, 245), 2, need_euler=True, forbid_primes=frozenset({3}))
        _check(any(s["n"] == 245 for s in r_245["solutions_found"]), "3|tnum with 3 forbidden missed n=245")
        # S22B-BUG-01 exact fail-closed prime-table exhaustion negative controls (NEVER return refuted=True!)
        n_5003_sq = (3**2) * (5003**2)
        n_5003_eu = 5 * (5003**2)
        _expect_err(
            lambda: oracle.solve_abundancy_exact(oracle.abundancy_exact(n_5003_sq), 2, need_euler=False),
            "PRIME_TABLE_EXHAUSTED",
            "3^2*5003^2 must fail closed",
        )
        _expect_err(
            lambda: oracle.solve_abundancy_exact(oracle.abundancy_exact(n_5003_eu), 2, need_euler=True),
            "PRIME_TABLE_EXHAUSTED",
            "5*5003^2 must fail closed",
        )
        _expect_err(
            lambda: oracle.solve_abundancy_exact(Fraction(2, 1), 1, prime_limit=2),
            "INT_OUT_OF_RANGE",
            "prime_limit < 3",
        )
        # Positive recovery when prime_limit covers 5003
        r_5003 = oracle.solve_abundancy_exact(oracle.abundancy_exact(n_5003_sq), 2, need_euler=False, prime_limit=6000)
        _check(any(s["n"] == n_5003_sq for s in r_5003["solutions_found"]), "prime_limit=6000 missed 3^2*5003^2")
        # Trigger prime table exhaustion & unfactored composite cofactor fail-closed guards cleanly
        orig_primes = oracle.ODD_PRIMES
        try:
            oracle.ODD_PRIMES = (3, 5)
            _expect_err(lambda: oracle.solve_abundancy_exact(Fraction(2, 1), 3), "PRIME_TABLE_EXHAUSTED", "small ODD_PRIMES")
            oracle.ODD_PRIMES = (3, 5, 7)
            _expect_err(
                lambda: oracle.solve_abundancy_exact(Fraction(12499, 10000), 2, need_euler=False, force_primes=(5,)),
                "UNFACTORED_COFACTOR",
                "unfactored composite cofactor 781=11*71 must fail closed",
            )
        finally:
            oracle.ODD_PRIMES = orig_primes

        # Spoof & outlaw & club refusal guards
        _expect_err(lambda: oracle.certify_odd_spoof("", ((3, 2),)), "INVALID_SPOOF_NAME", "empty spoof name")
        _expect_err(lambda: oracle.certify_odd_spoof(123, ((3, 2),)), "INVALID_SPOOF_NAME", "int spoof name")
        _expect_err(lambda: oracle.certify_odd_spoof("x", ()), "EMPTY_SPOOF", "empty factors")
        _expect_err(lambda: oracle.certify_odd_spoof("x", ((2, 1),)), "INVALID_SPOOF_BASE", "even base 2")
        _expect_err(lambda: oracle.certify_odd_spoof("x", ((1, 1),)), "INVALID_SPOOF_BASE", "unit base 1")
        _expect_err(lambda: oracle.certify_odd_spoof("x", ((-1, 1),)), "INVALID_SPOOF_BASE", "unit base -1")
        _expect_err(lambda: oracle.certify_odd_spoof("x", ((3, 2),)), "NOT_SPOOF_PERFECT", "not spoof perfect")

        _expect_err(lambda: oracle.certify_friendly_club("", (6, 28), Fraction(2, 1)), "INVALID_CLUB_NAME", "empty club")
        _expect_err(lambda: oracle.certify_friendly_club(1, (6, 28), Fraction(2, 1)), "INVALID_CLUB_NAME", "int club")
        _expect_err(lambda: oracle.certify_friendly_club("c", (6,), Fraction(2, 1)), "CLUB_TOO_SMALL", "1-member club")
        _expect_err(lambda: oracle.certify_friendly_club("c", (6, 28), Fraction(1, 1)), "INVALID_CLUB_RATIO", "ratio == 1")
        _expect_err(lambda: oracle.certify_friendly_club("c", (6, 28), 2), "INVALID_CLUB_RATIO", "int ratio")
        _expect_err(lambda: oracle.certify_friendly_club("c", (6, 12), Fraction(2, 1)), "FRIENDLY_CLUB_MISMATCH", "bad member")

        _expect_err(lambda: oracle.certify_type_a_outlaw(6, 4), "OUTLAW_NOT_COPRIME", "6/4 not coprime")
        _expect_err(lambda: oracle.certify_type_a_outlaw(7, 4), "NOT_TYPE_A_OUTLAW", "I(4)==7/4 not >")
        _expect_err(lambda: oracle.certify_type_b_odd_square_outlaw(5, 4), "OUTLAW_B_BAD_ARGS", "even den 4")
        _expect_err(lambda: oracle.certify_type_b_odd_square_outlaw(6, 3), "OUTLAW_B_BAD_ARGS", "not coprime 6/3")
        _expect_err(lambda: oracle.certify_type_b_odd_square_outlaw(11, 9), "OUTLAW_B_TRIVIAL", "I(9)>11/9 trivial")
        _expect_err(lambda: oracle.certify_type_b_odd_square_outlaw(13, 9), "OUTLAW_B_TRIVIAL", "I(9)==13/9 exact boundary")
        _expect_err(lambda: oracle.certify_type_b_odd_square_outlaw(7, 3), "OUTLAW_B_EVEN_ALLOWED", "I(6)<7/3")
        _expect_err(lambda: oracle.certify_type_b_odd_square_outlaw(9, 5), "OUTLAW_B_EVEN_ALLOWED", "I(10)==9/5 exact boundary")
        _expect_err(lambda: oracle.certify_type_b_odd_square_outlaw(26, 15), "OUTLAW_B_PARITY_UNPROVEN", "5==1 mod 4 allows 5^1")
        _expect_err(lambda: oracle.certify_type_b_odd_square_outlaw(52, 33), "OUTLAW_B_PARITY_UNPROVEN", "v2(52)==2 with 33 primes 3mod4")
        _expect_err(lambda: oracle.certify_type_b_odd_square_outlaw(53, 33), "OUTLAW_B_SQ_NO_OVERSHOOT", "I(33^2)<53/33")
        _expect_err(lambda: oracle.certify_type_b_odd_square_outlaw(61, 39), "OUTLAW_B_SQ_NO_OVERSHOOT", "I(39^2)==61/39 exact boundary")
        # S22B-DS-01: non-squarefree denominator exact square-closure (147 = 3*7^2 -> b_sq = 441, NOT 147^2)
        _check(oracle.square_closure_exact(1) == 1, "square_closure(1)")
        _check(oracle.square_closure_exact(9) == 9, "square_closure(9)")
        _check(oracle.square_closure_exact(33) == 1089, "square_closure(33)")
        _check(oracle.square_closure_exact(147) == 441, "square_closure(147)")
        _expect_err(lambda: oracle.square_closure_exact(0), "INT_OUT_OF_RANGE", "square_closure(0)")
        _check(oracle.abundancy_exact(441) == Fraction(247, 147), "I(441) must equal 247/147")
        _expect_err(
            lambda: oracle.certify_type_b_odd_square_outlaw(247, 147),
            "OUTLAW_B_SQ_NO_OVERSHOOT",
            "S22B-DS-01: 247/147 is NOT an outlaw (441 is an exact friend)",
        )
        r_241_147 = oracle.certify_type_b_odd_square_outlaw(241, 147)
        _check(
            r_241_147["unconditional_outlaw"] is True and r_241_147["I_den_squared"] == "247/147" and r_241_147["overshoot"] == "2/49",
            f"non-squarefree Type B positive check failed: {r_241_147}",
        )
        _check(oracle.sieve_friends_of_10(10) == [10], "sieve(10) failed")
        _expect_err(lambda: oracle.sieve_friends_of_10(9), "INT_OUT_OF_RANGE", "sieve < 10")

    def test_03_zone_b_audit_io_symlinks_pwd_fifo_proc_and_cli(self) -> None:
        cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
        cert_bytes = CERT_PATH.read_bytes()

        # In-memory verify_certificate_dict guards
        _check(audit.verify_certificate_dict(cert)["valid"] is True, "valid dict failed")
        _expect_err(lambda: audit.verify_certificate_dict([]), "INVALID_CERT_TYPE", "list cert")
        bad_k = copy.deepcopy(cert); bad_k["extra"] = 1
        _expect_err(lambda: audit.verify_certificate_dict(bad_k), "INVALID_CERT_KEYS", "extra key")
        bad_k2 = copy.deepcopy(cert); del bad_k2["payload"]
        _expect_err(lambda: audit.verify_certificate_dict(bad_k2), "INVALID_CERT_KEYS", "missing key")
        bad_v = copy.deepcopy(cert); bad_v["payload_sha256"] = "0" * 64
        _expect_err(lambda: audit.verify_certificate_dict(bad_v), "CERTIFICATE_MISMATCH", "tampered sha")
        bad_s = copy.deepcopy(cert); bad_s["payload_sha256"] = "\ud800"
        _expect_err(lambda: audit.verify_certificate_dict(bad_s), "INVALID_UTF8_SURROGATE", "surrogate in dict")
        bad_ser = copy.deepcopy(cert); bad_ser["payload"] = {"bad": object()}
        _expect_err(lambda: audit.verify_certificate_dict(bad_ser), "INVALID_JSON_VALUE", "unserializable")
        bad_flt = copy.deepcopy(cert); bad_flt["payload"] = {"bad": 3 / 2}
        _expect_err(lambda: audit.verify_certificate_dict(bad_flt), "INVALID_JSON_VALUE", "float in dict")
        bad_key = copy.deepcopy(cert); bad_key["payload"] = {1: "x"}
        _expect_err(lambda: audit.verify_certificate_dict(bad_key), "INVALID_JSON_KEY", "int key in dict")
        bad_big = copy.deepcopy(cert); bad_big["payload"] = {"n": 1 << oracle.MAX_RATIONAL_BITS}
        _expect_err(lambda: audit.verify_certificate_dict(bad_big), "INT_TOO_LARGE", "4001-bit int in dict")
        _check(audit.parse_strict_json_text('{"n":' + str((1 << oracle.MAX_RATIONAL_BITS) - 1) + ',"z":null,"b":true}', "ok")["z"] is None, "null/bool/4000-bit int failed")

        # Strict JSON text parser guards
        _check(audit.parse_strict_json_text("[1,2]", "arr", require_object=False) == [1, 2], "arr require_object=False failed")
        _expect_err(lambda: audit.parse_strict_json_text(123, "x"), "INVALID_JSON_TEXT", "non-str")
        _expect_err(lambda: audit.parse_strict_json_text("{}", "x", require_object=1), "INVALID_BOOL", "non-bool require_object")
        _expect_err(lambda: audit.parse_strict_json_text("{\x00}", "x"), "NUL_BYTE_FORBIDDEN", "NUL byte")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":1,"a":2}', "x"), "DUPLICATE_JSON_KEY", "dup key")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":NaN}', "x"), "NONFINITE_JSON", "NaN")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":1.5}', "x"), "FLOAT_FORBIDDEN", "float")
        _expect_err(lambda: audit.parse_strict_json_text("[1]", "x", require_object=True), "JSON_ROOT_NOT_OBJECT", "list root")
        _expect_err(lambda: audit.parse_strict_json_text("{bad", "x"), "INVALID_JSON", "bad syntax")
        _expect_err(lambda: audit.parse_strict_json_text('{"n":' + "9" * 5000 + "}", "x"), "INVALID_JSON", "5000-digit int")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":"\\ud800"}', "x"), "INVALID_UTF8_SURROGATE", "surrogate val")
        _expect_err(lambda: audit.parse_strict_json_text('{"\\ud800":1}', "x"), "INVALID_UTF8_SURROGATE", "surrogate key")

        # Exact MAX_JSON_DEPTH boundary (64 passes, 65 fails)
        ok_d: Any = 1
        for _ in range(audit.MAX_JSON_DEPTH - 1):
            ok_d = [ok_d]
        _check(type(audit.parse_strict_json_text(json.dumps({"x": ok_d}), "d64")) is dict, "depth 64 failed")
        _expect_err(lambda: audit.parse_strict_json_text(json.dumps({"x": [ok_d]}), "d65"), "MAX_DEPTH_EXCEEDED", "depth 65")

        # /proc/kallsyms st_size==0 capped read guard (S21F-BUG-01) & /dev/null non-regular write guard
        proc_kallsyms = Path("/proc/kallsyms")
        if proc_kallsyms.exists():
            _expect_err(lambda: audit.read_regular_bytes_capped(proc_kallsyms, "kallsyms", max_bytes=16), "FILE_TOO_LARGE", "/proc/kallsyms cap")
        dev_null = Path("/dev/null")
        if dev_null.exists():
            _expect_err(lambda: audit.write_regular_bytes_safe(dev_null, b"{}\n", "devnull"), "NOT_A_REGULAR_FILE", "/dev/null write")

        with tempfile.TemporaryDirectory(prefix="s22b_zb_") as td:
            root = Path(td)
            cfile = root / "c.json"
            audit.write_regular_bytes_safe(cfile, cert_bytes, "c")
            audit.write_regular_bytes_safe(cfile, b"{}\n", "c_shorter_overwrite")
            _check(cfile.read_bytes() == b"{}\n", "shorter overwrite did not ftruncate")
            audit.write_regular_bytes_safe(cfile, cert_bytes, "c_restore")
            nested_out = root / "new_nested" / "sub" / "w.json"
            audit.write_regular_bytes_safe(nested_out, cert_bytes, "nested_create")
            _check(nested_out.read_bytes() == cert_bytes, "nested dir_fd create failed")
            _check(audit.read_regular_bytes_capped(cfile, "c", max_bytes=len(cert_bytes)) == cert_bytes, "exact max_bytes failed")
            _expect_err(lambda: audit.read_regular_bytes_capped(cfile, "c", max_bytes=len(cert_bytes) - 1), "FILE_TOO_LARGE", "max_bytes - 1")
            hlink = root / "hlink.json"
            os.link(cfile, hlink)
            try:
                _expect_err(lambda: audit.write_regular_bytes_safe(hlink, b"tamper", "hlink"), "HARDLINK_FORBIDDEN", "hardlink write")
                _check(cfile.read_bytes() == cert_bytes, "hardlink refusal truncated target")
            finally:
                hlink.unlink()

            # Concrete Path, NUL, surrogate, root/leaf & dir_fd ancestor guards
            _expect_err(lambda: audit.read_regular_bytes_capped(_EvilPath(cfile), "evil"), "INVALID_PATH_TYPE", "EvilPath read")
            _expect_err(lambda: audit.read_regular_bytes_capped(str(cfile), "str"), "INVALID_PATH_TYPE", "str read")
            _expect_err(lambda: audit.read_regular_bytes_capped(Path("a\x00b.json"), "nul"), "NUL_BYTE_FORBIDDEN", "NUL Path read")
            _expect_err(lambda: audit.read_regular_bytes_capped(Path("bad_\ud800.json"), "surr_r"), "INVALID_UTF8_SURROGATE", "surrogate Path read")
            _expect_err(lambda: audit.write_regular_bytes_safe(_EvilPath(cfile), cert_bytes, "evil"), "INVALID_PATH_TYPE", "EvilPath write")
            _expect_err(lambda: audit.write_regular_bytes_safe(Path("bad_\ud800.json"), cert_bytes, "surr_w"), "INVALID_UTF8_SURROGATE", "surrogate Path write")
            _expect_err(lambda: audit.read_regular_bytes_capped(Path("/"), "root"), "NOT_A_REGULAR_FILE", "root path")
            _expect_err(lambda: audit.read_regular_bytes_capped(Path("/nonexistent_s22b_top_leaf"), "top_missing"), "FILE_READ_ERROR", "single-part missing")
            _expect_err(lambda: audit.read_regular_bytes_capped(root / "real_sub" / "..", "dotdot_leaf"), "NOT_A_REGULAR_FILE", "dotdot leaf")
            _expect_err(lambda: audit.read_regular_bytes_capped(root / "no_such_dir" / "missing.json", "no_dir"), "FILE_READ_ERROR", "missing ancestor dir")
            _check(not (root / "no_such_dir").exists(), "read mode must never create missing ancestor dir")
            _expect_err(lambda: audit.read_regular_bytes_capped(cfile / "under_file.json", "non_dir_anc"), "FILE_READ_ERROR", "non-dir ancestor")

            # Missing, directory, FIFO (read & write non-blocking!), chmod 000, ro parent
            _expect_err(lambda: audit.read_regular_bytes_capped(root / "missing.json", "missing"), "FILE_READ_ERROR", "missing")
            adir = root / "adir"; adir.mkdir()
            _expect_err(lambda: audit.read_regular_bytes_capped(adir, "adir"), "NOT_A_REGULAR_FILE", "dir read")
            _expect_err(lambda: audit.write_regular_bytes_safe(adir, cert_bytes, "adir"), "NOT_A_REGULAR_FILE", "dir write")
            if hasattr(os, "mkfifo"):
                fifo = root / "pipe.json"; os.mkfifo(fifo)
                _expect_err(lambda: audit.read_regular_bytes_capped(fifo, "fifo"), "NOT_A_REGULAR_FILE", "FIFO read")
                _expect_err(lambda: audit.write_regular_bytes_safe(fifo, cert_bytes, "fifo"), "NOT_A_REGULAR_FILE", "FIFO write")

            no_perm = root / "noperm.json"; no_perm.write_bytes(cert_bytes)
            os.chmod(no_perm, 0o000)
            try:
                if os.geteuid() != 0:
                    _expect_err(lambda: audit.read_regular_bytes_capped(no_perm, "noperm"), "FILE_READ_ERROR", "chmod 000")
            finally:
                os.chmod(no_perm, 0o600)

            ro_dir = root / "ro_dir"; ro_dir.mkdir()
            os.chmod(ro_dir, 0o500)
            try:
                if os.geteuid() != 0:
                    _expect_err(lambda: audit.write_regular_bytes_safe(ro_dir / "x.json", cert_bytes, "ro"), "FILE_WRITE_ERROR", "ro parent write")
                    _expect_err(lambda: audit.write_regular_bytes_safe(ro_dir / "newdir" / "x.json", cert_bytes, "ro_mk"), "FILE_WRITE_ERROR", "ro parent mkdir")
            finally:
                os.chmod(ro_dir, 0o700)

            # Symlink target (read & write), deep symlink ancestor, ..-collapsed symlink, relative-PWD symlink & deleted CWD
            sym = root / "sym.json"; os.symlink(cfile, sym)
            _expect_err(lambda: audit.verify_certificate_file(sym), "SYMLINK_FORBIDDEN", "symlink file read")
            _expect_err(lambda: audit.write_regular_bytes_safe(sym, cert_bytes, "sym_w"), "SYMLINK_FORBIDDEN", "symlink file write")
            real_sub = root / "real_sub" / "nested"; real_sub.mkdir(parents=True)
            (real_sub / "c.json").write_bytes(cert_bytes)
            sym_dir = root / "sym_dir"; os.symlink(root / "real_sub", sym_dir)
            _expect_err(lambda: audit.verify_certificate_file(sym_dir / "nested" / "c.json"), "SYMLINK_FORBIDDEN", "deep symlink")
            _expect_err(lambda: audit.verify_certificate_file(sym_dir / ".." / "real_sub" / "nested" / "c.json"), "SYMLINK_FORBIDDEN", "dotdot symlink")

            orig_cwd = os.getcwd()
            orig_pwd = os.environ.get("PWD")
            try:
                os.chdir(real_sub)
                os.environ["PWD"] = str(sym_dir / "nested")
                _expect_err(lambda: audit.verify_certificate_file(Path("c.json")), "SYMLINK_ANCESTOR_FORBIDDEN", "symlink PWD")
                os.environ["PWD"] = "relative/pwd"
                _check(audit.read_regular_bytes_capped(Path(".") / "c.json", "c") == cert_bytes, "relative PWD failed")
                os.environ["PWD"] = str(real_sub)
                _check(audit.read_regular_bytes_capped(Path("c.json"), "c") == cert_bytes, "real PWD failed")
                os.environ.pop("PWD", None)
                _check(audit.read_regular_bytes_capped(Path("c.json"), "c") == cert_bytes, "unset PWD failed")

                # Deleted-CWD refusal (CWD_UNAVAILABLE, rc=2)
                gone_dir = root / "gone_cwd"; gone_dir.mkdir()
                os.chdir(gone_dir)
                os.rmdir(gone_dir)
                _expect_err(lambda: audit.read_regular_bytes_capped(Path("rel.json"), "rel_r"), "CWD_UNAVAILABLE", "deleted CWD read")
                _expect_err(lambda: audit.write_regular_bytes_safe(Path("rel.json"), cert_bytes, "rel_w"), "CWD_UNAVAILABLE", "deleted CWD write")
                for gone_argv in (["--check", "rel.json"], ["--write", "rel.json"]):
                    gbuf = io.StringIO()
                    with redirect_stderr(gbuf):
                        rc_g = audit.main(gone_argv)
                    _check(rc_g == 2 and "CWD_UNAVAILABLE" in gbuf.getvalue(), f"deleted CWD CLI {gone_argv}: rc={rc_g} err={gbuf.getvalue()!r}")
            finally:
                os.chdir(orig_cwd)
                if orig_pwd is None:
                    os.environ.pop("PWD", None)
                else:
                    os.environ["PWD"] = orig_pwd

            # CRLF, invalid UTF-8, and pretty-printed canonical mismatch
            bad_utf8 = root / "bad_utf8.json"; bad_utf8.write_bytes(b"\xff\xfe")
            _expect_err(lambda: audit.verify_certificate_file(bad_utf8), "INVALID_UTF8", "bad utf8")
            crlf = root / "crlf.json"; crlf.write_bytes(cert_bytes.replace(b"\n", b"\r\n"))
            _expect_err(lambda: audit.verify_certificate_file(crlf), "CRLF_FORBIDDEN", "CRLF")
            pretty = root / "pretty.json"; pretty.write_text(json.dumps(cert, indent=2, sort_keys=True) + "\n", encoding="utf-8")
            _expect_err(lambda: audit.verify_certificate_file(pretty), "CERTIFICATE_BYTE_MISMATCH", "pretty JSON")

            # CLI main() positive + negative + strict argv & S22B-BUG-02 flag-path guards
            out_path = root / "written.json"
            _check(audit.main(["--write", str(out_path)]) == 0 and out_path.read_bytes() == cert_bytes, "CLI --write failed")
            buf = io.StringIO()
            with redirect_stdout(buf):
                rc_chk = audit.main(["--check", str(out_path)])
            _check(rc_chk == 0 and json.loads(buf.getvalue())["valid"] is True, "CLI --check failed")

            for bad_argv, exp_code in (
                (("--standalone", "--json"), "INVALID_ARGV"),
                ("--check", "INVALID_ARGV"),
                ([123], "INVALID_ARGV"),
                ([_StrSub("--check"), str(out_path)], "INVALID_ARGV"),
                (["--standalone\x00", "--json"], "NUL_BYTE_FORBIDDEN"),
                (["--check", "\ud800"], "INVALID_UTF8_SURROGATE"),
                (["--write", ""], "INVALID_PATH_ARG"),
                (["--check", ""], "INVALID_PATH_ARG"),
                (["--write", "--json"], "INVALID_PATH_ARG"),
                (["--check", "--json"], "INVALID_PATH_ARG"),
                (["--check", "--help"], "INVALID_PATH_ARG"),
                (["--write", "-"], "INVALID_PATH_ARG"),
                (["--write=--json"], "INVALID_CLI_ARGS"),
                (["--check=--json"], "INVALID_CLI_ARGS"),
                (["--write"], "INVALID_CLI_ARGS"),
                (["--check"], "INVALID_CLI_ARGS"),
                (["--unknown", "x"], "INVALID_CLI_ARGS"),
            ):
                ebuf = io.StringIO()
                with redirect_stderr(ebuf):
                    rc_b = audit.main(bad_argv)
                _check(
                    rc_b == 2 and exp_code in ebuf.getvalue(),
                    f"bad argv {bad_argv!r}: expected rc=2/{exp_code}, got rc={rc_b} err={ebuf.getvalue()!r}",
                )
            _check(not (Path(orig_cwd) / "--json").exists(), "S22B-BUG-02: --write --json created ./--json!")

            # Live subprocess --standalone --json & default zero-arg parity + symlinked PWD CLI refusal
            p_def = subprocess.run([sys.executable, "-I", "-O", "-B", str(ROOT / "odd_perfect_cyclotomic_audit.py")], capture_output=True, timeout=60)
            _check(p_def.returncode == 0 and p_def.stdout == cert_bytes, "subprocess default zero-arg mismatch")
            p_std = subprocess.run([sys.executable, "-I", "-O", "-B", str(ROOT / "odd_perfect_cyclotomic_audit.py"), "--standalone", "--json"], capture_output=True, timeout=60)
            _check(p_std.returncode == 0 and p_std.stdout == cert_bytes, "subprocess --standalone mismatch")
            p_pwd = subprocess.run(
                [sys.executable, "-I", "-O", "-B", str(ROOT / "odd_perfect_cyclotomic_audit.py"), "--check", "c.json"],
                cwd=str(real_sub),
                env={**os.environ, "PWD": str(sym_dir / "nested")},
                capture_output=True,
                text=True,
                timeout=60,
            )
            _check(p_pwd.returncode == 2 and "SYMLINK_ANCESTOR_FORBIDDEN" in p_pwd.stderr, f"subprocess symlink PWD rc={p_pwd.returncode} err={p_pwd.stderr!r}")


if __name__ == "__main__":
    unittest.main()
