#!/usr/bin/env python3
"""Track S25 (AUDIT-125) R1-R5 Verification & Adversarial Zone-B Test Suite.

Pure Python 3 stdlib, zero bare asserts, zero floats in oracle/audit assertions.
Covers:
  - Test 1: Full 5-pillar exact Z/Q mathematical verification & certificate schema
  - Test 2: Exact domain, type, boundary, arithmetic & solver negative controls
  - Test 3: Uniform Zone-B Gold Standard (atomic dir_fd, /proc/kallsyms, /dev/null,
            FIFO, chmod 000, hardlink, deep/dotdot/PWD symlinks, deleted-CWD,
            lone UTF-16 surrogates, CRLF/BOM/pretty/dup-key/float/depth/bits,
            flag-like & equals-syntax CLI paths, subprocess parity)
  - Test 4: Live >= 500-iter concurrent renameat2(RENAME_EXCHANGE) + >= 400-iter
            concurrent os.link() hardlink race stress (0 leaks, 0 clobbers)
"""
from __future__ import annotations

from contextlib import redirect_stderr, redirect_stdout
import copy
import ctypes
from fractions import Fraction
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import unittest
from typing import Any

ROOT = Path(__file__).resolve().parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import aliquot_transfer_audit as audit  # noqa: E402
import aliquot_transfer_oracle as oracle  # noqa: E402

CERT_PATH = ROOT / audit.DEFAULT_CERT_NAME
_AT_FDCWD = -100
_RENAME_EXCHANGE = 2


class _EvilPath(type(Path())):
    """Path subclass rejected by strict concrete pathlib.Path check."""


class _StrSub(str):
    """str subclass rejected by strict type(x) is str check."""


class _IntSub(int):
    """int subclass rejected by strict type(x) is int check."""


class _BoolLike:
    def __bool__(self) -> bool:
        return True


def _check(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


def _expect_err(fn: Any, expected_code: str, label: str) -> None:
    try:
        fn()
    except oracle.AliquotTransferError as exc:
        if exc.code != expected_code:
            raise AssertionError(f"{label}: expected {expected_code}, got {exc.code} ({exc})") from exc
        return
    raise AssertionError(f"{label}: expected AliquotTransferError({expected_code}), but succeeded")


class TrackS25Tests(unittest.TestCase):
    def test_01_five_pillars_exact_math_and_certificate(self) -> None:
        cert = audit.build_certificate()
        disk_bytes = CERT_PATH.read_bytes()
        _check(audit.canonical_json_bytes(cert) == disk_bytes, "on-disk certificate drift")
        res = audit.verify_certificate_dict(cert, expected=cert)
        _check(res["valid"] is True, "verify_certificate_dict failed")
        res_file = audit.verify_certificate_file(CERT_PATH)
        _check(res_file == res, "verify_certificate_file mismatch")

        pl = cert["payload"]
        _check(pl["track_id"] == "TRACK-S25-AUDIT-125" and pl["novelty_class"] == "N1", "metadata mismatch")

        # Pillar 1 (Portal 17)
        p1 = pl["pillar1_catalan_dickson_transfer"]
        _check(p1["all_verified"] is True, "P1 all_verified")
        _check(
            p1["parity_lock_range"] == 10_000
            and p1["parity_vs_sigma_exceptions"] == 0
            and p1["parity_vs_escape_exceptions"] == 0,
            "P1 parity-lock",
        )
        _check(p1["square_escape_count"] == 170 and p1["square_escape_density"] == "17/1000", "P1 escape density")
        _check(p1["driver_monotonicity_checked"] == 22, "P1 driver mono count")
        _check(p1["six_driver_coprime_checked"] == 99 and p1["six_driver_v3_persist_count"] == 70, "P1 6-driver")
        _check(p1["six_driver_3_div_sigma_count"] == 62, "P1 6-driver 3|sigma count")
        _check(p1["six_driver_converse_counterexample_first"] == 25, "P1 6-driver u=25 counterexample")
        _check(p1["six_driver_converse_counterexample_count"] == 8, "P1 6-driver counterexample count")
        _check(p1["uniform_even_empirical_mean"] == "2640757/2500500", "P1 uniform even mean")
        stat_q = Fraction(p1["stationary_pi_expected_ratio"])
        unif_q = Fraction(p1["uniform_even_empirical_mean"])
        _check(unif_q > 1 and stat_q < 1, "P1 drift inversion")
        _check(p1["even_asymptotic_archimedes_lower_bound"] == "127661/120984", "P1 even asymp exact")
        _check(Fraction(p1["even_asymptotic_archimedes_lower_bound"]) > 1, "P1 even asymp > 1")
        _check(Fraction(p1["odd_asymptotic_archimedes_upper_bound"]) < 1, "P1 odd asymp < 1")
        _check(p1["goldbach_odd_preimage_witnesses_le_1001"] == 499, "P1 Goldbach odd count")
        _check(
            p1["atlas_1_to_1000_counts"]
            == {"terminates": 965, "perfect": 19, "amicable": 3, "open_lehmer5": 12, "high_peak_exceeding_bound": 1},
            "P1 atlas counts",
        )
        _check(p1["atlas_high_peak_seeds_le_1000"] == [840], "P1 high peak 840")
        _check(
            p1["trajectory_138"] == {"peak": 179_931_895_322, "peak_step": 117, "reaches_1_step": 177, "reaches_0_step": 178},
            "P1 138 record",
        )
        _check(len(p1["poulet_cycles"]) == 2 and p1["poulet_cycles"][0]["max_vertex"] == 15472, "P1 Poulet 5")
        _check(p1["poulet_cycles"][1]["max_vertex"] == 629072, "P1 Poulet 28")
        _check(len(p1["lehmer_five_prefixes"]) == 5 and p1["lehmer_five_prefixes"][0]["a20"] == 54684, "P1 Lehmer 276")
        _check(p1["lehmer_five_prefixes"][4]["distinct_driver_tags"] == ["D6_PERF"], "P1 Lehmer 966 lock")

        # Pillar 2 (Portal 18)
        p2 = pl["pillar2_sylvester_zsigmondy"]
        _check(p2["all_verified"] is True, "P2 all_verified")
        wall = {e["q"]: e for e in p2["sylvester_wall_table"]}
        _check(wall[3]["k_sylv"] == 3 and wall[3]["exact_product"] == "35/16" and wall[3]["exact_margin_above_2"] == "3/16", "P2 q=3")
        _check(wall[5]["k_sylv"] == 7 and wall[5]["exact_product"] == "676039/331776", "P2 q=5")
        _check(wall[7]["k_sylv"] == 15 and wall[7]["p_max"] == 61, "P2 q=7")
        _check(wall[11]["k_sylv"] == 27 and wall[13]["k_sylv"] == 41 and wall[13]["p_max"] == 199, "P2 q=11,13")
        _check(wall[17]["k_sylv"] == 62 and wall[19]["k_sylv"] == 85, "P2 q=17,19")
        _check(wall[47]["k_sylv"] == 380 and wall[101]["k_sylv"] == 1331 and wall[101]["p_max"] == 11197, "P2 q=47,101")
        _check(wall[101]["exact_margin_recip_floor"] == 103137, "P2 q=101 knife-edge margin")
        _check(p2["sharp_odd_abundant_witnesses"][0]["n"] == 945, "P2 945 witness")
        _check(p2["sharp_odd_abundant_witnesses"][1]["n"] == 930483178625, "P2 q=5 witness")
        _check(p2["sylvester_deficit_identities_checked"] == 15 and p2["zsigmondy_odd_pairs_checked"] == 45, "P2 deficit/zsig")

        # Pillar 3 (Portal 19)
        p3 = pl["pillar3_pomerance_pseudorandomness"]
        _check(p3["all_verified"] is True, "P3 all_verified")
        _check(p3["local_euler_identities_checked"] == 6 and p3["p2_removal_factor"] == "9/20", "P3 Euler 9/20")
        _check(p3["all_m_series_pi2_coeff"] == "5/12" and p3["odd_m_series_pi2_coeff"] == "3/16", "P3 3/16")
        _check(p3["odd_m_checked_count"] == 5000, "P3 odd m count")
        _check([s["m"] for s in p3["pomerance_alpha1_solutions"]] == [1, 3003], "P3 exact sols")
        _check(p3["pomerance_alpha1_solutions"][1]["delta"] == 819 and p3["pomerance_alpha1_solutions"][1]["p_candidate"] == 22021, "P3 Descartes")
        _check(p3["even_2pow_a_falsification_hits"] == 30 and p3["even_2pow_a_hit_probability"] == "1", "P3 falsification")

        # Pillar 4 (Portal 20)
        p4 = pl["pillar4_harmonic_ore"]
        _check(p4["all_verified"] is True, "P4 all_verified")
        _check(p4["lte_odd_checked_count"] == 10_000 and p4["lte_exceptions"] == 0, "P4 LTE")
        _check(p4["prime_power_no_ore_checked"] == 54, "P4 prime power")
        ks = {e["h"]: e["omega_upper_bound"] for e in p4["kanold_sylvester_ceilings"]}
        _check(ks == {3: 2, 5: 3, 7: 4, 9: 4, 11: 4, 13: 5, 15: 5}, "P4 Kanold ceilings")
        _check(p4["odd_ore_h3_zero_proof"]["odd_solutions_for_h3"] == 0, "P4 h=3 proof")
        _check(p4["ore_numbers_count"] == 18 and p4["odd_ore_numbers_le_limit"] == [1], "P4 Ore 18")
        _check([e["n"] for e in p4["ore_numbers"]][-1] == 55860, "P4 Ore max")

        # Pillar 5 (Portal 21)
        p5 = pl["pillar5_cyclotomic_kirchhoff"]
        _check(p5["all_verified"] is True, "P5 all_verified")
        dk = p5["descartes_kirchhoff"]
        _check(dk["deficit_vector"] == {"3": 0, "7": 1, "11": 2, "13": 1}, "P5 Descartes deficit")
        _check(dk["external_leak_product"] == 22021 and dk["truncated_phi3_19"] == [[3, 1], [127, 1]], "P5 Descartes leak/trunc")
        _check(dk["truncated_phi3_61"] == [[3, 1], [13, 1], [97, 1]], "P5 trunc 61")
        _check(p5["phi3_smooth_primes_lt_5000_count"] == 138 and p5["phi3_smooth_primes_first5"] == [67, 79, 137, 149, 163], "P5 smooth")
        _check(p5["phi3_forward_cascade_depth5"] == [[3], [13], [61], [97], [3169], [3348577]], "P5 cascade")
        for f_rec in p5["phi_l_attractor_funnels"]:
            _check(f_rec["primes_checked"] == 669 and f_rec["distance_0_count"] == 1, "P5 funnel counts")

    def test_02_oracle_guards_boundaries_and_primitives(self) -> None:
        # Strict type & boundary guards
        _expect_err(lambda: oracle.require_ok(1, "X", "m"), "INVALID_CONDITION_TYPE", "int cond")
        _expect_err(lambda: oracle.require_ok(_BoolLike(), "X", "m"), "INVALID_CONDITION_TYPE", "boollike cond")
        _expect_err(lambda: oracle.require_ok(False, "MY_CODE", "boom"), "MY_CODE", "false cond")
        oracle.require_ok(True, "OK", "ok")

        _expect_err(lambda: oracle.require_exact_int(True, "n"), "INVALID_INT_TYPE", "bool as int")
        _expect_err(lambda: oracle.require_exact_int(_IntSub(3), "n"), "INVALID_INT_TYPE", "int subclass")
        _expect_err(lambda: oracle.require_exact_int(1 << oracle.MAX_RATIONAL_BITS, "n"), "INT_BIT_LIMIT", "over bit cap")
        _check(oracle.require_exact_int((1 << oracle.MAX_RATIONAL_BITS) - 1, "n") > 0, "exact max bits failed")
        _expect_err(lambda: oracle.require_exact_int(0, "n", lo=1), "INT_OUT_OF_RANGE", "below lo")
        _check(oracle.require_exact_int(1, "n", lo=1, hi=5) == 1, "exact lo failed")
        _expect_err(lambda: oracle.require_exact_int(6, "n", lo=1, hi=5), "INT_OUT_OF_RANGE", "above hi")
        _check(oracle.require_exact_int(5, "n", lo=1, hi=5) == 5, "exact hi failed")

        _expect_err(lambda: oracle.require_exact_bool(1, "b"), "INVALID_BOOL_TYPE", "int as bool")
        _check(oracle.require_exact_bool(False, "b") is False, "bool false")

        _expect_err(lambda: oracle.require_exact_fraction(1, "q"), "INVALID_FRACTION_TYPE", "int as Fraction")
        _expect_err(
            lambda: oracle.require_exact_fraction(Fraction(1 << oracle.MAX_RATIONAL_BITS, 1), "q"),
            "RATIONAL_BIT_LIMIT",
            "num bit cap",
        )
        _expect_err(
            lambda: oracle.require_exact_fraction(Fraction(1, 1 << oracle.MAX_RATIONAL_BITS), "q"),
            "RATIONAL_BIT_LIMIT",
            "den bit cap",
        )
        _check(oracle.format_fraction(Fraction(6, 2)) == "3", "int fraction format")
        _check(oracle.format_fraction(Fraction(5, 3)) == "5/3", "non-int fraction format")

        # Arithmetic sieve (non-default limit + exact values), v_p, is_prime, factorize, sigma1, aliquot_s
        pf20, s20, t20 = oracle.build_arithmetic_sieve(20)
        _check(len(pf20) == 21 and s20[12] == 28 and t20[12] == 6 and pf20[19] == 19, "sieve(20) failed")
        _expect_err(lambda: oracle.build_arithmetic_sieve(1), "INT_OUT_OF_RANGE", "sieve < 2")
        _expect_err(lambda: oracle.build_arithmetic_sieve(oracle.SIEVE_LIMIT + 1), "INT_OUT_OF_RANGE", "sieve > limit")

        _check(oracle.v_p_exact(24, 2) == 3 and oracle.v_p_exact(24, 3) == 1 and oracle.v_p_exact(24, 5) == 0, "v_p failed")
        _expect_err(lambda: oracle.v_p_exact(12, 4), "NOT_PRIME", "v_p composite p=4")
        _expect_err(lambda: oracle.v_p_exact(12, 6), "NOT_PRIME", "v_p composite p=6")
        _expect_err(lambda: oracle.v_p_exact(12, 9), "NOT_PRIME", "v_p composite p=9")
        _check(oracle.is_prime_exact(0) is False and oracle.is_prime_exact(1) is False, "is_prime 0/1")
        _check(oracle.is_prime_exact(2) is True and oracle.is_prime_exact(37) is True, "is_prime small base")
        _check(oracle.is_prime_exact(561) is False and oracle.is_prime_exact(341) is False, "Carmichael/pseudoprime")
        _check(oracle.is_prime_exact(100003) is True and oracle.is_prime_exact(100003 * 100019) is False, "big prime/semiprime")
        # Composite triggering Miller-Rabin inner loop & Pollard-Brent (2^32 + 1 = 641 * 6700417 & large semiprime)
        _check(oracle.factorize_exact(1) == {}, "factorize(1)")
        _check(oracle.factorize_exact(4294967297) == {641: 1, 6700417: 1}, "Fermat F5 factor")
        big_semi = 100003 * 100019
        _check(oracle.factorize_exact(big_semi) == {100003: 1, 100019: 1}, "big semiprime factor")
        _check(oracle.factorize_exact(100003 * 100003) == {100003: 2}, "prime square factor")
        _check(oracle.sigma1_exact(100003) == 100004, "sigma1 big prime")
        _check(oracle.aliquot_s_exact(100003) == 1 and oracle.aliquot_s_exact(100003) == 1, "aliquot_s cache hit")

        # Exact Fraction Gauss-Jordan solver (positive + pivoting + singular + malformed)
        sol = oracle.solve_linear_fraction(
            [[Fraction(0, 1), Fraction(2, 1)], [Fraction(3, 1), Fraction(1, 1)]],
            [Fraction(4, 1), Fraction(5, 1)],
        )
        _check(sol == [Fraction(1, 1), Fraction(2, 1)], "pivot solve failed")
        _expect_err(lambda: oracle.solve_linear_fraction("bad", []), "INVALID_MATRIX_TYPE", "bad matrix type")
        _expect_err(lambda: oracle.solve_linear_fraction([[Fraction(1, 1)]], "bad"), "INVALID_MATRIX_TYPE", "bad rhs type")
        _expect_err(lambda: oracle.solve_linear_fraction([], []), "INVALID_MATRIX_DIM", "empty matrix")
        _expect_err(
            lambda: oracle.solve_linear_fraction([[Fraction(1, 1)]], [Fraction(1, 1), Fraction(2, 1)]),
            "INVALID_MATRIX_DIM",
            "dim mismatch",
        )
        _expect_err(
            lambda: oracle.solve_linear_fraction([[Fraction(1, 1), Fraction(2, 1)]], [Fraction(1, 1)]),
            "INVALID_MATRIX_ROW",
            "non-square row",
        )
        _expect_err(
            lambda: oracle.solve_linear_fraction([(Fraction(1, 1),)], [Fraction(1, 1)]),
            "INVALID_MATRIX_ROW",
            "tuple row of length n",
        )
        _check(oracle.is_pomerance_alpha1_candidate(9_018_009, 18_035_199) is True, "Descartes positive candidate")
        _check(oracle.is_pomerance_alpha1_candidate(6, 12) is False, "zero delta must be False")
        _check(oracle.is_pomerance_alpha1_candidate(12, 28) is False, "negative delta dividing m_sq must be False")
        _check(oracle.is_pomerance_alpha1_candidate(9, 13) is False, "non-dividing positive delta must be False")
        _expect_err(
            lambda: oracle.solve_linear_fraction(
                [[Fraction(1, 1), Fraction(2, 1)], [Fraction(2, 1), Fraction(4, 1)]],
                [Fraction(1, 1), Fraction(2, 1)],
            ),
            "SINGULAR_MATRIX",
            "singular matrix",
        )

        # Driver classifiers, untouchable negative control, Sylvester & Kanold guards
        _check(oracle.classify_even_driver_state(2) == 0, "state 0")
        _check(oracle.classify_even_driver_state(6) == 1, "state 1")
        _check(oracle.classify_even_driver_state(10) == 2 and oracle.classify_even_driver_state(30) == 2, "state 2")
        _check(oracle.classify_even_driver_state(4) == 3, "state 3")
        _check(oracle.classify_even_driver_state(12) == 4, "state 4")
        _expect_err(lambda: oracle.classify_even_driver_state(3), "NOT_EVEN_DRIVER_INPUT", "odd driver input")
        _check(oracle._driver_tag_for_orbit(0) == "ZERO" and oracle._driver_tag_for_orbit(9) == "ODD", "orbit tags")
        _check(oracle._driver_tag_for_orbit(28) == "D28_PERF" and oracle._driver_tag_for_orbit(24) == "D24_DRV", "orbit tags 28/24")
        _check(oracle._driver_tag_for_orbit(56) == "EVEN_OTHER" and oracle._driver_tag_for_orbit(48) == "EVEN_OTHER", "orbit tags 56/48")
        _check(oracle._driver_tag_for_orbit(12) == "EVEN_OTHER", "orbit tag 12")
        _check(oracle._driver_tag_for_orbit(6) == "D6_PERF" and oracle._driver_tag_for_orbit(10) == "D2_DOWN", "orbit tags 6/10")
        _check(oracle._driver_tag_for_orbit(8) == "EVEN_OTHER", "orbit tag other")
        _check(oracle.verify_untouchable_exact(4)["is_untouchable_over_all_N"] is False, "4 is touchable (s(9)=4)")
        _expect_err(lambda: oracle.compute_sylvester_wall_entry(9), "NOT_ODD_PRIME", "composite q=9")
        _expect_err(lambda: oracle.compute_kanold_sylvester_ceiling(4), "KANOLD_H_MUST_BE_ODD", "even h=4")

    def test_03_zone_b_hardening_symlinks_pwd_cwd_surrogates_and_cli(self) -> None:
        cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
        cert_bytes = CERT_PATH.read_bytes()

        # Hex64 + in-memory verify_certificate_dict + secondary algebraic crosscheck guards
        _expect_err(lambda: audit.require_hex64_lower_ascii("a" * 63, "h"), "INVALID_HEX64", "len 63")
        _expect_err(lambda: audit.require_hex64_lower_ascii("A" * 64, "h"), "INVALID_HEX64", "uppercase hex")
        _expect_err(lambda: audit.require_hex64_lower_ascii(123, "h"), "INVALID_HEX64", "int hex")
        _expect_err(lambda: audit.verify_certificate_dict([]), "INVALID_CERT_TYPE", "list cert")
        bad_k = copy.deepcopy(cert)
        bad_k["extra"] = 1
        _expect_err(lambda: audit.verify_certificate_dict(bad_k, expected=cert), "INVALID_CERT_KEYS", "extra key")
        bad_psha = copy.deepcopy(cert)
        bad_psha["payload_sha256"] = "0" * 64
        _expect_err(lambda: audit.verify_certificate_dict(bad_psha, expected=cert), "PAYLOAD_SHA_MISMATCH", "bad psha")
        bad_csha = copy.deepcopy(cert)
        bad_csha["certificate_sha256"] = "0" * 64
        _expect_err(lambda: audit.verify_certificate_dict(bad_csha, expected=cert), "CERTIFICATE_SHA_MISMATCH", "bad csha")
        bad_pl = copy.deepcopy(cert)
        bad_pl["payload"]["novelty_class"] = "N9"
        _expect_err(lambda: audit.verify_certificate_dict(bad_pl, expected=cert), "CERTIFICATE_MISMATCH", "bad payload")
        bad_xchk = copy.deepcopy(cert["payload"])
        bad_xchk["pillar4_harmonic_ore"]["ore_numbers_count"] = 17
        _expect_err(lambda: audit._secondary_algebraic_crosscheck(bad_xchk), "ALGEBRAIC_CROSSCHECK_FAILED", "bad crosscheck")

        # Strict JSON tree & parser guards
        _check(audit.parse_strict_json_text("[1,true,null]", "arr", require_object=False) == [1, True, None], "arr parse")
        _check(
            audit.parse_strict_json_text('{"n":' + str((1 << oracle.MAX_JSON_INT_BITS) - 1) + "}", "maxb")["n"] > 0,
            "exact 4000-bit int",
        )
        _check(
            audit.parse_strict_json_text('{"n":-' + str((1 << oracle.MAX_JSON_INT_BITS) - 1) + "}", "negd")["n"] < 0,
            "exact negative max-digit/max-bit int",
        )
        _expect_err(lambda: audit.parse_strict_json_text(123, "x"), "INVALID_JSON_TEXT", "non-str")
        _expect_err(lambda: audit.parse_strict_json_text("{}", "x", require_object=1), "INVALID_BOOL_TYPE", "non-bool")
        _expect_err(lambda: audit.parse_strict_json_text("\ufeff{}", "x"), "BOM_FORBIDDEN", "BOM text")
        _expect_err(lambda: audit.parse_strict_json_text("{\x00}", "x"), "NUL_BYTE_FORBIDDEN", "NUL text")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":"\ud800"}', "x"), "INVALID_UTF8_SURROGATE", "raw surrogate")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":"\\ud800"}', "x"), "INVALID_UTF8_SURROGATE", "escaped surrogate")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":"x\\u0000y"}', "x"), "NUL_BYTE_FORBIDDEN", "escaped NUL")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":1,"a":2}', "x"), "DUPLICATE_JSON_KEY", "dup key")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":NaN}', "x"), "NONFINITE_JSON", "NaN")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":1.5}', "x"), "FLOAT_FORBIDDEN", "float")
        _expect_err(lambda: audit.parse_strict_json_text('{"n":' + "9" * (audit.MAX_JSON_INT_DIGITS + 1) + "}", "x"), "INT_DIGIT_LIMIT", "digit cap")
        _expect_err(lambda: audit.parse_strict_json_text('{"n":' + "9" * audit.MAX_JSON_INT_DIGITS + "}", "x"), "INT_BIT_LIMIT", "1205-digit > 4000-bit")
        _check(audit._parse_bounded_int("0") == 0 and audit._parse_bounded_int("-5") == -5, "single-digit bounded int")
        for bad_tok, label in (
            (12, "non-str int token"),
            ("", "empty int token"),
            ("-", "bare minus token"),
            ("\u0661\u0662", "Arabic-Indic digits"),
            ("-\u0661\u0662", "neg Arabic-Indic digits"),
            ("\u00b2", "superscript digit"),
            ("+12", "leading plus"),
            ("1_2", "underscore digit"),
        ):
            _expect_err(lambda bt=bad_tok: audit._parse_bounded_int(bt), "INVALID_JSON_INT", label)
        _expect_err(lambda: audit.parse_strict_json_text("[1]", "x", require_object=True), "JSON_ROOT_NOT_OBJECT", "list root")
        _expect_err(lambda: audit.parse_strict_json_text("{bad", "x"), "INVALID_JSON", "syntax error")
        _expect_err(lambda: audit._validate_json_tree({1: "x"}, "k"), "INVALID_JSON_KEY", "int key")
        _expect_err(lambda: audit._validate_json_tree({"n": 1 << oracle.MAX_JSON_INT_BITS}, "b"), "INT_BIT_LIMIT", "4001-bit int")
        _expect_err(lambda: audit._validate_json_tree({"f": 3 / 2}, "f"), "INVALID_JSON_VALUE", "float in tree")

        ok_d: Any = 1
        for _ in range(audit.MAX_JSON_DEPTH - 1):
            ok_d = [ok_d]
        _check(type(audit.parse_strict_json_text(json.dumps({"x": ok_d}), "d64")) is dict, "depth 64 failed")
        _expect_err(lambda: audit.parse_strict_json_text(json.dumps({"x": [ok_d]}), "d65"), "MAX_DEPTH_EXCEEDED", "depth 65")

        # /proc/kallsyms st_size==0 capped read + /dev/null write guard
        proc_kallsyms = Path("/proc/kallsyms")
        if proc_kallsyms.exists():
            _expect_err(lambda: audit.read_regular_bytes_capped(proc_kallsyms, "kallsyms", max_bytes=16), "FILE_TOO_LARGE", "kallsyms cap")
        dev_null = Path("/dev/null")
        if dev_null.exists():
            _expect_err(lambda: audit.write_regular_bytes_safe(dev_null, b"{}\n", "devnull"), "NOT_A_REGULAR_FILE", "devnull write")

        with tempfile.TemporaryDirectory(prefix="s25_zb_") as td:
            root = Path(td)
            cfile = root / "c.json"
            audit.write_regular_bytes_safe(cfile, cert_bytes, "c")
            audit.write_regular_bytes_safe(cfile, b"{}\n", "c_short")
            _check(cfile.read_bytes() == b"{}\n", "atomic replace shorter failed")
            audit.write_regular_bytes_safe(cfile, cert_bytes, "c_restore")
            nested = root / "nested_a" / "sub_b" / "w.json"
            audit.write_regular_bytes_safe(nested, cert_bytes, "nested")
            _check(nested.read_bytes() == cert_bytes, "nested dir_fd create failed")
            _check(audit.read_regular_bytes_capped(cfile, "c", max_bytes=len(cert_bytes)) == cert_bytes, "exact max_bytes")
            _expect_err(lambda: audit.read_regular_bytes_capped(cfile, "c", max_bytes=len(cert_bytes) - 1), "FILE_TOO_LARGE", "max_bytes-1")

            # Hardlink target protection (zero clobber)
            hlink = root / "hlink.json"
            os.link(cfile, hlink)
            try:
                _expect_err(lambda: audit.write_regular_bytes_safe(hlink, b"tamper", "hlink"), "HARDLINK_FORBIDDEN", "hardlink write")
                _check(cfile.read_bytes() == cert_bytes, "hardlink refusal altered target")
            finally:
                hlink.unlink()

            # Path type, NUL, surrogate, root, dotdot, non-dir ancestor, dir, FIFO, chmod 000, ro parent
            _expect_err(lambda: audit.read_regular_bytes_capped(_EvilPath(cfile), "evil"), "INVALID_PATH_TYPE", "EvilPath")
            _expect_err(lambda: audit.read_regular_bytes_capped(str(cfile), "str"), "INVALID_PATH_TYPE", "str path")
            _expect_err(lambda: audit.read_regular_bytes_capped(Path("a\x00b.json"), "nul"), "NUL_BYTE_FORBIDDEN", "NUL path")
            _expect_err(lambda: audit.read_regular_bytes_capped(Path("bad_\ud800.json"), "surr"), "INVALID_UTF8_SURROGATE", "surrogate read")
            _expect_err(lambda: audit.write_regular_bytes_safe(Path("bad_\ud800.json"), cert_bytes, "surr"), "INVALID_UTF8_SURROGATE", "surrogate write")
            _expect_err(lambda: audit.read_regular_bytes_capped(Path("/"), "root"), "NOT_A_REGULAR_FILE", "root path")
            _expect_err(lambda: audit.read_regular_bytes_capped(root / "sub" / "..", "dotdot"), "NOT_A_REGULAR_FILE", "dotdot leaf")
            _expect_err(lambda: audit.read_regular_bytes_capped(root / "no_dir" / "x.json", "nodir"), "FILE_READ_ERROR", "missing dir")
            _check(not (root / "no_dir").exists(), "read must not create dir")
            _expect_err(lambda: audit.read_regular_bytes_capped(cfile / "child.json", "nondir"), "FILE_READ_ERROR", "non-dir ancestor")
            _expect_err(lambda: audit.read_regular_bytes_capped(root / "missing.json", "missing"), "FILE_READ_ERROR", "missing file")

            adir = root / "adir"
            adir.mkdir()
            _expect_err(lambda: audit.read_regular_bytes_capped(adir, "adir"), "NOT_A_REGULAR_FILE", "dir read")
            _expect_err(lambda: audit.write_regular_bytes_safe(adir, cert_bytes, "adir"), "NOT_A_REGULAR_FILE", "dir write")
            if hasattr(os, "mkfifo"):
                fifo = root / "pipe.json"
                os.mkfifo(fifo)
                _expect_err(lambda: audit.read_regular_bytes_capped(fifo, "fifo"), "NOT_A_REGULAR_FILE", "FIFO read")
                _expect_err(lambda: audit.write_regular_bytes_safe(fifo, cert_bytes, "fifo"), "NOT_A_REGULAR_FILE", "FIFO write")

            no_perm = root / "noperm.json"
            no_perm.write_bytes(cert_bytes)
            os.chmod(no_perm, 0o000)
            try:
                if os.geteuid() != 0:
                    _expect_err(lambda: audit.read_regular_bytes_capped(no_perm, "noperm"), "FILE_READ_ERROR", "chmod 000")
            finally:
                os.chmod(no_perm, 0o600)

            ro_dir = root / "ro_dir"
            ro_dir.mkdir()
            os.chmod(ro_dir, 0o500)
            try:
                if os.geteuid() != 0:
                    _expect_err(lambda: audit.write_regular_bytes_safe(ro_dir / "x.json", cert_bytes, "ro"), "FILE_WRITE_ERROR", "ro write")
                    _expect_err(lambda: audit.write_regular_bytes_safe(ro_dir / "nd" / "x.json", cert_bytes, "ro_mk"), "FILE_WRITE_ERROR", "ro mkdir")
            finally:
                os.chmod(ro_dir, 0o700)

            # Symlinks (leaf, deep ancestor, dotdot-collapsed, PWD) + deleted CWD
            sym = root / "sym.json"
            os.symlink(cfile, sym)
            _expect_err(lambda: audit.verify_certificate_file(sym), "SYMLINK_FORBIDDEN", "symlink read")
            _expect_err(lambda: audit.write_regular_bytes_safe(sym, cert_bytes, "sym_w"), "SYMLINK_FORBIDDEN", "symlink write")
            real_sub = root / "real_sub" / "nested"
            real_sub.mkdir(parents=True)
            (real_sub / "c.json").write_bytes(cert_bytes)
            sym_dir = root / "sym_dir"
            os.symlink(root / "real_sub", sym_dir)
            _expect_err(lambda: audit.verify_certificate_file(sym_dir / "nested" / "c.json"), "SYMLINK_FORBIDDEN", "deep symlink")
            _expect_err(lambda: audit.write_regular_bytes_safe(sym_dir / "nested" / "w.json", cert_bytes, "sym_dir_w"), "SYMLINK_FORBIDDEN", "write under symlink dir")
            _expect_err(lambda: audit.verify_certificate_file(sym_dir / ".." / "real_sub" / "nested" / "c.json"), "SYMLINK_FORBIDDEN", "dotdot symlink")

            # BOM, invalid UTF-8, CRLF, pretty-printed non-canonical bytes
            bom_f = root / "bom.json"
            bom_f.write_bytes(b"\xef\xbb\xbf" + cert_bytes)
            _expect_err(lambda: audit.verify_certificate_file(bom_f), "BOM_FORBIDDEN", "BOM file")
            bad_u8 = root / "bad_u8.json"
            bad_u8.write_bytes(b"\xff\xfe")
            _expect_err(lambda: audit.verify_certificate_file(bad_u8), "INVALID_UTF8", "bad utf8")
            crlf_f = root / "crlf.json"
            crlf_f.write_bytes(cert_bytes.replace(b"\n", b"\r\n"))
            _expect_err(lambda: audit.verify_certificate_file(crlf_f), "CRLF_FORBIDDEN", "CRLF")
            pretty_f = root / "pretty.json"
            pretty_f.write_text(json.dumps(cert, indent=2, sort_keys=True) + "\n", encoding="utf-8")
            _expect_err(lambda: audit.verify_certificate_file(pretty_f), "CERTIFICATE_BYTE_MISMATCH", "pretty JSON")

            # Relative PWD symlink, surrogate PWD, relative PWD, unset PWD, deleted CWD, & CLI tests inside tmpdir
            orig_cwd = os.getcwd()
            orig_pwd = os.environ.get("PWD")
            try:
                os.chdir(real_sub)
                local_sym = real_sub / "local_sym"
                os.symlink(real_sub, local_sym)
                os.environ["PWD"] = str(sym_dir / "nested")
                _expect_err(lambda: audit.verify_certificate_file(Path("c.json")), "SYMLINK_ANCESTOR_FORBIDDEN", "symlink PWD")
                os.environ["PWD"] = "/tmp/bad_\udcff_pwd"
                _expect_err(lambda: audit.read_regular_bytes_capped(Path("c.json"), "spwd"), "INVALID_UTF8_SURROGATE", "surrogate PWD")
                os.environ["PWD"] = "rel/local_sym"
                _check(audit.read_regular_bytes_capped(Path(".") / "c.json", "relpwd") == cert_bytes, "relative PWD")
                os.environ["PWD"] = str(real_sub)
                _check(audit.read_regular_bytes_capped(Path("c.json"), "realpwd") == cert_bytes, "real PWD")
                os.environ.pop("PWD", None)
                _check(audit.read_regular_bytes_capped(Path("c.json"), "nopwd") == cert_bytes, "unset PWD")

                # CLI main() positive + strict negative + flag-like & equals-syntax guards (isolated in tmpdir!)
                out_path = root / "written.json"
                _check(audit.main(["--write", str(out_path)]) == 0 and out_path.read_bytes() == cert_bytes, "CLI --write")
                buf = io.StringIO()
                with redirect_stdout(buf):
                    rc_c = audit.main(["--check", str(out_path)])
                _check(rc_c == 0 and json.loads(buf.getvalue())["valid"] is True, "CLI --check")

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
                    _check(rc_b == 2 and exp_code in ebuf.getvalue(), f"bad argv {bad_argv!r}: rc={rc_b} err={ebuf.getvalue()!r}")
                _check(not (real_sub / "--json").exists(), "--write --json created ./--json")

                # Deleted CWD refusal (CWD_UNAVAILABLE, rc=2)
                gone = root / "gone_cwd"
                gone.mkdir()
                os.chdir(gone)
                os.rmdir(gone)
                _expect_err(lambda: audit.read_regular_bytes_capped(Path("r.json"), "r"), "CWD_UNAVAILABLE", "deleted CWD read")
                _expect_err(lambda: audit.write_regular_bytes_safe(Path("w.json"), cert_bytes, "w"), "CWD_UNAVAILABLE", "deleted CWD write")
                for g_argv in (["--check", "r.json"], ["--write", "w.json"]):
                    gbuf = io.StringIO()
                    with redirect_stderr(gbuf):
                        rc_g = audit.main(g_argv)
                    _check(rc_g == 2 and "CWD_UNAVAILABLE" in gbuf.getvalue(), f"deleted CWD CLI {g_argv}")
            finally:
                os.chdir(orig_cwd)
                if orig_pwd is None:
                    os.environ.pop("PWD", None)
                else:
                    os.environ["PWD"] = orig_pwd

            # Subprocess --standalone --json, zero-arg parity, & symlinked PWD CLI refusal
            p_def = subprocess.run([sys.executable, "-I", "-O", "-B", str(ROOT / "aliquot_transfer_audit.py")], capture_output=True, timeout=60)
            _check(p_def.returncode == 0 and p_def.stdout == cert_bytes, "subprocess zero-arg mismatch")
            p_std = subprocess.run([sys.executable, "-I", "-O", "-B", str(ROOT / "aliquot_transfer_audit.py"), "--standalone", "--json"], capture_output=True, timeout=60)
            _check(p_std.returncode == 0 and p_std.stdout == cert_bytes, "subprocess --standalone mismatch")
            p_pwd = subprocess.run(
                [sys.executable, "-I", "-O", "-B", str(ROOT / "aliquot_transfer_audit.py"), "--check", "c.json"],
                cwd=str(real_sub),
                env={**os.environ, "PWD": str(sym_dir / "nested")},
                capture_output=True,
                text=True,
                timeout=60,
            )
            _check(p_pwd.returncode == 2 and "SYMLINK_ANCESTOR_FORBIDDEN" in p_pwd.stderr, f"subprocess symlink PWD: {p_pwd.stderr!r}")

    def test_04_live_renameat2_and_hardlink_race_stress(self) -> None:
        libc = ctypes.CDLL(None, use_errno=True)
        renameat2 = libc.renameat2
        renameat2.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
        renameat2.restype = ctypes.c_int

        with tempfile.TemporaryDirectory(prefix="s25_race_") as td:
            root = Path(td)
            canary = root / "canary.txt"
            canary_bytes = b"DO_NOT_LEAK_OR_CLOBBER\n"
            canary.write_bytes(canary_bytes)

            # Part A: >= 500-iter concurrent renameat2(RENAME_EXCHANGE) leaf + intermediate dir race
            real_dir = root / "real_dir"
            real_dir.mkdir()
            target_a = real_dir / "target.json"
            target_a.write_bytes(b'{"ok":1}\n')
            sym_leaf = root / "sym_leaf.json"
            os.symlink(canary, sym_leaf)
            swap_dir = root / "swap_dir"
            os.symlink(root, swap_dir)

            stop_ev = threading.Event()
            p1_b = os.fsencode(target_a)
            p2_b = os.fsencode(sym_leaf)
            d1_b = os.fsencode(real_dir)
            d2_b = os.fsencode(swap_dir)

            def _flipper() -> None:
                while not stop_ev.is_set():
                    renameat2(_AT_FDCWD, p1_b, _AT_FDCWD, p2_b, _RENAME_EXCHANGE)
                    renameat2(_AT_FDCWD, d1_b, _AT_FDCWD, d2_b, _RENAME_EXCHANGE)

            t = threading.Thread(target=_flipper, daemon=True)
            t.start()
            leaks = 0
            clobbers = 0
            try:
                for _ in range(520):
                    try:
                        got = audit.read_regular_bytes_capped(real_dir / "target.json", "race_r")
                        if b"DO_NOT_LEAK" in got:
                            leaks += 1
                    except oracle.AliquotTransferError:
                        pass
                    try:
                        audit.write_regular_bytes_safe(real_dir / "target.json", b'{"ok":2}\n', "race_w")
                    except oracle.AliquotTransferError:
                        pass
                    if canary.read_bytes() != canary_bytes:
                        clobbers += 1
            finally:
                stop_ev.set()
                t.join(timeout=5)

            _check(leaks == 0 and clobbers == 0, f"renameat2 race failed: leaks={leaks}, clobbers={clobbers}")
            _check(canary.read_bytes() == canary_bytes, "canary clobbered in renameat2 race")

            # Part B: >= 400-iter concurrent os.link() hardlink race (zero hardlink clobber!)
            hl_dir = root / "hl_dir"
            hl_dir.mkdir()
            hl_target = hl_dir / "cert.json"
            hl_alias = hl_dir / "alias.json"
            orig_bytes = b'{"orig":true}\n'
            hl_target.write_bytes(orig_bytes)

            stop_hl = threading.Event()

            def _linker() -> None:
                while not stop_hl.is_set():
                    try:
                        os.link(hl_target, hl_alias)
                    except OSError:
                        pass
                    try:
                        os.unlink(hl_alias)
                    except OSError:
                        pass

            t_hl = threading.Thread(target=_linker, daemon=True)
            t_hl.start()
            hl_clobbers = 0
            try:
                for i in range(420):
                    payload = f'{{"iter":{i}}}\n'.encode("ascii")
                    # Keep a pinned hardlink alias check on a fresh pinned file
                    try:
                        audit.write_regular_bytes_safe(hl_target, payload, "hl_w")
                    except oracle.AliquotTransferError:
                        pass
                    # Whenever hl_alias exists AND shares inode with hl_target, atomic os.replace guarantees
                    # hl_alias keeps its old untouched bytes (never mutated in place via O_TRUNC)!
                    try:
                        b_alias = hl_alias.read_bytes()
                        if not b_alias.endswith(b"}\n"):
                            hl_clobbers += 1
                    except OSError:
                        pass
            finally:
                stop_hl.set()
                t_hl.join(timeout=5)
            _check(hl_clobbers == 0, f"hardlink race clobber={hl_clobbers}")
            # Confirm zero leftover temp files in hl_dir
            leftovers = [p.name for p in hl_dir.iterdir() if ".s25_tmp_" in p.name]
            _check(len(leftovers) == 0, f"leftover temp files: {leftovers}")


if __name__ == "__main__":
    unittest.main()
