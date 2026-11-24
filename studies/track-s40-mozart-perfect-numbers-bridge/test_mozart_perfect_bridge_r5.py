#!/usr/bin/env python3
"""Track S40 (Portal 38) R5 Regression, Adversarial Zone-B, Concurrency/TOCTOU & Mutation-Killing Suite.

100% pure Python 3 stdlib, zero bare asserts, zero AST floats, zero float() calls,
zero .isdigit(), zero mathematical RNG.
"""
from __future__ import annotations

import ast
from contextlib import redirect_stderr, redirect_stdout
import copy
import ctypes
from fractions import Fraction
import io
import json
import os
from pathlib import Path
import stat
import sys
import tempfile
import threading
import unittest
from unittest import mock
from typing import Any

_THIS_DIR = Path(__file__).resolve().parent
if str(_THIS_DIR) not in sys.path:
    sys.path.insert(0, str(_THIS_DIR))

import mozart_perfect_bridge_audit as aud  # noqa: E402
import mozart_perfect_bridge_oracle as orc  # noqa: E402


class _EvilPath(type(Path("."))):
    """Adversarial Path subclass rejected by _require_concrete_path."""


class _EvilInt(int):
    """Adversarial int subclass rejected by require_exact_int."""


class _EvilStr(str):
    """Adversarial str subclass rejected by _require_utf8_no_surrogate."""


class _EvilFrac(Fraction):
    """Adversarial Fraction subclass rejected by require_exact_fraction."""


def _resign(base_cert: dict[str, Any], mutator: Any) -> dict[str, Any]:
    c = copy.deepcopy(base_cert)
    mutator(c["payload"])
    c["payload_sha256"] = aud._sha256_canonical(c["payload"])
    outer = {
        "schema_version": c["schema_version"],
        "track_id": c["track_id"],
        "payload_sha256": c["payload_sha256"],
        "payload": c["payload"],
    }
    c["certificate_sha256"] = aud._sha256_canonical(outer)
    return c


class TestStaticHygieneAndOraclePrimitives(unittest.TestCase):
    def test_zero_bare_asserts_floats_isdigit_across_track(self) -> None:
        for fname in (
            "mozart_perfect_bridge_oracle.py",
            "mozart_perfect_bridge_audit.py",
            "test_mozart_perfect_bridge_r5.py",
        ):
            src = (_THIS_DIR / fname).read_text(encoding="utf-8")
            tree = ast.parse(src)
            self.assertEqual([n.lineno for n in ast.walk(tree) if isinstance(n, ast.Assert)], [])
            self.assertEqual([n.lineno for n in ast.walk(tree) if isinstance(n, ast.Constant) and type(n.value) is float], [])
            self.assertEqual(
                [n.lineno for n in ast.walk(tree) if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "float"],
                [],
            )
            self.assertEqual(
                [n.lineno for n in ast.walk(tree) if isinstance(n, ast.Attribute) and n.attr == "isdigit"],
                [],
            )

    def test_oracle_primitives_bit_caps_f2_zpoly_and_number_theory(self) -> None:
        # require_ok & require_exact_bool
        orc.require_ok(True, "OK", "ok")
        with self.assertRaises(orc.MozartPerfectBridgeError) as cm_c:
            orc.require_ok(1, "X", "bad")  # type: ignore[arg-type]
        self.assertEqual(cm_c.exception.code, "INVALID_CONDITION_TYPE")
        with self.assertRaises(orc.MozartPerfectBridgeError) as cm_f:
            orc.require_ok(False, "MY_ERR", "msg")
        self.assertEqual(cm_f.exception.code, "MY_ERR")
        self.assertIs(orc.require_exact_bool(False), False)
        with self.assertRaises(orc.MozartPerfectBridgeError) as cm_b:
            orc.require_exact_bool(0)
        self.assertEqual(cm_b.exception.code, "INVALID_BOOL_TYPE")

        # require_exact_int aligned 3,321-bit cap & exact bounds
        max_i = (1 << orc.MAX_INT_BITS) - 1
        over_i = 1 << orc.MAX_INT_BITS
        self.assertEqual(orc.require_exact_int(max_i), max_i)
        self.assertEqual(orc.require_exact_int(-max_i), -max_i)
        self.assertEqual(orc.require_exact_int(5, lo=5, hi=5), 5)
        for bad_i in (True, _EvilInt(1), "5"):
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm:
                orc.require_exact_int(bad_i)
            self.assertEqual(cm.exception.code, "INVALID_INT_TYPE")
        for big_i in (over_i, -over_i, 10**4300):
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm:
                orc.require_exact_int(big_i)
            self.assertEqual(cm.exception.code, "INT_BIT_LIMIT")
        with self.assertRaises(orc.MozartPerfectBridgeError) as cm_lo:
            orc.require_exact_int(4, lo=5)
        self.assertEqual(cm_lo.exception.code, "INT_OUT_OF_RANGE")
        with self.assertRaises(orc.MozartPerfectBridgeError) as cm_hi:
            orc.require_exact_int(6, hi=5)
        self.assertEqual(cm_hi.exception.code, "INT_OUT_OF_RANGE")
        with self.assertRaises(orc.MozartPerfectBridgeError) as cm_blo:
            orc.require_exact_int(5, lo=True)  # type: ignore[arg-type]
        self.assertEqual(cm_blo.exception.code, "INVALID_BOUND_TYPE")
        with self.assertRaises(orc.MozartPerfectBridgeError) as cm_bhi:
            orc.require_exact_int(5, hi=True)  # type: ignore[arg-type]
        self.assertEqual(cm_bhi.exception.code, "INVALID_BOUND_TYPE")

        # require_exact_fraction, format_rational, format_decimal (aligned 3,321-bit round-trip, zero raw ValueError!)
        max_q_n = Fraction(max_i, 1)
        max_q_d = Fraction(1, max_i)
        self.assertEqual(aud.parse_exact_rational(orc.format_rational(max_q_n)), max_q_n)
        self.assertEqual(aud.parse_exact_rational(orc.format_rational(max_q_d)), max_q_d)
        self.assertTrue(orc.format_decimal(max_q_n, 12).endswith(".000000000000"))
        for bad_fr in (1, _EvilFrac(1, 2)):
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm:
                orc.require_exact_fraction(bad_fr)
            self.assertEqual(cm.exception.code, "INVALID_FRACTION_TYPE")
        for over_fr in (Fraction(over_i, 1), Fraction(1, over_i), Fraction(10**4300, 1), Fraction(1, 10**4300)):
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm_r:
                orc.format_rational(over_fr)
            self.assertEqual(cm_r.exception.code, "RATIONAL_BIT_LIMIT")
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm_d:
                orc.format_decimal(over_fr, 6)
            self.assertEqual(cm_d.exception.code, "RATIONAL_BIT_LIMIT")

        self.assertEqual(orc.format_decimal(Fraction(-1, 10**9), 6), "0.000000")
        self.assertEqual(orc.format_decimal(Fraction(-5, 2), 0), "-3")
        self.assertEqual(orc.format_decimal(Fraction(1, 2), 0), "1")
        self.assertEqual(orc.format_decimal(Fraction(-3, 8), 2), "-0.38")

        # _require_int_seq, forward_difference, ducci_orbit_exact guards
        with self.assertRaises(orc.MozartPerfectBridgeError) as cm_st:
            orc.forward_difference("bad", 1)  # type: ignore[arg-type]
        self.assertEqual(cm_st.exception.code, "INVALID_SEQ_TYPE")
        with self.assertRaises(orc.MozartPerfectBridgeError) as cm_ss:
            orc.forward_difference([1], 0)
        self.assertEqual(cm_ss.exception.code, "SEQ_TOO_SHORT")
        with self.assertRaises(orc.MozartPerfectBridgeError) as cm_sl:
            orc.forward_difference([1] * 257, 1)
        self.assertEqual(cm_sl.exception.code, "SEQ_TOO_LONG")
        self.assertEqual(len(orc.forward_difference([1] * 256, 1)), 255)
        self.assertEqual(orc.forward_difference([10, 20], 0), [10, 20])
        self.assertEqual(orc.forward_difference([10, 20], 1), [10])
        with self.assertRaises(orc.MozartPerfectBridgeError) as cm_oh:
            orc.forward_difference([10, 20], 2)
        self.assertEqual(cm_oh.exception.code, "ORDER_TOO_HIGH")
        with self.assertRaises(orc.MozartPerfectBridgeError) as cm_dl:
            orc.ducci_orbit_exact([60, 62, 65, 64], max_steps=2)
        self.assertEqual(cm_dl.exception.code, "DUCCI_STEP_LIMIT")

        # F_2[x] & Z[x] helpers (including _zpoly_trim BoolOp kills + zpoly_divexact guards + is_prime/f2_is_irreducible)
        self.assertEqual(orc.f2_deg(0), -1)
        self.assertEqual(orc.f2_deg(1), 0)
        self.assertFalse(orc.f2_is_irreducible(0))
        self.assertFalse(orc.f2_is_irreducible(1))
        self.assertTrue(orc.f2_is_irreducible(0b10))
        self.assertTrue(orc.f2_is_irreducible(0b11))
        self.assertFalse(orc.f2_is_irreducible(0b100))  # even constant term
        self.assertFalse(orc.f2_is_irreducible(0b101))  # x^2 + 1 = (x+1)^2
        self.assertTrue(orc.f2_is_irreducible(0b111))   # x^2 + x + 1
        self.assertFalse(orc.f2_is_irreducible(0b10101))  # (x^2+x+1)^2

        self.assertEqual(orc._zpoly_trim([0]), [0])
        self.assertEqual(orc._zpoly_trim([0, 0]), [0])
        self.assertEqual(orc._zpoly_trim([1, 0]), [1])
        self.assertEqual(orc.zpoly_divexact([-1, 1], [-1, 1]), [1])
        self.assertEqual(orc.zpoly_divexact([-1, 0, 1], [-1, 1]), [1, 1])
        with self.assertRaises(orc.MozartPerfectBridgeError) as cm_nm:
            orc.zpoly_divexact([1, 2], [1, 2])
        self.assertEqual(cm_nm.exception.code, "NON_MONIC_ZPOLY")
        with self.assertRaises(orc.MozartPerfectBridgeError) as cm_dg:
            orc.zpoly_divexact([1], [-1, 1])
        self.assertEqual(cm_dg.exception.code, "ZPOLY_DEGREE_ERROR")
        with self.assertRaises(orc.MozartPerfectBridgeError) as cm_ne:
            orc.zpoly_divexact([1, 0, 1], [-1, 1])
        self.assertEqual(cm_ne.exception.code, "ZPOLY_NOT_EXACT")

        self.assertFalse(orc.is_prime_exact(1))
        self.assertTrue(orc.is_prime_exact(2))
        self.assertFalse(orc.is_prime_exact(4))
        self.assertFalse(orc.is_prime_exact(9))
        self.assertTrue(orc.is_prime_exact(19))
        self.assertFalse(orc.is_prime_exact(orc.MAX_PRIME_CHECK))
        with self.assertRaises(orc.MozartPerfectBridgeError) as cm_pc:
            orc.is_prime_exact(orc.MAX_PRIME_CHECK + 1)
        self.assertEqual(cm_pc.exception.code, "INT_OUT_OF_RANGE")
        self.assertEqual(orc.to_base_digits(496, 12), [3, 5, 4])


class TestParsersDeepSecondaryAuditAndTamperKills(unittest.TestCase):
    def test_strict_parsers_and_canonical_json_validation(self) -> None:
        max_i = (1 << orc.MAX_INT_BITS) - 1
        over_i = 1 << orc.MAX_INT_BITS
        self.assertEqual(aud._parse_bounded_int("0"), 0)
        self.assertEqual(aud._parse_bounded_int("10"), 10)
        self.assertEqual(aud._parse_bounded_int("-42"), -42)
        self.assertEqual(aud._parse_bounded_int(str(max_i)), max_i)
        self.assertEqual(aud._parse_bounded_int(str(-max_i)), -max_i)
        for bad_tok, code in (
            ("-0", "INVALID_JSON_INT"),
            ("-", "INVALID_JSON_INT"),
            ("", "INVALID_JSON_INT"),
            ("007", "INVALID_JSON_INT"),
            ("01", "INVALID_JSON_INT"),
            ("+1", "INVALID_JSON_INT"),
            ("\u0661", "INVALID_JSON_INT"),
            ("9" * (aud.MAX_JSON_INT_DIGITS + 1), "INT_DIGIT_LIMIT"),
            (str(over_i), "INT_BIT_LIMIT"),
        ):
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm:
                aud._parse_bounded_int(bad_tok)
            self.assertEqual(cm.exception.code, code)

        # parse_exact_rational including den == 2 boundary
        self.assertEqual(aud.parse_exact_rational("0"), Fraction(0))
        self.assertEqual(aud.parse_exact_rational("1/2"), Fraction(1, 2))
        self.assertEqual(aud.parse_exact_rational("-5/7"), Fraction(-5, 7))
        for bad_r, code in (
            ("1/2/3", "INVALID_RATIONAL"),
            ("3/1", "INVALID_RATIONAL"),
            ("3/0", "INVALID_RATIONAL"),
            ("2/4", "NON_CANONICAL_RATIONAL"),
        ):
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm:
                aud.parse_exact_rational(bad_r)
            self.assertEqual(cm.exception.code, code)

        # hex64
        good_h = "0123456789abcdef" * 4
        self.assertEqual(aud.require_hex64_lower_ascii(good_h), good_h)
        for bad_h in ("a" * 63, "A" * 64, "z" * 64):
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm:
                aud.require_hex64_lower_ascii(bad_h)
            self.assertEqual(cm.exception.code, "INVALID_HEX64")

        # parse_strict_json_text & canonical_json_bytes (aligned 3,321-bit cap, 10**4300, floats, cyclic dicts)
        self.assertEqual(aud.parse_strict_json_text("[1,null,true,false]", require_object=False), [1, None, True, False])
        exact_s = '{"k":"' + ("a" * 100) + '"}'
        self.assertEqual(len(aud.parse_strict_json_text(exact_s, max_bytes=len(exact_s))["k"]), 100)
        for bad_txt, code in (
            ("[1]", "JSON_ROOT_NOT_OBJECT"),
            ('{"a":1,"a":2}', "DUPLICATE_JSON_KEY"),
            ('{"a":1,"\\u0061":2}', "DUPLICATE_JSON_KEY"),
            ('{"x":1e2}', "FLOAT_LITERAL_FORBIDDEN"),
            ('{"x":NaN}', "NONFINITE_LITERAL_FORBIDDEN"),
            ('{"x":' + str(over_i) + "}", "INT_BIT_LIMIT"),
            ('{"x":' + "9" * (aud.MAX_JSON_INT_DIGITS + 1) + "}", "INT_DIGIT_LIMIT"),
            ('{"x":"a\\u0000b"}', "NUL_BYTE_FORBIDDEN"),
            ("{bad", "JSON_PARSE_ERROR"),
            ('{"a":' * (aud.MAX_JSON_DEPTH + 1) + "1" + "}" * (aud.MAX_JSON_DEPTH + 1), "JSON_DEPTH_LIMIT"),
            ('{"k":"' + ("a" * 101) + '"}', "JSON_TOO_LARGE"),
        ):
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm:
                aud.parse_strict_json_text(bad_txt, require_object=True, max_bytes=len(exact_s) if code == "JSON_TOO_LARGE" else aud.MAX_JSON_BYTES)
            self.assertEqual(cm.exception.code, code)

        cyc: dict[str, Any] = {}
        cyc["self"] = cyc
        deep_ok: Any = 1
        for _ in range(aud.MAX_JSON_DEPTH):
            deep_ok = [deep_ok]
        self.assertTrue(aud.canonical_json_bytes(deep_ok).startswith(b"["))
        self.assertTrue(aud.canonical_json_bytes({"v": [None, True, False, max_i, -max_i]}).startswith(b"{"))
        for bad_obj, code in (
            ({"x": over_i}, "INT_BIT_LIMIT"),
            ({"x": 10**4300}, "INT_BIT_LIMIT"),
            ({"x": -(10**4300)}, "INT_BIT_LIMIT"),
            (cyc, "JSON_DEPTH_LIMIT"),
            ([deep_ok], "JSON_DEPTH_LIMIT"),
            ({"x": (1, 2)}, "FORBIDDEN_JSON_TYPE"),
            ({"x": json.loads("1.5")}, "FORBIDDEN_JSON_TYPE"),
            ({"x": "\ud800"}, "INVALID_UTF8_SURROGATE"),
            ({"x": "a\x00b"}, "NUL_BYTE_FORBIDDEN"),
            ({1: "a"}, "INVALID_STR"),
        ):
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm:
                aud.canonical_json_bytes(bad_obj)
            self.assertEqual(cm.exception.code, code)

    def test_certificate_verification_and_full_replay_false_tamper_kills(self) -> None:
        cert = aud.build_standalone_certificate()
        self.assertTrue(cert["payload"]["summary"]["all_four_pillars_verified"])
        self.assertTrue(aud.verify_certificate_dict(cert, full_replay=True)["valid"])
        self.assertTrue(aud.verify_certificate_dict(cert, full_replay=False)["valid"])

        # Top-level structure & digest kills
        for bad_c, code in (
            ([], "INVALID_CERT_TYPE"),
            (dict(cert, extra=1), "INVALID_CERT_KEYS"),
            (dict(cert, schema_version="bad"), "INVALID_SCHEMA"),
            (dict(cert, track_id="bad"), "INVALID_TRACK_ID"),
            (dict(cert, payload=[1]), "INVALID_PAYLOAD_TYPE"),
        ):
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm:
                aud.verify_certificate_dict(bad_c, full_replay=True)
            self.assertEqual(cm.exception.code, code)

        flip_p = ("0" if cert["payload_sha256"][0] != "0" else "1") + cert["payload_sha256"][1:]
        with self.assertRaises(orc.MozartPerfectBridgeError) as cm_ps:
            aud.verify_certificate_dict(dict(cert, payload_sha256=flip_p))
        self.assertEqual(cm_ps.exception.code, "PAYLOAD_SHA256_MISMATCH")

        flip_c = ("0" if cert["certificate_sha256"][0] != "0" else "1") + cert["certificate_sha256"][1:]
        with self.assertRaises(orc.MozartPerfectBridgeError) as cm_cs:
            aud.verify_certificate_dict(dict(cert, certificate_sha256=flip_c))
        self.assertEqual(cm_cs.exception.code, "CERT_SHA256_MISMATCH")

        # full_replay=True checks exact digest match against build_standalone_certificate (kills REPLAY_MISMATCH)
        with mock.patch.object(aud, "build_standalone_certificate", return_value={"payload_sha256": "0" * 64}):
            self.assertTrue(aud.verify_certificate_dict(cert, full_replay=False)["valid"])
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm_rep:
                aud.verify_certificate_dict(cert, full_replay=True)
            self.assertEqual(cm_rep.exception.code, "REPLAY_MISMATCH")

        # Direct secondary_audit_payload rejects _EvilStr & float injections via _validate_json_tree
        sub_pl = copy.deepcopy(cert["payload"])
        sub_pl["track_id"] = _EvilStr(orc.TRACK_ID)
        with self.assertRaises(orc.MozartPerfectBridgeError) as cm_es:
            aud.secondary_audit_payload(sub_pl)
        self.assertEqual(cm_es.exception.code, "FORBIDDEN_JSON_TYPE")
        flt_pl = copy.deepcopy(cert["payload"])
        flt_pl["summary"]["pillar_count"] = json.loads("4.0")
        with self.assertRaises(orc.MozartPerfectBridgeError) as cm_fl:
            aud.secondary_audit_payload(flt_pl)
        self.assertEqual(cm_fl.exception.code, "FORBIDDEN_JSON_TYPE")

        # Schema helper direct kills
        self.assertEqual(aud._req_dict({"a": 1}, "d"), {"a": 1})
        for fn, code in (
            (lambda: aud._req_dict("x", "d"), "INVALID_SCHEMA_DICT"),
            (lambda: aud._req_dict({"a": 1}, "d", frozenset({"b"})), "INVALID_SCHEMA_KEYS"),
            (lambda: aud._req_list("abcd", "l", 4), "INVALID_SCHEMA_LIST"),
            (lambda: aud._req_list([1], "l", 2), "INVALID_SCHEMA_LIST"),
            (lambda: aud._req_int_f({}, "k", "i"), "MISSING_FIELD"),
            (lambda: aud._req_bool_f({}, "k", "b"), "MISSING_FIELD"),
        ):
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm_h:
                fn()
            self.assertEqual(cm_h.exception.code, code)

        # Re-signed hollow-table, strict nested-key, bool-for-int, int-for-bool, & semantic tampers under full_replay=False!
        tampers: tuple[tuple[Any, str], ...] = (
            (lambda p: p.__setitem__("extra", 1), "INVALID_SCHEMA_KEYS"),
            # Strict nested-key kills across all nested row/dict shapes
            (lambda p: p["pillar1_frobenius_canaday_euclid"]["mozart_2n_nilpotence"][0].__setitem__("extra", 1), "INVALID_SCHEMA_KEYS"),
            (lambda p: p["pillar1_frobenius_canaday_euclid"]["canaday_splitting_perfect_n1_to_n6"][0].__setitem__("extra", 1), "INVALID_SCHEMA_KEYS"),
            (lambda p: p["pillar2_cyclotomic_opn_obstruction"]["cyclotomic_sigma_factorization"].__setitem__("extra", 1), "INVALID_SCHEMA_KEYS"),
            (lambda p: p["pillar3_nyquist_pentagonal_ramanujan"]["euler_pentagonal_annihilator"].__setitem__("extra", 1), "INVALID_SCHEMA_KEYS"),
            (lambda p: p["pillar3_nyquist_pentagonal_ramanujan"]["ramanujan_e2_e4_convolution"]["perfect_number_witnesses"][0].__setitem__("extra", 1), "INVALID_SCHEMA_KEYS"),
            (lambda p: p["pillar4_anti_numerology_control"]["golden_ratio_bar_count_refutation"]["cases"][0].__setitem__("extra", 1), "INVALID_SCHEMA_KEYS"),
            # Semantic, shift-DoS, prime-DoS & negative-energy probes under full_replay=False & secondary_audit_payload
            (lambda p: p["pillar1_frobenius_canaday_euclid"].__setitem__("mozart_2n_nilpotence", []), "INVALID_SCHEMA_LIST"),
            (lambda p: p["pillar1_frobenius_canaday_euclid"]["mozart_2n_nilpotence"][0].update({"case_id": "FORGED", "length": 2, "exponent_n": 1, "steps_to_zero": 1}), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar1_frobenius_canaday_euclid"]["mozart_2n_nilpotence"][0].__setitem__("case_id", "RENAMED"), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar1_frobenius_canaday_euclid"]["mozart_2n_nilpotence"][0].__setitem__("exponent_n", -1), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar1_frobenius_canaday_euclid"]["mozart_2n_nilpotence"][0].__setitem__("exponent_n", 1 << 40), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar1_frobenius_canaday_euclid"]["mozart_2n_nilpotence"][0].__setitem__("steps_to_zero", 99), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar1_frobenius_canaday_euclid"]["mozart_2n_nilpotence"][0].__setitem__("outcome", "CYCLE"), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar1_frobenius_canaday_euclid"]["canaday_splitting_perfect_n1_to_n6"][0].__setitem__("n", -1), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar1_frobenius_canaday_euclid"]["canaday_splitting_perfect_n1_to_n6"][0].__setitem__("n", 1 << 40), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar1_frobenius_canaday_euclid"]["canaday_splitting_perfect_n1_to_n6"][0].__setitem__("degree", 99), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar1_frobenius_canaday_euclid"]["canaday_splitting_perfect_n1_to_n6"][0].__setitem__("sigma_x_eq_xp1_pow", False), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar1_frobenius_canaday_euclid"]["euclid_euler_even_perfect_p2_to_p19"][0].__setitem__("p", 0), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar1_frobenius_canaday_euclid"]["euclid_euler_even_perfect_p2_to_p19"][0].__setitem__("p", 1 << 40), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar1_frobenius_canaday_euclid"]["euclid_euler_even_perfect_p2_to_p19"][0].__setitem__("mersenne_Mp", 10**18 + 3), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar1_frobenius_canaday_euclid"]["euclid_euler_even_perfect_p2_to_p19"][0].__setitem__("even_perfect_N", 99), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar1_frobenius_canaday_euclid"]["euclid_euler_even_perfect_p2_to_p19"][0].__setitem__("sigma_2pm1_eq_Mp", False), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar1_frobenius_canaday_euclid"]["composite_exponent_m4_contrast"].__setitem__("z_sigma_N", 240), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar2_cyclotomic_opn_obstruction"]["cyclotomic_mozart_obstructions"][0].__setitem__("case_id", "FORGED"), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar2_cyclotomic_opn_obstruction"]["cyclotomic_mozart_obstructions"][0].__setitem__("verified", False), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar2_cyclotomic_opn_obstruction"]["cyclotomic_mozart_obstructions"][0].__setitem__("L", 999), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar2_cyclotomic_opn_obstruction"]["f2_odd_perfect_square_theorem"].__setitem__("odd_irreducibles_deg2_to_6_count", True), "INVALID_INT_TYPE"),
            (lambda p: p["pillar2_cyclotomic_opn_obstruction"]["f2_odd_perfect_square_theorem"].__setitem__("odd_prime_power_cases_checked", 62), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar2_cyclotomic_opn_obstruction"]["z_carry_propagation_obstruction"]["euler_primes_1_mod_4"][1].update({"q": 5, "phi2_q": 6, "v2_sigma_q1": 1, "v2_sigma_q5": 1}), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar2_cyclotomic_opn_obstruction"]["z_carry_propagation_obstruction"]["euler_primes_1_mod_4"][0].update({"q": 10**18 + 9, "phi2_q": 10**18 + 10, "v2_sigma_q1": 1, "v2_sigma_q5": 1}), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar2_cyclotomic_opn_obstruction"]["z_carry_propagation_obstruction"]["euler_primes_1_mod_4"][0].update({"q": 9, "phi2_q": 10, "v2_sigma_q1": 1, "v2_sigma_q5": 1}), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar2_cyclotomic_opn_obstruction"]["z_carry_propagation_obstruction"]["euler_primes_1_mod_4"][0].__setitem__("q", 0), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar2_cyclotomic_opn_obstruction"]["z_carry_propagation_obstruction"]["euler_primes_1_mod_4"][0].__setitem__("phi2_q", 99), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar2_cyclotomic_opn_obstruction"]["z_carry_propagation_obstruction"]["euler_primes_1_mod_4"][0].__setitem__("v2_sigma_q1", 2), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar2_cyclotomic_opn_obstruction"]["z_carry_propagation_obstruction"]["mod3_control_primes"][1].update({"q": 3, "v2_sigma_q1": 2}), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar2_cyclotomic_opn_obstruction"]["z_carry_propagation_obstruction"]["mod3_control_primes"][0].update({"q": 10**18 + 3, "v2_sigma_q1": 2}), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar2_cyclotomic_opn_obstruction"]["z_carry_propagation_obstruction"]["mod3_control_primes"][0].update({"q": 15, "v2_sigma_q1": 4}), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar2_cyclotomic_opn_obstruction"]["z_carry_propagation_obstruction"]["mod3_control_primes"][0].__setitem__("q", 0), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar2_cyclotomic_opn_obstruction"]["z_carry_propagation_obstruction"]["mod3_control_primes"][0].__setitem__("v2_sigma_q1", 1), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar2_cyclotomic_opn_obstruction"]["z_carry_propagation_obstruction"].__setitem__("integer_opn_conjecture_remains_open", False), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar3_nyquist_pentagonal_ramanujan"]["spectral_prism_comparison"][0].__setitem__("name", "WRONG"), "INVALID_SCHEMA_KEYS"),
            (lambda p: p["pillar3_nyquist_pentagonal_ramanujan"]["spectral_prism_comparison"][0]["energies_E1_to_E5"].__setitem__(3, 1), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar3_nyquist_pentagonal_ramanujan"]["spectral_prism_comparison"][0]["energies_E1_to_E5"].__setitem__(4, -5), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar3_nyquist_pentagonal_ramanujan"]["spectral_prism_comparison"][0].update({"length": 99, "energies_E1_to_E5": [100, 1, 0, 0, 0], "ratios_R2_to_R5_q": ["1/100", "0", "0", "0"], "ms_ratios_R2_to_R5_q": ["49/4850", "0", "0", "0"], "ratios_R2_to_R5_dec6": ["0.010000", "0.000000", "0.000000", "0.000000"], "ms_ratios_R2_to_R5_dec6": ["0.010103", "0.000000", "0.000000", "0.000000"]}), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar3_nyquist_pentagonal_ramanujan"]["spectral_prism_comparison"][0]["ratios_R2_to_R5_q"].__setitem__(2, "1"), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar3_nyquist_pentagonal_ramanujan"]["spectral_prism_comparison"][0]["ms_ratios_R2_to_R5_q"].__setitem__(2, "1"), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar3_nyquist_pentagonal_ramanujan"]["spectral_prism_comparison"][0]["ratios_R2_to_R5_dec6"].__setitem__(0, "9.999999"), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar3_nyquist_pentagonal_ramanujan"]["spectral_prism_comparison"][0]["ms_ratios_R2_to_R5_dec6"].__setitem__(0, "9.999999"), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar3_nyquist_pentagonal_ramanujan"]["spectral_prism_comparison"][3]["energies_E1_to_E5"].__setitem__(0, -1), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar3_nyquist_pentagonal_ramanujan"]["spectral_prism_comparison"][3].__setitem__("length", 2), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar3_nyquist_pentagonal_ramanujan"]["spectral_prism_comparison"][3]["energies_E1_to_E5"].__setitem__(1, 1), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar3_nyquist_pentagonal_ramanujan"]["spectral_prism_comparison"][3]["ratios_R2_to_R5_q"].__setitem__(0, "1"), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar3_nyquist_pentagonal_ramanujan"]["spectral_prism_comparison"][3]["ms_ratios_R2_to_R5_q"].__setitem__(0, "1"), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar3_nyquist_pentagonal_ramanujan"]["euler_pentagonal_annihilator"].__setitem__("zero_residual_count", 99), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar3_nyquist_pentagonal_ramanujan"]["euler_pentagonal_annihilator"].__setitem__("delta3_pent_plus_zero", False), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar3_nyquist_pentagonal_ramanujan"]["ramanujan_e2_e4_convolution"]["perfect_number_witnesses"][0].__setitem__("lhs_12_conv", 841), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar3_nyquist_pentagonal_ramanujan"]["ramanujan_e2_e4_convolution"]["perfect_number_witnesses"][0].__setitem__("sigma_3", 1), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar4_anti_numerology_control"]["transposition_invariance_control"]["cases"][0].__setitem__("stage_a_c_pitch_class_count", 999999), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar4_anti_numerology_control"]["transposition_invariance_control"]["cases"][0].__setitem__("stage_a_c_pitch_class_count", -1), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar4_anti_numerology_control"]["transposition_invariance_control"]["cases"][0].__setitem__("stage_b_energies_identical", False), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar4_anti_numerology_control"]["transposition_invariance_control"]["cases"][1].__setitem__("stage_a_histogram_preserved", True), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar4_anti_numerology_control"]["radix_invariance_control"]["cases"][0].__setitem__("stage_b_sigma_eq_2N_all_3", False), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar4_anti_numerology_control"]["radix_invariance_control"]["cases"][0].__setitem__("ends_in_6_or_8_in_this_base", True), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar4_anti_numerology_control"]["golden_ratio_bar_count_refutation"]["cases"][0].update({"sonata": "FORGED", "a": 1, "b": 1, "exact_golden_defect_Z": -1, "a_over_b_q": "1"}), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar4_anti_numerology_control"]["golden_ratio_bar_count_refutation"]["cases"][0].__setitem__("b", 0), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar4_anti_numerology_control"]["golden_ratio_bar_count_refutation"]["cases"][0].__setitem__("exact_golden_defect_Z", 0), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["pillar4_anti_numerology_control"]["golden_ratio_bar_count_refutation"]["cases"][0].__setitem__("nonzero_defect", False), "SECONDARY_AUDIT_FAILED"),
            (lambda p: p["summary"].__setitem__("all_four_pillars_verified", 1), "INVALID_BOOL_TYPE"),
            (lambda p: p["summary"].__setitem__("pillar_count", 3), "SECONDARY_AUDIT_FAILED"),
        )
        for mut_fn, exp_code in tampers:
            forged = _resign(cert, mut_fn)
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm_t:
                aud.verify_certificate_dict(forged, full_replay=False)
            self.assertEqual(cm_t.exception.code, exp_code)
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm_s:
                aud.secondary_audit_payload(forged["payload"])
            self.assertEqual(cm_s.exception.code, exp_code)


class TestZoneBIOConcurrencyAndCLI(unittest.TestCase):
    def test_zone_b_io_paths_caps_symlinks_pwd_hardlinks_and_deleted_cwd(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            nested = root / "sub1" / "sub2" / "cert.json"

            w_res = aud.write_certificate_file(nested)
            self.assertTrue(w_res["written"])
            self.assertEqual(stat.S_IMODE(os.lstat(nested).st_mode), 0o600)
            c_res = aud.check_certificate_file(nested)
            self.assertTrue(c_res["valid"])
            self.assertEqual(w_res["file_sha256"], c_res["file_sha256"])

            # Concrete path, NUL, surrogate, max_bytes cap
            for bad_p, code in (
                (_EvilPath(str(nested)), "INVALID_PATH_TYPE"),
                (Path("a\x00b"), "NUL_BYTE_FORBIDDEN"),
                (Path("bad\ud800.json"), "INVALID_UTF8_SURROGATE"),
            ):
                with self.assertRaises(orc.MozartPerfectBridgeError) as cm:
                    aud.read_regular_bytes_capped(bad_p)
                self.assertEqual(cm.exception.code, code)
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm_cap:
                aud.read_regular_bytes_capped(nested, "c", max_bytes=1 << 100)
            self.assertEqual(cm_cap.exception.code, "INT_OUT_OF_RANGE")

            # Direct _open_dir_chain BoolOp kills + root/dot/dotdot
            for bad_d in (Path("/"), Path("..")):
                with self.assertRaises(orc.MozartPerfectBridgeError) as cm_od:
                    aud._open_dir_chain(bad_d, "d", create_parents=False)
                self.assertEqual(cm_od.exception.code, "NOT_A_REGULAR_FILE")
            for bad_d in (Path("/"), Path("."), Path("..")):
                with self.assertRaises(orc.MozartPerfectBridgeError) as cm_d:
                    aud.read_regular_bytes_capped(bad_d)
                self.assertEqual(cm_d.exception.code, "NOT_A_REGULAR_FILE")

            # Missing parent read MUST NOT create directory (kills create_parents BoolOp!)
            missing_p = root / "missing_dir"
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm_mp:
                aud.read_regular_bytes_capped(missing_p / "x.json")
            self.assertEqual(cm_mp.exception.code, "FILE_READ_ERROR")
            self.assertFalse(missing_p.exists())

            # Leaf & intermediate symlinks (both read and write)
            sym_leaf = root / "sym_leaf.json"
            sym_leaf.symlink_to(nested)
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm_slr:
                aud.read_regular_bytes_capped(sym_leaf)
            self.assertEqual(cm_slr.exception.code, "SYMLINK_FORBIDDEN")
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm_slw:
                aud.write_regular_bytes_safe(sym_leaf, b"x")
            self.assertEqual(cm_slw.exception.code, "SYMLINK_FORBIDDEN")

            sym_dir = root / "sym_dir"
            sym_dir.symlink_to(nested.parent)
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm_sd:
                aud.read_regular_bytes_capped(Path(f"{sym_dir}/../sub2/cert.json"))
            self.assertEqual(cm_sd.exception.code, "SYMLINK_FORBIDDEN")
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm_sdw:
                aud.write_regular_bytes_safe(sym_dir / "x.json", b"a")
            self.assertEqual(cm_sdw.exception.code, "SYMLINK_FORBIDDEN")

            # FIFO, hardlink target, non-bytes payload, pre-replace temp st_nlink != 1
            fifo = root / "p.fifo"
            os.mkfifo(fifo)
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm_fr:
                aud.read_regular_bytes_capped(fifo)
            self.assertEqual(cm_fr.exception.code, "NOT_A_REGULAR_FILE")
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm_fw:
                aud.write_regular_bytes_safe(fifo, b"x")
            self.assertEqual(cm_fw.exception.code, "NOT_A_REGULAR_FILE")

            hl_a = root / "hl_a.json"
            hl_a.write_bytes(b"KEEP_ME\n")
            hl_b = root / "hl_b.json"
            os.link(hl_a, hl_b)
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm_hl:
                aud.write_regular_bytes_safe(hl_b, b"CLOBBER\n")
            self.assertEqual(cm_hl.exception.code, "HARDLINK_FORBIDDEN")
            self.assertEqual(hl_a.read_bytes(), b"KEEP_ME\n")

            with self.assertRaises(orc.MozartPerfectBridgeError) as cm_nb:
                aud.write_regular_bytes_safe(root / "nb.json", "not_bytes")  # type: ignore[arg-type]
            self.assertEqual(cm_nb.exception.code, "INVALID_PAYLOAD_BYTES")

            fake_st = mock.Mock(st_nlink=2)
            with mock.patch("os.fstat", return_value=fake_st):
                with self.assertRaises(orc.MozartPerfectBridgeError) as cm_tmp_hl:
                    aud.write_regular_bytes_safe(root / "tmp_hl.json", b"abc")
                self.assertEqual(cm_tmp_hl.exception.code, "HARDLINK_FORBIDDEN")
            self.assertFalse((root / "tmp_hl.json").exists())

            # Streaming >64 KiB boundary
            exact_f = root / "exact.bin"
            exact_f.write_bytes(b"x" * 70000)
            self.assertEqual(len(aud.read_regular_bytes_capped(exact_f, "ex", max_bytes=70000)), 70000)
            with self.assertRaises(orc.MozartPerfectBridgeError) as cm_big:
                aud.read_regular_bytes_capped(exact_f, "ex", max_bytes=69999)
            self.assertEqual(cm_big.exception.code, "FILE_TOO_LARGE")

            # Relative paths, atomic PWD check, deleted-CWD
            orig_cwd = os.getcwd()
            try:
                os.chdir(nested.parent)
                with mock.patch.dict(os.environ, {"PWD": str(nested.parent)}, clear=False):
                    self.assertEqual(aud.read_regular_bytes_capped(Path("./cert.json")), nested.read_bytes())
                with mock.patch.dict(os.environ, {"PWD": ""}, clear=False):
                    self.assertEqual(aud.read_regular_bytes_capped(Path("cert.json")), nested.read_bytes())
                with mock.patch.dict(os.environ, {"PWD": str(sym_dir)}, clear=False):
                    with self.assertRaises(orc.MozartPerfectBridgeError) as cm_pwd:
                        aud.read_regular_bytes_capped(Path("cert.json"))
                    self.assertEqual(cm_pwd.exception.code, "SYMLINK_ANCESTOR_FORBIDDEN")
                with mock.patch.dict(os.environ, {"PWD": str(root / "no_pwd")}, clear=False):
                    with self.assertRaises(orc.MozartPerfectBridgeError) as cm_gpwd:
                        aud.read_regular_bytes_capped(Path("cert.json"))
                    self.assertEqual(cm_gpwd.exception.code, "CWD_UNAVAILABLE")

                doomed = root / "doomed_cwd"
                doomed.mkdir()
                os.chdir(doomed)
                doomed.rmdir()
                for cli_args in (["--check", "rel.json", "--json"], ["--write", "rel.json", "--json"]):
                    eb = io.StringIO()
                    with redirect_stderr(eb):
                        rc = aud.main(cli_args)
                    self.assertEqual(rc, 2)
                    self.assertEqual(json.loads(eb.getvalue())["error_code"], "CWD_UNAVAILABLE")
            finally:
                os.chdir(orig_cwd)

            if os.geteuid() != 0:
                locked = root / "locked_dir"
                locked.mkdir()
                locked.chmod(0)
                try:
                    with self.assertRaises(orc.MozartPerfectBridgeError) as cm_ld:
                        aud.write_regular_bytes_safe(locked / "x.json", b"a")
                    self.assertEqual(cm_ld.exception.code, "FILE_WRITE_ERROR")
                finally:
                    locked.chmod(0o755)

            raw_v = nested.read_bytes()
            for fname, blob, code in (
                ("crlf.json", raw_v[:-1] + b"\r\n", "CRLF_FORBIDDEN"),
                ("nolf.json", raw_v[:-1], "MISSING_TRAILING_LF"),
                ("badu.json", b"\xff\xfe\n", "INVALID_UTF8"),
                ("nonc.json", b" " + raw_v, "NON_CANONICAL_BYTES"),
            ):
                p = root / fname
                p.write_bytes(blob)
                with self.assertRaises(orc.MozartPerfectBridgeError) as cm_fmt:
                    aud.check_certificate_file(p)
                self.assertEqual(cm_fmt.exception.code, code)

    def test_concurrency_16t_80t_renameat2_and_hardlink_races(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            payload = b'{"ok":true}\n'

            # 16T distinct
            errs_d: list[Exception] = []
            def _w_dist(idx: int) -> None:
                try:
                    p = root / f"d_{idx}.json"
                    aud.write_regular_bytes_safe(p, payload)
                    if stat.S_IMODE(os.lstat(p).st_mode) != 0o600:
                        errs_d.append(RuntimeError("bad_mode"))
                    if aud.read_regular_bytes_capped(p) != payload:
                        errs_d.append(RuntimeError("mismatch"))
                except Exception as exc:  # pragma: no cover
                    errs_d.append(exc)
            ts = [threading.Thread(target=_w_dist, args=(i,)) for i in range(16)]
            for t in ts:
                t.start()
            for t in ts:
                t.join()
            self.assertEqual(errs_d, [])

            # 16T same target
            same_p = root / "same.json"
            errs_s: list[Exception] = []
            def _w_same(idx: int) -> None:
                try:
                    aud.write_regular_bytes_safe(same_p, f'{{"id":{idx}}}\n'.encode("ascii"))
                except Exception as exc:  # pragma: no cover
                    errs_s.append(exc)
            ts = [threading.Thread(target=_w_same, args=(i,)) for i in range(16)]
            for t in ts:
                t.start()
            for t in ts:
                t.join()
            self.assertEqual(errs_s, [])
            self.assertIn(b'"id":', same_p.read_bytes())

            # 80T burst across 8 targets
            errs_b: list[Exception] = []
            def _w_burst(idx: int) -> None:
                try:
                    aud.write_regular_bytes_safe(root / f"b_{idx % 8}.json", payload)
                except Exception as exc:  # pragma: no cover
                    errs_b.append(exc)
            ts = [threading.Thread(target=_w_burst, args=(i,)) for i in range(80)]
            for t in ts:
                t.start()
            for t in ts:
                t.join()
            self.assertEqual(errs_b, [])
            self.assertEqual([p.name for p in root.iterdir() if p.name.endswith(".tmp")], [])

            # Live renameat2(RENAME_EXCHANGE) >= 500 iterations
            libc = ctypes.CDLL("libc.so.6", use_errno=True)
            outside = root / "outside"
            outside.mkdir()
            canary = outside / "target.json"
            canary.write_bytes(b"CANARY_OUTSIDE\n")
            slot = root / "slot"
            slot.mkdir()
            (slot / "target.json").write_bytes(b"LEGIT_INSIDE\n")
            sym = root / "sym_swap"
            sym.symlink_to(outside)
            stop = threading.Event()
            b1 = os.fsencode(slot)
            b2 = os.fsencode(sym)
            def _swapper() -> None:
                while not stop.is_set():
                    libc.syscall(316, -100, b1, -100, b2, 2)
            sw = threading.Thread(target=_swapper, daemon=True)
            sw.start()
            leaks = 0
            clobbers = 0
            try:
                for _ in range(550):
                    try:
                        if aud.read_regular_bytes_capped(slot / "target.json") != b"LEGIT_INSIDE\n":
                            leaks += 1
                    except orc.MozartPerfectBridgeError:
                        pass
                    try:
                        aud.write_regular_bytes_safe(slot / "target.json", b"LEGIT_INSIDE\n")
                    except orc.MozartPerfectBridgeError:
                        pass
                    if canary.read_bytes() != b"CANARY_OUTSIDE\n":
                        clobbers += 1
            finally:
                stop.set()
                sw.join(timeout=2)
            self.assertEqual(leaks, 0)
            self.assertEqual(clobbers, 0)

            # Live hardlink race (>= 500 iterations)
            hl_dir = root / "hl_race"
            hl_dir.mkdir()
            hl_tgt = hl_dir / "target.json"
            hl_alias = hl_dir / "alias.json"
            hl_tgt.write_bytes(b"INIT\n")
            stop_hl = threading.Event()
            hl_clobbers = 0
            def _hl_racer() -> None:
                while not stop_hl.is_set():
                    try:
                        os.link(hl_tgt, hl_alias)
                    except OSError:
                        pass
                    try:
                        os.unlink(hl_alias)
                    except OSError:
                        pass
            hl_t = threading.Thread(target=_hl_racer, daemon=True)
            hl_t.start()
            try:
                for _ in range(550):
                    try:
                        aud.write_regular_bytes_safe(hl_tgt, b"NEXT\n")
                    except orc.MozartPerfectBridgeError:
                        pass
                    try:
                        if hl_alias.exists():
                            if hl_alias.read_bytes() not in (b"INIT\n", b"NEXT\n"):
                                hl_clobbers += 1
                    except OSError:
                        pass
            finally:
                stop_hl.set()
                hl_t.join(timeout=2)
            self.assertEqual(hl_clobbers, 0)
            self.assertEqual([p.name for p in hl_dir.iterdir() if p.name.endswith(".tmp")], [])

    def test_cli_modes_space_and_equals_syntax_and_adversarial_argv(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            p1 = root / "c1.json"
            p2 = root / "c2.json"

            out_t = io.StringIO()
            with redirect_stdout(out_t):
                self.assertEqual(aud.main([]), 0)
            self.assertIn("OK ", out_t.getvalue())

            out_j = io.StringIO()
            with redirect_stdout(out_j):
                self.assertEqual(aud.main(["--standalone", "--json"]), 0)
            standalone_b = out_j.getvalue().encode("ascii")

            out_w1 = io.StringIO()
            with redirect_stdout(out_w1):
                self.assertEqual(aud.main(["--write", str(p1), "--json"]), 0)
            self.assertEqual(p1.read_bytes(), standalone_b)

            out_c1 = io.StringIO()
            with redirect_stdout(out_c1):
                self.assertEqual(aud.main(["--check", str(p1), "--json"]), 0)
            self.assertTrue(json.loads(out_c1.getvalue())["valid"])

            out_w2 = io.StringIO()
            with redirect_stdout(out_w2):
                self.assertEqual(aud.main([f"--write={p2}", "--json"]), 0)
            self.assertEqual(p2.read_bytes(), standalone_b)

            out_c2 = io.StringIO()
            with redirect_stdout(out_c2):
                self.assertEqual(aud.main([f"--check={p2}", "--json"]), 0)
            self.assertTrue(json.loads(out_c2.getvalue())["valid"])

            # Live CLI --check on shift-DoS & prime-DoS re-signed canonical certs returns rc=2 (0 raw crashes/timeouts)
            base_cert = aud.build_standalone_certificate()
            for idx, dos_mut in enumerate(
                (
                    lambda p: p["pillar1_frobenius_canaday_euclid"]["mozart_2n_nilpotence"][0].__setitem__("exponent_n", -1),
                    lambda p: p["pillar1_frobenius_canaday_euclid"]["canaday_splitting_perfect_n1_to_n6"][0].__setitem__("n", 1 << 40),
                    lambda p: p["pillar1_frobenius_canaday_euclid"]["euclid_euler_even_perfect_p2_to_p19"][0].__setitem__("p", 0),
                    lambda p: p["pillar1_frobenius_canaday_euclid"]["euclid_euler_even_perfect_p2_to_p19"][0].__setitem__("mersenne_Mp", 10**18 + 3),
                    lambda p: p["pillar2_cyclotomic_opn_obstruction"]["z_carry_propagation_obstruction"]["euler_primes_1_mod_4"][0].__setitem__("q", 10**18 + 9),
                )
            ):
                dp = root / f"dos_{idx}.json"
                dp.write_bytes(aud.canonical_json_bytes(_resign(base_cert, dos_mut)) + b"\n")
                eb_dos = io.StringIO()
                with redirect_stderr(eb_dos):
                    rc_dos = aud.main(["--check", str(dp), "--json"])
                self.assertEqual(rc_dos, 2)
                self.assertEqual(json.loads(eb_dos.getvalue())["error_code"], "SECONDARY_AUDIT_FAILED")

            for bad_argv, code in (
                ("bad", "INVALID_ARGV"),
                ([123], "INVALID_STR"),
                ([_EvilStr("--standalone")], "INVALID_STR"),
                (["\ud800"], "INVALID_UTF8_SURROGATE"),
                (["--json", "--json"], "DUPLICATE_FLAG"),
                (["--standalone", "--standalone"], "CONFLICTING_MODE"),
                (["--standalone", "--check", str(p1)], "CONFLICTING_MODE"),
                (["--standalone", f"--check={p1}"], "CONFLICTING_MODE"),
                (["--check"], "MISSING_PATH_ARG"),
                (["--write"], "MISSING_PATH_ARG"),
                (["--check", ""], "INVALID_PATH_ARG"),
                (["--check", "--json"], "INVALID_PATH_ARG"),
                (["--write", "--json"], "INVALID_PATH_ARG"),
                (["--check=--json"], "INVALID_PATH_ARG"),
                (["--write=--json"], "INVALID_PATH_ARG"),
                (["--write="], "INVALID_PATH_ARG"),
                (["--bogus"], "UNKNOWN_FLAG"),
            ):
                eb = io.StringIO()
                with redirect_stderr(eb):
                    rc = aud.main(bad_argv)  # type: ignore[arg-type]
                self.assertEqual(rc, 2)
                self.assertEqual(json.loads(eb.getvalue())["error_code"], code)
            self.assertFalse((root / "--json").exists())


if __name__ == "__main__":
    unittest.main()
