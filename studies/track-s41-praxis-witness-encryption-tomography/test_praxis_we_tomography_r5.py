#!/usr/bin/env python3
"""Track S41 (Portals 43 + 45): R5 Adversarial, Mutation, Race & 4-Pillar Test Suite.

Pure Python 3 stdlib unittest suite with zero AST float literals, zero float() calls,
zero bare asserts, zero .isdigit()/.isnumeric()/.isdecimal(), zero islink/is_symlink,
and zero mathematical RNG calls.
"""
from __future__ import annotations

import copy
import ctypes
from fractions import Fraction
import io
import json
import os
from pathlib import Path
import secrets
import stat
import subprocess
import sys
import tempfile
import threading
import unittest
from typing import Any

_THIS_DIR = str(Path(__file__).resolve().parent)
if _THIS_DIR not in sys.path:
    sys.path.insert(0, _THIS_DIR)

import praxis_we_tomography_audit as audit
import praxis_we_tomography_oracle as oracle


class _SubInt(int):
    pass


class _SubStr(str):
    pass


class _SubDict(dict):
    pass


class _SubList(list):
    pass


class _SubPath(type(Path("."))):
    pass


def _resign_cert(cert: dict[str, Any]) -> dict[str, Any]:
    payload_sha = oracle.sha256_hex(oracle.canonical_json_bytes(cert["payload"]))
    cert["payload_sha256"] = payload_sha
    body = {
        "schema": cert["schema"],
        "track_id": cert["track_id"],
        "payload_sha256": payload_sha,
        "payload": cert["payload"],
    }
    cert["certificate_sha256"] = oracle.sha256_hex(oracle.canonical_json_bytes(body))
    return cert


def _run_main_captured(argv: Any) -> tuple[int, str, str]:
    old_out, old_err = sys.stdout, sys.stderr
    buf_out, buf_err = io.StringIO(), io.StringIO()
    sys.stdout, sys.stderr = buf_out, buf_err
    try:
        rc = audit.main(argv)
    finally:
        sys.stdout, sys.stderr = old_out, old_err
    return rc, buf_out.getvalue(), buf_err.getvalue()


class Test01ZoneBPrimitivesAndParsers(unittest.TestCase):
    def _assert_err(self, code: str, fn: Any, *args: Any, **kwargs: Any) -> None:
        with self.assertRaises(oracle.PraxisTomographyError) as ctx:
            fn(*args, **kwargs)
        self.assertEqual(ctx.exception.code, code)

    def test_01_require_bool_int_str_hex64(self) -> None:
        self.assertIs(oracle.require_bool(True, "b"), True)
        self.assertIs(oracle.require_bool(False, "b"), False)
        self._assert_err("INVALID_BOOL", oracle.require_bool, 1, "b")
        self._assert_err("INVALID_BOOL", oracle.require_bool, "true", "b")

        self.assertEqual(oracle.require_int(0, "i", lo=0, hi=0), 0)
        self.assertEqual(oracle.require_int(-5, "i", lo=-5, hi=5), -5)
        self.assertEqual(oracle.require_int(5, "i", lo=-5, hi=5), 5)
        self._assert_err("INVALID_INT", oracle.require_int, True, "i")
        self._assert_err("INVALID_INT", oracle.require_int, _SubInt(1), "i")
        self._assert_err("INT_OUT_OF_RANGE", oracle.require_int, 4, "i", lo=5)
        self._assert_err("INT_OUT_OF_RANGE", oracle.require_int, 6, "i", hi=5)

        self.assertEqual(oracle.require_str("abc", "s", max_len=3), "abc")
        self._assert_err("INVALID_STR", oracle.require_str, _SubStr("a"), "s")
        self._assert_err("INVALID_STR", oracle.require_str, b"a", "s")
        self._assert_err("STR_TOO_LONG", oracle.require_str, "abcd", "s", max_len=3)
        self._assert_err("INT_OUT_OF_RANGE", oracle.require_str, "a", "s", max_len=0)
        self._assert_err("INT_OUT_OF_RANGE", oracle.require_str, "a", "s", max_len=oracle.HARD_MAX_BYTES_CAP + 1)
        self._assert_err("INVALID_UTF8_SURROGATE", oracle.require_str, "bad\ud800s", "s")

        h_a = "0123456789abcdef" * 4
        h_b = "fedcba9876543210" * 4
        self.assertEqual(oracle.require_hex64(h_a, "h"), h_a)
        self.assertTrue(oracle.constant_time_hex64_equal(h_a, h_a, "eq"))
        self.assertFalse(oracle.constant_time_hex64_equal(h_a, h_b, "neq"))
        self._assert_err("INVALID_HEX64", oracle.require_hex64, h_a[:-1], "h")
        self._assert_err("STR_TOO_LONG", oracle.require_hex64, h_a + "0", "h")
        self._assert_err("INVALID_HEX64", oracle.require_hex64, h_a.upper(), "h")
        self._assert_err("INVALID_HEX64", oracle.require_hex64, "g" * 64, "h")
        self._assert_err("INVALID_HEX64", oracle.constant_time_hex64_equal, "short", h_a, "eq")
        self._assert_err("INVALID_HEX64", oracle.constant_time_hex64_equal, h_a, "short", "eq")

    def test_02_symmetric_bounded_int_and_rational_limits(self) -> None:
        max_ok = (1 << oracle.MAX_INT_BITS) - 1
        min_fail = 1 << oracle.MAX_INT_BITS
        self.assertEqual(len(str(max_ok)), oracle.MAX_INT_DIGITS)
        self.assertEqual(len(str(min_fail)), oracle.MAX_INT_DIGITS)

        self.assertEqual(oracle.parse_bounded_int(0, "z"), 0)
        self.assertEqual(oracle.parse_bounded_int("0", "z"), 0)
        self.assertEqual(oracle.parse_bounded_int("-1", "z"), -1)
        self.assertEqual(oracle.parse_bounded_int(max_ok, "m"), max_ok)
        self.assertEqual(oracle.parse_bounded_int(-max_ok, "m"), -max_ok)
        self.assertEqual(oracle.parse_bounded_int(str(max_ok), "m"), max_ok)
        self.assertEqual(oracle.parse_bounded_int(f"-{max_ok}", "m"), -max_ok)
        self.assertEqual(oracle.parse_bounded_int(10 ** 999, "p"), 10 ** 999)
        self.assertEqual(oracle.parse_bounded_int("1" + "0" * 999, "p"), 10 ** 999)

        self._assert_err("INT_TOO_LARGE", oracle.parse_bounded_int, min_fail, "m")
        self._assert_err("INT_TOO_LARGE", oracle.parse_bounded_int, -min_fail, "m")
        self._assert_err("INT_TOO_LARGE", oracle.parse_bounded_int, str(min_fail), "m")
        self._assert_err("INT_TOO_LARGE", oracle.parse_bounded_int, f"-{min_fail}", "m")
        self._assert_err("INVALID_INT_STR", oracle.parse_bounded_int, "1" + "0" * 1001, "m")
        self._assert_err("INT_TOO_LARGE", oracle.parse_bounded_int, "1" + "0" * 1000, "m")
        self._assert_err("INVALID_INT_STR", oracle.parse_bounded_int, "-0", "m")
        self._assert_err("INVALID_INT_STR", oracle.parse_bounded_int, "01", "m")
        self._assert_err("INVALID_INT_STR", oracle.parse_bounded_int, "", "m")
        self._assert_err("INVALID_INT_STR", oracle.parse_bounded_int, "+1", "m")
        self._assert_err("INVALID_INT_STR", oracle.parse_bounded_int, "12a", "m")
        self._assert_err("INVALID_INT", oracle.parse_bounded_int, True, "m")
        self._assert_err("INT_OUT_OF_RANGE", oracle.parse_bounded_int, "4", "m", lo=5)

        self.assertEqual(oracle.parse_exact_rational(0), Fraction(0, 1))
        self.assertEqual(oracle.parse_exact_rational(max_ok), Fraction(max_ok, 1))
        self.assertEqual(oracle.parse_exact_rational(Fraction(max_ok, 1)), Fraction(max_ok, 1))
        self.assertEqual(oracle.parse_exact_rational(Fraction(1, max_ok)), Fraction(1, max_ok))
        self.assertEqual(oracle.parse_exact_rational("0"), Fraction(0, 1))
        self.assertEqual(oracle.parse_exact_rational("-7"), Fraction(-7, 1))
        self.assertEqual(oracle.parse_exact_rational("3/7"), Fraction(3, 7))
        self.assertEqual(oracle.parse_exact_rational("-3/7"), Fraction(-3, 7))
        self.assertEqual(oracle.parse_exact_rational(f"{max_ok}"), Fraction(max_ok, 1))
        self.assertEqual(oracle.parse_exact_rational(f"1/{max_ok}"), Fraction(1, max_ok))
        exact_max_str = f"-{max_ok}/{max_ok - 1}"
        self.assertEqual(len(exact_max_str), oracle.MAX_RATIONAL_CHARS)
        self.assertEqual(oracle.parse_exact_rational(exact_max_str), Fraction(-max_ok, max_ok - 1))

        self._assert_err("RATIONAL_TOO_LARGE", oracle.parse_exact_rational, min_fail)
        self._assert_err("RATIONAL_TOO_LARGE", oracle.parse_exact_rational, Fraction(min_fail, 1))
        self._assert_err("RATIONAL_TOO_LARGE", oracle.parse_exact_rational, Fraction(1, min_fail))
        self._assert_err("INVALID_RATIONAL_TYPE", oracle.parse_exact_rational, True)
        self._assert_err("INVALID_RATIONAL_TYPE", oracle.parse_exact_rational, None)
        self._assert_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "1" * (oracle.MAX_RATIONAL_CHARS + 1))
        self._assert_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "1/2/3")
        self._assert_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "01/3")
        self._assert_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "-0")
        self._assert_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "-0/3")
        self._assert_err("RATIONAL_TOO_LARGE", oracle.parse_exact_rational, "1" + "0" * 1000)
        self._assert_err("RATIONAL_TOO_LARGE", oracle.parse_exact_rational, str(min_fail))
        self._assert_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "1/03")
        self._assert_err("RATIONAL_TOO_LARGE", oracle.parse_exact_rational, "1/" + "1" + "0" * 1000)
        self._assert_err("RATIONAL_TOO_LARGE", oracle.parse_exact_rational, f"1/{min_fail + 1}")
        self._assert_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "3/1")
        self._assert_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "3/0")
        self._assert_err("NON_CANONICAL_RATIONAL", oracle.parse_exact_rational, "2/4")

        self.assertEqual(oracle.format_rational(Fraction(5, 1)), "5")
        self.assertEqual(oracle.format_rational(Fraction(-3, 7)), "-3/7")
        self._assert_err("INVALID_RATIONAL_TYPE", oracle.format_rational, 5)
        self._assert_err("RATIONAL_TOO_LARGE", oracle.format_rational, Fraction(min_fail, 1))
        self._assert_err("RATIONAL_TOO_LARGE", oracle.format_rational, Fraction(1, min_fail))

        self.assertEqual(oracle.format_decimal_trunc(Fraction(-1, 1000), places=2), "0.00")
        self.assertEqual(oracle.format_decimal_trunc(Fraction(-1, 1000), places=0), "0")
        self.assertEqual(oracle.format_decimal_trunc(Fraction(-7, 4), places=2), "-1.75")
        self.assertEqual(oracle.format_decimal_trunc(Fraction(-7, 4), places=0), "-1")
        self.assertEqual(oracle.format_decimal_trunc(Fraction(9, 2), places=1), "4.5")
        self.assertEqual(oracle.format_decimal_trunc(Fraction(1, 100), places=4), "0.0100")
        self._assert_err("INVALID_RATIONAL_TYPE", oracle.format_decimal_trunc, 1)
        self._assert_err("INT_OUT_OF_RANGE", oracle.format_decimal_trunc, Fraction(1, 2), places=-1)
        self._assert_err("INT_OUT_OF_RANGE", oracle.format_decimal_trunc, Fraction(1, 2), places=25)
        self._assert_err("RATIONAL_TOO_LARGE", oracle.format_decimal_trunc, Fraction(min_fail, 1))
        self._assert_err("RATIONAL_TOO_LARGE", oracle.format_decimal_trunc, Fraction(1, min_fail))

    def test_03_json_tree_strict_parser_and_sha(self) -> None:
        oracle.validate_json_tree_iterative({"a": [1, True, False, None, "ok"]})
        cyc_d: dict[str, Any] = {}
        cyc_d["self"] = cyc_d
        self._assert_err("JSON_CYCLE", oracle.validate_json_tree_iterative, cyc_d)
        cyc_l: list[Any] = []
        cyc_l.append(cyc_l)
        self._assert_err("JSON_CYCLE", oracle.validate_json_tree_iterative, cyc_l)

        # Depth boundary: depth 64 allowed, depth 65 rejected
        deep_ok: Any = 0
        for _ in range(oracle.MAX_JSON_DEPTH):
            deep_ok = [deep_ok]
        oracle.validate_json_tree_iterative(deep_ok)
        self._assert_err("JSON_DEPTH_EXCEEDED", oracle.validate_json_tree_iterative, [deep_ok])
        self._assert_err("INT_OUT_OF_RANGE", oracle.validate_json_tree_iterative, {}, max_depth=0)
        self._assert_err("INT_OUT_OF_RANGE", oracle.validate_json_tree_iterative, {}, max_depth=257)

        self._assert_err("INT_TOO_LARGE", oracle.validate_json_tree_iterative, 1 << oracle.MAX_INT_BITS)
        self._assert_err("FORBIDDEN_JSON_TYPE", oracle.validate_json_tree_iterative, _SubInt(1))
        self._assert_err("FORBIDDEN_JSON_TYPE", oracle.validate_json_tree_iterative, _SubStr("a"))
        self._assert_err("FORBIDDEN_JSON_TYPE", oracle.validate_json_tree_iterative, _SubDict())
        self._assert_err("FORBIDDEN_JSON_TYPE", oracle.validate_json_tree_iterative, _SubList())
        self._assert_err("FORBIDDEN_JSON_TYPE", oracle.validate_json_tree_iterative, (1, 2))
        self._assert_err("INVALID_UTF8_SURROGATE", oracle.validate_json_tree_iterative, {"\ud800": 1})

        self.assertEqual(oracle.parse_strict_json_text('{"x":1}'), {"x": 1})
        self.assertEqual(oracle.parse_strict_json_text("[1,2]", require_object=False), [1, 2])
        self._assert_err("JSON_NOT_OBJECT", oracle.parse_strict_json_text, "[1,2]", require_object=True)
        self._assert_err("DUPLICATE_JSON_KEY", oracle.parse_strict_json_text, '{"a":1,"a":2}')
        self._assert_err("FLOAT_FORBIDDEN", oracle.parse_strict_json_text, '{"a":1.5}')
        self._assert_err("NONFINITE_CONSTANT", oracle.parse_strict_json_text, '{"a":NaN}')
        self._assert_err("NONFINITE_CONSTANT", oracle.parse_strict_json_text, '{"a":Infinity}')
        self._assert_err("INVALID_JSON", oracle.parse_strict_json_text, "{bad")
        self._assert_err("INVALID_JSON", oracle.parse_strict_json_text, '{"big":' + ("9" * 4400) + "}")
        self._assert_err("JSON_DEPTH_EXCEEDED", oracle.parse_strict_json_text, "[" * 2000 + "]" * 2000, require_object=False)

        # UTF-8 multibyte byte cap: 6 chars <= 8 char limit, but 10 UTF-8 bytes > 8
        self.assertEqual(oracle.parse_strict_json_text('"\u00e9\u00e9\u00e9"', require_object=False, max_bytes=8), "\u00e9\u00e9\u00e9")
        self._assert_err("JSON_TOO_LARGE", oracle.parse_strict_json_text, '"\u00e9\u00e9\u00e9\u00e9"', require_object=False, max_bytes=8)
        self._assert_err("INVALID_BOOL", oracle.parse_strict_json_text, "{}", require_object=1)

        self.assertEqual(oracle.canonical_json_bytes({"b": 1, "a": 2}), b'{"a":2,"b":1}')
        self.assertEqual(len(oracle.sha256_hex(b"abc")), 64)
        self._assert_err("INVALID_BYTES", oracle.sha256_hex, "abc")


class Test02PublicMathHelpersAndGuards(unittest.TestCase):
    def _assert_err(self, code: str, fn: Any, *args: Any, **kwargs: Any) -> None:
        with self.assertRaises(oracle.PraxisTomographyError) as ctx:
            fn(*args, **kwargs)
        self.assertEqual(ctx.exception.code, code)

    def test_01_primality_and_pocklington(self) -> None:
        for p in (2, 3, 5, 37, 41, 53, 101, 257, 11003, 405928799, 1670836401704629):
            self.assertTrue(oracle.is_prime_deterministic_small(p), f"expected prime {p}")
        for c in (0, 1, 4, 9, 15, 25, 341, 561, 1105, 1681, 1729, 1763, 3277, 1670836401704629 * 3, 1 << 80):
            self.assertFalse(oracle.is_prime_deterministic_small(c), f"expected composite {c}")
        self._assert_err("INT_OUT_OF_RANGE", oracle.is_prime_deterministic_small, -1)
        self._assert_err("INT_OUT_OF_RANGE", oracle.is_prime_deterministic_small, (1 << 80) + 1)
        self._assert_err("INVALID_INT", oracle.is_prime_deterministic_small, True)

        ok_257 = oracle.verify_pocklington_prime(257, [(2, 8)], 3)
        self.assertTrue(ok_257["verified"])
        self.assertEqual(ok_257["factored_f_bits"], 9)
        bad_base_257 = oracle.verify_pocklington_prime(257, [(2, 8)], 2)
        self.assertFalse(bad_base_257["verified"])
        comp_341 = oracle.verify_pocklington_prime(341, [(5, 1), (17, 1)], 2)
        self.assertFalse(comp_341["verified"])
        comp_15 = oracle.verify_pocklington_prime(15, [(2, 1), (7, 1)], 2)
        self.assertFalse(comp_15["verified"])

        self._assert_err("INVALID_FACTOR_LIST", oracle.verify_pocklington_prime, 257, [], 3)
        self._assert_err("INVALID_FACTOR_LIST", oracle.verify_pocklington_prime, 257, "bad", 3)
        self._assert_err("INVALID_FACTOR_PAIR", oracle.verify_pocklington_prime, 257, [(2,)], 3)
        self._assert_err("INVALID_FACTOR_PAIR", oracle.verify_pocklington_prime, 257, ["bad"], 3)
        self._assert_err("INVALID_FACTOR_PAIR", oracle.verify_pocklington_prime, 257, [_SubList([2, 8])], 3)
        self._assert_err("DUPLICATE_PRIME_FACTOR", oracle.verify_pocklington_prime, 257, [(2, 4), (2, 4)], 3)
        self._assert_err("COMPOSITE_FACTOR", oracle.verify_pocklington_prime, 257, [(4, 4)], 3)
        self._assert_err("POCKLINGTON_DIVISIBILITY", oracle.verify_pocklington_prime, 257, [(3, 4)], 3)
        self._assert_err("POCKLINGTON_F_TOO_SMALL", oracle.verify_pocklington_prime, 257, [(2, 4)], 3)
        self._assert_err("POCKLINGTON_F_TOO_SMALL", oracle.verify_pocklington_prime, 9, [(3, 1)], 2)
        self._assert_err("INT_OUT_OF_RANGE", oracle.verify_pocklington_prime, 257, [(2, 8)], 1)

    def test_02_polynomial_and_extension_helpers(self) -> None:
        q = 5
        self.assertEqual(oracle.poly_add([1, 2], [4, 3], q), [])
        self.assertEqual(oracle.poly_add([1, 2, 0], [3], q), [4, 2])
        self.assertEqual(oracle.poly_sub([1, 2], [1, 2], q), [])
        self.assertEqual(oracle.poly_sub([2, 1], [4], q), [3, 1])
        self.assertEqual(oracle.poly_scale([1, 2], 0, q), [])
        self.assertEqual(oracle.poly_scale([], 3, q), [])
        self.assertEqual(oracle.poly_scale([1, 2], 3, q), [3, 1])
        self.assertEqual(oracle.poly_mul([], [1, 2], q), [])
        self.assertEqual(oracle.poly_mul([1, 2], [], q), [])
        self.assertEqual(oracle.poly_mul([2, 1], [3, 1], q), [1, 0, 1])
        self.assertEqual(oracle.poly_eval([1, 2, 3], 2, q), 2)
        self.assertEqual(oracle.poly_eval([], 2, q), 0)

        quo, rem = oracle.poly_divmod([1, 2], [1, 1, 1], q)
        self.assertEqual((quo, rem), ([], [1, 2]))
        quo2, rem2 = oracle.poly_divmod([1, 0, 1], [1, 1], q)
        self.assertEqual((quo2, rem2), ([4, 1], [2]))
        quo3, rem3 = oracle.poly_divmod([4, 0, 1], [1, 1], q)
        self.assertEqual((quo3, rem3), ([4, 1], []))
        self._assert_err("POLY_DIV_BY_ZERO", oracle.poly_divmod, [1], [], q)

        vp = oracle.poly_vanishing([1, 2], q)
        self.assertEqual(oracle.poly_eval(vp, 1, q), 0)
        self.assertEqual(oracle.poly_eval(vp, 2, q), 0)
        self.assertEqual(oracle.poly_eval(vp, 3, q), 2)
        ip = oracle.poly_interpolate([0, 1, 2], [0, 3, 1], q)
        self.assertEqual([oracle.poly_eval(ip, x, q) for x in (0, 1, 2)], [0, 3, 1])
        self.assertEqual(oracle.poly_sub_scale([0, 1], 0, q), [])
        self.assertEqual(oracle.poly_sub_scale([2, 1], 0, q), [2])
        self.assertEqual(oracle.poly_sub_scale([1, 2, 1], 3, q), [1, 1, 4])

        self._assert_err("MODULUS_NOT_PRIME", oracle.poly_add, [1], [1], 4)
        self._assert_err("INT_OUT_OF_RANGE", oracle.poly_add, [1], [1], 2)
        self._assert_err("INVALID_POLY", oracle.poly_add, "bad", [1], q)
        self._assert_err("INVALID_POINTS", oracle.poly_vanishing, [], q)
        self._assert_err("INVALID_POINTS", oracle.poly_vanishing, "bad", q)
        self._assert_err("INVALID_INTERP", oracle.poly_interpolate, "a", [1], q)
        self._assert_err("INVALID_INTERP", oracle.poly_interpolate, [1], "a", q)
        self._assert_err("INVALID_INTERP", oracle.poly_interpolate, [], [], q)
        self._assert_err("INVALID_INTERP", oracle.poly_interpolate, [1, 2], [1], q)
        self._assert_err("DUPLICATE_INTERP_POINT", oracle.poly_interpolate, [1, 6], [2, 3], q)

        # Extension field helpers over F_257[T]/(T^4 - 3)
        self.assertEqual(oracle.ext_mul_binom([0, 0, 1, 0], [0, 0, 1, 0], 257, 4, 3), [3, 0, 0, 0])
        w4 = pow(3, 64, 257)
        self.assertEqual(oracle.ext_frobenius([1, 2, 3, 4], 4, 257, w4), [1, 2, 3, 4])
        self.assertEqual(oracle.ext_frobenius([1, 1, 0, 0], 1, 257, w4), [1, w4, 0, 0])
        self._assert_err("INVALID_EXT_ELEM", oracle.ext_mul_binom, "ab", [1, 0], 257, 2, 3)
        self._assert_err("INVALID_EXT_ELEM", oracle.ext_mul_binom, [1, 0], "ab", 257, 2, 3)
        self._assert_err("INVALID_EXT_ELEM", oracle.ext_mul_binom, [1], [1, 0], 257, 2, 3)
        self._assert_err("INVALID_EXT_ELEM", oracle.ext_mul_binom, [1, 0], [1], 257, 2, 3)
        self._assert_err("INVALID_EXT_ELEM", oracle.ext_frobenius, [], 1, 257, w4)
        self._assert_err("INVALID_EXT_ELEM", oracle.ext_frobenius, "bad", 1, 257, w4)

        eye3 = [
            [[1, 0], [0, 0], [0, 0]],
            [[0, 0], [1, 0], [0, 0]],
            [[0, 0], [0, 0], [1, 0]],
        ]
        self.assertEqual(oracle.ext_det3_binom(eye3, 257, 2, 3), [1, 0])
        self._assert_err("INVALID_EXT_MAT", oracle.ext_det3_binom, _SubList(eye3), 257, 2, 3)
        self._assert_err("INVALID_EXT_MAT", oracle.ext_det3_binom, eye3[:2], 257, 2, 3)
        self._assert_err("INVALID_EXT_MAT", oracle.ext_det3_binom, [eye3[0], "bad", eye3[2]], 257, 2, 3)
        self._assert_err("INVALID_EXT_MAT", oracle.ext_det3_binom, [eye3[0], eye3[1][:2], eye3[2]], 257, 2, 3)

    def test_03_matrix_helpers_and_lemma_b2_guards(self) -> None:
        self.assertEqual(oracle.fq_matrix_rank([[0, 1], [1, 0]], 5), 2)
        self.assertEqual(oracle.fq_matrix_rank([[0, 0], [0, 1]], 5), 1)
        self.assertEqual(oracle.fq_matrix_rank([[1, 2], [2, 4]], 5), 1)
        self._assert_err("INVALID_MATRIX", oracle.fq_matrix_rank, [], 5)
        self._assert_err("INVALID_MATRIX", oracle.fq_matrix_rank, _SubList([[1]]), 5)
        self._assert_err("INVALID_MATRIX", oracle.fq_matrix_rank, [[]], 5)
        self._assert_err("INVALID_MATRIX", oracle.fq_matrix_rank, [[1, 2], [1]], 5)
        self._assert_err("INVALID_MATRIX", oracle.fq_matrix_rank, [[1, 2], _SubList([3, 4])], 5)

        self.assertEqual(oracle.q_matrix_det([[0, 1], [1, 0]]), Fraction(-1, 1))
        self.assertEqual(oracle.q_matrix_det([[1, 2], [2, 4]]), Fraction(0, 1))
        self.assertEqual(oracle.q_matrix_det([[Fraction(1, 2), Fraction(1, 3)], [Fraction(0, 1), Fraction(2, 1)]]), Fraction(1, 1))
        self._assert_err("INVALID_Q_MATRIX", oracle.q_matrix_det, [])
        self._assert_err("INVALID_Q_MATRIX", oracle.q_matrix_det, _SubList([[1]]))
        self._assert_err("INVALID_Q_MATRIX", oracle.q_matrix_det, [[1, 2], [3]])
        self._assert_err("INVALID_Q_MATRIX", oracle.q_matrix_det, [[1, 2], _SubList([3, 4])])

        self.assertEqual(oracle.q_matrix_rank([[0, 1], [1, 0]]), 2)
        self.assertEqual(oracle.q_matrix_rank([[0, 0], [0, 1]]), 1)
        self.assertEqual(oracle.q_matrix_rank([[1, 2], [2, 4]]), 1)
        self._assert_err("INVALID_Q_MATRIX", oracle.q_matrix_rank, [])
        self._assert_err("INVALID_Q_MATRIX", oracle.q_matrix_rank, _SubList([[1]]))
        self._assert_err("INVALID_Q_MATRIX", oracle.q_matrix_rank, [[]])
        self._assert_err("INVALID_Q_MATRIX", oracle.q_matrix_rank, [[1, 2], [1]])
        self._assert_err("INVALID_Q_MATRIX", oracle.q_matrix_rank, [[1, 2], _SubList([3, 4])])

        val_b2 = oracle.evaluate_lemma_b2_bound(2, 10, 10, 2, Fraction(1, 1000), Fraction(1, 1000), 1 << 120, lam=10)
        self.assertGreater(val_b2, Fraction(0, 1))
        self._assert_err("NEGATIVE_PROB_PARAM", oracle.evaluate_lemma_b2_bound, 2, 10, 10, 2, Fraction(-1, 10), Fraction(0, 1), 100, lam=10)
        self._assert_err("NEGATIVE_PROB_PARAM", oracle.evaluate_lemma_b2_bound, 2, 10, 10, 2, Fraction(0, 1), Fraction(-1, 10), 100, lam=10)


class Test03ZoneBFileIOConcurrencyRacesAndCLI(unittest.TestCase):
    def _assert_err(self, code: str, fn: Any, *args: Any, **kwargs: Any) -> None:
        with self.assertRaises(oracle.PraxisTomographyError) as ctx:
            fn(*args, **kwargs)
        self.assertEqual(ctx.exception.code, code)

    def test_01_safe_path_read_write_and_pwd_guards(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            reg = root / "ok.bin"
            audit.write_regular_file_bytes(reg, b"hello")
            self.assertEqual(stat.S_IMODE(reg.stat().st_mode), 0o600)
            self.assertEqual(audit.read_regular_bytes_capped(reg, max_bytes=5), b"hello")
            self._assert_err("FILE_TOO_LARGE", audit.read_regular_bytes_capped, reg, max_bytes=4)

            # Multi-chunk > 65536 bytes streaming read
            big = root / "big.bin"
            big_bytes = b"A" * 70000
            audit.write_regular_file_bytes(big, big_bytes)
            self.assertEqual(audit.read_regular_bytes_capped(big), big_bytes)

            # Non-existent leaf is allowed by require_safe_path, fails on read
            missing = root / "does_not_exist.json"
            self.assertEqual(audit.require_safe_path(missing), missing)
            self._assert_err("FILE_READ_ERROR", audit.read_regular_bytes_capped, missing)

            # Type, NUL, surrogate, directory, symlink leaf & ancestor, non-dir ancestor
            self._assert_err("INVALID_PATH_TYPE", audit.require_safe_path, str(reg))
            self._assert_err("INVALID_PATH_TYPE", audit.require_safe_path, _SubPath(str(reg)))
            self._assert_err("INVALID_PATH", audit.require_safe_path, Path(str(root) + "/a\x00b"))
            self._assert_err("INVALID_UTF8_SURROGATE", audit.require_safe_path, Path(str(root) + "/bad\ud800"))
            self._assert_err("NON_REGULAR_FILE", audit.require_safe_path, Path("/"))
            self._assert_err("NON_REGULAR_FILE", audit.require_safe_path, root / "..")
            self._assert_err("NON_REGULAR_FILE", audit.read_regular_bytes_capped, root)
            self._assert_err("NON_REGULAR_FILE", audit.write_regular_file_bytes, root, b"x")
            self._assert_err("PATH_STAT_ERROR", audit.require_safe_path, reg / "child")
            self._assert_err("FILE_IO_ERROR", audit.require_safe_path, root / "no_dir" / "child")

            sym_leaf = root / "sym_leaf"
            os.symlink(reg, sym_leaf)
            self._assert_err("SYMLINK_FORBIDDEN", audit.require_safe_path, sym_leaf)
            self._assert_err("SYMLINK_FORBIDDEN", audit.read_regular_bytes_capped, sym_leaf)
            self._assert_err("SYMLINK_FORBIDDEN", audit.write_regular_file_bytes, sym_leaf, b"x")

            sub = root / "sub"
            sub.mkdir()
            sym_dir = root / "sym_dir"
            os.symlink(sub, sym_dir)
            self._assert_err("SYMLINK_FORBIDDEN", audit.require_safe_path, sym_dir / "file.json")

            # FIFO fails closed without blocking on both read and write
            fifo = root / "pipe.fifo"
            os.mkfifo(fifo)
            self._assert_err("NON_REGULAR_FILE", audit.read_regular_bytes_capped, fifo)
            self._assert_err("NON_REGULAR_FILE", audit.write_regular_file_bytes, fifo, b"x")

            # Hardlink target rejection preserves original data
            hl = root / "hl.bin"
            os.link(reg, hl)
            self._assert_err("HARDLINK_FORBIDDEN", audit.write_regular_file_bytes, hl, b"evil")
            self.assertEqual(reg.read_bytes(), b"hello")
            os.unlink(hl)
            # Overwrite succeeds once hardlink removed
            audit.write_regular_file_bytes(reg, b"world")
            self.assertEqual(reg.read_bytes(), b"world")
            self._assert_err("INVALID_WRITE_DATA", audit.write_regular_file_bytes, reg, "str")
            self._assert_err("INVALID_WRITE_DATA", audit.write_regular_file_bytes, reg, bytearray(b"x"))

            # PWD checks on relative paths
            old_cwd = os.getcwd()
            old_pwd = os.environ.get("PWD")
            try:
                os.chdir(sub)
                os.environ["PWD"] = str(sym_dir)
                self._assert_err("SYMLINK_FORBIDDEN", audit.require_safe_path, Path("rel.json"))
                os.environ["PWD"] = "relative/pwd"
                self.assertEqual(audit.require_safe_path(Path("rel.json")), Path("rel.json"))
                os.environ["PWD"] = ""
                self.assertEqual(audit.require_safe_path(Path("rel.json")), Path("rel.json"))
                os.environ.pop("PWD", None)
                self.assertEqual(audit.require_safe_path(Path("rel.json")), Path("rel.json"))
                os.environ["PWD"] = "/bad\udc80"
                self._assert_err("INVALID_UTF8_SURROGATE", audit.require_safe_path, Path("rel.json"))
            finally:
                os.chdir(old_cwd)
                if old_pwd is None:
                    os.environ.pop("PWD", None)
                else:
                    os.environ["PWD"] = old_pwd

            # Deleted CWD fails closed with CWD_UNAVAILABLE
            doomed = root / "doomed"
            doomed.mkdir()
            old_cwd2 = os.getcwd()
            try:
                os.chdir(doomed)
                os.rmdir(doomed)
                self._assert_err("CWD_UNAVAILABLE", audit.require_safe_path, Path("rel.json"))
            finally:
                os.chdir(old_cwd2)

    def test_02_temp_eexist_retry_and_prereplace_hardlink_guard(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            target = root / "out.bin"
            # Pre-create the first candidate name to force EEXIST retry -> succeeds on attempt 2
            orig_token_hex = audit.secrets.token_hex
            orig_fstat = audit.os.fstat
            try:
                audit.secrets.token_hex = lambda _n: "0000000000000000"  # type: ignore[assignment]
                next_seq = audit._TMP_COUNTER + 1
                collider = root / f".s41_praxis_tmp_{os.getpid()}_{next_seq}_0000000000000000"
                collider.write_bytes(b"taken")
                audit.write_regular_file_bytes(target, b"ok-after-retry")
                self.assertEqual(target.read_bytes(), b"ok-after-retry")
                collider.unlink()

                # Exhaust all 32 attempts
                base_seq = audit._TMP_COUNTER + 1
                blockers = []
                for k in range(audit._TMP_MAX_ATTEMPTS):
                    bpath = root / f".s41_praxis_tmp_{os.getpid()}_{base_seq + k}_0000000000000000"
                    bpath.write_bytes(b"block")
                    blockers.append(bpath)
                self._assert_err("TEMP_RETRY_EXHAUSTED", audit.write_regular_file_bytes, target, b"fail")
                for bpath in blockers:
                    bpath.unlink()
            finally:
                audit.secrets.token_hex = orig_token_hex  # type: ignore[assignment]

            # Pre-replace fstat.st_nlink == 2 must abort and clean up temp file
            class _FakeStat:
                st_nlink = 2

            try:
                audit.os.fstat = lambda _fd: _FakeStat()  # type: ignore[assignment]
                self._assert_err("HARDLINK_FORBIDDEN", audit.write_regular_file_bytes, target, b"hijack")
            finally:
                audit.os.fstat = orig_fstat  # type: ignore[assignment]
            leftovers = [p.name for p in root.iterdir() if p.name.startswith(".s41_praxis_tmp_")]
            self.assertEqual(leftovers, [])
            self.assertEqual(target.read_bytes(), b"ok-after-retry")

    def test_03_concurrency_16t_80t_renameat2_and_hardlink_races(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            # 16T distinct files
            errs: list[BaseException] = []
            def _w_distinct(idx: int) -> None:
                try:
                    p = root / f"d_{idx}.bin"
                    data = f"distinct-{idx}-payload".encode("ascii")
                    audit.write_regular_file_bytes(p, data)
                    if p.read_bytes() != data or stat.S_IMODE(p.stat().st_mode) != 0o600:
                        raise RuntimeError("distinct mismatch")
                except BaseException as exc:
                    errs.append(exc)
            ts = [threading.Thread(target=_w_distinct, args=(i,)) for i in range(16)]
            for t in ts:
                t.start()
            for t in ts:
                t.join()
            self.assertEqual(errs, [])

            # 16T same file + 80T barrier burst
            shared = root / "shared.bin"
            valid_payloads = {f"thread-{i:03d}-exact-atomic".encode("ascii") for i in range(80)}
            bar16 = threading.Barrier(16)
            def _w_same(idx: int, bar: threading.Barrier) -> None:
                try:
                    bar.wait()
                    audit.write_regular_file_bytes(shared, f"thread-{idx:03d}-exact-atomic".encode("ascii"))
                except BaseException as exc:
                    errs.append(exc)
            ts16 = [threading.Thread(target=_w_same, args=(i, bar16)) for i in range(16)]
            for t in ts16:
                t.start()
            for t in ts16:
                t.join()
            self.assertEqual(errs, [])
            self.assertIn(shared.read_bytes(), valid_payloads)
            self.assertEqual(stat.S_IMODE(shared.stat().st_mode), 0o600)

            bar80 = threading.Barrier(80)
            ts80 = [threading.Thread(target=_w_same, args=(i, bar80)) for i in range(80)]
            for t in ts80:
                t.start()
            for t in ts80:
                t.join()
            self.assertEqual(errs, [])
            self.assertIn(shared.read_bytes(), valid_payloads)
            self.assertEqual(stat.S_IMODE(shared.stat().st_mode), 0o600)

            # >= 420 hardlink race cycles
            hl_target = root / "hl_race.bin"
            hl_alias = root / "hl_alias.bin"
            audit.write_regular_file_bytes(hl_target, b"initial")
            stop_hl = threading.Event()
            hl_cycles = [0]
            def _hl_toggler() -> None:
                while not stop_hl.is_set() or hl_cycles[0] < 440:
                    try:
                        os.link(hl_target, hl_alias)
                    except OSError:
                        pass
                    try:
                        os.unlink(hl_alias)
                    except OSError:
                        pass
                    hl_cycles[0] += 1
                    if stop_hl.is_set() and hl_cycles[0] >= 440:
                        break
            t_hl = threading.Thread(target=_hl_toggler)
            t_hl.start()
            for i in range(120):
                try:
                    audit.write_regular_file_bytes(hl_target, f"hl-iter-{i}".encode("ascii"))
                except oracle.PraxisTomographyError as exc:
                    self.assertIn(exc.code, ("HARDLINK_FORBIDDEN", "FILE_WRITE_ERROR"))
            stop_hl.set()
            t_hl.join()
            self.assertGreaterEqual(hl_cycles[0], 420)
            if hl_alias.exists():
                hl_alias.unlink()

            # >= 500 renameat2(RENAME_EXCHANGE) directory swap races
            dir_a = root / "slot"
            dir_b = root / "swap_sym"
            dir_real = root / "real_dir"
            dir_a.mkdir()
            dir_real.mkdir()
            os.symlink(dir_real, dir_b)
            (dir_a / "f.bin").write_bytes(b"real-a")
            (dir_real / "f.bin").write_bytes(b"sym-b")
            libc = ctypes.CDLL("libc.so.6", use_errno=True)
            sys_renameat2 = 316
            rename_exchange = 2
            at_fdcwd = -100
            ba = os.fsencode(str(dir_a))
            bb = os.fsencode(str(dir_b))
            swap_cnt = [0]
            stop_sw = threading.Event()
            def _swapper() -> None:
                while not stop_sw.is_set() or swap_cnt[0] < 550:
                    rc_s = libc.syscall(sys_renameat2, at_fdcwd, ba, at_fdcwd, bb, rename_exchange)
                    if rc_s == 0:
                        swap_cnt[0] += 1
                    else:
                        break
                    if stop_sw.is_set() and swap_cnt[0] >= 550:
                        break
            t_sw = threading.Thread(target=_swapper)
            t_sw.start()
            for i in range(150):
                try:
                    audit.read_regular_bytes_capped(dir_a / "f.bin")
                except oracle.PraxisTomographyError as exc:
                    self.assertIn(exc.code, ("SYMLINK_FORBIDDEN", "FILE_READ_ERROR", "PATH_STAT_ERROR", "FILE_IO_ERROR"))
                try:
                    audit.write_regular_file_bytes(dir_a / "w.bin", f"w-{i}".encode("ascii"))
                except oracle.PraxisTomographyError as exc:
                    self.assertIn(exc.code, ("SYMLINK_FORBIDDEN", "FILE_WRITE_ERROR", "PATH_STAT_ERROR", "FILE_IO_ERROR"))
            stop_sw.set()
            t_sw.join()
            self.assertGreaterEqual(swap_cnt[0], 500)

            leaked = [p.name for p in root.rglob(".s41_praxis_tmp_*")]
            self.assertEqual(leaked, [])

    def test_04_strict_cli_argv_matrix_and_file_framing(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            p_cert = root / "c.json"
            rc, out, err = _run_main_captured(["--write", str(p_cert), "--json"])
            self.assertEqual(rc, 0)
            self.assertEqual(err, "")
            self.assertTrue(json.loads(out)["written"])
            self.assertEqual(stat.S_IMODE(p_cert.stat().st_mode), 0o600)

            rc2, out2, err2 = _run_main_captured([f"--check={p_cert}", "--json"])
            self.assertEqual(rc2, 0)
            self.assertEqual(err2, "")
            chk = json.loads(out2)
            self.assertTrue(chk["valid"])
            self.assertTrue(chk["secondary_audit"]["secondary_audit_passed"])

            rc3, out3, err3 = _run_main_captured(["--check", str(p_cert)])
            self.assertEqual(rc3, 0)
            self.assertTrue(out3.startswith("OK "))

            p_cert2 = root / "c2.json"
            rc4, out4, err4 = _run_main_captured([f"--write={p_cert2}"])
            self.assertEqual(rc4, 0)
            self.assertTrue(out4.startswith("OK "))
            self.assertEqual(p_cert2.read_bytes(), p_cert.read_bytes())

            # File framing failures: CRLF, missing LF, invalid UTF-8, non-canonical pretty JSON
            raw = p_cert.read_bytes()
            p_crlf = root / "crlf.json"
            p_crlf.write_bytes(raw[:-1] + b"\r\n")
            self._assert_err("CRLF_FORBIDDEN", audit.check_certificate_file, p_crlf)

            p_nolf = root / "nolf.json"
            p_nolf.write_bytes(raw[:-1])
            self._assert_err("MISSING_TRAILING_LF", audit.check_certificate_file, p_nolf)

            p_utf8 = root / "utf8.json"
            p_utf8.write_bytes(b"\xff\xfe\n")
            self._assert_err("INVALID_UTF8", audit.check_certificate_file, p_utf8)

            p_pretty = root / "pretty.json"
            p_pretty.write_text(json.dumps(json.loads(raw.decode("utf-8")), indent=2) + "\n", encoding="utf-8")
            self._assert_err("NON_CANONICAL_BYTES", audit.check_certificate_file, p_pretty)

            # Rejections leave zero stray files
            before_files = sorted(p.name for p in root.iterdir())
            bad_argvs: list[tuple[Any, str]] = [
                ("not-a-list", "INVALID_ARGV"),
                ([123], "INVALID_ARGV"),
                (["--json", "--json"], "DUPLICATE_FLAG"),
                (["--standalone", "--standalone"], "CONFLICTING_MODE"),
                (["--standalone", "--check", str(p_cert)], "CONFLICTING_MODE"),
                (["--write", str(root / "stray.json"), "--check", str(p_cert)], "CONFLICTING_MODE"),
                (["--standalone", f"--check={p_cert}"], "CONFLICTING_MODE"),
                (["--check"], "MISSING_PATH_ARG"),
                (["--write"], "MISSING_PATH_ARG"),
                (["--write=--json"], "INVALID_PATH_ARG"),
                (["--write", "--json"], "INVALID_PATH_ARG"),
                (["--write="], "INVALID_PATH_ARG"),
                (["--check="], "INVALID_PATH_ARG"),
                (["--check", "-x"], "INVALID_PATH_ARG"),
                (["--sta"], "UNKNOWN_FLAG"),
                (["--ch", str(p_cert)], "UNKNOWN_FLAG"),
                (["--help"], "UNKNOWN_FLAG"),
                (["--check", "bad\ud800"], "INVALID_UTF8_SURROGATE"),
            ]
            for bad_argv, expected_code in bad_argvs:
                rc_b, out_b, err_b = _run_main_captured(bad_argv)
                self.assertEqual(rc_b, 2, f"expected rc=2 for {bad_argv!r}")
                self.assertEqual(out_b, "")
                self.assertEqual(json.loads(err_b)["error_code"], expected_code)
            after_files = sorted(p.name for p in root.iterdir())
            self.assertEqual(before_files, after_files)


class Test04PayloadAndSecondaryAuditTamperMatrix(unittest.TestCase):
    base_cert: dict[str, Any] = {}

    @classmethod
    def setUpClass(cls) -> None:
        cls.base_cert = oracle.build_standalone_certificate()

    def _clone(self) -> dict[str, Any]:
        return copy.deepcopy(self.base_cert)

    def _assert_verify_err(self, cert: Any, code: str, full_replay: bool = False) -> None:
        with self.assertRaises(oracle.PraxisTomographyError) as ctx:
            audit.verify_certificate_dict(cert, full_replay=full_replay)
        self.assertEqual(ctx.exception.code, code)

    def test_01_envelope_and_structural_gates(self) -> None:
        res_f = audit.verify_certificate_dict(self._clone(), full_replay=False)
        self.assertTrue(res_f["valid"])
        self.assertTrue(res_f["secondary_audit"]["secondary_audit_passed"])

        self._assert_verify_err("not-dict", "CERT_NOT_DICT")
        with self.assertRaises(oracle.PraxisTomographyError) as ctx_b:
            oracle.validate_certificate_payload(self._clone(), full_replay=1)  # type: ignore[arg-type]
        self.assertEqual(ctx_b.exception.code, "INVALID_BOOL")

        c = self._clone()
        c["extra"] = 1
        self._assert_verify_err(c, "INVALID_CERT_KEYS")

        c = self._clone()
        c["schema"] = "wrong"
        self._assert_verify_err(c, "INVALID_SCHEMA")

        c = self._clone()
        c["track_id"] = "wrong"
        self._assert_verify_err(c, "INVALID_TRACK_ID")

        c = self._clone()
        c["payload"] = []
        self._assert_verify_err(c, "PAYLOAD_NOT_DICT")

        c = self._clone()
        c["payload"]["oracle_class"] = "tampered"
        self._assert_verify_err(c, "PAYLOAD_SHA_MISMATCH")

        c = self._clone()
        c["certificate_sha256"] = "0" * 64
        self._assert_verify_err(c, "CERT_SHA_MISMATCH")

        # Structural gates on re-signed payloads
        c = self._clone()
        c["payload"]["extra_top"] = 1
        self._assert_verify_err(_resign_cert(c), "INVALID_PAYLOAD_KEYS")

        c = self._clone()
        c["payload"]["oracle_class"] = "approx"
        self._assert_verify_err(_resign_cert(c), "INVALID_PAYLOAD_META")

        c = self._clone()
        c["payload"]["novelty_classification"] = "N0"
        self._assert_verify_err(_resign_cert(c), "INVALID_PAYLOAD_META")

        c = self._clone()
        c["payload"]["zero_floats_exact_arithmetic"] = False
        self._assert_verify_err(_resign_cert(c), "INVALID_PAYLOAD_META")

        c = self._clone()
        c["payload"]["all_verified"] = False
        self._assert_verify_err(_resign_cert(c), "INVALID_PAYLOAD_META")

        c = self._clone()
        c["payload"]["literature_anchors_n0"] = "not-list"
        self._assert_verify_err(_resign_cert(c), "INVALID_PAYLOAD_META")

        c = self._clone()
        c["payload"]["literature_anchors_n0"] = ["only-one"]
        self._assert_verify_err(_resign_cert(c), "INVALID_PAYLOAD_META")

        c = self._clone()
        c["payload"]["literature_anchors_n0"] = [1, 2, 3, 4]
        self._assert_verify_err(_resign_cert(c), "INVALID_STR")

        c = self._clone()
        c["payload"]["literature_anchors_n0"] = ["", "b", "c", "d"]
        self._assert_verify_err(_resign_cert(c), "INVALID_PAYLOAD_META")

        # Direct _validate_payload_structure with 4-tuple rejects non-list anchors
        p_tup = copy.deepcopy(self.base_cert["payload"])
        p_tup["literature_anchors_n0"] = tuple(p_tup["literature_anchors_n0"])
        with self.assertRaises(oracle.PraxisTomographyError) as ctx_tup:
            oracle._validate_payload_structure(p_tup)
        self.assertEqual(ctx_tup.exception.code, "INVALID_PAYLOAD_META")

        c = self._clone()
        c["payload"]["pillar1_executable_praxis_protocol"] = "bad"
        self._assert_verify_err(_resign_cert(c), "INVALID_PILLAR_TYPE")

        c = self._clone()
        c["payload"]["pillar1_executable_praxis_protocol"]["pillar_verified"] = False
        self._assert_verify_err(_resign_cert(c), "PILLAR_NOT_VERIFIED")

        # Bijective bool-vs-int gates
        c = self._clone()
        c["payload"]["pillar1_executable_praxis_protocol"]["field_q"] = True
        self._assert_verify_err(_resign_cert(c), "BOOL_IN_NON_BOOL_FIELD")

        c = self._clone()
        c["payload"]["pillar1_executable_praxis_protocol"]["eq5_tie_divisions_exact"] = 1
        self._assert_verify_err(_resign_cert(c), "NON_BOOL_IN_BOOL_FIELD")

        c = self._clone()
        c["payload"]["pillar1_executable_praxis_protocol"]["chunk_j_delta"] = [True, 5]
        self._assert_verify_err(_resign_cert(c), "BOOL_IN_LIST")

    def test_02_secondary_audit_resigned_tamper_matrix(self) -> None:
        # Direct secondary_audit_payload guards (top-level keys, metadata, anchors, strict types)
        with self.assertRaises(oracle.PraxisTomographyError) as ctx1:
            audit.secondary_audit_payload("not-dict")
        self.assertEqual(ctx1.exception.code, "AUDIT_PAYLOAD_TYPE")
        with self.assertRaises(oracle.PraxisTomographyError) as ctx_k:
            audit.secondary_audit_payload({"all_verified": True})
        self.assertEqual(ctx_k.exception.code, "AUDIT_PAYLOAD_KEYS")
        p_av = copy.deepcopy(self.base_cert["payload"])
        p_av["all_verified"] = False
        with self.assertRaises(oracle.PraxisTomographyError) as ctx2:
            audit.secondary_audit_payload(p_av)
        self.assertEqual(ctx2.exception.code, "AUDIT_ALL_VERIFIED_FALSE")
        for m_key, m_val in (
            ("oracle_class", "approx"),
            ("novelty_classification", "N0"),
            ("zero_floats_exact_arithmetic", False),
        ):
            p_m = copy.deepcopy(self.base_cert["payload"])
            p_m[m_key] = m_val
            with self.assertRaises(oracle.PraxisTomographyError) as ctx_m:
                audit.secondary_audit_payload(p_m)
            self.assertEqual(ctx_m.exception.code, "AUDIT_PAYLOAD_META")

        # Standalone secondary_audit_payload anchor checks (tuple, ints, wrong strings)
        p_anc_tup = copy.deepcopy(self.base_cert["payload"])
        p_anc_tup["literature_anchors_n0"] = tuple(p_anc_tup["literature_anchors_n0"])
        with self.assertRaises(oracle.PraxisTomographyError) as ctx_at:
            audit.secondary_audit_payload(p_anc_tup)
        self.assertEqual(ctx_at.exception.code, "AUDIT_LITERATURE_ANCHORS")
        p_anc_int = copy.deepcopy(self.base_cert["payload"])
        p_anc_int["literature_anchors_n0"] = [1, 2, 3, 4]
        with self.assertRaises(oracle.PraxisTomographyError) as ctx_ai:
            audit.secondary_audit_payload(p_anc_int)
        self.assertEqual(ctx_ai.exception.code, "INVALID_STR")
        p_anc_bad = copy.deepcopy(self.base_cert["payload"])
        p_anc_bad["literature_anchors_n0"] = ["x", "y", "z", "w"]
        with self.assertRaises(oracle.PraxisTomographyError) as ctx_ab:
            audit.secondary_audit_payload(p_anc_bad)
        self.assertEqual(ctx_ab.exception.code, "AUDIT_LITERATURE_ANCHORS")

        # Direct non-list and bool/non-int moore_det_indep_f257_4 in standalone secondary_audit_payload
        p_md_tup = copy.deepcopy(self.base_cert["payload"])
        p_md_tup["pillar2_rank_gap_and_polya_obstructions"]["rank3_linear_tensor_and_moore"]["moore_det_indep_f257_4"] = (0, 0, 96, 0)
        with self.assertRaises(oracle.PraxisTomographyError) as ctx_mt:
            audit.secondary_audit_payload(p_md_tup)
        self.assertEqual(ctx_mt.exception.code, "AUDIT_P2_R3")
        for bad_mdet in ([1, "evil", None, 0], [0, 0, 96, True]):
            p_md_bad = copy.deepcopy(self.base_cert["payload"])
            p_md_bad["pillar2_rank_gap_and_polya_obstructions"]["rank3_linear_tensor_and_moore"]["moore_det_indep_f257_4"] = bad_mdet
            with self.assertRaises(oracle.PraxisTomographyError) as ctx_mb:
                audit.secondary_audit_payload(p_md_bad)
            self.assertEqual(ctx_mb.exception.code, "INVALID_INT")

        # SubDict in pillar1 kills _require_exact_dict_keys type check; 4-tuple table6 kills list check
        p_sub = copy.deepcopy(self.base_cert["payload"])
        p_sub["pillar1_executable_praxis_protocol"] = _SubDict(p_sub["pillar1_executable_praxis_protocol"])
        with self.assertRaises(oracle.PraxisTomographyError) as ctx4:
            audit.secondary_audit_payload(p_sub)
        self.assertEqual(ctx4.exception.code, "AUDIT_P1_KEYS")

        p_t6tup = copy.deepcopy(self.base_cert["payload"])
        p_t6tup["pillar4_honest_scope_and_cs19_bridge"]["table6_lean_vs_paper_deltas"] = tuple(
            p_t6tup["pillar4_honest_scope_and_cs19_bridge"]["table6_lean_vs_paper_deltas"]
        )
        with self.assertRaises(oracle.PraxisTomographyError) as ctx5:
            audit.secondary_audit_payload(p_t6tup)
        self.assertEqual(ctx5.exception.code, "AUDIT_P4_TABLE6")

        tampers: list[tuple[str, Any, str]] = [
            ("top_lit_forged", lambda p: p.__setitem__("literature_anchors_n0", ["x", "y", "z", "w"]), "AUDIT_LITERATURE_ANCHORS"),
            ("p1_extra_key", lambda p: p["pillar1_executable_praxis_protocol"].__setitem__("extra", 1), "AUDIT_P1_KEYS"),
            ("p1_bad_q", lambda p: p["pillar1_executable_praxis_protocol"].__setitem__("field_q", 251), "AUDIT_P1_PARAMS"),
            ("p1_bad_flag", lambda p: p["pillar1_executable_praxis_protocol"].__setitem__("eq7_mask_identity_exact", False), "AUDIT_P1_FLAGS"),
            ("p1_bad_kap", lambda p: p["pillar1_executable_praxis_protocol"].__setitem__("kappa_recovered", 64), "AUDIT_P1_DECRYPT"),
            ("p1_coord_kap1", lambda p: p["pillar1_executable_praxis_protocol"].update({"kappa_expected": 1, "kappa_recovered": 1}), "AUDIT_P1_DECRYPT"),
            ("p1_bad_offset", lambda p: p["pillar1_executable_praxis_protocol"].__setitem__("search_offset_t", 3), "AUDIT_P1_DECRYPT"),
            ("p1_coord_search999", lambda p: p["pillar1_executable_praxis_protocol"].update({"search_center_cw": 999, "search_offset_t": 0, "r_w_exact": 999}), "AUDIT_P1_DECRYPT"),
            ("p1_ct_sha_zero", lambda p: p["pillar1_executable_praxis_protocol"].__setitem__("ciphertext_sha256", "0" * 64), "AUDIT_P1_DECRYPT"),
            ("p1_kap_lo", lambda p: p["pillar1_executable_praxis_protocol"].__setitem__("kappa_expected", 0), "INT_OUT_OF_RANGE"),
            ("p1_kap_hi", lambda p: p["pillar1_executable_praxis_protocol"].__setitem__("kappa_recovered", 257), "INT_OUT_OF_RANGE"),
            ("p2_extra_key", lambda p: p["pillar2_rank_gap_and_polya_obstructions"].__setitem__("extra", 1), "AUDIT_P2_KEYS"),
            ("p2_bad_base", lambda p: p["pillar2_rank_gap_and_polya_obstructions"].__setitem__("example21_unsat_witness_count", 1), "AUDIT_P2_BASE"),
            ("p2_r2_keys", lambda p: p["pillar2_rank_gap_and_polya_obstructions"]["rank2_sos_praxis_cheat"].__setitem__("extra", 1), "AUDIT_P2_R2_KEYS"),
            ("p2_r2_minors_keys", lambda p: p["pillar2_rank_gap_and_polya_obstructions"]["rank2_sos_praxis_cheat"]["principal_minors_by_size"].__setitem__("size_5", []), "AUDIT_P2_R2_MINORS"),
            ("p2_r2_val", lambda p: p["pillar2_rank_gap_and_polya_obstructions"]["rank2_sos_praxis_cheat"].__setitem__("fig4_f101_det", 69), "AUDIT_P2_R2"),
            ("p2_r3_keys", lambda p: p["pillar2_rank_gap_and_polya_obstructions"]["rank3_linear_tensor_and_moore"].__setitem__("extra", 1), "AUDIT_P2_R3_KEYS"),
            ("p2_r3_mdet_zero", lambda p: p["pillar2_rank_gap_and_polya_obstructions"]["rank3_linear_tensor_and_moore"].__setitem__("moore_det_indep_f257_4", [0, 0, 0, 0]), "AUDIT_P2_R3"),
            ("p2_r3_mdet_forged", lambda p: p["pillar2_rank_gap_and_polya_obstructions"]["rank3_linear_tensor_and_moore"].__setitem__("moore_det_indep_f257_4", [1, 0, 0, 0]), "AUDIT_P2_R3"),
            ("p2_r3_mdet_shortcircuit", lambda p: p["pillar2_rank_gap_and_polya_obstructions"]["rank3_linear_tensor_and_moore"].__setitem__("moore_det_indep_f257_4", [1, "evil", None, 0]), "INVALID_INT"),
            ("p2_r3_mdet_len", lambda p: p["pillar2_rank_gap_and_polya_obstructions"]["rank3_linear_tensor_and_moore"].__setitem__("moore_det_indep_f257_4", [1, 2, 3]), "AUDIT_P2_R3"),
            ("p2_r4_keys", lambda p: p["pillar2_rank_gap_and_polya_obstructions"]["rank4_alternating_sum_cheat"].__setitem__("extra", 1), "AUDIT_P2_R4_KEYS"),
            ("p2_r4_rank", lambda p: p["pillar2_rank_gap_and_polya_obstructions"]["rank4_alternating_sum_cheat"].__setitem__("exact_rank_f257", 3), "AUDIT_P2_R4"),
            ("p2_pol_keys", lambda p: p["pillar2_rank_gap_and_polya_obstructions"]["polya_1913_obstruction"].__setitem__("extra", 1), "AUDIT_P2_POLYA_KEYS"),
            ("p2_pol_val", lambda p: p["pillar2_rank_gap_and_polya_obstructions"]["polya_1913_obstruction"].__setitem__("z_valid_sign_flip_count", 1), "AUDIT_P2_POLYA"),
            ("p3_keys", lambda p: p["pillar3_table4_admissibility_and_hair_sahai"].__setitem__("extra", 1), "AUDIT_P3_KEYS"),
            ("p3_t4_keys", lambda p: p["pillar3_table4_admissibility_and_hair_sahai"]["table4_core"].__setitem__("extra", 1), "AUDIT_P3_T4_KEYS"),
            ("p3_p57_keys", lambda p: p["pillar3_table4_admissibility_and_hair_sahai"]["prop57_counts"].__setitem__("extra", 1), "AUDIT_P3_P57_KEYS"),
            ("p3_b2_keys", lambda p: p["pillar3_table4_admissibility_and_hair_sahai"]["lemma_b2"].__setitem__("extra", 1), "AUDIT_P3_B2_KEYS"),
            ("p3_hs_keys", lambda p: p["pillar3_table4_admissibility_and_hair_sahai"]["appendix_c_hair_sahai"].__setitem__("extra", 1), "AUDIT_P3_HS_KEYS"),
            ("p3_t4_val", lambda p: p["pillar3_table4_admissibility_and_hair_sahai"]["table4_core"].__setitem__("n", 4607), "AUDIT_P3_TABLE4"),
            ("p3_flag", lambda p: p["pillar3_table4_admissibility_and_hair_sahai"].__setitem__("capelli_irreducible_t4608_minus_5", False), "AUDIT_P3_FLAGS"),
            ("p3_p57_val", lambda p: p["pillar3_table4_admissibility_and_hair_sahai"]["prop57_counts"].__setitem__("L", 208296360), "AUDIT_P3_PROP57"),
            ("p3_b2_val", lambda p: p["pillar3_table4_admissibility_and_hair_sahai"]["lemma_b2"].__setitem__("E_diff_margin_trunc8", "0.00000080"), "AUDIT_P3_LEMMAB2"),
            ("p3_hs_val", lambda p: p["pillar3_table4_admissibility_and_hair_sahai"]["appendix_c_hair_sahai"].__setitem__("R", 3), "AUDIT_P3_HAIR_SAHAI"),
            ("p4_keys", lambda p: p["pillar4_honest_scope_and_cs19_bridge"].__setitem__("extra", 1), "AUDIT_P4_KEYS"),
            ("p4_sec_keys", lambda p: p["pillar4_honest_scope_and_cs19_bridge"]["security_accounting"].__setitem__("extra", 1), "AUDIT_P4_SEC_KEYS"),
            ("p4_cs19_keys", lambda p: p["pillar4_honest_scope_and_cs19_bridge"]["cs19_sealed_witness_bridge"].__setitem__("extra", 1), "AUDIT_P4_CS19_KEYS"),
            ("p4_sec_val", lambda p: p["pillar4_honest_scope_and_cs19_bridge"]["security_accounting"].__setitem__("bn254_etnfs_bits", 104), "AUDIT_P4_SECURITY"),
            ("p4_t6_nonlist", lambda p: p["pillar4_honest_scope_and_cs19_bridge"].__setitem__("table6_lean_vs_paper_deltas", {}), "AUDIT_P4_TABLE6"),
            ("p4_t6_len", lambda p: p["pillar4_honest_scope_and_cs19_bridge"]["table6_lean_vs_paper_deltas"].pop(), "AUDIT_P4_TABLE6"),
            ("p4_t6_empty", lambda p: p["pillar4_honest_scope_and_cs19_bridge"]["table6_lean_vs_paper_deltas"][0].__setitem__("lean_scope", ""), "AUDIT_P4_TABLE6"),
            ("p4_t6_forged_lean", lambda p: p["pillar4_honest_scope_and_cs19_bridge"]["table6_lean_vs_paper_deltas"][0].__setitem__("lean_scope", "FORGED"), "AUDIT_P4_TABLE6"),
            ("p4_t6_forged_paper", lambda p: p["pillar4_honest_scope_and_cs19_bridge"]["table6_lean_vs_paper_deltas"][0].__setitem__("paper_scope", "FORGED"), "AUDIT_P4_TABLE6"),
            ("p4_t6_ids", lambda p: p["pillar4_honest_scope_and_cs19_bridge"]["table6_lean_vs_paper_deltas"][0].__setitem__("id", "T6-99"), "AUDIT_P4_TABLE6"),
            ("p4_cs19_sha_zero", lambda p: p["pillar4_honest_scope_and_cs19_bridge"]["cs19_sealed_witness_bridge"].__setitem__("commitment_ciphertext_sha256", "0" * 64), "AUDIT_P4_CS19"),
            ("p4_cs19_kap99", lambda p: p["pillar4_honest_scope_and_cs19_bridge"]["cs19_sealed_witness_bridge"].__setitem__("valid_witness_kappa", 99), "AUDIT_P4_CS19"),
            ("p4_cs19_kap0", lambda p: p["pillar4_honest_scope_and_cs19_bridge"]["cs19_sealed_witness_bridge"].__setitem__("valid_witness_kappa", 0), "INT_OUT_OF_RANGE"),
            ("p4_cs19_kap257", lambda p: p["pillar4_honest_scope_and_cs19_bridge"]["cs19_sealed_witness_bridge"].__setitem__("valid_witness_kappa", 257), "INT_OUT_OF_RANGE"),
            ("p4_cs19_status", lambda p: p["pillar4_honest_scope_and_cs19_bridge"]["cs19_sealed_witness_bridge"].__setitem__("invalid_witness_status", "OK"), "AUDIT_P4_CS19"),
        ]
        self.assertGreaterEqual(len(tampers), 48)
        for name, mutator, expected_code in tampers:
            c = self._clone()
            mutator(c["payload"])
            _resign_cert(c)
            with self.subTest(tamper=name):
                self._assert_verify_err(c, expected_code, full_replay=False)
                with self.assertRaises(oracle.PraxisTomographyError) as ctx_s:
                    audit.secondary_audit_payload(c["payload"])
                self.assertEqual(ctx_s.exception.code, expected_code)

        # Verify oracle.validate_certificate_payload(full_replay=True) catches re-signed drift independently
        c_narr = self._clone()
        c_narr["payload"]["literature_anchors_n0"][0] = "Altered Anchor"
        _resign_cert(c_narr)
        self.assertTrue(oracle.validate_certificate_payload(c_narr, full_replay=False)["valid"])
        with self.assertRaises(oracle.PraxisTomographyError) as ctx_r:
            oracle.validate_certificate_payload(c_narr, full_replay=True)
        self.assertEqual(ctx_r.exception.code, "RECOMPUTATION_MISMATCH")
        self._assert_verify_err(c_narr, "AUDIT_LITERATURE_ANCHORS", full_replay=False)
        self._assert_verify_err(c_narr, "RECOMPUTATION_MISMATCH", full_replay=True)


class Test99EndToEndPillarsAndCLI(unittest.TestCase):
    def test_01_all_four_pillars_and_cli_standalone(self) -> None:
        cert = oracle.build_standalone_certificate()
        res = audit.verify_certificate_dict(cert, full_replay=True)
        self.assertTrue(res["valid"])
        self.assertTrue(res["secondary_audit"]["secondary_audit_passed"])
        self.assertEqual(res["secondary_audit"]["pillars_checked"], 4)
        self.assertEqual(res["secondary_audit"]["table6_deltas_checked"], 4)
        self.assertEqual(res["secondary_audit"]["polya_matrices_checked"], 512)

        p1 = cert["payload"]["pillar1_executable_praxis_protocol"]
        self.assertEqual(p1["field_q"], 257)
        self.assertEqual(p1["kappa_expected"], 65)
        self.assertEqual(p1["kappa_recovered"], 65)
        self.assertEqual(p1["search_center_cw"] + p1["search_offset_t"], p1["r_w_exact"])
        self.assertTrue(p1["pillar_verified"])

        p2 = cert["payload"]["pillar2_rank_gap_and_polya_obstructions"]
        self.assertEqual(p2["example21_true_witness_count"], 1)
        self.assertEqual(p2["example21_unsat_witness_count"], 0)
        self.assertEqual(p2["rank2_sos_praxis_cheat"]["fig4_f101_det"], 68)
        self.assertEqual(p2["rank3_linear_tensor_and_moore"]["moore_det_indep_f257_4"], [0, 0, 96, 0])
        self.assertEqual(p2["rank4_alternating_sum_cheat"]["exact_rank_f257"], 4)
        self.assertEqual(p2["polya_1913_obstruction"]["f2_perm_eq_det_count"], 512)
        self.assertEqual(p2["polya_1913_obstruction"]["z_valid_sign_flip_count"], 0)
        self.assertEqual(p2["polya_1913_obstruction"]["max_permutation_matches_out_of_6"], 5)

        p3 = cert["payload"]["pillar3_table4_admissibility_and_hair_sahai"]
        self.assertEqual(p3["bn254_q_str"], str(oracle.BN254_Q))
        self.assertEqual(p3["pocklington_factored_f_bits"], 161)
        self.assertEqual(p3["prop57_counts"]["L"], 208296361)
        self.assertEqual(p3["lemma_b2"]["E_diff_margin_trunc8"], "0.00000081")
        self.assertEqual(p3["appendix_c_hair_sahai"]["K"], 219348150)
        self.assertEqual(p3["appendix_c_hair_sahai"]["m"], 85917354266100)
        self.assertEqual(p3["appendix_c_hair_sahai"]["k_prop_c1_lower_bound"], 39888960295450910)

        p4 = cert["payload"]["pillar4_honest_scope_and_cs19_bridge"]
        self.assertEqual(p4["security_accounting"]["reduction_loss_bits"], "9/2")
        self.assertEqual(p4["security_accounting"]["reduction_loss_decimal"], "4.5")
        self.assertEqual(p4["security_accounting"]["etnfs_margin_above_ggm_bits"], 3)
        self.assertEqual(p4["cs19_sealed_witness_bridge"]["valid_witness_kappa"], 21)
        self.assertTrue(p4["cs19_sealed_witness_bridge"]["valid_witness_unmasked_exact"])
        self.assertTrue(p4["cs19_sealed_witness_bridge"]["invalid_witness_rejected"])

        # CLI standalone (default zero-arg and --standalone --json)
        rc0, out0, err0 = _run_main_captured([])
        self.assertEqual(rc0, 0)
        self.assertEqual(err0, "")
        self.assertIn(cert["certificate_sha256"], out0)

        rc1, out1, err1 = _run_main_captured(["--standalone", "--json"])
        self.assertEqual(rc1, 0)
        self.assertEqual(err1, "")
        self.assertEqual(json.loads(out1), cert)

        # Subprocess invocation checks sys.argv[1:] path
        proc = subprocess.run(
            [sys.executable, "-I", "-B", str(Path(_THIS_DIR) / "praxis_we_tomography_audit.py"), "--standalone", "--json"],
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(proc.returncode, 0)
        self.assertEqual(json.loads(proc.stdout)["certificate_sha256"], cert["certificate_sha256"])


if __name__ == "__main__":
    unittest.main()
