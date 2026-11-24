#!/usr/bin/env python3
"""Track S22a (AUDIT-122A R2) R1-R5 Adversarial Verification & Mutation-Kill Suite.

Covers:
  1. Theorem 1: Quasi-modular E_2 <-> E_4 (E_8 shells) / E_6 / E_8 / Delta / Leech Theta,
     perfect-defect operator (6n-1)*delta_perf(n), and strict q-series input guards.
  2. Theorem 2: Euclid-Euler bijection, 12 Mersenne prime Lucas-Lehmer certificates up to M_127,
     Z[sqrt(3)] trace invariant, exhaustive sieve <= 10,000, and D3 divisibility-checked
     verify_mersenne_factor_euler.
  3. Theorem 3: Perfect fixed points, 5 amicable pairs, Poulet 5- & 28-cycles, terminating &
     aspiring controls, D2 exact LTE prime-power driver proof (incl. (3,3) check), D4 strict
     classify_aliquot_driver_tag guards, and 26-term Lehmer-5 276 trajectory.
  4. Strict type, RFC 8259 ASCII int, 4000-bit / 10**4300 caps, cyclic JSON, full-cardinality
     secondary_audit_payload (full_replay=True and full_replay=False), and certificate tamper tests.
  5. R2-grade Zone-B hardening: D1 atomic dir_fd traversal, D5 hardlink refusal & pre-replace
     st_nlink==1 + EEXIST retry + 0o600 mode, D6 strict CLI argv (rejecting `--check --json`
     and stray flags), deleted CWD, streaming >64 KiB reads, 16T/80T concurrency, live >=520-iter
     renameat2(RENAME_EXCHANGE), and live >=420-iter hardlink races.

100% pure Python 3 stdlib, ZERO bare asserts, ZERO AST float literals, ZERO float() calls.
"""
from __future__ import annotations

import copy
import ctypes
from fractions import Fraction
import hashlib
import io
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import threading
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import perfect_quasi_modular_audit as audit  # noqa: E402
import perfect_quasi_modular_oracle as oracle  # noqa: E402

_AT_FDCWD = -100
_RENAME_EXCHANGE = 2


class _IntSub(int):
    pass


class _StrSub(str):
    pass


class _PathSub(type(Path())):
    pass


class _ListSub(list):
    pass


class _DictSub(dict):
    pass


def _flip_hex(h: str) -> str:
    return ("0" if h[0] != "0" else "1") + h[1:]


def _resign(cert_copy: dict) -> dict:
    p_sha = hashlib.sha256(oracle.canonical_json_bytes(cert_copy["payload"])).hexdigest()
    cert_copy["payload_sha256"] = p_sha
    env = {
        "schema": cert_copy["schema"],
        "track_id": cert_copy["track_id"],
        "payload_sha256": p_sha,
        "payload": cert_copy["payload"],
    }
    cert_copy["certificate_sha256"] = hashlib.sha256(oracle.canonical_json_bytes(env)).hexdigest()
    return cert_copy


def _get_renameat2():
    libc = ctypes.CDLL("libc.so.6", use_errno=True)
    fn = libc.renameat2
    fn.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
    fn.restype = ctypes.c_int
    return fn


class TestTrackS22aPerfectQuasiModularR2(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.cert = oracle.build_certificate()

    def _expect_err(self, code: str, fn) -> None:
        with self.assertRaises(oracle.PerfectModularError) as ctx:
            fn()
        self.assertEqual(ctx.exception.code, code)

    # ------------------------------------------------------------------
    # 1. Theorem 1: Quasi-Modular E_2 <-> E_4 (E_8) / Delta / Leech
    # ------------------------------------------------------------------
    def test_01_theorem1_quasi_modular_and_leech_bridge(self) -> None:
        t1 = self.cert["payload"]["theorem1_quasi_modular_e2_e4_leech"]
        self.assertTrue(t1["all_passed"])
        self.assertEqual(t1["degree_verified"], 36)
        self.assertTrue(t1["ode1_12thetaE2_eq_E2sq_minus_E4"])
        self.assertTrue(t1["ode2_3thetaE4_eq_E2E4_minus_E6"])
        self.assertTrue(t1["ode3_2thetaE6_eq_E2E6_minus_E4sq"])
        self.assertTrue(t1["e4_sq_equals_e8"])
        self.assertTrue(t1["ramanujan_sigma1_sigma3_convolution_exact"])
        self.assertTrue(t1["perfect_defect_operator_law_exact"])
        self.assertEqual(t1["perfect_numbers_detected_up_to_deg"], [6, 28])
        self.assertEqual(t1["tau_first_6"], [1, -24, 252, -1472, 4830, -6048])
        self.assertEqual(t1["leech_theta_first_5"], [1, 0, 196560, 16773120, 398034000])
        self.assertTrue(t1["delta_exact_divisible_1728_and_matches_euler_product"])
        self.assertTrue(t1["hecke_multiplicativity_ok"])
        self.assertTrue(t1["hecke_prime_square_recurrence_ok"])
        self.assertTrue(t1["leech_theta_exact_bridge_ok"])
        self.assertTrue(t1["naive_modular_anomaly_drop_refuted"])

        w = t1["spot_witnesses"]
        self.assertEqual(w["n_6"]["r_E8_shell_240_sigma3"], 60480)
        self.assertEqual(w["n_6"]["delta_perf"], 0)
        self.assertEqual(w["n_6"]["perfect_operator_residual"], 0)
        self.assertEqual(w["n_10"]["delta_perf"], -2)
        self.assertEqual(w["n_10"]["perfect_operator_residual"], -118)
        self.assertEqual(w["n_12"]["delta_perf"], 4)
        self.assertEqual(w["n_12"]["perfect_operator_residual"], 284)
        self.assertEqual(w["n_28"]["r_E8_shell_240_sigma3"], 6026880)
        self.assertEqual(w["n_28"]["perfect_operator_residual"], 0)

        self.assertEqual(oracle.sigma_k(1, 0), 1)
        self.assertEqual(oracle.sigma_k(12, 0), 6)
        self.assertEqual(oracle.sigma_k(28, 1), 56)
        self.assertEqual(oracle.perfect_defect(28), 0)
        self.assertEqual(oracle.perfect_defect(10), -2)
        self.assertEqual(oracle.qseries_mul([1, 2], [3, 4], 1), [3, 10])
        self.assertEqual(oracle.qseries_mul([0, 2], [3, 4], 1), [0, 6])
        self.assertEqual(oracle.qseries_mul([5], [7], 0), [35])
        self.assertEqual(oracle.qseries_theta([5, 7, 11]), [0, 7, 22])
        self._expect_err("SERIES_LENGTH", lambda: oracle.qseries_mul([1], [1, 2], 1))
        self._expect_err("SERIES_LENGTH", lambda: oracle.qseries_mul([1, 2], [1], 1))
        self._expect_err("INVALID_SERIES_TYPE", lambda: oracle.qseries_mul((1, 2), [1, 2], 1))  # type: ignore[arg-type]
        self._expect_err("INVALID_INT_TYPE", lambda: oracle.qseries_mul([3 / 2, 1], [1, 2], 1))  # type: ignore[list-item]
        self._expect_err("SERIES_LENGTH", lambda: oracle.qseries_theta([]))
        self._expect_err("INVALID_INT_TYPE", lambda: oracle.qseries_theta([True]))
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.certify_theorem1_quasi_modular_bridge(27))
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.certify_theorem1_quasi_modular_bridge(65))
        t1_min = oracle.certify_theorem1_quasi_modular_bridge(28)
        self.assertTrue(t1_min["all_passed"])

    # ------------------------------------------------------------------
    # 2. Theorem 2: Euclid-Euler, Lucas-Lehmer, & D3 Divisibility Check
    # ------------------------------------------------------------------
    def test_02_theorem2_mersenne_lucas_lehmer_and_sieve(self) -> None:
        t2 = self.cert["payload"]["theorem2_mersenne_lucas_lehmer_euclid_euler"]
        self.assertTrue(t2["all_passed"])
        self.assertEqual(t2["mersenne_prime_exponents_certified"], [2, 3, 5, 7, 13, 17, 19, 31, 61, 89, 107, 127])
        self.assertTrue(t2["first_12_all_lucas_lehmer_prime_and_euclid_euler"])
        self.assertTrue(t2["direct_factorization_sigma_first_5_ok"])
        self.assertTrue(t2["z_sqrt3_trace_invariant_ok"])
        self.assertEqual(t2["exhaustive_sieve_up_to_10000"], [6, 28, 496, 8128])
        self.assertEqual(t2["m127_even_perfect_str"], str((1 << 126) * ((1 << 127) - 1)))
        self.assertTrue(t2["all_composite_counterexamples_certified"])
        self.assertEqual(len(t2["composite_mersenne_counterexamples"]), 5)
        self.assertEqual(t2["composite_mersenne_counterexamples"][0]["ll_nonzero_residue_str"], "1736")
        self.assertEqual(t2["composite_mersenne_counterexamples"][4]["p"], 67)

        for n, want in ((0, False), (1, False), (2, True), (3, True), (4, False), (9, False), (25, False), (49, False), (29, True), (37, True), (10**14, False)):
            self.assertEqual(oracle.is_prime_exact(n), want)
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.is_prime_exact(10**14 + 1))
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.is_prime_exact(10**18 + 3))
        self._expect_err("NOT_PRIME_EXPONENT", lambda: oracle.lucas_lehmer_certificate(4))
        self._expect_err("NOT_PRIME_EXPONENT", lambda: oracle.lucas_lehmer_certificate(9))
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.lucas_lehmer_certificate(1))
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.lucas_lehmer_certificate(522))
        self._expect_err("NOT_PRIME_EXPONENT", lambda: oracle.verify_z_sqrt3_lucas_invariant(9))
        self.assertFalse(oracle.verify_z_sqrt3_lucas_invariant(5, s0=3))
        self.assertFalse(oracle.verify_z_sqrt3_lucas_invariant(5, s0=27))

        # D3 closure: verify_mersenne_factor_euler must check prime p AND exact divisibility pow(2, p, q) == 1
        self.assertTrue(oracle.verify_mersenne_factor_euler(11, 23))
        self.assertTrue(oracle.verify_mersenne_factor_euler(11, 89))
        self.assertFalse(oracle.verify_mersenne_factor_euler(11, 15))   # composite q
        self.assertFalse(oracle.verify_mersenne_factor_euler(11, 17))   # fails 2p|(q-1)
        self.assertFalse(oracle.verify_mersenne_factor_euler(11, 67))   # fails q==+-1 mod 8
        self.assertFalse(oracle.verify_mersenne_factor_euler(11, 199))  # prime, 22|198, 199==7 mod 8, YET 199 !| M_11!
        self.assertFalse(oracle.verify_mersenne_factor_euler(11, 2047))  # composite divisor of M_11 satisfying 22|2046 & 7 mod 8!
        self._expect_err("NOT_PRIME_EXPONENT", lambda: oracle.verify_mersenne_factor_euler(9, 73))
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.verify_mersenne_factor_euler(2, 3))
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.verify_z_sqrt3_lucas_invariant(2))
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.verify_z_sqrt3_lucas_invariant(14))
        self.assertEqual(oracle.sieve_perfect_numbers_up_to(1), [])
        self.assertEqual(oracle.sieve_perfect_numbers_up_to(6), [6])
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.sieve_perfect_numbers_up_to(0))
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.sieve_perfect_numbers_up_to(20_001))

    # ------------------------------------------------------------------
    # 3. Theorem 3: Aliquot Dynamics, D2 LTE Proof, D4 Tag Guard, Lehmer 276
    # ------------------------------------------------------------------
    def test_03_theorem3_aliquot_drivers_and_lehmer276(self) -> None:
        t3 = self.cert["payload"]["theorem3_aliquot_dynamics_drivers_lehmer276"]
        self.assertTrue(t3["all_passed"])
        self.assertTrue(t3["perfect_fixed_points_ok"])
        self.assertEqual(t3["amicable_pairs_certified"], 5)
        self.assertTrue(t3["amicable_all_ok"])
        self.assertTrue(t3["poulet_5_cycle"]["verified"])
        self.assertEqual(t3["poulet_5_cycle"]["period"], 5)
        self.assertTrue(t3["poulet_28_cycle"]["verified"])
        self.assertEqual(t3["poulet_28_cycle"]["period"], 28)
        self.assertTrue(t3["terminating_control_ok"])
        self.assertTrue(t3["aspiring_95_25_6_ok"])

        drv = t3["guy_selfridge_driver_classification"]
        self.assertTrue(drv["verified"])
        self.assertEqual(drv["non_perfect_prime_power_drivers_found"], [2, 24])
        self.assertEqual(drv["even_perfect_drivers_found_count"], 7)
        self.assertTrue(drv["composite_3perfect_drivers_120_672_523776_ok"])
        self.assertTrue(drv["guide_12_correctly_rejected_as_driver"])

        # D2 LTE direct checks including the (p, e) = (3, 3) case
        self.assertEqual(oracle.v2_exact(1), 0)
        self.assertEqual(oracle.v2_exact(40), 3)
        self.assertEqual(oracle.v2_exact(oracle.sigma_k(27, 1)), oracle.v2_exact(4) + oracle.v2_exact(4) - 1)
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.v2_exact(0))

        self.assertTrue(oracle.is_guy_selfridge_driver_condition(1, 1))
        self.assertTrue(oracle.is_guy_selfridge_driver_condition(3, 3))
        self.assertFalse(oracle.is_guy_selfridge_driver_condition(2, 3))
        self.assertFalse(oracle.is_guy_selfridge_driver_condition(4, 1))

        # D4 strict exact-int guards on classify_aliquot_driver_tag
        self.assertEqual(oracle.classify_aliquot_driver_tag(28, 2), "driver_28_perfect")
        self.assertEqual(oracle.classify_aliquot_driver_tag(56, 3), "transition")
        self.assertEqual(oracle.classify_aliquot_driver_tag(20, 2), "transition")
        self.assertEqual(oracle.classify_aliquot_driver_tag(24, 3), "driver_24_abundant")
        self.assertEqual(oracle.classify_aliquot_driver_tag(48, 4), "transition")
        self.assertEqual(oracle.classify_aliquot_driver_tag(40, 3), "transition")
        self.assertEqual(oracle.classify_aliquot_driver_tag(10, 1), "downdriver_2")
        self._expect_err("INVALID_INT_TYPE", lambda: oracle.classify_aliquot_driver_tag(56 / 2, 2))  # type: ignore[arg-type]
        self._expect_err("INVALID_INT_TYPE", lambda: oracle.classify_aliquot_driver_tag(28, 4 / 2))  # type: ignore[arg-type]
        self._expect_err("INVALID_INT_TYPE", lambda: oracle.classify_aliquot_driver_tag(True, 0))
        self._expect_err("INVALID_INT_TYPE", lambda: oracle.classify_aliquot_driver_tag(28, True))
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.classify_aliquot_driver_tag(0, 0))
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.classify_aliquot_driver_tag(28, -1))

        self._expect_err("EVEN_ODD_PART", lambda: oracle.is_guy_selfridge_driver_condition(1, 2))
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.verify_prime_power_driver_classification_bound(3))
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.verify_prime_power_driver_classification_bound(31))

        bad_cyc = oracle.trace_aliquot_cycle_exact(220, 1)
        self.assertFalse(bad_cyc["verified"])
        self.assertFalse(bad_cyc["closes_exact"])
        dup_cyc = oracle.trace_aliquot_cycle_exact(6, 2)
        self.assertFalse(dup_cyc["verified"])
        self.assertFalse(dup_cyc["all_vertices_distinct"])
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.trace_aliquot_cycle_exact(1, 1))
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.trace_aliquot_cycle_exact(6, 0))
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.trace_aliquot_cycle_exact(6, 65))

        l276 = t3["lehmer_276_driver_trajectory"]
        self.assertTrue(l276["verified"])
        self.assertEqual(l276["a0"], 276)
        self.assertEqual(l276["a_final"], 465780)
        self.assertEqual(l276["consecutive_driver_28_steps"], 18)
        self.assertEqual(l276["lehmer5_abundancies"]["276"], "56/23")
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.trace_lehmer276_driver_trajectory(9))
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.trace_lehmer276_driver_trajectory(26))
        l276_10 = oracle.trace_lehmer276_driver_trajectory(10)
        self.assertTrue(l276_10["verified"])
        self.assertEqual(l276_10["a_final"], 5964)

    # ------------------------------------------------------------------
    # 4. Strict Type, RFC 8259 JSON, Secondary Audit, & Tamper Controls
    # ------------------------------------------------------------------
    def test_04_strict_type_json_secondary_and_certificate_guards(self) -> None:
        self._expect_err("INVALID_CONDITION_TYPE", lambda: oracle.require_ok(1, "C", "m"))  # type: ignore[arg-type]
        self._expect_err("TEST_FAIL", lambda: oracle.require_ok(False, "TEST_FAIL", "m"))

        self.assertEqual(oracle.require_exact_int(0, "x", lo=0, hi=0), 0)
        self.assertEqual(oracle.require_exact_int((1 << 4000) - 1, "x"), (1 << 4000) - 1)
        self._expect_err("INVALID_INT_TYPE", lambda: oracle.require_exact_int(True, "x"))
        self._expect_err("INVALID_INT_TYPE", lambda: oracle.require_exact_int(_IntSub(5), "x"))
        self._expect_err("INVALID_INT_TYPE", lambda: oracle.require_exact_int(2 / 1, "x"))
        self._expect_err("INT_BIT_LIMIT", lambda: oracle.require_exact_int(1 << 4000, "x"))
        self._expect_err("INVALID_BOUND_TYPE", lambda: oracle.require_exact_int(5, "x", lo=True))
        self._expect_err("INVALID_BOUND_TYPE", lambda: oracle.require_exact_int(5, "x", hi=False))
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.require_exact_int(4, "x", lo=5))
        self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.require_exact_int(6, "x", hi=5))

        self.assertIs(oracle.require_bool(True, "b"), True)
        self._expect_err("INVALID_BOOL_TYPE", lambda: oracle.require_bool(1, "b"))
        self.assertEqual(oracle.require_str("ok", "s"), "ok")
        self._expect_err("INVALID_STR_TYPE", lambda: oracle.require_str(_StrSub("ok"), "s"))
        self._expect_err("INVALID_STR_CHAR", lambda: oracle.require_str("a\x00b", "s"))
        self._expect_err("INVALID_STR_CHAR", lambda: oracle.require_str("a\ud800b", "s"))
        self._expect_err("INVALID_STR_CHAR", lambda: oracle.require_str("a\udfffb", "s"))

        valid_hex = "0123456789abcdef" * 4
        self.assertEqual(oracle.require_hex64_lower_ascii(valid_hex, "h"), valid_hex)
        self._expect_err("INVALID_HEX64", lambda: oracle.require_hex64_lower_ascii(valid_hex[:-1], "h"))
        self._expect_err("INVALID_HEX64", lambda: oracle.require_hex64_lower_ascii(valid_hex.upper(), "h"))
        self._expect_err("INVALID_HEX64", lambda: oracle.require_hex64_lower_ascii("\u00e9" * 64, "h"))
        self._expect_err("INVALID_HEX64", lambda: oracle.require_hex64_lower_ascii(123, "h"))

        # Rational bit cap (<= 4000 bits, strictly safe below Python's 4300-digit str limit)
        self.assertEqual(oracle.format_rational(Fraction(6, 2)), "3")
        self.assertEqual(oracle.format_rational(Fraction(28, 11)), "28/11")
        self.assertTrue(len(oracle.format_rational(Fraction((1 << 4000) - 1, 1))) < 1300)
        self._expect_err("INVALID_FRACTION", lambda: oracle.format_rational(3))  # type: ignore[arg-type]
        self._expect_err("RATIONAL_BIT_LIMIT", lambda: oracle.format_rational(Fraction(1 << 4000, 1)))
        self._expect_err("RATIONAL_BIT_LIMIT", lambda: oracle.format_rational(Fraction(1, 1 << 4000)))
        self._expect_err("RATIONAL_BIT_LIMIT", lambda: oracle.format_rational(Fraction(10**4300, 1)))

        # Direct RFC 8259 ASCII-only bounded int parser checks (1205 digits <-> 4000 bits round-trip symmetric!)
        self.assertEqual(oracle._parse_bounded_int("0"), 0)
        self.assertEqual(oracle._parse_bounded_int("-123"), -123)
        max_4000 = (1 << 4000) - 1
        self.assertEqual(len(str(max_4000)), oracle.MAX_INT_DIGITS)
        self.assertEqual(oracle._parse_bounded_int(str(max_4000)), max_4000)
        self.assertEqual(oracle.parse_strict_json_text(oracle.canonical_json_bytes({"x": max_4000}).decode("utf-8")), {"x": max_4000})
        self.assertEqual(oracle.parse_strict_json_text(oracle.canonical_json_bytes({"x": -max_4000}).decode("utf-8")), {"x": -max_4000})
        self._expect_err("INVALID_JSON_INT", lambda: oracle._parse_bounded_int(""))
        self._expect_err("INVALID_JSON_INT", lambda: oracle._parse_bounded_int(123))  # type: ignore[arg-type]
        self._expect_err("INT_DIGIT_LIMIT", lambda: oracle._parse_bounded_int("-"))
        self._expect_err("INT_DIGIT_LIMIT", lambda: oracle._parse_bounded_int("9" * (oracle.MAX_INT_DIGITS + 1)))
        self._expect_err("INVALID_JSON_INT", lambda: oracle._parse_bounded_int("\u0661\u0662"))
        self._expect_err("INVALID_JSON_INT", lambda: oracle._parse_bounded_int("01"))
        self._expect_err("INVALID_JSON_INT", lambda: oracle._parse_bounded_int("-0"))

        # Strict JSON text parser & canonical_json_bytes
        self.assertEqual(oracle.parse_strict_json_text('{"a":1,"b":[true,null,"x"]}'), {"a": 1, "b": [True, None, "x"]})
        self.assertEqual(oracle.parse_strict_json_text("[1,2]", require_object=False), [1, 2])
        self.assertEqual(oracle.parse_strict_json_text(f'{{"n": -{max_4000}}}'), {"n": -max_4000})
        self._expect_err("BOM_FORBIDDEN", lambda: oracle.parse_strict_json_text('\ufeff{"a":1}'))
        exact_1m_json = '{"a":"' + ("x" * (oracle.MAX_JSON_BYTES - 8)) + '"}'
        self.assertEqual(len(exact_1m_json.encode("utf-8")), oracle.MAX_JSON_BYTES)
        self.assertEqual(len(oracle.parse_strict_json_text(exact_1m_json)["a"]), oracle.MAX_JSON_BYTES - 8)
        self._expect_err("JSON_TOO_LARGE", lambda: oracle.parse_strict_json_text('{"a":"' + ("x" * oracle.MAX_JSON_BYTES) + '"}'))
        self._expect_err("INT_DIGIT_LIMIT", lambda: oracle.parse_strict_json_text(f'{{"n": {"9" * (oracle.MAX_INT_DIGITS + 1)}}}'))
        self._expect_err("INT_BIT_LIMIT", lambda: oracle.parse_strict_json_text(f'{{"n": {1 << 4000}}}'))
        self._expect_err("FLOAT_FORBIDDEN", lambda: oracle.parse_strict_json_text('{"x": 1.5}'))
        self._expect_err("NONFINITE_CONSTANT", lambda: oracle.parse_strict_json_text('{"x": NaN}'))
        self._expect_err("DUPLICATE_KEY", lambda: oracle.parse_strict_json_text('{"a": 1, "a": 2}'))
        self._expect_err("JSON_PARSE_ERROR", lambda: oracle.parse_strict_json_text("{bad"))
        self._expect_err("JSON_ROOT_NOT_OBJECT", lambda: oracle.parse_strict_json_text("[1, 2]"))
        self._expect_err("INVALID_BOOL_TYPE", lambda: oracle.parse_strict_json_text("{}", require_object=1))  # type: ignore[arg-type]
        d64 = '{"a":' * 64 + '1' + '}' * 64
        d65 = '{"a":' * 65 + '1' + '}' * 65
        oracle.parse_strict_json_text(d64)
        self._expect_err("JSON_DEPTH_EXCEEDED", lambda: oracle.parse_strict_json_text(d65))

        self.assertIn(b"x", oracle.canonical_json_bytes({"x": (1 << 4000) - 1}))
        self._expect_err("FORBIDDEN_JSON_TYPE", lambda: oracle.canonical_json_bytes({"x": 3 / 2}))
        self._expect_err("INT_BIT_LIMIT", lambda: oracle.canonical_json_bytes({"x": 1 << 4000}))
        self._expect_err("INT_BIT_LIMIT", lambda: oracle.canonical_json_bytes({"x": 10**4300}))
        cyc: dict = {}
        cyc["self"] = cyc
        self._expect_err("JSON_DEPTH_EXCEEDED", lambda: oracle.canonical_json_bytes(cyc))

        # Certificate verification under both full_replay=True and full_replay=False
        self.assertTrue(audit.verify_certificate_dict(copy.deepcopy(self.cert), full_replay=True)["valid"])
        self.assertTrue(audit.verify_certificate_dict(copy.deepcopy(self.cert), full_replay=False)["valid"])
        self._expect_err("INVALID_BOOL_TYPE", lambda: audit.verify_certificate_dict(copy.deepcopy(self.cert), full_replay=1))  # type: ignore[arg-type]
        self._expect_err("CERT_NOT_DICT", lambda: oracle.validate_certificate_payload([]))
        bad_keys = copy.deepcopy(self.cert)
        bad_keys["extra"] = 1
        self._expect_err("CERT_KEYS_MISMATCH", lambda: oracle.validate_certificate_payload(bad_keys))
        bad_schema = copy.deepcopy(self.cert)
        bad_schema["schema"] = "wrong"
        self._expect_err("CERT_SCHEMA_MISMATCH", lambda: oracle.validate_certificate_payload(bad_schema))
        bad_track = copy.deepcopy(self.cert)
        bad_track["track_id"] = "wrong"
        self._expect_err("CERT_TRACK_MISMATCH", lambda: oracle.validate_certificate_payload(bad_track))
        bad_pay_type = copy.deepcopy(self.cert)
        bad_pay_type["payload"] = []
        self._expect_err("PAYLOAD_NOT_DICT", lambda: oracle.validate_certificate_payload(bad_pay_type))
        bad_p_sha = copy.deepcopy(self.cert)
        bad_p_sha["payload_sha256"] = _flip_hex(bad_p_sha["payload_sha256"])
        self._expect_err("PAYLOAD_SHA_MISMATCH", lambda: oracle.validate_certificate_payload(bad_p_sha))
        bad_c_sha = copy.deepcopy(self.cert)
        bad_c_sha["certificate_sha256"] = _flip_hex(bad_c_sha["certificate_sha256"])
        self._expect_err("CERT_SHA_MISMATCH", lambda: oracle.validate_certificate_payload(bad_c_sha))

        # Re-signed tampered payloads MUST fail closed even under full_replay=False!
        def _tamper_nonreplay(mutator) -> None:
            c = copy.deepcopy(self.cert)
            mutator(c["payload"])
            _resign(c)
            self._expect_err("SECONDARY_AUDIT_FAILED", lambda: audit.verify_certificate_dict(c, full_replay=False))

        _tamper_nonreplay(lambda p: p.__setitem__("all_passed", 1))
        _tamper_nonreplay(lambda p: p.pop("audit_id"))
        _tamper_nonreplay(lambda p: p.__setitem__("theorem1_quasi_modular_e2_e4_leech", []))
        _tamper_nonreplay(lambda p: p["theorem1_quasi_modular_e2_e4_leech"].__setitem__("degree_verified", True))
        _tamper_nonreplay(lambda p: p["theorem1_quasi_modular_e2_e4_leech"]["tau_first_6"].__setitem__(0, True))
        _tamper_nonreplay(lambda p: p["theorem1_quasi_modular_e2_e4_leech"]["leech_theta_first_5"].__setitem__(1, False))
        _tamper_nonreplay(lambda p: p["theorem1_quasi_modular_e2_e4_leech"].__setitem__("perfect_numbers_detected_up_to_deg", []))
        _tamper_nonreplay(lambda p: p["theorem1_quasi_modular_e2_e4_leech"].__setitem__("perfect_numbers_detected_up_to_deg", 123))
        _tamper_nonreplay(lambda p: p["theorem1_quasi_modular_e2_e4_leech"]["spot_witnesses"].pop("n_6"))
        _tamper_nonreplay(lambda p: p["theorem1_quasi_modular_e2_e4_leech"]["spot_witnesses"]["n_6"].pop("sigma_1"))
        _tamper_nonreplay(lambda p: p["theorem1_quasi_modular_e2_e4_leech"]["spot_witnesses"]["n_6"].__setitem__("sigma_1", True))
        _tamper_nonreplay(lambda p: p["theorem1_quasi_modular_e2_e4_leech"]["spot_witnesses"]["n_6"].__setitem__("r_E8_shell_240_sigma3", 1))
        _tamper_nonreplay(lambda p: p["theorem2_mersenne_lucas_lehmer_euclid_euler"].__setitem__("composite_mersenne_counterexamples", []))
        _tamper_nonreplay(lambda p: p["theorem2_mersenne_lucas_lehmer_euclid_euler"].__setitem__("composite_mersenne_counterexamples", 0))
        _tamper_nonreplay(lambda p: p["theorem2_mersenne_lucas_lehmer_euclid_euler"].__setitem__("composite_mersenne_counterexamples", None))
        _tamper_nonreplay(lambda p: p["theorem2_mersenne_lucas_lehmer_euclid_euler"].__setitem__("composite_mersenne_counterexamples", "12345"))
        _tamper_nonreplay(lambda p: p["theorem2_mersenne_lucas_lehmer_euclid_euler"]["composite_mersenne_counterexamples"][0].pop("p"))
        _tamper_nonreplay(lambda p: p["theorem2_mersenne_lucas_lehmer_euclid_euler"]["composite_mersenne_counterexamples"][0].__setitem__("ll_nonzero_residue_str", "0"))
        _tamper_nonreplay(lambda p: p["theorem2_mersenne_lucas_lehmer_euclid_euler"]["composite_mersenne_counterexamples"][0].__setitem__("ll_nonzero_residue_str", 0))
        _tamper_nonreplay(lambda p: p["theorem2_mersenne_lucas_lehmer_euclid_euler"]["composite_mersenne_counterexamples"][0].__setitem__("ll_nonzero_residue_str", None))
        _tamper_nonreplay(lambda p: p["theorem2_mersenne_lucas_lehmer_euclid_euler"]["composite_mersenne_counterexamples"][0].__setitem__("ll_nonzero_residue_str", "999999"))
        _tamper_nonreplay(lambda p: p["theorem2_mersenne_lucas_lehmer_euclid_euler"]["composite_mersenne_counterexamples"][4].__setitem__("ll_nonzero_residue_str", "1"))
        _tamper_nonreplay(lambda p: p["theorem3_aliquot_dynamics_drivers_lehmer276"].__setitem__("amicable_pairs_certified", True))
        _tamper_nonreplay(lambda p: p["theorem3_aliquot_dynamics_drivers_lehmer276"]["poulet_5_cycle"].pop("start"))
        _tamper_nonreplay(lambda p: p["theorem3_aliquot_dynamics_drivers_lehmer276"]["lehmer_276_driver_trajectory"].__setitem__("a_final", 0))
        _tamper_nonreplay(lambda p: p["theorem3_aliquot_dynamics_drivers_lehmer276"]["lehmer_276_driver_trajectory"]["lehmer5_first_steps"].pop("276"))
        _tamper_nonreplay(lambda p: p["theorem3_aliquot_dynamics_drivers_lehmer276"]["lehmer_276_driver_trajectory"]["lehmer5_abundancies"].__setitem__("276", "1"))

        # Forged LL residue drift is rejected under BOTH full_replay=False and direct secondary_audit_payload
        drift = copy.deepcopy(self.cert)
        drift["payload"]["theorem2_mersenne_lucas_lehmer_euclid_euler"]["composite_mersenne_counterexamples"][0]["ll_nonzero_residue_str"] = "1737"
        _resign(drift)
        self._expect_err("SECONDARY_AUDIT_FAILED", lambda: audit.verify_certificate_dict(drift, full_replay=False))
        self._expect_err("SECONDARY_AUDIT_FAILED", lambda: oracle.secondary_audit_payload(drift["payload"]))

        # Direct secondary_audit_payload rejects subclass and float injections via _validate_json_tree_iterative
        for mut_sub in (
            lambda p: p.__setitem__("audit_id", _StrSub("AUDIT-122A")),
            lambda p: p["theorem1_quasi_modular_e2_e4_leech"].__setitem__("degree_verified", _IntSub(36)),
            lambda p: p["theorem2_mersenne_lucas_lehmer_euclid_euler"]["composite_mersenne_counterexamples"][0].__setitem__(
                "prime_factors_str", _ListSub(["23", "89"])
            ),
            lambda p: p["theorem3_aliquot_dynamics_drivers_lehmer276"].__setitem__(
                "poulet_5_cycle", _DictSub(p["theorem3_aliquot_dynamics_drivers_lehmer276"]["poulet_5_cycle"])
            ),
            lambda p: p["theorem1_quasi_modular_e2_e4_leech"].__setitem__("degree_verified", 3 / 2),
        ):
            p_sub = copy.deepcopy(self.cert["payload"])
            mut_sub(p_sub)
            self._expect_err("FORBIDDEN_JSON_TYPE", lambda ps=p_sub: oracle.secondary_audit_payload(ps))

        # Live CLI --check on scalar comp_list / ll_nonzero_residue_str must exit rc=2 JSON FAIL (never raw TypeError traceback)
        with tempfile.TemporaryDirectory() as td_cli:
            for lbl, mut_c in (
                ("comp_int", lambda p: p["theorem2_mersenne_lucas_lehmer_euclid_euler"].__setitem__("composite_mersenne_counterexamples", 0)),
                ("comp_none", lambda p: p["theorem2_mersenne_lucas_lehmer_euclid_euler"].__setitem__("composite_mersenne_counterexamples", None)),
                ("ll_int", lambda p: p["theorem2_mersenne_lucas_lehmer_euclid_euler"]["composite_mersenne_counterexamples"][0].__setitem__("ll_nonzero_residue_str", 0)),
                ("ll_none", lambda p: p["theorem2_mersenne_lucas_lehmer_euclid_euler"]["composite_mersenne_counterexamples"][0].__setitem__("ll_nonzero_residue_str", None)),
            ):
                c_cli = copy.deepcopy(self.cert)
                mut_c(c_cli["payload"])
                _resign(c_cli)
                p_cli = Path(td_cli) / f"{lbl}.json"
                p_cli.write_bytes(oracle.canonical_json_bytes(c_cli) + b"\n")
                proc = subprocess.run(
                    [sys.executable, "-I", "-B", str(HERE / "perfect_quasi_modular_audit.py"), "--check", str(p_cli)],
                    capture_output=True,
                    text=True,
                    timeout=30,
                )
                self.assertEqual(proc.returncode, 1, lbl)
                self.assertEqual(proc.stdout, "", lbl)
                self.assertNotIn("Traceback", proc.stderr, lbl)
                err_j = json.loads(proc.stderr)
                self.assertEqual(err_j["status"], "FAIL", lbl)
                self.assertEqual(err_j["code"], "SECONDARY_AUDIT_FAILED", lbl)

        # full_replay=True canonical replay mismatch check
        alt_expected = copy.deepcopy(self.cert)
        alt_expected["payload_sha256"] = _flip_hex(alt_expected["payload_sha256"])
        with mock.patch.object(oracle, "build_certificate", return_value=alt_expected):
            self._expect_err("CANONICAL_CERT_MISMATCH", lambda: audit.verify_certificate_dict(copy.deepcopy(self.cert), full_replay=True))

    # ------------------------------------------------------------------
    # 5. Zone-B Atomic dir_fd, D1/D5/D6, Hardlink/renameat2/16T/80T Races
    # ------------------------------------------------------------------
    def test_05_zone_b_dirfd_hardlinks_cli_and_live_races(self) -> None:
        self._expect_err("INVALID_PATH_TYPE", lambda: oracle.require_concrete_path("not_a_path", "p"))
        self._expect_err("INVALID_PATH_TYPE", lambda: oracle.require_concrete_path(_PathSub("x"), "p"))
        self._expect_err("INVALID_BYTES_TYPE", lambda: oracle.write_regular_bytes_safe(Path("/nonexistent/x"), "str"))  # type: ignore[arg-type]
        self._expect_err("INVALID_PATH", lambda: oracle.read_regular_bytes_capped(Path("")))
        self._expect_err("INVALID_PATH", lambda: oracle.read_regular_bytes_capped(Path(".")))
        self._expect_err("INVALID_PATH", lambda: oracle.read_regular_bytes_capped(Path("/")))
        self._expect_err("INVALID_PATH", lambda: oracle.read_regular_bytes_capped(Path("a/..")))

        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            real_sub = root / "real_sub"
            real_sub.mkdir()
            cert_file = real_sub / "cert.json"
            cert_text = oracle.canonical_json_bytes(self.cert).decode("utf-8") + "\n"
            oracle.write_regular_utf8_file(cert_file, cert_text)
            self.assertEqual(stat.S_IMODE(os.lstat(cert_file).st_mode), 0o600)
            self.assertTrue(oracle.verify_certificate_file(cert_file)["valid"])
            self.assertTrue(oracle.verify_certificate_file(cert_file, full_replay=False)["valid"])

            # Non-canonical bytes (CRLF and pretty-printed JSON) rejected
            crlf_file = root / "crlf.json"
            crlf_file.write_bytes(cert_text.replace("\n", "\r\n").encode("utf-8"))
            self._expect_err("CRLF_FORBIDDEN", lambda: oracle.verify_certificate_file(crlf_file))
            pretty_file = root / "pretty.json"
            pretty_file.write_text(json.dumps(self.cert, indent=2, sort_keys=True) + "\n", encoding="utf-8")
            self._expect_err("NONCANONICAL_CERT_BYTES", lambda: oracle.verify_certificate_file(pretty_file))

            # D1: Direct symlink, intermediate symlink, & lexical sym_dir/../real_sub/cert.json
            sym_file = root / "sym_cert.json"
            os.symlink(cert_file, sym_file)
            self._expect_err("SYMLINK_FORBIDDEN", lambda: oracle.read_regular_utf8_file(sym_file))
            self._expect_err("SYMLINK_FORBIDDEN", lambda: oracle.write_regular_utf8_file(sym_file, "{}"))
            sym_dir = root / "sym_dir"
            os.symlink(real_sub, sym_dir)
            self._expect_err("SYMLINK_FORBIDDEN", lambda: oracle.read_regular_utf8_file(sym_dir / "cert.json"))
            self._expect_err("SYMLINK_FORBIDDEN", lambda: oracle.read_regular_utf8_file(sym_dir / ".." / "real_sub" / "cert.json"))
            self._expect_err("SYMLINK_FORBIDDEN", lambda: oracle.write_regular_utf8_file(sym_dir / "out.json", "{}"))
            # Regular file used as intermediate directory component
            self._expect_err("FILE_READ_ERROR", lambda: oracle.read_regular_utf8_file(cert_file / "child.json"))

            # Directory & FIFO rejection (zero hang!)
            self._expect_err("NOT_A_REGULAR_FILE", lambda: oracle.read_regular_utf8_file(real_sub))
            self._expect_err("NOT_A_REGULAR_FILE", lambda: oracle.write_regular_utf8_file(real_sub, "{}"))
            fifo_path = root / "pipe.fifo"
            os.mkfifo(fifo_path)
            self._expect_err("NOT_A_REGULAR_FILE", lambda: oracle.read_regular_utf8_file(fifo_path))
            self._expect_err("NOT_A_REGULAR_FILE", lambda: oracle.write_regular_utf8_file(fifo_path, "{}"))

            # Streaming >64 KiB read, max_bytes bounds, chmod 000, BOM, bad UTF-8, oversized
            stream_file = root / "stream70k.bin"
            payload_70k = b"z" * 70_000
            stream_file.write_bytes(payload_70k)
            self.assertEqual(oracle.read_regular_bytes_capped(stream_file, max_bytes=70_000), payload_70k)
            self._expect_err("FILE_TOO_LARGE", lambda: oracle.read_regular_bytes_capped(stream_file, max_bytes=69_999))
            self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.read_regular_bytes_capped(stream_file, max_bytes=0))
            self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.read_regular_bytes_capped(stream_file, max_bytes=oracle.MAX_READ_CAP_BYTES + 1))
            self._expect_err("INT_OUT_OF_RANGE", lambda: oracle.read_regular_bytes_capped(stream_file, max_bytes=1 << 100))

            unreadable = root / "chmod000.json"
            unreadable.write_bytes(b"{}")
            os.chmod(unreadable, 0o000)
            try:
                if os.geteuid() != 0:
                    self._expect_err("FILE_READ_ERROR", lambda: oracle.read_regular_bytes_capped(unreadable))
            finally:
                os.chmod(unreadable, 0o600)

            self._expect_err("FILE_READ_ERROR", lambda: oracle.read_regular_utf8_file(root / "missing.json"))
            self._expect_err("FILE_WRITE_ERROR", lambda: oracle.write_regular_utf8_file(root / "no_dir" / "out.json", "{}"))
            bom_file = root / "bom.json"
            bom_file.write_bytes(b"\xef\xbb\xbf{}")
            self._expect_err("BOM_FORBIDDEN", lambda: oracle.read_regular_utf8_file(bom_file))
            bad_utf8 = root / "bad.bin"
            bad_utf8.write_bytes(b"\xff\xfe")
            self._expect_err("INVALID_UTF8", lambda: oracle.read_regular_utf8_file(bad_utf8))
            exact_file = root / "exact_1m.txt"
            exact_file.write_bytes(b"a" * oracle.MAX_JSON_BYTES)
            self.assertEqual(len(oracle.read_regular_utf8_file(exact_file)), oracle.MAX_JSON_BYTES)
            big_file = root / "big.json"
            big_file.write_bytes(b" " * (oracle.MAX_JSON_BYTES + 1))
            self._expect_err("FILE_TOO_LARGE", lambda: oracle.read_regular_utf8_file(big_file))

            # D5: Pre-existing hardlink target refused (peer untouched)
            hl_a = root / "hl_target.json"
            hl_b = root / "hl_peer.json"
            hl_a.write_bytes(b"original-peer")
            os.link(hl_a, hl_b)
            self._expect_err("HARDLINK_FORBIDDEN", lambda: oracle.write_regular_bytes_safe(hl_a, b"overwrite"))
            self.assertEqual(hl_b.read_bytes(), b"original-peer")

            # D5: Live pre-replace fstat(tmp_fd).st_nlink == 1 probe via os.fsync hook
            tmp_probe_dir = root / "tmp_probe"
            tmp_probe_dir.mkdir()
            probe_target = tmp_probe_dir / "target.json"
            probe_evil = tmp_probe_dir / "evil_hardlink"
            orig_fsync = os.fsync
            linked_once = False

            def _hijack_fsync(fd_arg: int) -> None:
                nonlocal linked_once
                if not linked_once:
                    for name in os.listdir(tmp_probe_dir):
                        if name.startswith(".s22a_tmp_"):
                            os.link(tmp_probe_dir / name, probe_evil)
                            linked_once = True
                            break
                orig_fsync(fd_arg)

            os.fsync = _hijack_fsync  # type: ignore[assignment]
            try:
                self._expect_err("HARDLINK_FORBIDDEN", lambda: oracle.write_regular_bytes_safe(probe_target, b"x"))
            finally:
                os.fsync = orig_fsync  # type: ignore[assignment]
            self.assertTrue(linked_once)
            self.assertFalse(probe_target.exists())
            self.assertEqual([n for n in os.listdir(tmp_probe_dir) if n.startswith(".s22a_tmp_")], [])

            # D5: EEXIST retry success and exhaustion
            eexist_dir = root / "eexist"
            eexist_dir.mkdir()
            orig_open = os.open
            state = {"fail_left": 1}

            def _flaky_open(path_arg, flags, mode=0o777, *, dir_fd=None):
                if isinstance(path_arg, str) and path_arg.startswith(".s22a_tmp_") and state["fail_left"] > 0:
                    state["fail_left"] -= 1
                    raise FileExistsError("simulated collision")
                return orig_open(path_arg, flags, mode, dir_fd=dir_fd)

            os.open = _flaky_open  # type: ignore[assignment]
            try:
                oracle.write_regular_bytes_safe(eexist_dir / "ok.json", b"retry-ok")
                state["fail_left"] = 20
                self._expect_err("TEMP_EXHAUSTED", lambda: oracle.write_regular_bytes_safe(eexist_dir / "fail.json", b"x"))
            finally:
                os.open = orig_open  # type: ignore[assignment]
            self.assertEqual((eexist_dir / "ok.json").read_bytes(), b"retry-ok")

            # Symlinked PWD, relative PWD, stale nonexistent PWD, & deleted CWD
            env_sym = {**os.environ, "PWD": str(sym_dir), "PYTHONDONTWRITEBYTECODE": "1"}
            proc_pwd = subprocess.run(
                [sys.executable, "-I", "-O", "-B", "-W", "error", str(HERE / "perfect_quasi_modular_audit.py"), "--check", "cert.json"],
                cwd=str(real_sub),
                env=env_sym,
                capture_output=True,
                text=True,
            )
            self.assertEqual(proc_pwd.returncode, 1)
            self.assertIn("SYMLINK_FORBIDDEN", proc_pwd.stderr)

            env_rel_pwd = {**os.environ, "PWD": "rel/" + str(sym_dir).lstrip("/"), "PYTHONDONTWRITEBYTECODE": "1"}
            proc_rel_pwd = subprocess.run(
                [sys.executable, "-I", "-O", "-B", "-W", "error", str(HERE / "perfect_quasi_modular_audit.py"), "--check", "cert.json"],
                cwd=str(real_sub),
                env=env_rel_pwd,
                capture_output=True,
                text=True,
            )
            self.assertEqual(proc_rel_pwd.returncode, 0)

            env_stale = {**os.environ, "PWD": str(root / "nonexistent_pwd"), "PYTHONDONTWRITEBYTECODE": "1"}
            proc_ok = subprocess.run(
                [sys.executable, "-I", "-O", "-B", "-W", "error", str(HERE / "perfect_quasi_modular_audit.py"), "--check", "cert.json"],
                cwd=str(real_sub),
                env=env_stale,
                capture_output=True,
                text=True,
            )
            self.assertEqual(proc_ok.returncode, 0)
            self.assertIn('"valid":true', proc_ok.stdout)

            # Deleted CWD check -> CWD_UNAVAILABLE
            del_dir = root / "deleted_cwd"
            del_dir.mkdir()
            proc_del = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    "-c",
                    f"import os, sys; sys.path.insert(0, {str(HERE)!r}); import perfect_quasi_modular_audit as a; "
                    f"os.chdir({str(del_dir)!r}); os.rmdir({str(del_dir)!r}); "
                    f"os.environ.pop('PWD', None); raise SystemExit(a.main(['--check', 'cert.json']))",
                ],
                capture_output=True,
                text=True,
            )
            self.assertEqual(proc_del.returncode, 1)
            self.assertIn("CWD_UNAVAILABLE", proc_del.stderr)

            # D6: Strict CLI modes & exact-form refusals (incl. --check --json!)
            def _run_cli(argv) -> tuple[int, str, str]:
                old_out, old_err = sys.stdout, sys.stderr
                buf_out_bytes = io.BytesIO()
                buf_out_text = io.TextIOWrapper(buf_out_bytes, encoding="utf-8")
                buf_err = io.StringIO()
                sys.stdout, sys.stderr = buf_out_text, buf_err
                try:
                    rc = audit.main(argv)
                    buf_out_text.flush()
                finally:
                    sys.stdout, sys.stderr = old_out, old_err
                return rc, buf_out_bytes.getvalue().decode("utf-8"), buf_err.getvalue()

            rc, out_zero, _ = _run_cli([])
            self.assertEqual(rc, 0)
            self.assertEqual(out_zero, cert_text)

            rc, out_s, _ = _run_cli(["--standalone", "--json"])
            self.assertEqual(rc, 0)
            self.assertEqual(out_s, cert_text)

            out_w = root / "written.json"
            rc, out_ws, _ = _run_cli(["--write", str(out_w)])
            self.assertEqual(rc, 0)
            self.assertIn('"status":"WROTE"', out_ws)
            self.assertEqual(stat.S_IMODE(os.lstat(out_w).st_mode), 0o600)

            rc, out_cs, _ = _run_cli(["--check", str(out_w)])
            self.assertEqual(rc, 0)
            self.assertIn('"valid":true', out_cs)

            orig_def = audit.DEFAULT_CERT_PATH
            audit.DEFAULT_CERT_PATH = root / "default_written.json"
            try:
                rc_def, _, _ = _run_cli(["--write"])
                self.assertEqual(rc_def, 0)
                self.assertTrue(audit.DEFAULT_CERT_PATH.is_file())
            finally:
                audit.DEFAULT_CERT_PATH = orig_def

            for bad_argv, expected_code in (
                ("not_a_list", "INVALID_ARGV_TYPE"),
                ([123], "INVALID_STR_TYPE"),
                ([_StrSub("--json")], "INVALID_STR_TYPE"),
                (["\ud800"], "INVALID_STR_CHAR"),
                (["--standalone"], "INVALID_CLI_ARGS"),
                (["--standalone", "--json", "--json"], "INVALID_CLI_ARGS"),
                (["--check"], "INVALID_CLI_ARGS"),
                (["--check", "--json"], "INVALID_PATH_ARG"),
                (["--check", "-bad"], "INVALID_PATH_ARG"),
                (["--check", ""], "INVALID_PATH_ARG"),
                (["--check", str(out_w), "--json"], "INVALID_CLI_ARGS"),
                (["--write", "--json"], "INVALID_PATH_ARG"),
                (["--write", "-bad"], "INVALID_PATH_ARG"),
                (["--write", str(out_w), "--json"], "INVALID_CLI_ARGS"),
                (["--standalone", "--write"], "INVALID_CLI_ARGS"),
                (["--bogus"], "INVALID_CLI_ARGS"),
            ):
                rc_b, _, err_b = _run_cli(bad_argv)  # type: ignore[arg-type]
                self.assertEqual(rc_b, 1, f"Expected rc=1 for {bad_argv!r}")
                self.assertIn(expected_code, err_b)

            # Live concurrency: 16T distinct, 16T same-target, 80T burst
            conc_dir = root / "conc"
            conc_dir.mkdir()
            errs: list[BaseException] = []

            def _w_distinct(idx: int) -> None:
                try:
                    for j in range(4):
                        p = conc_dir / f"d_{idx}.json"
                        oracle.write_regular_bytes_safe(p, f"{idx}:{j}".encode("ascii"))
                except BaseException as exc:
                    errs.append(exc)

            ts = [threading.Thread(target=_w_distinct, args=(i,)) for i in range(16)]
            for t in ts:
                t.start()
            for t in ts:
                t.join()
            self.assertEqual(errs, [])
            for i in range(16):
                self.assertEqual(stat.S_IMODE(os.lstat(conc_dir / f"d_{i}.json").st_mode), 0o600)

            same_p = conc_dir / "same.json"
            def _w_same(idx: int) -> None:
                try:
                    for j in range(4):
                        oracle.write_regular_bytes_safe(same_p, f"s:{idx}:{j}".encode("ascii"))
                except BaseException as exc:
                    errs.append(exc)

            ts = [threading.Thread(target=_w_same, args=(i,)) for i in range(16)]
            for t in ts:
                t.start()
            for t in ts:
                t.join()
            self.assertEqual(errs, [])
            self.assertEqual(stat.S_IMODE(os.lstat(same_p).st_mode), 0o600)

            barrier = threading.Barrier(80)
            burst_p = conc_dir / "burst.json"
            def _w_burst(idx: int) -> None:
                try:
                    barrier.wait()
                    oracle.write_regular_bytes_safe(burst_p, f"b:{idx}".encode("ascii"))
                except BaseException as exc:
                    errs.append(exc)

            ts = [threading.Thread(target=_w_burst, args=(i,)) for i in range(80)]
            for t in ts:
                t.start()
            for t in ts:
                t.join()
            self.assertEqual(errs, [])
            self.assertEqual([n for n in os.listdir(conc_dir) if n.startswith(".s22a_tmp_")], [])

            # Live >= 520-iter renameat2(RENAME_EXCHANGE) symlink/directory swap race
            race_dir = root / "race_exch"
            race_dir.mkdir()
            d_real = race_dir / "real_dir"
            d_real.mkdir()
            (d_real / "data.txt").write_bytes(b"safe-data")
            canary_dir = race_dir / "canary_dir"
            canary_dir.mkdir()
            (canary_dir / "data.txt").write_bytes(b"CANARY-LEAK")
            d_sym = race_dir / "sym_slot"
            os.symlink(canary_dir, d_sym)
            slot = race_dir / "slot"
            os.rename(d_real, slot)
            renameat2 = _get_renameat2()
            stop_ev = threading.Event()
            b_slot = os.fsencode(slot)
            b_sym = os.fsencode(d_sym)

            def _swapper() -> None:
                while not stop_ev.is_set():
                    renameat2(_AT_FDCWD, b_slot, _AT_FDCWD, b_sym, _RENAME_EXCHANGE)

            sw_t = threading.Thread(target=_swapper)
            sw_t.start()
            try:
                for _ in range(520):
                    try:
                        got = oracle.read_regular_bytes_capped(slot / "data.txt")
                        self.assertNotEqual(got, b"CANARY-LEAK")
                    except oracle.PerfectModularError as exc:
                        self.assertIn(exc.code, ("SYMLINK_FORBIDDEN", "FILE_READ_ERROR"))
                    try:
                        oracle.write_regular_bytes_safe(slot / "w.txt", b"safe-write")
                    except oracle.PerfectModularError as exc:
                        self.assertIn(exc.code, ("SYMLINK_FORBIDDEN", "FILE_WRITE_ERROR"))
            finally:
                stop_ev.set()
                sw_t.join()
            self.assertFalse((canary_dir / "w.txt").exists())

            # Live >= 420-iter os.link / os.unlink hardlink race (0 peer clobbers, 0 temp leaks)
            hl_race_dir = root / "hl_race"
            hl_race_dir.mkdir()
            hl_tgt = hl_race_dir / "tgt.txt"
            hl_peer = hl_race_dir / "peer.txt"
            hl_tgt.write_bytes(b"PEER-IMMUTABLE")
            stop_hl = threading.Event()

            def _linker() -> None:
                while not stop_hl.is_set():
                    try:
                        os.link(hl_tgt, hl_peer)
                    except OSError:
                        pass
                    try:
                        os.unlink(hl_peer)
                    except OSError:
                        pass

            lt = threading.Thread(target=_linker)
            lt.start()
            try:
                for i in range(420):
                    try:
                        oracle.write_regular_bytes_safe(hl_tgt, f"fresh-{i}".encode("ascii"))
                    except oracle.PerfectModularError as exc:
                        self.assertEqual(exc.code, "HARDLINK_FORBIDDEN")
            finally:
                stop_hl.set()
                lt.join()
            self.assertEqual([n for n in os.listdir(hl_race_dir) if n.startswith(".s22a_tmp_")], [])

            if audit.DEFAULT_CERT_PATH.is_file():
                self.assertTrue(oracle.verify_certificate_file(audit.DEFAULT_CERT_PATH)["valid"])


def main() -> int:
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(TestTrackS22aPerfectQuasiModularR2)
    runner = unittest.TextTestRunner(verbosity=2, stream=sys.stderr)
    res = runner.run(suite)
    out = {
        "suite": "test_perfect_quasi_modular_r5",
        "tests_run": res.testsRun,
        "failures": len(res.failures),
        "errors": len(res.errors),
        "ok": res.wasSuccessful(),
    }
    print(json.dumps(out, sort_keys=True, separators=(",", ":")))
    return 0 if res.wasSuccessful() else 1


if __name__ == "__main__":
    raise SystemExit(main())
