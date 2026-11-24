#!/usr/bin/env python3
"""Comprehensive R5 verification, mutation-killing, and live race-stress suite for Track S22c.

100% pure Python 3 stdlib, ZERO bare asserts, ZERO AST floats, ZERO float() calls,
ZERO .isdigit() calls, ZERO third-party imports.
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
import stat
import subprocess
import sys
import tempfile
import threading
from typing import Any
import unittest

ROOT = Path(__file__).resolve().parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import f2x_perfect_poly_audit as audit  # noqa: E402
import f2x_perfect_poly_oracle as oracle  # noqa: E402

_AT_FDCWD = -100
_RENAME_EXCHANGE = 2


class _EvilPath(type(Path())):
    """Path subclass used to verify strict concrete-Path enforcement."""


class _StrSub(str):
    """str subclass used to verify strict exact-str enforcement."""


class _IntSub(int):
    """int subclass used to verify strict exact-int enforcement."""


class _DictSub(dict):
    """dict subclass used to verify strict exact-dict enforcement."""


class _ListSub(list):
    """list subclass used to verify strict exact-list enforcement."""


def _check(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


def _expect_err(fn: Any, expected_code: str, label: str) -> None:
    try:
        fn()
    except oracle.F2xPerfectError as exc:
        if exc.code != expected_code:
            raise AssertionError(f"{label}: expected {expected_code}, got {exc.code} ({exc.detail})") from exc
        return
    raise AssertionError(f"{label}: expected F2xPerfectError({expected_code}), but succeeded")


def _flip_hex64(h: str) -> str:
    return ("0" if h[0] != "0" else "1") + h[1:]


def _rehash_cert(cert: dict[str, Any]) -> dict[str, Any]:
    out = copy.deepcopy(cert)
    psha = hashlib.sha256(audit.canonical_json_bytes(out["payload"])).hexdigest()
    out["payload_sha256"] = psha
    env = {
        "schema_version": out["schema_version"],
        "track_id": out["track_id"],
        "payload_sha256": psha,
        "payload": out["payload"],
    }
    out["certificate_sha256"] = hashlib.sha256(audit.canonical_json_bytes(env)).hexdigest()
    return out


class TestTrackS22cF2xPerfectPolynomials(unittest.TestCase):
    """Exact math, oracle guards, Zone-B audit hardening, and concurrent race stress."""

    _cert: dict[str, Any]
    _cert_bytes: bytes

    @classmethod
    def setUpClass(cls) -> None:
        cls._cert = audit.build_certificate()
        cls._cert_bytes = audit.canonical_json_bytes(cls._cert)

    def test_01_all_four_pillars_and_oracle_domain_guards(self) -> None:
        cert = self._cert
        pl = cert["payload"]
        _check(pl["all_pillars_verified"] is True, "all_pillars_verified not True")
        _check(pl["oracle_class"] == "exact", "oracle_class mismatch")
        _check(pl["novelty_label"] == "N1", "novelty_label mismatch")

        p1 = pl["pillar1_f2x_ring_and_sigma"]
        _check(p1["all_verified"] is True, "P1 all_verified")
        _check(tuple(p1["irred_counts_deg_1_to_12"]) == oracle.EXPECTED_IRRED_COUNTS_1_TO_12, "P1 irred counts")
        _check(p1["rabin_vs_sieve_checked_deg_1_to_8"] == 510, "P1 Rabin count")
        _check(p1["rabin_vs_sieve_matches_deg_1_to_8"] == 510, "P1 Rabin matches")
        _check(p1["multiplicativity_and_divisor_checks"] == 6, "P1 mult checks")
        _check(p1["geometric_sigma_identity_checks"] == 36, "P1 geom checks")
        _check(p1["canaday_anchor_x_xp1"]["sigma_a_mask"] == 6, "P1 anchor")

        p2 = pl["pillar2_splitting_perfect_characterization"]
        _check(p2["all_verified"] is True, "P2 all_verified")
        _check(p2["nonconstant_pairs_checked"] == 288, "P2 pairs checked")
        _check(p2["perfect_splitting_pairs"] == [[1, 1], [3, 3], [7, 7], [15, 15]], "P2 splitting pairs")
        _check(len(p2["duality_witnesses_n_1_to_6"]) == 6, "P2 duality witnesses")

        p3 = pl["pillar3_canaday_11_and_deg14_census"]
        _check(p3["all_verified"] is True, "P3 all_verified")
        _check(p3["total_monic_polys_deg_1_to_14"] == 32_766, "P3 total deg<=14")
        _check(p3["perfect_count_deg_1_to_14"] == 9, "P3 count deg<=14")
        _check(p3["splitting_count_deg_1_to_14"] == 3, "P3 splitting deg<=14")
        _check(p3["sporadic_count_deg_1_to_14"] == 6, "P3 sporadic deg<=14")
        _check(p3["density_deg_1_to_14_q"] == "3/10922", "P3 density exact fraction")
        _check(p3["neg_zero_normalization_witness"] == "0.000000", "P3 -0.00 norm")
        _check(p3["canaday_11_sporadic_count"] == 11, "P3 Canaday 11 count")
        _check(p3["canaday_11_verified_count"] == 11, "P3 Canaday 11 verified")
        _check(p3["canaday_direct_divisor_cross_checks"] == 6, "P3 direct divisor checks")
        _check(p3["canaday_conjugate_twin_pairs"] == 5, "P3 twin pairs")
        _check(p3["canaday_self_symmetric_masks"] == [67184], "P3 self symmetric")

        p4 = pl["pillar4_odd_perfect_obstruction_frontier"]
        _check(p4["all_verified"] is True, "P4 all_verified")
        _check(p4["direct_odd_at_deg_16"] == 16_384, "P4 odd at deg 16")
        _check(p4["direct_odd_checked_deg_2_to_16"] == 32_767, "P4 odd deg 2..16")
        _check(p4["direct_odd_perfect_found"] == 0, "P4 odd deg<=16 found")
        _check(p4["odd_irreducibles_tested_deg_2_to_8"] == 69, "P4 odd irreds deg 2..8")
        _check(p4["theorem_4a_even_exponent_witnesses"] == 276, "P4 4A witnesses")
        _check(p4["theorem_4b_char2_derivative_witnesses"] == 276, "P4 4B witnesses")
        _check(p4["square_lifted_odd_squares_checked"] == 2_047, "P4 odd squares checked")
        _check(p4["square_lifted_total_odd_polys_covered_deg_2_to_24"] == 8_388_607, "P4 odd covered deg<=24")
        _check(p4["square_lifted_odd_perfect_found"] == 0, "P4 odd sq found")

        # Exact primitive domain & boundary guards
        oracle.require_ok(True, "OK", "ok")
        _expect_err(lambda: oracle.require_ok(1, "X", "bad"), "INVALID_CONDITION_TYPE", "int cond")  # type: ignore[arg-type]
        _expect_err(lambda: oracle.require_ok(False, "FAIL_CODE", "nope"), "FAIL_CODE", "false cond")

        _check(oracle.require_exact_int(5, "v", lo=5, hi=5) == 5, "exact int bounds")
        _check(oracle.require_exact_int((1 << oracle.MAX_EXACT_INT_BITS) - 1, "maxb") > 0, "exact max bit int")
        for bad_i in (True, _IntSub(1), "1", None):
            _expect_err(lambda bi=bad_i: oracle.require_exact_int(bi, "v"), "INVALID_INT_TYPE", f"bad int {bad_i!r}")
        _expect_err(lambda: oracle.require_exact_int(1 << oracle.MAX_EXACT_INT_BITS, "big"), "INT_BIT_LIMIT", "big int")
        _expect_err(lambda: oracle.require_exact_int(4, "v", lo=5), "INT_OUT_OF_RANGE", "below lo")
        _expect_err(lambda: oracle.require_exact_int(6, "v", hi=5), "INT_OUT_OF_RANGE", "above hi")
        _expect_err(lambda: oracle.require_exact_int(5, "v", lo=True), "INVALID_BOUND_TYPE", "bool lo")  # type: ignore[arg-type]
        _expect_err(lambda: oracle.require_exact_int(5, "v", hi=True), "INVALID_BOUND_TYPE", "bool hi")  # type: ignore[arg-type]

        _check(oracle.require_exact_bool(False, "b") is False, "exact bool")
        _expect_err(lambda: oracle.require_exact_bool(0, "b"), "INVALID_BOOL_TYPE", "int bool")

        _check(oracle.format_fraction(Fraction(5, 1)) == "5", "int fraction")
        _check(oracle.format_fraction(Fraction(3, 4)) == "3/4", "reduced fraction")
        _check(oracle.require_exact_fraction(Fraction((1 << oracle.MAX_EXACT_INT_BITS) - 1, 1), "fn") > 0, "max num frac")
        _check(oracle.require_exact_fraction(Fraction(1, (1 << oracle.MAX_EXACT_INT_BITS) - 1), "fd") > 0, "max den frac")
        _expect_err(lambda: oracle.require_exact_fraction(1, "f"), "INVALID_FRACTION_TYPE", "int as frac")  # type: ignore[arg-type]
        _expect_err(lambda: oracle.require_exact_fraction(Fraction(1 << oracle.MAX_EXACT_INT_BITS, 1), "f"), "RATIONAL_BIT_LIMIT", "big num")
        _expect_err(lambda: oracle.require_exact_fraction(Fraction(1, 1 << oracle.MAX_EXACT_INT_BITS), "f"), "RATIONAL_BIT_LIMIT", "big den")

        # Decimal formatter including -0.00 normalization & positive/negative rounding
        _check(oracle.format_decimal_rounded(Fraction(-1, 10_000_000), digits=6) == "0.000000", "neg zero norm")
        _check(oracle.format_decimal_rounded(Fraction(-5, 2), digits=2) == "-2.50", "neg decimal")
        _check(oracle.format_decimal_rounded(Fraction(1, 3), digits=4) == "0.3333", "pos decimal")
        # Exact 4096-bit rational formatting must NEVER hit Python's 4300-digit ValueError,
        # and >4096-bit / 10**4300 inputs must fail closed with RATIONAL_BIT_LIMIT!
        max_4096 = (1 << oracle.MAX_EXACT_INT_BITS) - 1
        _check(len(oracle.format_fraction(Fraction(max_4096, 1))) > 1200, "4096-bit format_fraction safe")
        _check(oracle.format_decimal_rounded(Fraction(max_4096, 1), digits=12).endswith(".000000000000"), "4096-bit dec12 safe")
        _expect_err(lambda: oracle.format_fraction(Fraction(10**4300, 1)), "RATIONAL_BIT_LIMIT", "10**4300 format_fraction")
        _expect_err(lambda: oracle.format_decimal_rounded(Fraction(10**4300, 1), digits=6), "RATIONAL_BIT_LIMIT", "10**4300 dec6")
        _expect_err(lambda: oracle.format_decimal_rounded(Fraction(1, 2), digits=0), "INT_OUT_OF_RANGE", "digits 0")
        _expect_err(lambda: oracle.format_decimal_rounded(Fraction(1, 2), digits=13), "INT_OUT_OF_RANGE", "digits 13")

        # Polynomial helper edge cases
        _check(oracle.poly_deg(0) == -1, "deg(0)==-1")
        _check(oracle.format_poly_f2(0) == "0", "fmt 0")
        _check(oracle.format_poly_f2(1) == "1", "fmt 1")
        _check(oracle.format_poly_f2(2) == "x", "fmt x")
        _check(oracle.format_poly_f2(7) == "x^2+x+1", "fmt x^2+x+1")
        _check(oracle.format_factorization_f2({}) == "1", "fmt empty fac")
        _check(oracle.poly_derivative(0) == 0, "deriv 0")
        _check(oracle.poly_derivative(5) == 0, "deriv x^2+1 == 0")
        _check(oracle.poly_derivative(7) == 1, "deriv x^2+x+1 == 1")
        _check(oracle.poly_is_odd(7) is True, "x^2+x+1 odd")
        _check(oracle.poly_is_odd(2) is False, "x has eval0=0 eval1=1")
        _check(oracle.poly_is_odd(6) is False, "x(x+1) not odd")
        _check(oracle.poly_is_odd(5) is False, "x^2+1=(x+1)^2 not odd")
        _check(oracle.is_irreducible_f2(0) is False, "0 not irred")
        _check(oracle.is_irreducible_f2(1) is False, "1 not irred")
        _check(oracle.is_irreducible_f2(2) is True, "x irred")
        _check(oracle.is_irreducible_f2(3) is True, "x+1 irred")
        _check(oracle.is_irreducible_f2(4) is False, "x^2 not irred")
        _check(oracle.is_irreducible_f2(5) is False, "(x+1)^2 not irred")
        _check(oracle.is_irreducible_f2(7) is True, "x^2+x+1 irred")
        _check(oracle.is_irreducible_f2(21) is False, "(x^2+x+1)^2 not irred")
        # Product of two distinct degree-2/3 irreducibles (e.g. (x^2+x+1)*(x^3+x+1)=53, deg 5, fails x^{2^5}==x)
        _check(oracle.is_irreducible_f2(oracle.poly_mul(7, 11)) is False, "7*11 not irred")
        # Product of two distinct degree-3 irreducibles (11*13=127, deg 6: passes x^{2^6}==x, caught by gcd(p, x^{2^3}-x)!)
        _check(oracle.is_irreducible_f2(oracle.poly_mul(11, 13)) is False, "11*13 caught by Rabin gcd")
        _check(oracle._distinct_prime_factors_int(12) == [2, 3], "prime factors 12")
        _check(oracle.poly_gcd(0, 7) == 7, "gcd(0,7)")
        _check(oracle.poly_gcd(7, 0) == 7, "gcd(7,0)")
        _expect_err(lambda: oracle.poly_divmod(7, 0), "INT_OUT_OF_RANGE", "div by 0")
        _expect_err(lambda: oracle.poly_is_odd(0), "INT_OUT_OF_RANGE", "odd 0")

        # Sieve & factor_with_sieve fallback branches (large irreducible > sieve, large composite > sieve!)
        spf4, cof4 = oracle.build_f2_spf_sieve(4)  # limit = 32
        _check(oracle.factor_with_sieve(1, spf4, cof4) == {}, "factor 1")
        # Degree 5 irreducible (37 = x^5 + x^2 + 1) > limit 32 -> Rabin accepts as irreducible!
        _check(oracle.is_irreducible_f2(37) is True, "37 irred")
        _check(oracle.factor_with_sieve(37, spf4, cof4) == {37: 1}, "factor irred > sieve")
        # Composite 2 * 7 * 37 > limit 32 (factors 2 and 7 stripped, 37 accepted as irred)
        comp_ok = oracle.poly_mul(oracle.poly_mul(2, 7), 37)
        _check(oracle.factor_with_sieve(comp_ok, spf4, cof4) == {2: 1, 7: 1, 37: 1}, "factor mixed > sieve")
        # Composite 7 * 7 = 49 > limit 32 -> after stripping 7, rem=7 < limit 32 (hits `if a < limit: break`)
        _check(oracle.factor_with_sieve(oracle.poly_mul(7, 7), spf4, cof4) == {7: 2}, "factor drops below limit")
        # Unfactorable composite of two deg-5 irreducibles (37 * 37 = 1041) > spf4 limit -> FACTOR_RANGE_EXCEEDED!
        _expect_err(
            lambda: oracle.factor_with_sieve(oracle.poly_mul(37, 37), spf4, cof4),
            "FACTOR_RANGE_EXCEEDED",
            "composite beyond sieve range",
        )
        # Public helper validation guards (sieve tables + factors dict)
        _check(oracle.factor_with_sieve(2, [0, 0, 2, 3], [0, 0, 1, 1]) == {2: 1}, "exact len==4 sieve boundary")
        _expect_err(lambda: oracle.factor_with_sieve(2, (0, 0, 2, 3), [0, 0, 1, 1]), "INVALID_SIEVE_TABLE", "tuple spf")  # type: ignore[arg-type]
        _expect_err(lambda: oracle.factor_with_sieve(2, [0, 0, 2, 3], (0, 0, 1, 1)), "INVALID_SIEVE_TABLE", "tuple cof")  # type: ignore[arg-type]
        _expect_err(lambda: oracle.factor_with_sieve(2, [0, 0, 2, 3], [0, 0, 1]), "INVALID_SIEVE_TABLE", "len mismatch")
        _expect_err(lambda: oracle.factor_with_sieve(2, [0, 0, 2], [0, 0, 1]), "INVALID_SIEVE_TABLE", "len < 4")
        _expect_err(lambda: oracle.sigma_from_factors("bad"), "INVALID_FACTORS_TYPE", "str factors")  # type: ignore[arg-type]
        _expect_err(lambda: oracle.sigma_from_factors(_DictSub({2: 1})), "INVALID_FACTORS_TYPE", "dict sub factors")
        _expect_err(lambda: oracle.format_factorization_f2("bad"), "INVALID_FACTORS_TYPE", "str fmt factors")  # type: ignore[arg-type]
        _expect_err(lambda: oracle.format_factorization_f2({1: 1}), "INT_OUT_OF_RANGE", "factor prime < 2")
        _expect_err(lambda: oracle.format_factorization_f2({2: 0}), "INT_OUT_OF_RANGE", "factor exp < 1")

        # Also verify degree-20 Canaday witness against direct small-sieve fallback
        _check(oracle.sigma_from_factors(oracle.factor_with_sieve(1098176, *oracle.build_f2_spf_sieve(12))) == 1098176, "Canaday deg 20")
        # Direct verification of Phase 2 odd sigma table on deg 5..6 (kills any Phase 2 mutation!)
        spf6, cof6 = oracle.build_f2_spf_sieve(6)
        sig6, perf4, odd_cnt6, odd_p6 = oracle._compute_sigma_table_for_census(spf6, cof6, 4, 6)
        _check(perf4 == [6] and odd_cnt6 == 31 and odd_p6 == [], "small census summary")
        for odd_m in range(33, 128, 2):
            if oracle.poly_is_odd(odd_m):
                expected_s = oracle.sigma_from_factors(oracle.factor_with_sieve(odd_m, spf6, cof6))
                _check(sig6[odd_m] == expected_s, f"Phase 2 sigma mismatch at {odd_m}")

    def test_02_certificate_schema_hash_and_secondary_audit_tamper_suite(self) -> None:
        cert = self._cert
        _check(audit.verify_certificate_dict(cert, expected=cert, full_replay=True)["valid"] is True, "full_replay=True")
        _check(audit.verify_certificate_dict(cert, full_replay=False)["valid"] is True, "full_replay=False")
        # Verify on-disk frozen certificate matches freshly computed certificate
        disk_cert = ROOT / audit.DEFAULT_CERT_NAME
        if disk_cert.exists():
            _check(audit.verify_certificate_file(disk_cert)["valid"] is True, "on-disk cert valid")

        # Envelope & type rejections
        _expect_err(lambda: audit.verify_certificate_dict(cert, full_replay=1), "INVALID_BOOL_TYPE", "bool replay")  # type: ignore[arg-type]
        _expect_err(lambda: audit.verify_certificate_dict("not-dict"), "INVALID_CERT_TYPE", "str cert")
        _expect_err(lambda: audit.verify_certificate_dict(_DictSub(cert)), "INVALID_CERT_TYPE", "dict sub cert")

        c_keys = copy.deepcopy(cert)
        del c_keys["payload"]
        _expect_err(lambda: audit.verify_certificate_dict(c_keys), "INVALID_CERT_KEYS", "missing key")

        c_ver = copy.deepcopy(cert)
        c_ver["schema_version"] = "0.0.0"
        _expect_err(lambda: audit.verify_certificate_dict(c_ver), "INVALID_SCHEMA_VERSION", "bad schema")

        c_tid = copy.deepcopy(cert)
        c_tid["track_id"] = "WRONG"
        _expect_err(lambda: audit.verify_certificate_dict(c_tid), "INVALID_TRACK_ID", "bad track_id")

        for bad_hex in ("ä" * 64, "A" * 64, "0" * 63, 123):
            c_h = copy.deepcopy(cert)
            c_h["payload_sha256"] = bad_hex
            _expect_err(lambda ch=c_h: audit.verify_certificate_dict(ch), "INVALID_HEX64", f"bad hex {bad_hex!r}")

        c_psha = copy.deepcopy(cert)
        c_psha["payload_sha256"] = _flip_hex64(c_psha["payload_sha256"])
        _expect_err(lambda: audit.verify_certificate_dict(c_psha), "PAYLOAD_SHA_MISMATCH", "flipped payload sha")

        c_csha = copy.deepcopy(cert)
        c_csha["certificate_sha256"] = _flip_hex64(c_csha["certificate_sha256"])
        _expect_err(lambda: audit.verify_certificate_dict(c_csha), "CERTIFICATE_SHA_MISMATCH", "flipped cert sha")

        # Crafted self-consistent payload tampering rejected by secondary_audit_payload EVEN with full_replay=False!
        tamper_cases: list[tuple[str, Any]] = [
            ("all_pillars_verified=False", lambda p: p.__setitem__("all_pillars_verified", False)),
            ("novelty_label=N2", lambda p: p.__setitem__("novelty_label", "N2")),
            ("prior_art_bogus", lambda p: p["prior_art_quarantine_n0"].__setitem__(0, "bogus prior art")),
            ("p1_rabin_matches=0", lambda p: p["pillar1_f2x_ring_and_sigma"].__setitem__("rabin_vs_sieve_matches_deg_1_to_8", 0)),
            ("p2_duality_empty", lambda p: p["pillar2_splitting_perfect_characterization"].__setitem__("duality_witnesses_n_1_to_6", [])),
            ("p2_duality_bad_deg", lambda p: p["pillar2_splitting_perfect_characterization"]["duality_witnesses_n_1_to_6"][0].__setitem__("degree", 99)),
            ("p2_neg_ctrl_true", lambda p: p["pillar2_splitting_perfect_characterization"]["negative_controls"][0].__setitem__("is_perfect", True)),
            ("p2_neg_ctrl_ab99", lambda p: p["pillar2_splitting_perfect_characterization"]["negative_controls"][0].update({"a": 99, "b": 99})),
            ("p3_dec6_wrong", lambda p: p["pillar3_canaday_11_and_deg14_census"].__setitem__("density_deg_1_to_14_dec6", "0.999999")),
            ("p3_total_monic_zero", lambda p: p["pillar3_canaday_11_and_deg14_census"].__setitem__("total_monic_polys_deg_1_to_14", 0)),
            ("p3_perfect_count_zero", lambda p: p["pillar3_canaday_11_and_deg14_census"].__setitem__("perfect_count_deg_1_to_14", 0)),
            ("p3_density_q_zero", lambda p: p["pillar3_canaday_11_and_deg14_census"].__setitem__("density_deg_1_to_14_q", "0")),
            ("p3_census_bad_mask", lambda p: p["pillar3_canaday_11_and_deg14_census"]["census_deg_1_to_14"][0].__setitem__("mask", 10)),
            ("p3_census_bad_shift", lambda p: p["pillar3_canaday_11_and_deg14_census"]["census_deg_1_to_14"][0].__setitem__("shift_x_plus_1_mask", 999)),
            ("p3_census_flip_split", lambda p: p["pillar3_canaday_11_and_deg14_census"]["census_deg_1_to_14"][0].__setitem__("is_splitting", False)),
            ("p3_census_bogus_fac", lambda p: p["pillar3_canaday_11_and_deg14_census"]["census_deg_1_to_14"][0].__setitem__("factorization", "bogus")),
            ("p3_canaday_bad_mask", lambda p: p["pillar3_canaday_11_and_deg14_census"]["canaday_11_sporadic"][0].__setitem__("mask", 6)),
            ("p3_canaday_bad_omega2", lambda p: p["pillar3_canaday_11_and_deg14_census"]["canaday_11_sporadic"][0].__setitem__("omega", 2)),
            ("p3_canaday_bad_omega99", lambda p: p["pillar3_canaday_11_and_deg14_census"]["canaday_11_sporadic"][0].__setitem__("omega", 99)),
            ("p3_canaday_bogus_fac", lambda p: p["pillar3_canaday_11_and_deg14_census"]["canaday_11_sporadic"][0].__setitem__("factorization", "bogus")),
            ("p3_canaday_empty", lambda p: p["pillar3_canaday_11_and_deg14_census"].__setitem__("canaday_11_sporadic", [])),
            ("p4_4a_witnesses=0", lambda p: p["pillar4_odd_perfect_obstruction_frontier"].__setitem__("theorem_4a_even_exponent_witnesses", 0)),
            ("p4_covered=0", lambda p: p["pillar4_odd_perfect_obstruction_frontier"].__setitem__("square_lifted_total_odd_polys_covered_deg_2_to_24", 0)),
        ]
        for label, mutator in tamper_cases:
            c_tamper = copy.deepcopy(cert)
            mutator(c_tamper["payload"])
            _expect_err(
                lambda ct=c_tamper: audit.verify_certificate_dict(_rehash_cert(ct), full_replay=False),
                "SECONDARY_AUDIT_FAILED",
                f"forged {label} under full_replay=False",
            )
            _expect_err(
                lambda pl_t=c_tamper["payload"]: audit.secondary_audit_payload(pl_t),
                "SECONDARY_AUDIT_FAILED",
                f"forged {label} direct secondary_audit_payload",
            )

        # Zero-denominator rational string "1/0" fails closed on both surfaces (never ZeroDivisionError)
        c_rat_z = copy.deepcopy(cert)
        c_rat_z["payload"]["pillar3_canaday_11_and_deg14_census"]["density_deg_1_to_14_q"] = "1/0"
        _expect_err(
            lambda: audit.verify_certificate_dict(_rehash_cert(c_rat_z), full_replay=False),
            "INVALID_RATIONAL",
            "density_deg_1_to_14_q=1/0 under full_replay=False",
        )
        _expect_err(
            lambda: audit.secondary_audit_payload(c_rat_z["payload"]),
            "INVALID_RATIONAL",
            "density_deg_1_to_14_q=1/0 direct secondary_audit_payload",
        )

        # Strict nested-keyset enforcement under full_replay=False (extra keys rejected in every nested dict!)
        nested_extra_cases: list[tuple[str, Any]] = [
            ("p1_extra", lambda p: p["pillar1_f2x_ring_and_sigma"].__setitem__("extra", 1)),
            ("p1_anchor_extra", lambda p: p["pillar1_f2x_ring_and_sigma"]["canaday_anchor_x_xp1"].__setitem__("extra", 1)),
            ("p2_extra", lambda p: p["pillar2_splitting_perfect_characterization"].__setitem__("extra", 1)),
            ("p2_dual_extra", lambda p: p["pillar2_splitting_perfect_characterization"]["duality_witnesses_n_1_to_6"][0].__setitem__("extra", 1)),
            ("p2_neg_extra", lambda p: p["pillar2_splitting_perfect_characterization"]["negative_controls"][0].__setitem__("extra", 1)),
            ("p3_extra", lambda p: p["pillar3_canaday_11_and_deg14_census"].__setitem__("extra", 1)),
            ("p3_census_extra", lambda p: p["pillar3_canaday_11_and_deg14_census"]["census_deg_1_to_14"][0].__setitem__("extra", 1)),
            ("p3_canaday_extra", lambda p: p["pillar3_canaday_11_and_deg14_census"]["canaday_11_sporadic"][0].__setitem__("extra", 1)),
            ("p4_extra", lambda p: p["pillar4_odd_perfect_obstruction_frontier"].__setitem__("extra", 1)),
        ]
        for label, mutator in nested_extra_cases:
            c_ext = copy.deepcopy(cert)
            mutator(c_ext["payload"])
            _expect_err(
                lambda ce=c_ext: audit.verify_certificate_dict(_rehash_cert(ce), full_replay=False),
                "SECONDARY_AUDIT_SCHEMA_ERROR",
                f"extra nested key {label} under full_replay=False",
            )

        # Bool-as-int forgery inside payload rejected by exact-int secondary_audit_payload even with full_replay=False!
        c_bool_int = copy.deepcopy(cert)
        c_bool_int["payload"]["pillar4_odd_perfect_obstruction_frontier"]["direct_odd_perfect_found"] = False
        _expect_err(
            lambda: audit.verify_certificate_dict(_rehash_cert(c_bool_int), full_replay=False),
            "INVALID_INT_TYPE",
            "bool-as-int in P4",
        )

        # Full replay mismatch check (valid cert compared against altered expected cert -> CERTIFICATE_MISMATCH)
        alt_expected = copy.deepcopy(cert)
        alt_expected["payload_sha256"] = _flip_hex64(alt_expected["payload_sha256"])
        _expect_err(
            lambda: audit.verify_certificate_dict(cert, expected=alt_expected, full_replay=True),
            "CERTIFICATE_MISMATCH",
            "valid cert vs altered expected caught by full_replay",
        )

        # Direct secondary_audit_payload schema error paths
        _expect_err(lambda: audit.secondary_audit_payload("bad"), "SECONDARY_AUDIT_SCHEMA_ERROR", "str payload")
        _expect_err(lambda: audit.secondary_audit_payload(_DictSub(cert["payload"])), "SECONDARY_AUDIT_SCHEMA_ERROR", "dict sub payload")
        _expect_err(lambda: audit.secondary_audit_payload({}), "SECONDARY_AUDIT_SCHEMA_ERROR", "empty payload")
        extra_pl = copy.deepcopy(cert["payload"])
        extra_pl["unexpected_extra_key"] = 1
        _expect_err(lambda: audit.secondary_audit_payload(extra_pl), "SECONDARY_AUDIT_SCHEMA_ERROR", "extra payload key")
        bad_miss_pl = copy.deepcopy(cert["payload"])
        del bad_miss_pl["pillar1_f2x_ring_and_sigma"]["irred_counts_deg_1_to_12"]
        _expect_err(lambda: audit.secondary_audit_payload(bad_miss_pl), "SECONDARY_AUDIT_SCHEMA_ERROR", "missing nested key")
        bad_pl = copy.deepcopy(cert["payload"])
        bad_pl["pillar2_splitting_perfect_characterization"]["perfect_splitting_pairs"] = [[1, 1, 1]]
        _expect_err(lambda: audit.secondary_audit_payload(bad_pl), "SECONDARY_AUDIT_SCHEMA_ERROR", "len3 pair")
        bad_pl2 = copy.deepcopy(cert["payload"])
        bad_pl2["pillar1_f2x_ring_and_sigma"]["irred_counts_deg_1_to_12"] = "not-a-list"
        _expect_err(lambda: audit.secondary_audit_payload(bad_pl2), "SECONDARY_AUDIT_SCHEMA_ERROR", "str not list")
        bad_pl3 = copy.deepcopy(cert["payload"])
        bad_pl3["pillar1_f2x_ring_and_sigma"]["irred_counts_deg_1_to_12"] = _ListSub([2])
        _expect_err(lambda: audit.secondary_audit_payload(bad_pl3), "INVALID_JSON_VALUE", "list sub in payload")

    def test_03_zone_b_parsers_filesystem_pwd_cli_and_hygiene(self) -> None:
        cert = self._cert
        cert_bytes = self._cert_bytes

        # Strict ASCII-only integer & rational parsers (zero .isdigit(), zero bare ValueError)
        _check(audit._parse_bounded_int("0") == 0, "int 0")
        _check(audit._parse_bounded_int("-42") == -42, "int -42")
        for bad_i_tok, code in (
            (123, "INVALID_JSON_INT"),
            ("-0", "INVALID_JSON_INT"),
            ("-", "INVALID_JSON_INT"),
            ("", "INVALID_JSON_INT"),
            ("01", "INVALID_JSON_INT"),
            ("-01", "INVALID_JSON_INT"),
            ("\u0661", "INVALID_JSON_INT"),  # Arabic-Indic digit 1 (traps .isdigit()!)
            ("9" * (audit.MAX_JSON_INT_DIGITS + 1), "INT_DIGIT_LIMIT"),
        ):
            _expect_err(lambda bt=bad_i_tok: audit._parse_bounded_int(bt), code, f"bad int tok {bad_i_tok!r}")

        _check(audit.parse_exact_rational("0") == Fraction(0, 1), "rat 0")
        _check(audit.parse_exact_rational("-7") == Fraction(-7, 1), "rat -7")
        _check(audit.parse_exact_rational("1/2") == Fraction(1, 2), "rat 1/2 exact den=2 boundary")
        _check(audit.parse_exact_rational("-3/4") == Fraction(-3, 4), "rat -3/4")
        max_4096_s = str((1 << oracle.MAX_JSON_INT_BITS) - 1)
        _check(len(max_4096_s) == audit.MAX_JSON_INT_DIGITS, "4096-bit digit count symmetry")
        _check(oracle.format_fraction(audit.parse_exact_rational(max_4096_s)) == max_4096_s, "rat exact 4096-bit num roundtrip")
        _check(oracle.format_fraction(audit.parse_exact_rational("1/" + max_4096_s)) == "1/" + max_4096_s, "rat exact 4096-bit den roundtrip")
        for bad_r_tok in (
            123,
            "1/2/3",
            "-0",
            "-0/3",
            "",
            "-",
            "01/3",
            "1/03",
            "1/",
            "1/1",
            "2/4",
            "\u0661/3",
            "1/\u0663",
        ):
            _expect_err(lambda br=bad_r_tok: audit.parse_exact_rational(br), "INVALID_RATIONAL", f"bad rat {bad_r_tok!r}")
        for big_r_tok, exp_code in (
            ("9" * audit.MAX_JSON_INT_DIGITS, "INT_BIT_LIMIT"),
            ("1/" + "9" * audit.MAX_JSON_INT_DIGITS, "INT_BIT_LIMIT"),
            ("9" * (audit.MAX_JSON_INT_DIGITS + 1), "INT_DIGIT_LIMIT"),
            ("1/" + "9" * (audit.MAX_JSON_INT_DIGITS + 1), "INT_DIGIT_LIMIT"),
            ("9" * 4305, "INT_DIGIT_LIMIT"),
            ("1/" + "9" * 4305, "INT_DIGIT_LIMIT"),
        ):
            _expect_err(lambda br=big_r_tok: audit.parse_exact_rational(br), exp_code, f"big rat {len(big_r_tok)}")

        # Strict JSON tree & parser guards (zero AST floats: use json.loads for runtime floats)
        _check(audit.parse_strict_json_text("[1,true,null]", "arr", require_object=False) == [1, True, None], "arr")
        _check(
            audit.parse_strict_json_text('{"n":' + str((1 << oracle.MAX_JSON_INT_BITS) - 1) + "}", "maxb")["n"] > 0,
            "exact 4096-bit int",
        )
        _check(
            audit.parse_strict_json_text('{"n":-' + str((1 << oracle.MAX_JSON_INT_BITS) - 1) + "}", "negb")["n"] < 0,
            "exact neg 4096-bit int",
        )
        _expect_err(lambda: audit.parse_strict_json_text(123, "x"), "INVALID_JSON_TEXT", "non-str")  # type: ignore[arg-type]
        _expect_err(lambda: audit.parse_strict_json_text("{}", "x", require_object=1), "INVALID_BOOL_TYPE", "non-bool")  # type: ignore[arg-type]
        _expect_err(lambda: audit.parse_strict_json_text("\ufeff{}", "x"), "BOM_FORBIDDEN", "BOM")
        _expect_err(lambda: audit.parse_strict_json_text("{\x00}", "x"), "NUL_BYTE_FORBIDDEN", "NUL")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":"\ud800"}', "x"), "INVALID_UTF8_SURROGATE", "raw surr")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":"\\ud800"}', "x"), "INVALID_UTF8_SURROGATE", "esc surr")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":"x\\u0000y"}', "x"), "NUL_BYTE_FORBIDDEN", "esc NUL")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":1,"a":2}', "x"), "DUPLICATE_JSON_KEY", "dup key")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":NaN}', "x"), "NONFINITE_JSON", "NaN")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":1.5}', "x"), "FLOAT_FORBIDDEN", "float")
        _expect_err(lambda: audit.parse_strict_json_text('{"n":' + "9" * (audit.MAX_JSON_INT_DIGITS + 1) + "}", "x"), "INT_DIGIT_LIMIT", "digit cap")
        _expect_err(lambda: audit.parse_strict_json_text('{"n":' + "9" * audit.MAX_JSON_INT_DIGITS + "}", "x"), "INT_BIT_LIMIT", "bit cap")
        _expect_err(lambda: audit.parse_strict_json_text("[1]", "x", require_object=True), "JSON_ROOT_NOT_OBJECT", "list root")
        _expect_err(lambda: audit.parse_strict_json_text("{bad", "x"), "INVALID_JSON", "syntax error")
        exact_cap_json = '{"a":"' + ("x" * (audit.MAX_JSON_BYTES - 8)) + '"}'
        _check(len(exact_cap_json.encode("utf-8")) == audit.MAX_JSON_BYTES, "exact JSON byte cap len")
        _check(type(audit.parse_strict_json_text(exact_cap_json, "exact_cap")) is dict, "exact JSON byte cap ok")
        _expect_err(
            lambda: audit.parse_strict_json_text('{"a":"' + ("x" * (audit.MAX_JSON_BYTES - 7)) + '"}', "over_cap"),
            "FILE_TOO_LARGE",
            "over JSON byte cap",
        )
        _expect_err(lambda: audit._validate_json_tree({1: "x"}, "k"), "INVALID_JSON_KEY", "int key")
        _expect_err(lambda: audit._validate_json_tree({"n": 1 << oracle.MAX_JSON_INT_BITS}, "b"), "INT_BIT_LIMIT", "4097-bit")
        runtime_float = json.loads("1.5")
        runtime_nan = json.loads("NaN")
        _expect_err(lambda: audit._validate_json_tree({"f": runtime_float}, "f"), "INVALID_JSON_VALUE", "float in tree")
        _expect_err(lambda: audit.canonical_json_bytes({"n": 10**4300}), "INT_BIT_LIMIT", "canonical 10**4300")
        _expect_err(lambda: audit.canonical_json_bytes({"f": runtime_float}), "INVALID_JSON_VALUE", "canonical float")
        _expect_err(lambda: audit.canonical_json_bytes({"f": runtime_nan}), "INVALID_JSON_VALUE", "canonical NaN")
        cyc: dict[str, Any] = {}
        cyc["self"] = cyc
        _expect_err(lambda: audit.canonical_json_bytes(cyc), "MAX_DEPTH_EXCEEDED", "canonical cyclic dict")

        ok_d: Any = 1
        for _ in range(audit.MAX_JSON_DEPTH - 1):
            ok_d = [ok_d]
        _check(type(audit.parse_strict_json_text(json.dumps({"x": ok_d}), "d64")) is dict, "depth 64")
        _expect_err(lambda: audit.parse_strict_json_text(json.dumps({"x": [ok_d]}), "d65"), "MAX_DEPTH_EXCEEDED", "depth 65")

        # /proc/kallsyms st_size==0 capped read + read-only /dev/null guard + scratch FIFO write guard
        proc_kallsyms = Path("/proc/kallsyms")
        if proc_kallsyms.exists():
            _expect_err(lambda: audit.read_regular_bytes_capped(proc_kallsyms, "kallsyms", max_bytes=16), "FILE_TOO_LARGE", "kallsyms cap")
        dev_null = Path("/dev/null")
        if dev_null.exists():
            _expect_err(lambda: audit.read_regular_bytes_capped(dev_null, "devnull"), "NOT_A_REGULAR_FILE", "devnull read")
        if hasattr(os, "mkfifo"):
            with tempfile.TemporaryDirectory(prefix="s22c_fifo_") as ftd:
                nonreg_fifo = Path(ftd) / "nonreg_fifo"
                os.mkfifo(nonreg_fifo)
                _expect_err(lambda: audit.write_regular_bytes_safe(nonreg_fifo, b"{}\n", "nonreg_fifo"), "NOT_A_REGULAR_FILE", "scratch FIFO write")

        with tempfile.TemporaryDirectory(prefix="s22c_zb_") as td:
            root = Path(td)
            cfile = root / "c.json"
            _expect_err(
                lambda: audit.write_regular_bytes_safe(root / "never_created" / "x.json", "not-bytes", "bad_payload"),  # type: ignore[arg-type]
                "INVALID_PAYLOAD_BYTES",
                "non-bytes payload",
            )
            _check(not (root / "never_created").exists(), "bad payload created parent dir")

            audit.write_regular_bytes_safe(cfile, cert_bytes, "c")
            _check(stat.S_IMODE(os.stat(cfile).st_mode) == 0o600, "mode must be 0o600")
            audit.write_regular_bytes_safe(cfile, b"{}\n", "c_short")
            _check(cfile.read_bytes() == b"{}\n", "atomic replace shorter")
            audit.write_regular_bytes_safe(cfile, cert_bytes, "c_restore")

            # Streaming >64 KiB read/write round-trip
            big_payload = b"A" * 70_000
            big_file = root / "big.bin"
            audit.write_regular_bytes_safe(big_file, big_payload, "big")
            _check(audit.read_regular_bytes_capped(big_file, "big") == big_payload, "streaming >64KiB")

            # Deterministic CSPRNG EEXIST collision retry
            fixed_tok_a = "deadbeef00000001"
            fixed_tok_b = "deadbeef00000002"
            pre_tmp = root / f".s22c.{os.getpid()}.{fixed_tok_a}.tmp"
            pre_tmp.write_bytes(b"pre")
            tok_iter = iter((fixed_tok_a, fixed_tok_b))
            orig_token_hex = audit.secrets.token_hex
            try:
                audit.secrets.token_hex = lambda _n=8: next(tok_iter)  # type: ignore[assignment]
                audit.write_regular_bytes_safe(cfile, cert_bytes, "c_retry")
            finally:
                audit.secrets.token_hex = orig_token_hex
            _check(pre_tmp.read_bytes() == b"pre", "preexisting tmp altered")
            pre_tmp.unlink()
            _check([p.name for p in root.glob(".s22c.*.tmp")] == [], "leftover retry tmp")

            # Live pre-replace temp st_nlink != 1 detection (hardlink injected during fsync)
            orig_fsync = audit.os.fsync
            linked_alias = root / "injected_tmp_link"
            hook_armed = [True]

            def _inject_tmp_link(fd_arg: int) -> None:
                if hook_armed[0]:
                    tmps = list(root.glob(".s22c.*.tmp"))
                    if tmps:
                        hook_armed[0] = False
                        _check(stat.S_IMODE(os.lstat(tmps[0]).st_mode) == 0o600, "live temp mode not 0o600")
                        os.link(tmps[0], linked_alias)
                orig_fsync(fd_arg)

            try:
                audit.os.fsync = _inject_tmp_link  # type: ignore[assignment]
                _expect_err(
                    lambda: audit.write_regular_bytes_safe(cfile, b'{"tamper":1}\n', "tmp_hl"),
                    "HARDLINK_FORBIDDEN",
                    "pre-replace temp hardlink",
                )
            finally:
                audit.os.fsync = orig_fsync
                if linked_alias.exists():
                    linked_alias.unlink()
            _check(cfile.read_bytes() == cert_bytes, "pre-replace hardlink altered target")
            _check([p.name for p in root.glob(".s22c.*.tmp")] == [], "leftover temp after pre-replace hardlink")

            nested = root / "nested_a" / "sub_b" / "w.json"
            audit.write_regular_bytes_safe(nested, cert_bytes, "nested")
            _check(nested.read_bytes() == cert_bytes, "nested dir_fd create")
            _check(audit.read_regular_bytes_capped(cfile, "c", max_bytes=len(cert_bytes)) == cert_bytes, "exact max_bytes")
            _check(audit.read_regular_bytes_capped(cfile, "c", max_bytes=audit.MAX_ALLOWED_CAP_BYTES) == cert_bytes, "exact 64MiB")
            _expect_err(
                lambda: audit.read_regular_bytes_capped(cfile, "c", max_bytes=audit.MAX_ALLOWED_CAP_BYTES + 1),
                "INT_OUT_OF_RANGE",
                "over 64MiB cap",
            )
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
            _expect_err(lambda: audit.read_regular_bytes_capped(str(cfile), "str"), "INVALID_PATH_TYPE", "str path")  # type: ignore[arg-type]
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
            _expect_err(lambda: audit.write_regular_bytes_safe(sym_dir / "nested" / "w.json", cert_bytes, "sym_dir_w"), "SYMLINK_FORBIDDEN", "write under symdir")
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

            # Relative PWD symlink, surrogate PWD, relative PWD, unset PWD, deleted CWD, & CLI tests
            orig_cwd = os.getcwd()
            orig_pwd = os.environ.get("PWD")
            try:
                os.chdir(real_sub)
                os.environ["PWD"] = str(sym_dir / "nested")
                _expect_err(lambda: audit.verify_certificate_file(Path("c.json")), "SYMLINK_ANCESTOR_FORBIDDEN", "symlink PWD")
                os.environ["PWD"] = "/nonexistent_s22c_pwd_dir"
                _expect_err(lambda: audit.read_regular_bytes_capped(Path("c.json"), "missing_pwd"), "CWD_UNAVAILABLE", "missing PWD")
                os.environ["PWD"] = "/tmp/bad_\udcff_pwd"
                _expect_err(lambda: audit.read_regular_bytes_capped(Path("c.json"), "spwd"), "INVALID_UTF8_SURROGATE", "surrogate PWD")
                os.environ["PWD"] = "rel/local_sym"
                _check(audit.read_regular_bytes_capped(Path(".") / "c.json", "relpwd") == cert_bytes, "relative PWD")
                os.environ["PWD"] = str(real_sub)
                _check(audit.read_regular_bytes_capped(Path("c.json"), "realpwd") == cert_bytes, "real PWD")
                os.environ.pop("PWD", None)
                _check(audit.read_regular_bytes_capped(Path("c.json"), "nopwd") == cert_bytes, "unset PWD")

                # CLI main() positive + strict negative + flag-like & equals-syntax guards
                out_path = root / "written.json"
                obuf = io.StringIO()
                with redirect_stdout(obuf):
                    rc_w = audit.main(["--write", str(out_path)])
                _check(rc_w == 0 and out_path.read_bytes() == cert_bytes, "CLI --write")

                cbuf = io.StringIO()
                with redirect_stdout(cbuf):
                    rc_c = audit.main(["--check", str(out_path)])
                _check(rc_c == 0 and json.loads(cbuf.getvalue())["valid"] is True, "CLI --check")

                _tuple_argv = ("--standalone", "--json")
                for bad_argv, exp_code in (
                    (_tuple_argv, "INVALID_ARGV"),
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
                    (["--write="], "INVALID_CLI_ARGS"),
                    (["--check="], "INVALID_CLI_ARGS"),
                    (["--write"], "INVALID_CLI_ARGS"),
                    (["--check"], "INVALID_CLI_ARGS"),
                    (["--unknown", "x"], "INVALID_CLI_ARGS"),
                ):
                    ebuf = io.StringIO()
                    with redirect_stderr(ebuf):
                        rc_b = audit.main(bad_argv)  # type: ignore[arg-type]
                    err_txt = ebuf.getvalue()
                    _check(rc_b == 2 and exp_code in err_txt, f"bad argv {bad_argv!r}: rc={rc_b} err={err_txt!r}")
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

            # Subprocess zero-arg, --standalone --json parity, & symlinked PWD CLI refusal
            p_def = subprocess.run([sys.executable, "-I", "-O", "-B", str(ROOT / "f2x_perfect_poly_audit.py")], capture_output=True, timeout=60)
            _check(p_def.returncode == 0 and p_def.stdout == cert_bytes, "subprocess zero-arg mismatch")
            p_std = subprocess.run([sys.executable, "-I", "-O", "-B", str(ROOT / "f2x_perfect_poly_audit.py"), "--standalone", "--json"], capture_output=True, timeout=60)
            _check(p_std.returncode == 0 and p_std.stdout == cert_bytes, "subprocess --standalone mismatch")
            p_pwd = subprocess.run(
                [sys.executable, "-I", "-O", "-B", str(ROOT / "f2x_perfect_poly_audit.py"), "--check", "c.json"],
                cwd=str(real_sub),
                env={**os.environ, "PWD": str(sym_dir / "nested")},
                capture_output=True,
                text=True,
                timeout=60,
            )
            _check(p_pwd.returncode == 2 and "SYMLINK_ANCESTOR_FORBIDDEN" in p_pwd.stderr, f"subprocess symlink PWD: {p_pwd.stderr!r}")

    def test_04_live_renameat2_hardlink_and_16t_80t_race_stress(self) -> None:
        libc = ctypes.CDLL(None, use_errno=True)
        renameat2 = libc.renameat2
        renameat2.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
        renameat2.restype = ctypes.c_int

        with tempfile.TemporaryDirectory(prefix="s22c_race_") as td:
            root = Path(td)
            canary = root / "canary.txt"
            canary_bytes = b"DO_NOT_LEAK_OR_CLOBBER\n"
            canary.write_bytes(canary_bytes)

            # Part A: >= 520-iter concurrent renameat2(RENAME_EXCHANGE) leaf + intermediate dir race
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
                    except oracle.F2xPerfectError:
                        pass
                    try:
                        audit.write_regular_bytes_safe(real_dir / "target.json", b'{"ok":2}\n', "race_w")
                    except oracle.F2xPerfectError:
                        pass
                    if canary.read_bytes() != canary_bytes:
                        clobbers += 1
            finally:
                stop_ev.set()
                t.join(timeout=5)

            _check(leaks == 0 and clobbers == 0, f"renameat2 race failed: leaks={leaks}, clobbers={clobbers}")
            _check(canary.read_bytes() == canary_bytes, "canary clobbered in renameat2 race")

            # Part B: >= 420-iter concurrent os.link()/os.unlink() hardlink inode-immutability race
            hl_dir = root / "hl_dir"
            hl_dir.mkdir()
            hl_target = hl_dir / "cert.json"
            hl_alias = hl_dir / "alias.json"
            hl_target.write_bytes(b'{"iter":-1}\n')

            stop_hl = threading.Event()
            links_created = [0]
            hl_clobbers = [0]

            def _linker() -> None:
                while not stop_hl.is_set():
                    try:
                        os.link(hl_target, hl_alias)
                        links_created[0] += 1
                    except OSError:
                        continue
                    try:
                        snap = hl_alias.read_bytes()
                        for _ in range(8):
                            if hl_alias.read_bytes() != snap:
                                hl_clobbers[0] += 1
                    except OSError:
                        pass
                    finally:
                        try:
                            os.unlink(hl_alias)
                        except OSError:
                            pass

            t_hl = threading.Thread(target=_linker, daemon=True)
            t_hl.start()
            try:
                for i in range(420):
                    payload = f'{{"iter":{i}}}\n'.encode("ascii")
                    try:
                        audit.write_regular_bytes_safe(hl_target, payload, "hl_w")
                    except oracle.F2xPerfectError as exc:
                        _check(exc.code == "HARDLINK_FORBIDDEN", f"unexpected hardlink error {exc.code}")
            finally:
                stop_hl.set()
                t_hl.join(timeout=5)
            _check(hl_clobbers[0] == 0 and links_created[0] > 0, f"hardlink race failed: clobbers={hl_clobbers[0]}")
            leftovers = [p.name for p in hl_dir.iterdir() if p.name.startswith(".s22c.")]
            _check(len(leftovers) == 0, f"leftover temp files: {leftovers}")

            # Part C: Concurrent writer stress (16T distinct + 16T same-target + 80T barrier burst)
            cw_dir = root / "cw_dir"
            cw_dir.mkdir()
            cw_errs: list[str] = []

            def _distinct_worker(idx: int) -> None:
                p = cw_dir / f"t_{idx}.json"
                data = f'{{"worker":{idx}}}\n'.encode("ascii")
                try:
                    for _ in range(4):
                        audit.write_regular_bytes_safe(p, data, f"dw_{idx}")
                    if p.read_bytes() != data or stat.S_IMODE(os.stat(p).st_mode) != 0o600:
                        cw_errs.append(f"distinct_mismatch_{idx}")
                except BaseException as exc:
                    cw_errs.append(f"distinct_{idx}:{exc}")

            t_dist = [threading.Thread(target=_distinct_worker, args=(i,)) for i in range(16)]
            for th in t_dist:
                th.start()
            for th in t_dist:
                th.join(timeout=15)
            _check(cw_errs == [], f"16T distinct write errors: {cw_errs}")

            same_target = cw_dir / "shared.json"
            valid_16 = {f'{{"same":{i}}}\n'.encode("ascii") for i in range(16)}

            def _same_worker(idx: int) -> None:
                data = f'{{"same":{idx}}}\n'.encode("ascii")
                try:
                    for _ in range(4):
                        audit.write_regular_bytes_safe(same_target, data, f"sw_{idx}")
                except BaseException as exc:
                    cw_errs.append(f"same_{idx}:{exc}")

            t_same = [threading.Thread(target=_same_worker, args=(i,)) for i in range(16)]
            for th in t_same:
                th.start()
            for th in t_same:
                th.join(timeout=15)
            _check(cw_errs == [] and same_target.read_bytes() in valid_16, f"16T same-target errors: {cw_errs}")

            burst_target = cw_dir / "burst80.json"
            valid_80 = {f'{{"burst":{i}}}\n'.encode("ascii") for i in range(80)}
            bar80 = threading.Barrier(80)

            def _burst_worker(idx: int) -> None:
                data = f'{{"burst":{idx}}}\n'.encode("ascii")
                try:
                    bar80.wait(timeout=10)
                    audit.write_regular_bytes_safe(burst_target, data, f"bw_{idx}")
                except BaseException as exc:
                    cw_errs.append(f"burst_{idx}:{exc}")

            t_burst = [threading.Thread(target=_burst_worker, args=(i,)) for i in range(80)]
            for th in t_burst:
                th.start()
            for th in t_burst:
                th.join(timeout=20)
            cw_leftovers = [p.name for p in cw_dir.iterdir() if p.name.startswith(".s22c.")]
            _check(
                cw_errs == [] and burst_target.read_bytes() in valid_80 and cw_leftovers == [],
                f"80T burst errors={cw_errs} leftovers={cw_leftovers}",
            )


if __name__ == "__main__":
    unittest.main()
