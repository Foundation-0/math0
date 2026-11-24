#!/usr/bin/env python3
"""Borel-Ecalle Resurgence & Zagier Quantum Modularity Verification Test Suite.

Pure Python 3 stdlib, zero bare asserts, zero AST float literals.
Covers:
  - Test 1: Full 4-pillar exact Z/Q mathematical verification & certificate match
  - Test 2: Exported helper soundness, exact algebra & domain negative controls
  - Test 3: Strict fail-closed I/O hardening (atomic dir_fd PWD/ancestor/leaf, 0o600 temp
            mode, /proc/kallsyms, scratch FIFO, chmod 000, hardlink, deep/dotdot
            symlinks, Darwin system prefix normalization, deleted-CWD, lone surrogates,
            strict RFC 8259 ASCII int parser, canonical_json_bytes tree validation,
            full_replay=True/False + exact-int bool-proof secondary_audit_payload,
            flag/equals CLI refusal, subprocess parity)
  - Test 4: Live multi-thread concurrent atomic writer (16T distinct + 16T same-target
            + 80T barrier burst) + live >= 520-iter renameat2(RENAME_EXCHANGE) +
            >= 420-iter os.link/os.unlink hardlink race stress (0 leaks, 0 clobbers, 0 temps)
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
import unittest
from typing import Any

ROOT = Path(__file__).resolve().parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import resurgence_quantum_modularity_audit as audit  # noqa: E402
import resurgence_quantum_modularity_oracle as oracle  # noqa: E402

CERT_PATH = ROOT / audit.DEFAULT_CERT_NAME
_AT_FDCWD = -100
_RENAME_EXCHANGE = 2


class _EvilPath(type(Path())):
    """Path subclass rejected by strict concrete pathlib.Path check."""


class _StrSub(str):
    """str subclass rejected by strict type(x) is str check."""


class _IntSub(int):
    """int subclass rejected by strict type(x) is int check."""


class _DictSub(dict):
    """dict subclass rejected by strict type(x) is dict check."""


class _ListSub(list):
    """list subclass rejected by strict type(x) is list check."""


class _BoolLike:
    def __bool__(self) -> bool:
        return True


def _check(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


def _expect_err(fn: Any, expected_code: str, label: str) -> None:
    try:
        fn()
    except oracle.ResurgenceError as exc:
        if exc.code != expected_code:
            raise AssertionError(f"{label}: expected {expected_code}, got {exc.code} ({exc})") from exc
        return
    raise AssertionError(f"{label}: expected ResurgenceError({expected_code}), but succeeded")


def _rehash_cert(cert: dict[str, Any]) -> dict[str, Any]:
    psha = hashlib.sha256(audit.canonical_json_bytes(cert["payload"])).hexdigest()
    cert["payload_sha256"] = psha
    env = {
        "schema_version": cert["schema_version"],
        "track_id": cert["track_id"],
        "payload_sha256": psha,
        "payload": cert["payload"],
    }
    cert["certificate_sha256"] = hashlib.sha256(audit.canonical_json_bytes(env)).hexdigest()
    return cert


class TrackS27Tests(unittest.TestCase):
    def test_01_four_pillars_exact_math_and_certificate(self) -> None:
        cert = audit.build_certificate()
        disk_bytes = CERT_PATH.read_bytes()
        _check(audit.canonical_json_bytes(cert) == disk_bytes, "on-disk certificate drift")
        res_t = audit.verify_certificate_dict(cert, expected=cert, full_replay=True)
        res_f = audit.verify_certificate_dict(cert, full_replay=False)
        _check(res_t["valid"] is True and res_t["full_replay"] is True, "verify full_replay=True failed")
        _check(res_f["valid"] is True and res_f["full_replay"] is False, "verify full_replay=False failed")
        _check(audit.verify_certificate_file(CERT_PATH) == res_t, "verify_certificate_file mismatch")

        pl = cert["payload"]
        _check(pl["track_id"] == oracle.TRACK_ID and pl["novelty_class"] == "N1", "metadata mismatch")

        # Pillar 1
        p1 = pl["pillar1_borel_euler"]
        _check(p1["all_verified"] is True and p1["euler_order_N"] == 20, "P1 all_verified")
        _check(p1["borel_pole_closure_exact"] is True and p1["borel_derivative_rule_exact"] is True, "P1 pole/deriv")
        _check(p1["borel_convolution_homomorphism_exact"] is True and p1["borel_convolution_associative"] is True, "P1 conv")
        tr = p1["superasymptotic_truncation_z_1_10"]
        _check(tr["n_star"] == 10 and tr["term_10_mag"] == "567/15625000" and tr["minimal_at_n9_and_n10"] is True, "P1 trunc")

        # Pillar 2
        p2 = pl["pillar2_alien_bridge_stokes"]
        _check(p2["all_verified"] is True and p2["linear_euler_bridge_and_stokes_exact"] is True, "P2 Euler")
        _check(p2["alien_leibniz_rule_exact"] is True and p2["riccati_c1_exact_polynomial_control"] is True, "P2 Leibniz/c1")
        ric = p2["riccati_c_half"]
        _check(ric["all_3_sector_ode_residuals_zero"] is True and ric["stokes_automorphism_3sector_exact"] is True, "P2 Riccati")
        _check(ric["a0_first_8"][:4] == ["1", "-1/2", "1/2", "-7/8"] and ric["psi1_first_6"][:3] == ["1", "-1/2", "3/8"], "P2 coeffs")
        _check(ric["monotone_convergence_verified"] is True and ric["stokes_C_matches_inv_pi_within_1e5"] is True, "P2 large-order")

        # Pillar 3
        p3 = pl["pillar3_bernoulli_stirling_eisenstein"]
        _check(p3["all_verified"] is True and p3["odd_bernoulli_vanish_B3_to_B23"] is True, "P3 Bernoulli")
        _check(p3["bernoulli_even_B2_to_B24"]["B_2"] == "1/6" and p3["bernoulli_even_B2_to_B24"]["B_12"] == "-691/2730", "P3 B2/B12")
        _check(p3["bernoulli_even_B2_to_B24"]["B_24"] == "-236364091/2730", "P3 B24")
        _check(p3["stirling_c1_to_c6"][:4] == ["1/12", "-1/360", "1/1260", "-1/1680"], "P3 Stirling")
        _check(p3["stirling_ratio_crosses_1_at_k4_to_5"] is True and p3["borel_pole_lattice_2pi_i_bounds_exact"] is True, "P3 divergence")
        _check(p3["euler_maclaurin_power_sums_p1_to_5_exact"] is True and p3["eisenstein_bridge_s22a"]["E4_squared_equals_E8_mod_q13"] is True, "P3 EM/E8")

        # Pillar 4
        p4 = pl["pillar4_zagier_quantum_modularity"]
        _check(p4["all_verified"] is True, "P4 all_verified")
        rt = p4["kontsevich_roots_of_unity"]
        _check(rt["F_1"] == [1, 0] and rt["F_minus1"] == [3, 0] and rt["F_i_in_Z_i"] == [8, -3], "P4 F(1,-1,i)")
        _check(rt["F_omega_in_Z_omega"] == [5, -1] and rt["F_zeta6_in_Z_omega"] == [4, -13], "P4 F(w,z6)")
        _check(p4["fishburn_A022493_0_to_10"] == [1, 1, 2, 5, 15, 53, 217, 1014, 5335, 31240, 201608], "P4 Fishburn")
        _check(p4["zagier_strange_identity_L_match_all_10"] is True and p4["zagier_strange_identity_C0_to_C9"][1] == 23, "P4 Zagier")
        tb = p4["trefoil_habiro_s23b_bridge"]
        _check(tb["J2_matches_S23b_V31"] is True and tb["kashaev_collapse_N2_N3_N4"] == [True, True, True], "P4 Kashaev")
        _check(tb["s23b_SU2_levels_k1_k2_k4_match"] is True and tb["s23b_k4_norm_sq"] == 3, "P4 S23b levels")

    def test_02_exported_helpers_soundness_and_negative_controls(self) -> None:
        # Strict primitive guards
        _expect_err(lambda: oracle.require_ok(1, "X", "m"), "INVALID_CONDITION_TYPE", "int cond")
        _expect_err(lambda: oracle.require_ok(_BoolLike(), "X", "m"), "INVALID_CONDITION_TYPE", "boollike")
        _expect_err(lambda: oracle.require_ok(False, "MY_CODE", "boom"), "MY_CODE", "false cond")
        oracle.require_ok(True, "OK", "ok")

        _expect_err(lambda: oracle.require_exact_int(True, "n"), "INVALID_INT_TYPE", "bool as int")
        _expect_err(lambda: oracle.require_exact_int(_IntSub(3), "n"), "INVALID_INT_TYPE", "int sub")
        _expect_err(lambda: oracle.require_exact_int(1 << oracle.MAX_INT_BITS, "n"), "INT_BIT_LIMIT", "bit cap")
        _check(oracle.require_exact_int((1 << oracle.MAX_INT_BITS) - 1, "n") > 0, "exact max bits")
        _expect_err(lambda: oracle.require_exact_int(0, "n", lo=1), "INT_OUT_OF_RANGE", "below lo")
        _expect_err(lambda: oracle.require_exact_int(6, "n", lo=1, hi=5), "INT_OUT_OF_RANGE", "above hi")
        _check(oracle.require_exact_int(5, "n", lo=1, hi=5) == 5, "exact hi")
        _expect_err(lambda: oracle.require_exact_bool(1, "b"), "INVALID_BOOL_TYPE", "int bool")
        _check(oracle.require_exact_bool(False, "b") is False, "false bool")
        _expect_err(lambda: oracle.require_exact_fraction(1, "q"), "INVALID_FRACTION_TYPE", "int frac")
        _expect_err(lambda: oracle.require_exact_fraction(Fraction(1 << oracle.MAX_RATIONAL_BITS, 1), "q"), "RATIONAL_BIT_LIMIT", "num cap")
        _expect_err(lambda: oracle.require_exact_fraction(Fraction(1, 1 << oracle.MAX_RATIONAL_BITS), "q"), "RATIONAL_BIT_LIMIT", "den cap")
        _expect_err(lambda: oracle.format_fraction(Fraction(1 << 15_000, 1)), "RATIONAL_BIT_LIMIT", "15000-bit format_fraction")
        _expect_err(lambda: oracle.format_decimal_trunc(Fraction(1 << 15_000, 1), 6), "RATIONAL_BIT_LIMIT", "15000-bit format_decimal")
        max_rat = Fraction((1 << oracle.MAX_RATIONAL_BITS) - 1, 1)
        _check(len(oracle.format_fraction(max_rat)) > 0 and oracle.format_decimal_trunc(max_rat, 2).endswith(".00"), "exact max rational bits")
        _check(oracle.format_fraction(Fraction(4, 2)) == "2" and oracle.format_fraction(Fraction(5, 2)) == "5/2", "format frac")

        # Exact decimal formatting including -0.00 normalization & places=0
        _check(oracle.format_decimal_trunc(Fraction(-1, 1000), 2) == "0.00", "-0.00 normalized")
        _check(oracle.format_decimal_trunc(Fraction(-1, 1000), 0) == "0", "-0 places=0 normalized")
        _check(oracle.format_decimal_trunc(Fraction(-7, 2), 2) == "-3.50" and oracle.format_decimal_trunc(Fraction(7, 2), 0) == "3", "signed trunc")

        # Series / polynomial / Borel guards
        _expect_err(lambda: oracle.require_fraction_series((Fraction(1, 1),), "s"), "INVALID_SERIES_TYPE", "tuple series")
        _expect_err(lambda: oracle.require_fraction_series([], "s"), "INVALID_SERIES_LEN", "empty series")
        _check(len(oracle.require_fraction_series([Fraction(1, 1)] * 128, "s")) == 128, "exact max_len 128")
        _expect_err(lambda: oracle.require_fraction_series([Fraction(1, 1)] * 129, "s"), "INVALID_SERIES_LEN", "too long series")
        _expect_err(lambda: oracle.require_fraction_series([1], "s"), "INVALID_FRACTION_TYPE", "raw int in series")
        _check(oracle.poly_mul_exact([Fraction(1, 1), Fraction(0, 1), Fraction(2, 1)], [Fraction(3, 1), Fraction(0, 1)], 1) == [Fraction(3, 1), Fraction(0, 1)], "poly_mul trunc")
        _check(oracle.series_z_shift_mul([Fraction(0, 1), Fraction(1, 1)], [Fraction(0, 1), Fraction(1, 1)], 2) == [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)], "z_shift zero")
        _check(oracle.borel_convolve([Fraction(1, 1), Fraction(0, 1)], [Fraction(1, 1), Fraction(0, 1)], 1) == [Fraction(0, 1), Fraction(1, 1)], "borel_convolve deg 1")
        _check(oracle.borel_convolve([Fraction(1, 1)], [Fraction(1, 1)], 0) == [Fraction(0, 1)], "borel_convolve deg 0")

        # Riccati & Stokes guards
        _expect_err(lambda: oracle.riccati_transseries_sectors(Fraction(1, 3), 6), "INVALID_RICCATI_C", "non-half-int c")
        _expect_err(lambda: oracle.riccati_transseries_sectors(Fraction(0, 1), 6), "INVALID_RICCATI_C", "zero c")
        _expect_err(lambda: oracle.riccati_transseries_sectors(Fraction(-1, 2), 6), "INVALID_RICCATI_C", "negative c")
        _expect_err(lambda: oracle.stokes_shift_transseries([], Fraction(0, 1), Fraction(1, 1)), "INVALID_SECTORS", "empty sectors")
        _expect_err(lambda: oracle.stokes_shift_transseries(([Fraction(1, 1)],), Fraction(0, 1), Fraction(1, 1)), "INVALID_SECTORS", "tuple sectors")
        _expect_err(lambda: oracle.stokes_shift_transseries([[Fraction(1, 1)]] * 9, Fraction(0, 1), Fraction(1, 1)), "INVALID_SECTORS", "9 sectors")
        _check(oracle._pi_machin_enclosure(7)[0] < oracle._pi_machin_enclosure(7)[1], "odd-term machin enclosure")

        # Bernoulli, divisor sum, Kontsevich, Fishburn, Habiro guards
        _check(oracle.bernoulli_numbers_exact(0) == [Fraction(1, 1)], "B_0 only")
        _check(oracle.sigma_divisor_sum(6, 1) == 12 and oracle.sigma_divisor_sum(1, 0) == 1, "sigma")
        _expect_err(lambda: oracle.kontsevich_f_root_of_unity(5), "UNSUPPORTED_ROOT_ORDER", "unsupported order 5")
        _check(oracle.fishburn_numbers_exact(0) == [1], "fishburn deg 0")
        _check(oracle.habiro_trefoil_colored_jones(1) == {0: 1}, "habiro N=1")

    def test_03_zone_b_hardening_symlinks_pwd_cwd_surrogates_and_cli(self) -> None:
        cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
        cert_bytes = CERT_PATH.read_bytes()

        # Hex64 + verify_certificate_dict + full_replay=True/False + bool-proof secondary_audit_payload
        _expect_err(lambda: audit.require_hex64_lower_ascii("a" * 63, "h"), "INVALID_HEX64", "len 63")
        _expect_err(lambda: audit.require_hex64_lower_ascii("A" * 64, "h"), "INVALID_HEX64", "uppercase hex")
        _expect_err(lambda: audit.require_hex64_lower_ascii(123, "h"), "INVALID_HEX64", "int hex")
        _expect_err(lambda: audit.verify_certificate_dict(cert, full_replay="yes"), "INVALID_BOOL_TYPE", "str full_replay")
        _expect_err(lambda: audit.verify_certificate_file(CERT_PATH, full_replay="yes"), "INVALID_BOOL_TYPE", "file str full_replay")
        _expect_err(lambda: audit.verify_certificate_dict([]), "INVALID_CERT_TYPE", "list cert")
        bad_k = copy.deepcopy(cert)
        bad_k["extra"] = 1
        _expect_err(lambda: audit.verify_certificate_dict(bad_k, expected=cert), "INVALID_CERT_KEYS", "extra key")
        bad_sc = copy.deepcopy(cert)
        bad_sc["schema_version"] = "9.9.9"
        _expect_err(lambda: audit.verify_certificate_dict(bad_sc, full_replay=False), "INVALID_SCHEMA", "bad schema")
        bad_tk = copy.deepcopy(cert)
        bad_tk["track_id"] = "WRONG"
        _expect_err(lambda: audit.verify_certificate_dict(bad_tk, full_replay=False), "INVALID_TRACK_ID", "bad track")
        bad_psha = copy.deepcopy(cert)
        bad_psha["payload_sha256"] = "0" * 64
        _expect_err(lambda: audit.verify_certificate_dict(bad_psha, expected=cert), "PAYLOAD_SHA_MISMATCH", "bad psha")
        bad_csha = copy.deepcopy(cert)
        bad_csha["certificate_sha256"] = "0" * 64
        _expect_err(lambda: audit.verify_certificate_dict(bad_csha, expected=cert), "CERTIFICATE_SHA_MISMATCH", "bad csha")
        _expect_err(lambda: audit.verify_certificate_dict(bad_csha, full_replay=False), "CERTIFICATE_SHA_MISMATCH", "bad csha no-replay")

        # Self-consistent rehashed tampered payloads: caught by secondary_audit_payload even when full_replay=False,
        # and verified against expected replay digests when full_replay=True!
        bad_rehash_sec = _rehash_cert(copy.deepcopy(cert))
        bad_rehash_sec["payload"]["pillar1_borel_euler"]["euler_order_N"] = 99
        _rehash_cert(bad_rehash_sec)
        _expect_err(lambda: audit.verify_certificate_dict(bad_rehash_sec, full_replay=False), "ALGEBRAIC_CROSSCHECK_FAILED", "rehashed tamper full_replay=False")

        for mutate_resign, lbl in (
            (lambda p: p["pillar1_borel_euler"].__setitem__("borel_pole_location", "-2"), "pole loc"),
            (lambda p: p["pillar1_borel_euler"].__setitem__("euler_ode_residual_zero", False), "euler ode"),
            (lambda p: p["pillar2_alien_bridge_stokes"]["riccati_c_half"].__setitem__("monotone_convergence_verified", False), "riccati mono"),
            (lambda p: p["pillar3_bernoulli_stirling_eisenstein"]["bernoulli_even_B2_to_B24"].__setitem__("B_12", "0"), "B_12 zero"),
            (lambda p: p["pillar3_bernoulli_stirling_eisenstein"].__setitem__("stirling_c1_to_c6", []), "empty stirling"),
            (lambda p: p["pillar4_zagier_quantum_modularity"]["fishburn_A022493_0_to_10"].__setitem__(1, -999), "fish[1]"),
            (lambda p: p["pillar4_zagier_quantum_modularity"]["zagier_strange_identity_C0_to_C9"].__setitem__(0, -999), "zag[0]"),
            (lambda p: p["pillar4_zagier_quantum_modularity"]["trefoil_habiro_s23b_bridge"].__setitem__("J2_coeffs", {}), "empty J2"),
            (lambda p: p["pillar4_zagier_quantum_modularity"]["trefoil_habiro_s23b_bridge"].__setitem__("kashaev_collapse_N2_N3_N4", [False, False, False]), "kashaev"),
            (lambda p: p.__setitem__("novelty_class", "N9"), "novelty_class"),
        ):
            rc = copy.deepcopy(cert)
            mutate_resign(rc["payload"])
            _rehash_cert(rc)
            _expect_err(lambda x=rc: audit.verify_certificate_dict(x, full_replay=False), "ALGEBRAIC_CROSSCHECK_FAILED", f"FR=False {lbl}")

        # Extra key rejected across ALL 14 nested dicts under BOTH verify_certificate_dict(full_replay=False) & secondary_audit_payload
        dict_paths: list[tuple[str, ...]] = []
        def _walk_dicts(obj: Any, path: tuple[str, ...] = ()) -> None:
            if type(obj) is dict:
                dict_paths.append(path)
                for k, v in obj.items():
                    _walk_dicts(v, path + (k,))
        _walk_dicts(cert["payload"])
        _check(len(dict_paths) == 14, f"expected 14 nested dicts, got {len(dict_paths)}")
        for dp in dict_paths:
            rc = copy.deepcopy(cert)
            cur = rc["payload"]
            for k in dp:
                cur = cur[k]
            cur["__ROGUE__"] = 1
            _expect_err(lambda x=rc["payload"]: audit.secondary_audit_payload(x), "ALGEBRAIC_CROSSCHECK_FAILED", f"sec extra key {dp}")
            _rehash_cert(rc)
            _expect_err(lambda x=rc: audit.verify_certificate_dict(x, full_replay=False), "ALGEBRAIC_CROSSCHECK_FAILED", f"FR0 extra key {dp}")

        # Mocked expected mismatch on psha, csha & canonical bytes
        fake_exp_psha = copy.deepcopy(cert)
        fake_exp_psha["payload_sha256"] = "0" * 64
        _expect_err(lambda: audit.verify_certificate_dict(cert, expected=fake_exp_psha, full_replay=True), "PAYLOAD_SHA_MISMATCH", "replay psha mismatch")
        fake_exp_csha = copy.deepcopy(cert)
        fake_exp_csha["certificate_sha256"] = "0" * 64
        _expect_err(lambda: audit.verify_certificate_dict(cert, expected=fake_exp_csha, full_replay=True), "CERTIFICATE_SHA_MISMATCH", "replay csha mismatch")
        fake_exp_body = copy.deepcopy(cert)
        fake_exp_body["payload"]["novelty_class"] = "N9"
        _expect_err(lambda: audit.verify_certificate_dict(cert, expected=fake_exp_body, full_replay=True), "CERTIFICATE_MISMATCH", "replay body mismatch")

        # Direct secondary_audit_payload float, subclass, bool-for-int, & hollow dict probes
        _expect_err(lambda: audit.secondary_audit_payload("not_dict"), "ALGEBRAIC_CROSSCHECK_FAILED", "str payload")
        _expect_err(lambda: audit.secondary_audit_payload(_DictSub(copy.deepcopy(cert["payload"]))), "ALGEBRAIC_CROSSCHECK_FAILED", "DictSub payload")
        _expect_err(lambda: audit.secondary_audit_payload({}), "ALGEBRAIC_CROSSCHECK_FAILED", "empty payload")
        _expect_err(lambda: audit.secondary_audit_payload({"pillar1_borel_euler": None}), "ALGEBRAIC_CROSSCHECK_FAILED", "null section")
        bad_leaf = copy.deepcopy(cert["payload"])
        bad_leaf["pillar1_borel_euler"]["superasymptotic_truncation_z_1_10"] = None
        _expect_err(lambda: audit.secondary_audit_payload(bad_leaf), "ALGEBRAIC_CROSSCHECK_FAILED", "null leaf section")
        bad_bool = copy.deepcopy(cert["payload"])
        bad_bool["pillar4_zagier_quantum_modularity"]["fishburn_A022493_0_to_10"][0] = True
        _expect_err(lambda: audit.secondary_audit_payload(bad_bool), "ALGEBRAIC_CROSSCHECK_FAILED", "bool-for-int fish[0]")
        for mutate_fn, exp_c, lbl in (
            (lambda p: p.__setitem__("novelty_class", _StrSub("N1")), "INVALID_JSON_VALUE", "StrSub novelty"),
            (lambda p: p["pillar1_borel_euler"].__setitem__("euler_order_N", _IntSub(20)), "INVALID_JSON_VALUE", "IntSub order"),
            (lambda p: p.__setitem__("pillar1_borel_euler", _DictSub(p["pillar1_borel_euler"])), "INVALID_JSON_VALUE", "DictSub p1"),
            (lambda p: p["pillar4_zagier_quantum_modularity"].__setitem__("fishburn_A022493_0_to_10", _ListSub(p["pillar4_zagier_quantum_modularity"]["fishburn_A022493_0_to_10"])), "INVALID_JSON_VALUE", "ListSub fish"),
            (lambda p: p["pillar1_borel_euler"].__setitem__("borel_pole_location", 3 / 2), "INVALID_JSON_VALUE", "float pole"),
            (lambda p: p["pillar4_zagier_quantum_modularity"].__setitem__("fishburn_A022493_0_to_10", tuple(p["pillar4_zagier_quantum_modularity"]["fishburn_A022493_0_to_10"])), "INVALID_JSON_VALUE", "tuple fish"),
            (lambda p: p["pillar4_zagier_quantum_modularity"].__setitem__("fishburn_A022493_0_to_10", [1]), "ALGEBRAIC_CROSSCHECK_FAILED", "short fish"),
            (lambda p: p["pillar4_zagier_quantum_modularity"]["fishburn_A022493_0_to_10"].__setitem__(8, 0), "ALGEBRAIC_CROSSCHECK_FAILED", "bad fish[8]"),
        ):
            bp = copy.deepcopy(cert["payload"])
            mutate_fn(bp)
            _expect_err(lambda x=bp: audit.secondary_audit_payload(x), exp_c, lbl)

        # Strict JSON tree, RFC 8259 ASCII int parser, & canonical_json_bytes guards
        _check(audit.parse_strict_json_text("[1,true,null]", "arr", require_object=False) == [1, True, None], "arr parse")
        _check(audit.parse_strict_json_text('{"n":' + str((1 << oracle.MAX_INT_BITS) - 1) + "}", "maxb")["n"] > 0, "exact 3322-bit int")
        _check(audit.parse_strict_json_text('{"n":-' + str((1 << oracle.MAX_INT_BITS) - 1) + "}", "negd")["n"] < 0, "exact neg 3322-bit int")
        _check(audit._parse_bounded_int("0") == 0 and audit._parse_bounded_int("-5") == -5 and audit._parse_bounded_int("10") == 10, "valid ints")
        for bad_tok in (12, _StrSub("5"), "", "-", "١٢", "-١٢", "²", "+12", "1_2", "007", "-01", "-0"):
            _expect_err(lambda t=bad_tok: audit._parse_bounded_int(t), "INVALID_JSON_INT", f"bad int token {bad_tok!r}")
        _expect_err(lambda: audit._parse_bounded_int("9" * audit.MAX_JSON_INT_DIGITS), "INT_BIT_LIMIT", "direct 3326-bit token")
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
        _expect_err(lambda: audit.parse_strict_json_text('{"n":' + "9" * audit.MAX_JSON_INT_DIGITS + "}", "x"), "INT_BIT_LIMIT", "1001-digit > 3322-bit")
        _expect_err(lambda: audit.parse_strict_json_text("[1]", "x", require_object=True), "JSON_ROOT_NOT_OBJECT", "list root")
        _expect_err(lambda: audit.parse_strict_json_text("{bad", "x"), "INVALID_JSON", "syntax error")
        exact_js = '{"k":"' + ("a" * 32) + '"}'
        _check(len(audit.parse_strict_json_text(exact_js, "exact_sz", max_bytes=len(exact_js))["k"]) == 32, "exact max_bytes")
        _expect_err(lambda: audit.parse_strict_json_text(exact_js, "over_sz", max_bytes=len(exact_js) - 1), "JSON_TOO_LARGE", "max_bytes-1")
        _expect_err(lambda: audit.parse_strict_json_text('{"k":"' + ("a" * audit.MAX_JSON_BYTES) + '"}', "over_1mb"), "JSON_TOO_LARGE", ">1 MiB default")
        _expect_err(lambda: audit._validate_json_tree({1: "x"}, "k"), "INVALID_JSON_KEY", "int key")
        _expect_err(lambda: audit._validate_json_tree({"n": 1 << oracle.MAX_INT_BITS}, "b"), "INT_BIT_LIMIT", "3323-bit int")
        _expect_err(lambda: audit._validate_json_tree({"f": 3 / 2}, "f"), "INVALID_JSON_VALUE", "float in tree")
        _expect_err(lambda: audit.canonical_json_bytes({"f": 3 / 2}), "INVALID_JSON_VALUE", "float canonical")
        _expect_err(lambda: audit.canonical_json_bytes({"n": 10**4300}), "INT_BIT_LIMIT", "10**4300 canonical")
        cyc: dict[str, Any] = {}
        cyc["self"] = cyc
        _expect_err(lambda: audit.canonical_json_bytes(cyc), "MAX_DEPTH_EXCEEDED", "cyclic canonical")

        ok_d: Any = 1
        for _ in range(audit.MAX_JSON_DEPTH - 1):
            ok_d = [ok_d]
        _check(type(audit.parse_strict_json_text(json.dumps({"x": ok_d}), "d64")) is dict, "depth 64 failed")
        _expect_err(lambda: audit.parse_strict_json_text(json.dumps({"x": [ok_d]}), "d65"), "MAX_DEPTH_EXCEEDED", "depth 65")

        # /proc/kallsyms st_size==0 capped read + scratch FIFO non-regular write guard
        proc_kallsyms = Path("/proc/kallsyms")
        if proc_kallsyms.exists():
            _expect_err(lambda: audit.read_regular_bytes_capped(proc_kallsyms, "kallsyms", max_bytes=16), "FILE_TOO_LARGE", "kallsyms cap")
        if hasattr(os, "mkfifo"):
            with tempfile.TemporaryDirectory(prefix="s27_fifo_") as ftd:
                scratch_fifo = Path(ftd) / "nonreg.fifo"
                os.mkfifo(scratch_fifo)
                _expect_err(
                    lambda: audit.write_regular_bytes_safe(scratch_fifo, b"{}\n", "nonreg_fifo"),
                    "NOT_A_REGULAR_FILE",
                    "scratch FIFO write",
                )

        # Mocked macOS Darwin /var, /tmp, /etc root-owned system alias normalization
        from unittest import mock as _mock
        _fake_root_lnk = os.stat_result((stat.S_IFLNK | 0o777, 0, 0, 1, 0, 0, 0, 0, 0, 0))
        _fake_nonroot_lnk = os.stat_result((stat.S_IFLNK | 0o777, 0, 0, 1, 1000, 0, 0, 0, 0, 0))
        _fake_root_dir = os.stat_result((stat.S_IFDIR | 0o755, 0, 0, 2, 0, 0, 0, 0, 0, 0))
        with _mock.patch.object(audit.sys, "platform", "linux"), _mock.patch.object(audit.os, "lstat", return_value=_fake_root_lnk), _mock.patch.object(audit.os, "readlink", return_value="private/var"):
            _check(audit._normalize_darwin_system_prefix(Path("/var/folders/x")) == Path("/var/folders/x"), "non-darwin unchanged")
        with _mock.patch.object(audit.sys, "platform", "darwin"):
            with _mock.patch.object(audit.os, "lstat", return_value=_fake_root_lnk), _mock.patch.object(audit.os, "readlink", return_value="private/var"):
                _check(audit._normalize_darwin_system_prefix(Path("var/folders/x")) == Path("var/folders/x"), "darwin relative unchanged")
                _check(audit._normalize_darwin_system_prefix(Path("a/var/x")) == Path("a/var/x"), "darwin relative with parts[1]==var unchanged")
                _check(audit._normalize_darwin_system_prefix(Path("/var")) == Path("/var"), "darwin exact /var unchanged by default")
                _check(audit._normalize_darwin_system_prefix(Path("/var"), allow_exact=True) == Path("/private/var"), "darwin allow_exact /var normalized")
                _check(audit._normalize_darwin_system_prefix(Path("/var/../etc/x")) == Path("/var/../etc/x"), "darwin dotdot unchanged")
                _check(audit._normalize_darwin_system_prefix(Path("/usr/local/x")) == Path("/usr/local/x"), "darwin non-alias unchanged")
                _check(audit._normalize_darwin_system_prefix(Path("/var/folders/x")) == Path("/private/var/folders/x"), "darwin relative readlink normalized")
            with _mock.patch.object(audit.os, "lstat", return_value=_fake_root_lnk), _mock.patch.object(audit.os, "readlink", return_value="/private/tmp"):
                _check(audit._normalize_darwin_system_prefix(Path("/tmp/a/b")) == Path("/private/tmp/a/b"), "darwin absolute readlink normalized")
            with _mock.patch.object(audit.os, "lstat", return_value=_fake_root_lnk), _mock.patch.object(audit.os, "readlink", return_value="/evil"):
                _check(audit._normalize_darwin_system_prefix(Path("/var/folders/x")) == Path("/var/folders/x"), "darwin bad target unchanged")
            with _mock.patch.object(audit.os, "lstat", return_value=_fake_nonroot_lnk), _mock.patch.object(audit.os, "readlink", return_value="private/var"):
                _check(audit._normalize_darwin_system_prefix(Path("/var/folders/x")) == Path("/var/folders/x"), "darwin non-root symlink unchanged")
            with _mock.patch.object(audit.os, "lstat", return_value=_fake_root_dir), _mock.patch.object(audit.os, "readlink", return_value="private/var"):
                _check(audit._normalize_darwin_system_prefix(Path("/var/folders/x")) == Path("/var/folders/x"), "darwin non-symlink unchanged")
            with _mock.patch.object(audit.os, "lstat", side_effect=OSError("no lstat")):
                _check(audit._normalize_darwin_system_prefix(Path("/var/folders/x")) == Path("/var/folders/x"), "darwin lstat OSError unchanged")

        with tempfile.TemporaryDirectory(prefix="s27_zb_") as td:
            root = Path(td)
            cfile = root / "c.json"
            audit.write_regular_bytes_safe(cfile, cert_bytes, "c")
            _check(stat.S_IMODE(os.lstat(cfile).st_mode) == 0o600, "written file mode must be 0o600")
            audit.write_regular_bytes_safe(cfile, b"{}\n", "c_short")
            _check(cfile.read_bytes() == b"{}\n", "atomic replace shorter failed")
            audit.write_regular_bytes_safe(cfile, cert_bytes, "c_restore")
            nested = root / "nested_a" / "sub_b" / "w.json"
            audit.write_regular_bytes_safe(nested, cert_bytes, "nested")
            _check(nested.read_bytes() == cert_bytes, "nested dir_fd create failed")
            _check(audit.read_regular_bytes_capped(cfile, "c", max_bytes=len(cert_bytes)) == cert_bytes, "exact max_bytes")
            _check(audit.read_regular_bytes_capped(cfile, "c_cap", max_bytes=audit.MAX_READ_CAP_BYTES) == cert_bytes, "max cap read")
            _expect_err(lambda: audit.read_regular_bytes_capped(cfile, "c", max_bytes=len(cert_bytes) - 1), "FILE_TOO_LARGE", "max_bytes-1")
            _expect_err(lambda: audit.read_regular_bytes_capped(cfile, "big1", max_bytes=1 << 100), "INT_OUT_OF_RANGE", "1<<100")
            _expect_err(lambda: audit.read_regular_bytes_capped(cfile, "big2", max_bytes=audit.MAX_READ_CAP_BYTES + 1), "INT_OUT_OF_RANGE", "cap+1")
            _expect_err(lambda: audit.write_regular_bytes_safe(cfile, "not_bytes", "nb"), "INVALID_PAYLOAD_TYPE", "str write")
            _expect_err(lambda: audit.write_regular_bytes_safe(cfile, bytearray(b"{}"), "ba"), "INVALID_PAYLOAD_TYPE", "bytearray write")

            hlink = root / "hlink.json"
            os.link(cfile, hlink)
            try:
                _expect_err(lambda: audit.write_regular_bytes_safe(hlink, b"tamper", "hlink"), "HARDLINK_FORBIDDEN", "hardlink write")
                _check(cfile.read_bytes() == cert_bytes, "hardlink refusal altered target")
            finally:
                hlink.unlink()

            # Pre-replace fstat(fd).st_nlink == 1 guard tested with a real kernel hardlink on the temp file
            orig_fsync = os.fsync
            hijack_link = root / "tmp_hijack.json"
            linked_once = [False]

            def _hijack_fsync(fd_arg: int) -> None:
                if not linked_once[0]:
                    tmps = [p for p in root.iterdir() if ".s27_tmp_" in p.name]
                    if tmps:
                        os.link(tmps[0], hijack_link)
                        linked_once[0] = True
                orig_fsync(fd_arg)

            os.fsync = _hijack_fsync  # type: ignore[assignment]
            try:
                _expect_err(lambda: audit.write_regular_bytes_safe(cfile, b'{"hijack":1}\n', "tmp_hl"), "HARDLINK_FORBIDDEN", "temp hardlink pre-replace")
                _check(linked_once[0] is True and cfile.read_bytes() == cert_bytes, "temp hardlink altered target")
            finally:
                os.fsync = orig_fsync  # type: ignore[assignment]
                if hijack_link.exists():
                    hijack_link.unlink()

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

            orig_cwd = os.getcwd()
            orig_pwd = os.environ.get("PWD")
            try:
                os.chdir(real_sub)
                os.environ["PWD"] = str(sym_dir / "nested")
                _expect_err(lambda: audit.verify_certificate_file(Path("c.json")), "SYMLINK_ANCESTOR_FORBIDDEN", "symlink PWD")
                os.environ["PWD"] = "/tmp/bad_\udcff_pwd"
                _expect_err(lambda: audit.read_regular_bytes_capped(Path("c.json"), "spwd"), "INVALID_UTF8_SURROGATE", "surrogate PWD")
                os.environ["PWD"] = str(cfile / "non_dir")
                _check(audit.read_regular_bytes_capped(Path("c.json"), "nondir_pwd") == cert_bytes, "non-dir PWD falls through cleanly")
                os.environ["PWD"] = "rel/" + str(sym_dir).lstrip("/")
                _check(audit.read_regular_bytes_capped(Path(".") / "c.json", "relpwd") == cert_bytes, "relative PWD")
                os.environ["PWD"] = str(real_sub)
                _check(audit.read_regular_bytes_capped(Path("c.json"), "realpwd") == cert_bytes, "real PWD")
                os.environ.pop("PWD", None)
                _check(audit.read_regular_bytes_capped(Path("c.json"), "nopwd") == cert_bytes, "unset PWD")

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

            p_def = subprocess.run([sys.executable, "-I", "-O", "-B", str(ROOT / "resurgence_quantum_modularity_audit.py")], capture_output=True, timeout=60)
            _check(p_def.returncode == 0 and p_def.stdout == cert_bytes, "subprocess zero-arg mismatch")
            p_std = subprocess.run([sys.executable, "-I", "-O", "-B", str(ROOT / "resurgence_quantum_modularity_audit.py"), "--standalone", "--json"], capture_output=True, timeout=60)
            _check(p_std.returncode == 0 and p_std.stdout == cert_bytes, "subprocess --standalone mismatch")
            p_pwd = subprocess.run(
                [sys.executable, "-I", "-O", "-B", str(ROOT / "resurgence_quantum_modularity_audit.py"), "--check", "c.json"],
                cwd=str(real_sub),
                env={**os.environ, "PWD": str(sym_dir / "nested")},
                capture_output=True,
                text=True,
                timeout=60,
            )
            _check(p_pwd.returncode == 2 and "SYMLINK_ANCESTOR_FORBIDDEN" in p_pwd.stderr, f"subprocess symlink PWD: {p_pwd.stderr!r}")

    def test_04_live_multithread_renameat2_and_hardlink_races(self) -> None:
        libc = ctypes.CDLL(None, use_errno=True)
        renameat2 = libc.renameat2
        renameat2.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
        renameat2.restype = ctypes.c_int

        with tempfile.TemporaryDirectory(prefix="s27_race_") as td:
            root = Path(td)

            # 4a. 16T distinct-target + 16T same-target + 80T barrier burst concurrent atomic writes
            mt_dir = root / "mt_dir"
            mt_dir.mkdir()
            mt_errors: list[str] = []

            def _w_distinct(tid: int) -> None:
                p = mt_dir / f"t_{tid}.json"
                for k in range(15):
                    try:
                        audit.write_regular_bytes_safe(p, f'{{"t":{tid},"k":{k}}}\n'.encode("ascii"), "mt_d")
                    except Exception as exc:
                        mt_errors.append(f"distinct {tid}: {exc}")

            t_list = [threading.Thread(target=_w_distinct, args=(i,)) for i in range(16)]
            for th in t_list:
                th.start()
            for th in t_list:
                th.join(timeout=15)

            shared = mt_dir / "shared.json"
            def _w_same(tid: int) -> None:
                for k in range(15):
                    try:
                        audit.write_regular_bytes_safe(shared, f'{{"t":{tid},"k":{k}}}\n'.encode("ascii"), "mt_s")
                    except Exception as exc:
                        mt_errors.append(f"same {tid}: {exc}")

            t_list = [threading.Thread(target=_w_same, args=(i,)) for i in range(16)]
            for th in t_list:
                th.start()
            for th in t_list:
                th.join(timeout=15)

            bar = threading.Barrier(80)
            def _w_burst(tid: int) -> None:
                bar.wait(timeout=10)
                try:
                    audit.write_regular_bytes_safe(mt_dir / f"b_{tid}.json", f'{{"b":{tid}}}\n'.encode("ascii"), "mt_b")
                except Exception as exc:
                    mt_errors.append(f"burst {tid}: {exc}")

            t_list = [threading.Thread(target=_w_burst, args=(i,)) for i in range(80)]
            for th in t_list:
                th.start()
            for th in t_list:
                th.join(timeout=15)
            _check(len(mt_errors) == 0, f"multi-thread write errors: {mt_errors[:5]}")
            _check(len([p for p in mt_dir.iterdir() if ".s27_tmp_" in p.name]) == 0, "leftover mt temps")

            # 4b. Pre-replace fstat(fd).st_nlink == 1 check via live link-on-temp probe
            victim = root / "victim.txt"
            victim_bytes = b"DO_NOT_LEAK_OR_CLOBBER\n"
            victim.write_bytes(victim_bytes)

            real_dir = root / "real_dir"
            real_dir.mkdir()
            target_a = real_dir / "target.json"
            target_a.write_bytes(b'{"ok":1}\n')
            sym_leaf = root / "sym_leaf.json"
            os.symlink(victim, sym_leaf)
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
                    except oracle.ResurgenceError:
                        pass
                    try:
                        audit.write_regular_bytes_safe(real_dir / "target.json", b'{"ok":2}\n', "race_w")
                    except oracle.ResurgenceError:
                        pass
                    if victim.read_bytes() != victim_bytes:
                        clobbers += 1
            finally:
                stop_ev.set()
                t.join(timeout=5)
            _check(leaks == 0 and clobbers == 0, f"renameat2 race failed: leaks={leaks}, clobbers={clobbers}")

            # 4c. Live os.link / os.unlink hardlink race stress (>= 420 iterations)
            hl_dir = root / "hl_dir"
            hl_dir.mkdir()
            hl_target = hl_dir / "cert.json"
            hl_alias = hl_dir / "alias.json"
            hl_target.write_bytes(b'{"orig":true}\n')

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
                    try:
                        audit.write_regular_bytes_safe(hl_target, f'{{"iter":{i}}}\n'.encode("ascii"), "hl_w")
                    except oracle.ResurgenceError:
                        pass
                    try:
                        if not hl_alias.read_bytes().endswith(b"}\n"):
                            hl_clobbers += 1
                    except OSError:
                        pass
            finally:
                stop_hl.set()
                t_hl.join(timeout=5)
            _check(hl_clobbers == 0, f"hardlink clobbers={hl_clobbers}")
            leftovers = [p.name for p in hl_dir.iterdir() if ".s27_tmp_" in p.name]
            _check(len(leftovers) == 0, f"leftover temps: {leftovers}")


if __name__ == "__main__":
    unittest.main()
