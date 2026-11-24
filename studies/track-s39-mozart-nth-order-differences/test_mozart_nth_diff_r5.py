#!/usr/bin/env python3
"""Track S39 (Portal 37) R1-R5 Verification & Adversarial Zone-B Test Suite.

Pure Python 3 stdlib, zero bare asserts, zero AST float literals and zero float()
calls (runtime negative fixtures use json.loads("1.5") / json.loads("NaN") /
json.loads("1.0") solely to test fail-closed float rejection in Zone-B parsers).
Covers:
  - Test 1: Full 4-pillar exact Z/Q mathematical verification & certificate parity
  - Test 2: Exact domain, type, boundary, Frobenius, Ducci, S_5 & K.516f guards
  - Test 3: Uniform R2-grade Zone-B Gold Standard (atomic dir_fd PWD/openat,
            0o600 CSPRNG temp + pre-replace st_nlink == 1 + fsync + os.replace,
            64 KiB streaming capped read, canonical_json_bytes tree validation,
            ASCII-only parsers rejecting -0/leading zeros, exact-int
            secondary_audit_payload & full_replay=False verification,
            /proc/kallsyms, /dev/null, FIFO, chmod 000, hardlink, deep/dotdot/PWD
            symlinks, deleted-CWD, lone surrogates, space & equals CLI, subprocess)
  - Test 4: Live >= 520-iter concurrent renameat2(RENAME_EXCHANGE) + >= 420-iter
            concurrent os.link()/os.unlink() hardlink inode-immutability race +
            16T distinct / 16T same-target / 80T barrier burst concurrent writers
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

import mozart_nth_diff_audit as audit  # noqa: E402
import mozart_nth_diff_oracle as oracle  # noqa: E402

CERT_PATH = ROOT / audit.DEFAULT_CERT_NAME
_AT_FDCWD = -100
_RENAME_EXCHANGE = 2


class _EvilPath(type(Path())):
    """Path subclass rejected by strict concrete pathlib.Path check."""


class _StrSub(str):
    """str subclass rejected by strict type(x) is str check."""


class _IntSub(int):
    """int subclass rejected by strict type(x) is int check."""


class _DictSub(dict):  # type: ignore[type-arg]
    """dict subclass rejected by strict type(x) is dict check."""


class _ListSub(list):  # type: ignore[type-arg]
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
    except oracle.MozartNthDiffError as exc:
        if exc.code != expected_code:
            raise AssertionError(f"{label}: expected {expected_code}, got {exc.code} ({exc})") from exc
        return
    raise AssertionError(f"{label}: expected MozartNthDiffError({expected_code}), but succeeded")


class TrackS39Tests(unittest.TestCase):
    def test_01_four_pillars_exact_math_and_certificate(self) -> None:
        cert = audit.build_certificate()
        disk_bytes = CERT_PATH.read_bytes()
        _check(audit.canonical_json_bytes(cert) == disk_bytes, "on-disk certificate drift")
        res = audit.verify_certificate_dict(cert, expected=cert)
        _check(res["valid"] is True, "verify_certificate_dict failed")
        res_nr = audit.verify_certificate_dict(cert, full_replay=False)
        _check(res_nr == res, "verify_certificate_dict(full_replay=False) mismatch")
        res_file = audit.verify_certificate_file(CERT_PATH)
        _check(res_file == res, "verify_certificate_file mismatch")

        pl = cert["payload"]
        _check(
            pl["track_id"] == "TRACK-S39-MOZART-NTH-DIFF"
            and pl["novelty_class"] == "N1"
            and pl["all_pillars_verified"] is True,
            "top-level metadata mismatch",
        )

        # Pillar 1: Frobenius period-p annihilation over Z_12 ~= Z_3 x Z_4
        p1 = pl["pillar1_frobenius_z12"]
        _check(p1["all_verified"] is True, "P1 all_verified")
        _check(
            [c["prime_p"] for c in p1["frobenius_prime_checks"]] == [2, 3, 5, 7]
            and all(c["verified"] is True for c in p1["frobenius_prime_checks"]),
            "P1 prime checks",
        )
        _check(
            [c["order_q"] for c in p1["frobenius_prime_power_checks"]] == [4, 8, 9]
            and all(c["verified"] is True for c in p1["frobenius_prime_power_checks"]),
            "P1 prime-power checks",
        )
        k550 = p1["k550_period3_annihilation"]
        _check(
            k550["delta2_mod3"] == [1, 1, 1, 1, 1, 1, 1, 2]
            and k550["delta3_mod3"] == [0, 0, 0, 0, 0, 0, 1]
            and k550["leap_semitones"] == 8
            and k550["exact_annihilation_verified"] is True,
            "P1 K.550 annihilation",
        )
        k545 = p1["k545_alberti_period4_annihilation"]
        _check(
            k545["delta4_mod2"] == [0] * 12
            and k545["s4_minus_I_exact_Z"] == [0] * 12
            and k545["integer_energies_E1_to_E5"] == [415, 1432, 5248, 19584, 72384],
            "P1 K.545 Alberti",
        )
        crt = p1["crt_z12_decomposition"]
        _check(
            crt["crt_bijection_and_chords_verified"] is True
            and len(crt["augmented_triads_by_r4"]) == 4
            and len(crt["diminished_7ths_by_r3"]) == 3,
            "P1 CRT decomposition",
        )

        # Pillar 2: Nyquist-third spectral prism vs white noise & random walks
        p2 = pl["pillar2_spectral_prism"]
        _check(
            p2["all_verified"] is True
            and p2["white_noise_variances_n1_to_n5"] == [2, 6, 20, 70, 252]
            and p2["white_noise_ratios_R1_to_R5_q"] == ["2", "3", "10/3", "7/2", "18/5"]
            and p2["random_walk_ratios_R2_to_R5_q"] == ["2", "3", "10/3", "7/2"]
            and p2["unity_cutoff_lambda"] == 6
            and p2["nyquist_ceiling"] == 4
            and p2["strict_textural_ordering_verified"] is True,
            "P2 spectral prism",
        )
        _check(
            [r["gain_exact"] for r in p2["sinusoidal_gain_table"]] == [0, 1, 2, 3, 4],
            "P2 sinusoidal gain table",
        )
        r2_by_name = {r["name"]: r["ratios_R2_to_R5_q"][0] for r in p2["mozart_corpus_prism"]}
        _check(
            r2_by_name == {
                "Scale": "1/6",
                "K.550": "161/87",
                "K.331": "193/92",
                "K.525": "808/291",
                "K.545_Mel": "661/248",
                "K.545_Alberti": "1432/415",
            },
            "P2 exact rational R2 values",
        )

        # Pillar 3: Ducci 2^k classical phrase nilpotence
        p3 = pl["pillar3_ducci_nilpotence"]
        _check(p3["all_verified"] is True and p3["nilpotent_iff_power_of_2_L2_to_L12"] is True, "P3 verified")
        ducci_map = {r["case_id"]: r for r in p3["mozart_ducci_orbits"]}
        _check(
            ducci_map["K551_4note_CDFE"]["steps_to_zero"] == 4
            and ducci_map["K551_8note_CDFE_EDCB"]["steps_to_zero"] == 7
            and ducci_map["K545_Alberti_L4"]["steps_to_zero"] == 4
            and ducci_map["K550_8note_phrase"]["steps_to_zero"] == 8
            and ducci_map["K550_3note_sigh_L3"]["cycle_period"] == 3
            and ducci_map["K550_3note_sigh_L3"]["cycle_entry_step"] == 1
            and ducci_map["K550_3note_sigh_L3"]["terminal_state"] == [1, 0, 1]
            and ducci_map["K331_6_8_bar_L6"]["cycle_period"] == 6
            and ducci_map["K331_6_8_bar_L6"]["cycle_entry_step"] == 4
            and ducci_map["K331_6_8_bar_L6"]["terminal_state"] == [1, 1, 0, 0, 1, 1],
            "P3 Mozart Ducci orbits",
        )
        f2_zero_lens = [r["L"] for r in p3["f2_impulse_characterization_L2_to_L12"] if r["outcome"] == "ZERO"]
        _check(f2_zero_lens == [2, 4, 8], "P3 F_2^L 2^k nilpotence set")

        # Pillar 4: K.551 S_5 counterpoint, K.516f dice game, & Putz 1995 CS-13 anti-numerology
        p4 = pl["pillar4_combinatorial_invariance_cs13"]
        _check(p4["all_verified"] is True, "P4 verified")
        s5 = p4["k551_s5_quintuple_counterpoint"]
        _check(
            s5["valid_model"]["clean_permutations"] == 120
            and s5["valid_model"]["violating_permutations"] == 0
            and s5["parallel_5th_counter_model"]["violating_permutations"] == 60
            and s5["parallel_8ve_counter_model"]["violating_permutations"] == 120,
            "P4 K.551 S_5 counterpoint",
        )
        k516f = p4["k516f_dice_game_invariance"]
        _check(
            k516f["minuets_fixed_bar8"] == 379_749_833_583_241
            and k516f["minuets_two_bar8_endings"] == 759_499_667_166_482
            and k516f["seam_compatibility_11x11_sum"] == 121
            and k516f["seam_matrix_exact_rank_1"] is True
            and k516f["matrix_product_14bar_paths"] == 379_749_833_583_241
            and k516f["broken_chromatic_seam_sum"] == 110,
            "P4 K.516f dice game",
        )
        putz = p4["putz_1995_cs13_anti_numerology"]
        _check(
            putz["phi_inv_bracket_verified"] is True
            and putz["sonatas_checked"] == 15
            and putz["nonzero_exact_defect_count"] == 15
            and putz["fail_2pct_ab_count"] == 9
            and putz["range_compression_factor_q"] == "400/143",
            "P4 Putz 1995 CS-13",
        )

    def test_02_oracle_guards_boundaries_frobenius_ducci_s5_and_k516f(self) -> None:
        # Strict primitive guards (int, bool, Fraction, bounds, formatting)
        _expect_err(lambda: oracle.require_ok(1, "X", "m"), "INVALID_CONDITION_TYPE", "int cond")
        _expect_err(lambda: oracle.require_ok(_BoolLike(), "X", "m"), "INVALID_CONDITION_TYPE", "boollike cond")
        _expect_err(lambda: oracle.require_ok(False, "MY_CODE", "boom"), "MY_CODE", "false cond")
        oracle.require_ok(True, "OK", "ok")

        _expect_err(lambda: oracle.require_exact_int(True, "n"), "INVALID_INT_TYPE", "bool as int")
        _expect_err(lambda: oracle.require_exact_int(_IntSub(3), "n"), "INVALID_INT_TYPE", "int subclass")
        _expect_err(lambda: oracle.require_exact_int(1 << oracle.MAX_RATIONAL_BITS, "n"), "INT_BIT_LIMIT", "int bit cap")
        _check(oracle.require_exact_int((1 << oracle.MAX_RATIONAL_BITS) - 1, "n") > 0, "exact max bits int")
        _expect_err(lambda: oracle.require_exact_int(1, "n", lo="0"), "INVALID_BOUND_TYPE", "bad lo type")  # type: ignore[arg-type]
        _expect_err(lambda: oracle.require_exact_int(1, "n", hi="5"), "INVALID_BOUND_TYPE", "bad hi type")  # type: ignore[arg-type]
        _expect_err(lambda: oracle.require_exact_int(0, "n", lo=1), "INT_OUT_OF_RANGE", "below lo")
        _check(oracle.require_exact_int(1, "n", lo=1, hi=5) == 1, "exact lo int")
        _expect_err(lambda: oracle.require_exact_int(6, "n", lo=1, hi=5), "INT_OUT_OF_RANGE", "above hi")
        _check(oracle.require_exact_int(5, "n", lo=1, hi=5) == 5, "exact hi int")

        _expect_err(lambda: oracle.require_exact_bool(1, "b"), "INVALID_BOOL_TYPE", "int as bool")
        _check(oracle.require_exact_bool(False, "b") is False, "bool false")

        _expect_err(lambda: oracle.require_exact_fraction(1, "q"), "INVALID_FRACTION_TYPE", "int as Fraction")
        _expect_err(
            lambda: oracle.require_exact_fraction(Fraction(1 << oracle.MAX_RATIONAL_BITS, 1), "q"),
            "RATIONAL_BIT_LIMIT",
            "num bit cap",
        )
        _check(oracle.require_exact_fraction(Fraction((1 << oracle.MAX_RATIONAL_BITS) - 1, 1), "q") > 0, "exact num bits")
        _expect_err(
            lambda: oracle.require_exact_fraction(Fraction(1, 1 << oracle.MAX_RATIONAL_BITS), "q"),
            "RATIONAL_BIT_LIMIT",
            "den bit cap",
        )
        _check(oracle.require_exact_fraction(Fraction(1, (1 << oracle.MAX_RATIONAL_BITS) - 1), "q") > 0, "exact den bits")
        _expect_err(lambda: oracle.require_exact_fraction(Fraction(1, 2), "q", lo=0), "INVALID_BOUND_TYPE", "bad frac lo")  # type: ignore[arg-type]
        _expect_err(lambda: oracle.require_exact_fraction(Fraction(1, 2), "q", hi=1), "INVALID_BOUND_TYPE", "bad frac hi")  # type: ignore[arg-type]
        _expect_err(
            lambda: oracle.require_exact_fraction(Fraction(0, 1), "q", lo=Fraction(1, 2)),
            "FRACTION_OUT_OF_RANGE",
            "frac below lo",
        )
        _expect_err(
            lambda: oracle.require_exact_fraction(Fraction(2, 1), "q", hi=Fraction(1, 1)),
            "FRACTION_OUT_OF_RANGE",
            "frac above hi",
        )
        _check(oracle.require_exact_fraction(Fraction(1, 2), "q", lo=Fraction(1, 2), hi=Fraction(1, 2)) == Fraction(1, 2), "exact frac bounds")

        _check(oracle.format_fraction(Fraction(6, 2)) == "3", "int frac format")
        _check(oracle.format_fraction(Fraction(5, 3)) == "5/3", "non-int frac format")
        _check(oracle.format_decimal_rounded(Fraction(-5, 4), 4) == "-1.2500", "neg dec format")
        _check(oracle.format_decimal_rounded(Fraction(2, 3), 6) == "0.666667", "pos dec rounding")
        _check(oracle.format_decimal_rounded(Fraction(-1, 10**9), 6) == "0.000000", "no negative zero dec")
        _check(oracle.format_decimal_rounded(Fraction(0, 1), 6) == "0.000000", "zero dec format")
        _expect_err(lambda: oracle.format_decimal_rounded(Fraction(1, 2), 0), "INT_OUT_OF_RANGE", "digits 0")

        # S39-VER-01 R2: 4096-bit cap prevents >4300-digit int->str raw ValueError in formatters
        max_q_num = Fraction((1 << oracle.MAX_RATIONAL_BITS) - 1, 1)
        max_q_den = Fraction(1, (1 << oracle.MAX_RATIONAL_BITS) - 1)
        _check(audit.parse_exact_rational(oracle.format_fraction(max_q_num)) == max_q_num, "4096-bit num roundtrip")
        _check(audit.parse_exact_rational(oracle.format_fraction(max_q_den)) == max_q_den, "4096-bit den roundtrip")
        _check(oracle.format_decimal_rounded(max_q_num, 12).endswith(".000000000000"), "4096-bit dec12 safe")
        for over_q, lbl in (
            (Fraction((1 << 16_384) - 1, 1), "16384b num"),
            (Fraction(1, (1 << 16_384) - 1), "16384b den"),
            (Fraction(10**4300, 1), "10**4300 num"),
            (Fraction(1, 10**4300), "10**4300 den"),
        ):
            _expect_err(lambda q=over_q: oracle.format_fraction(q), "RATIONAL_BIT_LIMIT", f"fmt_frac {lbl}")
            _expect_err(lambda q=over_q: oracle.format_decimal_rounded(q, 6), "RATIONAL_BIT_LIMIT", f"fmt_dec6 {lbl}")
            _expect_err(lambda q=over_q: oracle.format_decimal_rounded(q, 1), "RATIONAL_BIT_LIMIT", f"fmt_dec1 {lbl}")

        # Finite-difference, shift, cyclic, energy, Ducci, & Frobenius guards
        _expect_err(lambda: oracle.forward_difference("bad", 1), "INVALID_SEQ_TYPE", "str seq")  # type: ignore[arg-type]
        _expect_err(lambda: oracle.forward_difference([1], 0), "SEQ_TOO_SHORT", "len 1 seq")
        _expect_err(lambda: oracle.forward_difference([1] * 257, 1), "SEQ_TOO_LONG", "len 257 seq")
        _check(len(oracle.forward_difference([1] * 256, 1)) == 255, "exact max len 256 seq")
        _check(oracle.forward_difference([10, 20], 0) == [10, 20], "order 0 exact")
        _check(oracle.forward_difference([10, 20], 1) == [10], "exact order == len-1")
        _expect_err(lambda: oracle.forward_difference([10, 20], 2), "ORDER_TOO_HIGH", "order == len")

        _check(oracle.shift_difference([10, 20], 1) == [10], "exact lag == len-1")
        _expect_err(lambda: oracle.shift_difference([10, 20], 2), "LAG_TOO_HIGH", "lag == len")
        _check(oracle.cyclic_forward_difference([1, 4]) == [3, -3], "cyclic 2-elem")
        _check(oracle.l2_energy_exact([3]) == 9, "1-elem energy")

        _check(oracle.ducci_orbit([0, 0], max_steps=1)["steps_to_zero"] == 0, "already zero Ducci")
        _expect_err(lambda: oracle.ducci_orbit([60, 62, 65, 64], max_steps=2), "DUCCI_STEP_LIMIT", "Ducci step limit")
        _check(oracle.ducci_orbit([60, 62, 65, 64], max_steps=4)["steps_to_zero"] == 4, "exact max_steps == 4")

        _expect_err(lambda: oracle.verify_frobenius_binomial_mod_p(4, 1), "NOT_PRIME", "composite p=4")
        _expect_err(lambda: oracle.verify_frobenius_binomial_mod_p(9, 1), "NOT_PRIME", "composite p=9")
        _check(oracle._is_prime_small(1) is False and oracle._is_prime_small(2) is True, "small prime edge")

        # S_5 counterpoint guards (including legal parallel 3rd to kill BoolOp SUBCOND_DEL on iv_t in (0,7) and d_iv == 0!)
        _expect_err(lambda: oracle.check_s5_invertible_counterpoint("bad"), "INVALID_VOICES_TYPE", "str voices")  # type: ignore[arg-type]
        _expect_err(lambda: oracle.check_s5_invertible_counterpoint([[0, 2]] * 4), "INVALID_VOICE_COUNT", "4 voices")
        _expect_err(
            lambda: oracle.check_s5_invertible_counterpoint([[0, 2], [4, 5, 7], [7, 4], [2, 0], [9, 11]]),
            "VOICE_LEN_MISMATCH",
            "ragged voices",
        )
        # Legal parallel major 3rd (v0: 0->2, v1: 4->6 => iv_t=4, d_iv=0) must STILL pass 120/120!
        legal_p3 = (
            (0, 2),
            (4, 6),
            (7, 4),
            (11, 9),
            (2, 1),
        )
        _check(oracle.check_s5_invertible_counterpoint(legal_p3)["clean_permutations"] == 120, "legal parallel 3rd must pass 120/120")

        # K.516f seam helper guards (kills SWAP + SUBCOND_DEL on exit/entry not in c_maj!)
        _check(oracle._k516f_bar_seam_compatible(0, 4) is True, "diatonic C->E ok")
        _check(oracle._k516f_bar_seam_compatible(1, 0) is False, "chromatic exit C# rejected")
        _check(oracle._k516f_bar_seam_compatible(0, 1) is False, "chromatic entry C# rejected")
        _check(oracle._k516f_bar_seam_compatible(5, 11) is False, "diatonic tritone F->B rejected")

    def test_03_zone_b_hardening_parsers_secondary_audit_and_cli(self) -> None:
        cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
        cert_bytes = CERT_PATH.read_bytes()

        # Hex64 + verify_certificate_dict (full_replay=True & False) + exact-int secondary_audit_payload
        _expect_err(lambda: audit.require_hex64_lower_ascii("a" * 63, "h"), "INVALID_HEX64", "len 63")
        _expect_err(lambda: audit.require_hex64_lower_ascii("A" * 64, "h"), "INVALID_HEX64", "uppercase hex")
        _expect_err(lambda: audit.require_hex64_lower_ascii(123, "h"), "INVALID_HEX64", "int hex")
        _expect_err(lambda: audit.require_hex64_lower_ascii(["a"] * 64, "h"), "INVALID_HEX64", "list len 64")

        _expect_err(lambda: audit.verify_certificate_dict([]), "INVALID_CERT_TYPE", "list cert")
        _expect_err(lambda: audit.verify_certificate_dict(cert, full_replay=1), "INVALID_BOOL_TYPE", "non-bool full_replay")  # type: ignore[arg-type]
        bad_k = copy.deepcopy(cert)
        bad_k["extra"] = 1
        _expect_err(lambda: audit.verify_certificate_dict(bad_k, expected=cert), "INVALID_CERT_KEYS", "extra key")
        bad_sv = copy.deepcopy(cert)
        bad_sv["schema_version"] = "9.9.9"
        _expect_err(lambda: audit.verify_certificate_dict(bad_sv, full_replay=False), "INVALID_SCHEMA_VERSION", "bad schema")
        bad_tid = copy.deepcopy(cert)
        bad_tid["track_id"] = "OTHER"
        _expect_err(lambda: audit.verify_certificate_dict(bad_tid, full_replay=False), "INVALID_TRACK_ID", "bad track_id")
        bad_psha = copy.deepcopy(cert)
        bad_psha["payload_sha256"] = "0" * 64
        _expect_err(lambda: audit.verify_certificate_dict(bad_psha, full_replay=False), "PAYLOAD_SHA_MISMATCH", "bad psha")
        bad_csha = copy.deepcopy(cert)
        bad_csha["certificate_sha256"] = "0" * 64
        _expect_err(lambda: audit.verify_certificate_dict(bad_csha, full_replay=False), "CERTIFICATE_SHA_MISMATCH", "bad csha")
        bad_pl = copy.deepcopy(cert)
        bad_pl["payload"]["novelty_class"] = "N9"
        _expect_err(lambda: audit.verify_certificate_dict(bad_pl, expected=cert), "PAYLOAD_SHA_MISMATCH", "unsigned bad payload")

        # Re-signed metadata alteration MUST fail EVEN with full_replay=False;
        # CERTIFICATE_MISMATCH is still independently exercised via expected=alt_expected.
        resigned_pl = copy.deepcopy(cert)
        resigned_pl["payload"]["novelty_class"] = "N9"
        resigned_pl["payload_sha256"] = hashlib.sha256(audit.canonical_json_bytes(resigned_pl["payload"])).hexdigest()
        resigned_env = {
            "schema_version": resigned_pl["schema_version"],
            "track_id": resigned_pl["track_id"],
            "payload_sha256": resigned_pl["payload_sha256"],
            "payload": resigned_pl["payload"],
        }
        resigned_pl["certificate_sha256"] = hashlib.sha256(audit.canonical_json_bytes(resigned_env)).hexdigest()
        _expect_err(lambda: audit.verify_certificate_dict(resigned_pl, full_replay=False), "SECONDARY_AUDIT_FAILED", "re-signed metadata full_replay=False")
        _expect_err(lambda: audit.verify_certificate_dict(cert, expected=resigned_pl, full_replay=True), "CERTIFICATE_MISMATCH", "expected mismatch full_replay=True")
        _check(audit.verify_certificate_dict(cert)["valid"] is True, "default full_replay=True expected=None")

        # Re-signed bool-for-int forgery MUST fail EVEN with full_replay=False
        def _resign(base_cert: dict[str, Any], mutator: Any) -> dict[str, Any]:
            c = copy.deepcopy(base_cert)
            mutator(c["payload"])
            c["payload_sha256"] = hashlib.sha256(audit.canonical_json_bytes(c["payload"])).hexdigest()
            env = {
                "schema_version": c["schema_version"],
                "track_id": c["track_id"],
                "payload_sha256": c["payload_sha256"],
                "payload": c["payload"],
            }
            c["certificate_sha256"] = hashlib.sha256(audit.canonical_json_bytes(env)).hexdigest()
            return c

        bool_forge = _resign(
            cert,
            lambda p: p["pillar1_frobenius_z12"]["frobenius_prime_checks"][0].__setitem__("exponent_r", True),
        )
        _expect_err(lambda: audit.verify_certificate_dict(bool_forge, full_replay=False), "INVALID_INT_TYPE", "re-signed bool-for-int")

        # S39-VER-02 R2: ALL 11+ re-signed tamper vectors MUST fail under full_replay=False!
        ver02_tampers: tuple[tuple[Any, str, str], ...] = (
            (
                lambda p: p["pillar2_spectral_prism"]["mozart_corpus_prism"][4]["ratios_R2_to_R5_q"].__setitem__(0, "999"),
                "SECONDARY_AUDIT_FAILED",
                "K.545_Mel R2=999",
            ),
            (
                lambda p: p["pillar1_frobenius_z12"].__setitem__("frobenius_prime_checks", []),
                "SECONDARY_AUDIT_FAILED",
                "empty frobenius_prime_checks",
            ),
            (
                lambda p: p["pillar1_frobenius_z12"].__setitem__("frobenius_prime_power_checks", []),
                "SECONDARY_AUDIT_FAILED",
                "empty frobenius_prime_power_checks",
            ),
            (
                lambda p: p["pillar1_frobenius_z12"]["frobenius_prime_checks"][0].__setitem__("verified", False),
                "SECONDARY_AUDIT_FAILED",
                "frobenius verified=False",
            ),
            (
                lambda p: p["pillar1_frobenius_z12"]["crt_z12_decomposition"].__setitem__("bijection_table_x_r3_r4", []),
                "SECONDARY_AUDIT_FAILED",
                "empty crt bijection",
            ),
            (
                lambda p: p["pillar1_frobenius_z12"]["crt_z12_decomposition"]["bijection_table_x_r3_r4"][0].__setitem__(1, 2),
                "SECONDARY_AUDIT_FAILED",
                "corrupted crt row",
            ),
            (
                lambda p: p["pillar2_spectral_prism"].__setitem__("sinusoidal_gain_table", []),
                "SECONDARY_AUDIT_FAILED",
                "empty sinusoidal_gain_table",
            ),
            (
                lambda p: p["pillar2_spectral_prism"]["sinusoidal_gain_table"][1].__setitem__("eigenwave_diff_energy", 99),
                "SECONDARY_AUDIT_FAILED",
                "corrupted sinusoidal energy",
            ),
            (
                lambda p: p["pillar2_spectral_prism"]["sinusoidal_gain_table"][1].__setitem__("eigenwave_energy", 0),
                "SECONDARY_AUDIT_FAILED",
                "zero sinusoidal energy",
            ),
            (
                lambda p: p["pillar3_ducci_nilpotence"].__setitem__("mozart_ducci_orbits", []),
                "SECONDARY_AUDIT_FAILED",
                "empty mozart_ducci_orbits",
            ),
            (
                lambda p: p["pillar4_combinatorial_invariance_cs13"]["putz_1995_cs13_anti_numerology"].__setitem__("sonata_splits", []),
                "SECONDARY_AUDIT_FAILED",
                "empty putz sonata_splits",
            ),
            (
                lambda p: p["pillar4_combinatorial_invariance_cs13"]["putz_1995_cs13_anti_numerology"]["sonata_splits"][0].__setitem__("total_bars", 999),
                "SECONDARY_AUDIT_FAILED",
                "corrupted putz total_bars",
            ),
            (
                lambda p: p["pillar4_combinatorial_invariance_cs13"]["putz_1995_cs13_anti_numerology"]["sonata_splits"][0].__setitem__("b_dev_recap_bars", 0),
                "SECONDARY_AUDIT_FAILED",
                "zero putz b_dev_recap_bars",
            ),
            (
                lambda p: p["pillar4_combinatorial_invariance_cs13"]["putz_1995_cs13_anti_numerology"]["sonata_splits"][0].__setitem__("a_over_b_q", "1/2"),
                "SECONDARY_AUDIT_FAILED",
                "corrupted putz a_over_b_q",
            ),
            (
                lambda p: p["pillar2_spectral_prism"]["mozart_corpus_prism"][0].__setitem__("energies_E1_to_E5", []),
                "SECONDARY_AUDIT_SCHEMA_ERROR",
                "empty prism energies",
            ),
            (
                lambda p: p["pillar2_spectral_prism"]["mozart_corpus_prism"][0]["energies_E1_to_E5"].__setitem__(1, 999),
                "SECONDARY_AUDIT_FAILED",
                "corrupted prism E2 != E1*R2",
            ),
            (
                lambda p: p["pillar2_spectral_prism"]["mozart_corpus_prism"][0]["energies_E1_to_E5"].__setitem__(0, 0),
                "SECONDARY_AUDIT_FAILED",
                "zero prism E1",
            ),
            (
                lambda p: p["pillar4_combinatorial_invariance_cs13"]["k551_s5_quintuple_counterpoint"]["parallel_8ve_counter_model"].__setitem__("violating_permutations", 0),
                "SECONDARY_AUDIT_FAILED",
                "s5_p8 violating_permutations=0",
            ),
            (
                lambda p: p["pillar4_combinatorial_invariance_cs13"]["k516f_dice_game_invariance"].__setitem__("minuets_two_bar8_endings", 0),
                "SECONDARY_AUDIT_FAILED",
                "k516f minuets_two_bar8_endings=0",
            ),
            (
                lambda p: p["pillar4_combinatorial_invariance_cs13"]["k516f_dice_game_invariance"].__setitem__("broken_chromatic_seam_sum", 999),
                "SECONDARY_AUDIT_FAILED",
                "k516f broken_chromatic_seam_sum=999",
            ),
            (
                lambda p: p["pillar4_combinatorial_invariance_cs13"]["putz_1995_cs13_anti_numerology"].__setitem__("range_compression_factor_q", "3"),
                "SECONDARY_AUDIT_FAILED",
                "putz range_compression_factor_q=3",
            ),
            (
                lambda p: p["pillar4_combinatorial_invariance_cs13"]["putz_1995_cs13_anti_numerology"].__setitem__("fail_2pct_ab_count", 0),
                "SECONDARY_AUDIT_FAILED",
                "putz fail_2pct_ab_count=0",
            ),
            # Strict nested keysets, bijective bools, division-free cross-checks, & full leaf pinning
            (
                lambda p: p["pillar1_frobenius_z12"].__setitem__("__rogue_key__", 1),
                "SECONDARY_AUDIT_SCHEMA_ERROR",
                "rogue key in p1",
            ),
            (
                lambda p: p["pillar4_combinatorial_invariance_cs13"]["putz_1995_cs13_anti_numerology"]["sonata_splits"][0].__setitem__("__rogue_key__", 1),
                "SECONDARY_AUDIT_SCHEMA_ERROR",
                "rogue key in putz row",
            ),
            (
                lambda p: p["pillar4_combinatorial_invariance_cs13"]["k516f_dice_game_invariance"].__setitem__("verified", 0),
                "INVALID_BOOL_TYPE",
                "int-for-bool p4.k516f.verified=0",
            ),
            (
                lambda p: p["pillar1_frobenius_z12"]["crt_z12_decomposition"].__setitem__("bijection_table_x_r3_r4", [[0, 0, 0]] * 12),
                "SECONDARY_AUDIT_FAILED",
                "duplicate CRT rows",
            ),
            (
                lambda p: p["pillar1_frobenius_z12"]["frobenius_prime_checks"][0].__setitem__("prime_p", 10**18 + 3),
                "SECONDARY_AUDIT_FAILED",
                "huge prime_p",
            ),
            (
                lambda p: p["pillar1_frobenius_z12"]["frobenius_prime_checks"][0].__setitem__("exponent_r", -1),
                "SECONDARY_AUDIT_FAILED",
                "negative exponent_r",
            ),
            (
                lambda p: p["pillar1_frobenius_z12"]["frobenius_prime_checks"][0].__setitem__("exponent_r", 1 << 40),
                "SECONDARY_AUDIT_FAILED",
                "huge exponent_r",
            ),
            (
                lambda p: p["pillar2_spectral_prism"].__setitem__("white_noise_ratios_R1_to_R5_q", ["1/0"] * 5),
                "INVALID_RATIONAL",
                "zero-denom wn_ratios",
            ),
            (
                lambda p: p["pillar2_spectral_prism"]["sinusoidal_gain_table"][0].__setitem__("cos_omega_q", "0"),
                "SECONDARY_AUDIT_FAILED",
                "tampered cos_omega_q",
            ),
            (
                lambda p: p["pillar2_spectral_prism"]["mozart_corpus_prism"][0]["ratios_R2_to_R5_dec6"].__setitem__(0, "9.999999"),
                "SECONDARY_AUDIT_FAILED",
                "tampered prism dec6",
            ),
            (
                lambda p: p["pillar3_ducci_nilpotence"]["mozart_ducci_orbits"][0].__setitem__("outcome", "FORGED"),
                "SECONDARY_AUDIT_FAILED",
                "forged Ducci outcome",
            ),
            (
                lambda p: p["pillar3_ducci_nilpotence"]["f2_impulse_characterization_L2_to_L12"][0].__setitem__("L", -999),
                "SECONDARY_AUDIT_FAILED",
                "forged F2 L=-999",
            ),
            (
                lambda p: p["pillar4_combinatorial_invariance_cs13"]["putz_1995_cs13_anti_numerology"]["sonata_splits"][0].__setitem__("exact_golden_defect_Z", 0),
                "SECONDARY_AUDIT_FAILED",
                "zeroed Putz defect",
            ),
            (
                lambda p: p["pillar4_combinatorial_invariance_cs13"]["k551_s5_quintuple_counterpoint"]["parallel_5th_counter_model"]["first_violation"].__setitem__("step_t", 9),
                "SECONDARY_AUDIT_FAILED",
                "tampered s5 first_violation",
            ),
            (
                lambda p: p.__setitem__("oracle_class", "approx"),
                "SECONDARY_AUDIT_FAILED",
                "tampered oracle_class",
            ),
        )
        for mut_fn, exp_code, lbl in ver02_tampers:
            forged = _resign(cert, mut_fn)
            _expect_err(lambda f=forged: audit.verify_certificate_dict(f, full_replay=False), exp_code, f"full_replay=False {lbl}")

        # Schema-safe fail-closed exact-int secondary_audit_payload across crafted malformed inputs
        _expect_err(lambda: audit.secondary_audit_payload(123), "SECONDARY_AUDIT_SCHEMA_ERROR", "int payload")
        _expect_err(lambda: audit.secondary_audit_payload([]), "SECONDARY_AUDIT_SCHEMA_ERROR", "list payload")
        _expect_err(lambda: audit.secondary_audit_payload({}), "SECONDARY_AUDIT_SCHEMA_ERROR", "empty payload")

        bad_tuple_pl = copy.deepcopy(cert["payload"])
        bad_tuple_pl["pillar1_frobenius_z12"]["frobenius_prime_checks"] = tuple(
            bad_tuple_pl["pillar1_frobenius_z12"]["frobenius_prime_checks"]
        )
        _expect_err(lambda: audit.secondary_audit_payload(bad_tuple_pl), "INVALID_JSON_VALUE", "tuple list in tree")

        bad_list_pl = copy.deepcopy(cert["payload"])
        bad_list_pl["pillar1_frobenius_z12"]["frobenius_prime_checks"] = {}
        _expect_err(lambda: audit.secondary_audit_payload(bad_list_pl), "SECONDARY_AUDIT_SCHEMA_ERROR", "dict instead of list")

        bad_rlen = copy.deepcopy(cert["payload"])
        bad_rlen["pillar2_spectral_prism"]["mozart_corpus_prism"][0]["ratios_R2_to_R5_q"] = ["1/6"]
        _expect_err(lambda: audit.secondary_audit_payload(bad_rlen), "SECONDARY_AUDIT_SCHEMA_ERROR", "short R list")

        bad_pname = copy.deepcopy(cert["payload"])
        bad_pname["pillar2_spectral_prism"]["mozart_corpus_prism"][0]["name"] = ["Scale"]
        _expect_err(lambda: audit.secondary_audit_payload(bad_pname), "SECONDARY_AUDIT_SCHEMA_ERROR", "unhashable list prism name")

        bad_psub = copy.deepcopy(cert["payload"])
        bad_psub["pillar2_spectral_prism"]["mozart_corpus_prism"][0]["name"] = _StrSub("Scale")
        _expect_err(lambda: audit.secondary_audit_payload(bad_psub), "INVALID_JSON_VALUE", "str-subclass prism name")

        bad_isub = copy.deepcopy(cert["payload"])
        bad_isub["pillar2_spectral_prism"]["unity_cutoff_lambda"] = _IntSub(6)
        _expect_err(lambda: audit.secondary_audit_payload(bad_isub), "INVALID_JSON_VALUE", "int-subclass in direct payload")

        bad_lsub = copy.deepcopy(cert["payload"])
        bad_lsub["pillar1_frobenius_z12"]["k550_period3_annihilation"]["delta3_mod3"] = _ListSub([0, 0, 0, 0, 0, 0, 1])
        _expect_err(lambda: audit.secondary_audit_payload(bad_lsub), "INVALID_JSON_VALUE", "list-subclass in direct payload")

        bad_dsub = copy.deepcopy(cert["payload"])
        bad_dsub["pillar1_frobenius_z12"]["k550_period3_annihilation"] = _DictSub(
            bad_dsub["pillar1_frobenius_z12"]["k550_period3_annihilation"]
        )
        _expect_err(lambda: audit.secondary_audit_payload(bad_dsub), "INVALID_JSON_VALUE", "dict-subclass in direct payload")

        bad_pset = copy.deepcopy(cert["payload"])
        bad_pset["pillar2_spectral_prism"]["mozart_corpus_prism"][0]["name"] = "Other"
        _expect_err(lambda: audit.secondary_audit_payload(bad_pset), "SECONDARY_AUDIT_SCHEMA_ERROR", "unknown prism name")

        bad_alg = copy.deepcopy(cert["payload"])
        bad_alg["pillar1_frobenius_z12"]["k550_period3_annihilation"]["delta3_mod3"] = [0, 0, 0, 0, 0, 0, 2]
        _expect_err(lambda: audit.secondary_audit_payload(bad_alg), "SECONDARY_AUDIT_FAILED", "tampered K.550 d3")

        bad_rat_pl = copy.deepcopy(cert["payload"])
        bad_rat_pl["pillar4_combinatorial_invariance_cs13"]["putz_1995_cs13_anti_numerology"]["range_compression_factor_q"] = "\u00b2"
        _expect_err(lambda: audit.secondary_audit_payload(bad_rat_pl), "INVALID_RATIONAL", "superscript in payload")

        bad_flt_pl = copy.deepcopy(cert["payload"])
        bad_flt_pl["pillar4_combinatorial_invariance_cs13"]["k551_s5_quintuple_counterpoint"]["valid_model"]["clean_permutations"] = json.loads("120.0")
        _expect_err(lambda: audit.secondary_audit_payload(bad_flt_pl), "INVALID_JSON_VALUE", "float in direct payload")

        for mut_fn, lbl in (
            (lambda p: p["pillar1_frobenius_z12"]["k550_period3_annihilation"]["delta3_mod3"].__setitem__(0, False), "bool in d3_mod3"),
            (lambda p: p["pillar2_spectral_prism"]["sinusoidal_gain_table"][0].__setitem__("gain_exact", False), "bool gain_exact"),
            (lambda p: p["pillar3_ducci_nilpotence"]["mozart_ducci_orbits"][0].__setitem__("cycle_period", False), "bool cycle_period"),
            (lambda p: p["pillar4_combinatorial_invariance_cs13"]["k551_s5_quintuple_counterpoint"]["valid_model"].__setitem__("violating_permutations", False), "bool s5 viol"),
        ):
            mp = copy.deepcopy(cert["payload"])
            mut_fn(mp)
            _expect_err(lambda x=mp: audit.secondary_audit_payload(x), "INVALID_INT_TYPE", lbl)

        # Strict ASCII-only _parse_bounded_int & parse_exact_rational guards (symmetrical 4096-bit cap)
        max_4096_s = str((1 << oracle.MAX_RATIONAL_BITS) - 1)
        over_4096_s = str(1 << oracle.MAX_RATIONAL_BITS)
        _check(
            audit._parse_bounded_int("0") == 0
            and audit._parse_bounded_int("-5") == -5
            and audit._parse_bounded_int("10") == 10
            and audit._parse_bounded_int(max_4096_s) == (1 << oracle.MAX_RATIONAL_BITS) - 1,
            "valid bounded ints",
        )
        _expect_err(lambda: audit._parse_bounded_int(over_4096_s), "INT_BIT_LIMIT", "direct 4097-bit int")
        _expect_err(lambda: audit._parse_bounded_int("9" * 1235), "INT_DIGIT_LIMIT", "direct 1235-digit int")
        for bad_int_tok, lbl in (
            (12, "non-str int"),
            ("", "empty int"),
            ("-", "bare minus"),
            ("-0", "negative zero"),
            ("007", "leading zero pos"),
            ("-01", "leading zero neg"),
            ("\u0661\u0662", "Arabic-Indic"),
            ("-\u0661\u0662", "neg Arabic-Indic"),
            ("\u00b2", "superscript"),
            ("+12", "leading plus"),
            ("1_2", "underscore"),
        ):
            _expect_err(lambda bt=bad_int_tok: audit._parse_bounded_int(bt), "INVALID_JSON_INT", lbl)

        _check(audit.parse_exact_rational("0") == 0 and audit.parse_exact_rational("-5") == -5, "int rational")
        _check(audit.parse_exact_rational("3/2") == Fraction(3, 2), "den=2 rational")
        _check(audit.parse_exact_rational("3/7") == Fraction(3, 7) and audit.parse_exact_rational("-11/4") == Fraction(-11, 4), "frac rational")
        _check(audit.parse_exact_rational(max_4096_s) == Fraction((1 << oracle.MAX_RATIONAL_BITS) - 1, 1), "exact 4096-bit rational num")
        _check(audit.parse_exact_rational("1/" + max_4096_s) == Fraction(1, (1 << oracle.MAX_RATIONAL_BITS) - 1), "exact 4096-bit rational den")
        _expect_err(lambda: audit.parse_exact_rational(over_4096_s), "RATIONAL_BIT_LIMIT", "4097-bit rational num")
        _expect_err(lambda: audit.parse_exact_rational("1/" + over_4096_s), "RATIONAL_BIT_LIMIT", "4097-bit rational den")
        _expect_err(lambda: audit.parse_exact_rational("9" * audit.MAX_JSON_INT_DIGITS), "RATIONAL_BIT_LIMIT", "1234-digit >4096-bit rational num")
        _expect_err(lambda: audit.parse_exact_rational("1/" + "9" * audit.MAX_JSON_INT_DIGITS), "RATIONAL_BIT_LIMIT", "1234-digit >4096-bit rational den")
        for bad_rat_tok, lbl in (
            (12, "non-str rat"),
            ("", "empty rat"),
            ("-", "dash rat"),
            ("-0", "neg zero rat"),
            ("01", "leading zero num"),
            ("1/02", "leading zero den"),
            ("3/1", "non-canonical den=1"),
            ("2/4", "non-reduced rational"),
            ("1/2/3", "two slashes"),
            ("/2", "empty num"),
            ("-/2", "dash-only num"),
            ("1/", "empty den"),
            ("1/0", "zero den"),
            ("1/-2", "neg den"),
            ("\u00b2", "superscript rat"),
            ("1/\u00b2", "superscript den"),
            ("\u0661\u0662/\u0663", "Arabic-Indic rat"),
            ("+1/2", "plus rat"),
            ("9" * (audit.MAX_JSON_INT_DIGITS + 1), "num too long"),
            ("1/" + "9" * (audit.MAX_JSON_INT_DIGITS + 1), "den too long"),
        ):
            _expect_err(lambda bt=bad_rat_tok: audit.parse_exact_rational(bt), "INVALID_RATIONAL", lbl)

        # Strict JSON tree, parser, & canonical_json_bytes guards
        _check(audit.parse_strict_json_text("[1,true,null]", "arr", require_object=False) == [1, True, None], "arr parse")
        _check(
            audit.parse_strict_json_text('{"n":' + str((1 << oracle.MAX_JSON_INT_BITS) - 1) + "}", "maxb")["n"] > 0,
            "exact 4096-bit int",
        )
        _check(
            audit.parse_strict_json_text('{"n":-' + str((1 << oracle.MAX_JSON_INT_BITS) - 1) + "}", "negd")["n"] < 0,
            "exact neg 4096-bit int",
        )
        _expect_err(lambda: audit.parse_strict_json_text(123, "x"), "INVALID_JSON_TEXT", "non-str")
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

        # /proc/kallsyms st_size==0 capped read + /dev/null write guard + max_bytes 64 MiB cap
        proc_kallsyms = Path("/proc/kallsyms")
        if proc_kallsyms.exists():
            _expect_err(lambda: audit.read_regular_bytes_capped(proc_kallsyms, "kallsyms", max_bytes=16), "FILE_TOO_LARGE", "kallsyms cap")
        dev_null = Path("/dev/null")
        if dev_null.exists():
            _expect_err(lambda: audit.write_regular_bytes_safe(dev_null, b"{}\n", "devnull"), "NOT_A_REGULAR_FILE", "devnull write")

        with tempfile.TemporaryDirectory(prefix="s39_zb_") as td:
            root = Path(td)
            cfile = root / "c.json"
            _expect_err(
                lambda: audit.write_regular_bytes_safe(root / "never_created" / "x.json", "not-bytes", "bad_payload"),  # type: ignore[arg-type]
                "INVALID_PAYLOAD_BYTES",
                "non-bytes payload",
            )
            _check(not (root / "never_created").exists(), "bad payload created parent dir")

            audit.write_regular_bytes_safe(cfile, cert_bytes, "c")
            _check(stat.S_IMODE(os.stat(cfile).st_mode) == 0o600, "temp/final file mode must be 0o600")
            audit.write_regular_bytes_safe(cfile, b"{}\n", "c_short")
            _check(cfile.read_bytes() == b"{}\n", "atomic replace shorter failed")
            audit.write_regular_bytes_safe(cfile, cert_bytes, "c_restore")
            # Streaming >64 KiB read/write round-trip
            big_payload = b"M" * 70_000
            big_file = root / "big.bin"
            audit.write_regular_bytes_safe(big_file, big_payload, "big")
            _check(audit.read_regular_bytes_capped(big_file, "big") == big_payload, "streaming >64KiB read failed")
            # Deterministic CSPRNG temp collision retry (EEXIST)
            fixed_tok_a = "deadbeef00000001"
            fixed_tok_b = "deadbeef00000002"
            pre_tmp = root / f".s39.{os.getpid()}.{fixed_tok_a}.tmp"
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
            _check([p.name for p in root.glob(".s39.*.tmp")] == [], "leftover retry tmp")
            # Live pre-replace temp st_nlink != 1 detection (hardlink injected during fsync)
            orig_fsync = audit.os.fsync
            linked_alias = root / "injected_tmp_link"
            hook_armed = [True]

            def _inject_tmp_link(fd_arg: int) -> None:
                if hook_armed[0]:
                    tmps = list(root.glob(".s39.*.tmp"))
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
            _check([p.name for p in root.glob(".s39.*.tmp")] == [], "leftover temp after pre-replace hardlink")

            nested = root / "nested_a" / "sub_b" / "w.json"
            audit.write_regular_bytes_safe(nested, cert_bytes, "nested")
            _check(nested.read_bytes() == cert_bytes, "nested dir_fd create failed")
            _check(audit.read_regular_bytes_capped(cfile, "c", max_bytes=len(cert_bytes)) == cert_bytes, "exact max_bytes")
            _check(audit.read_regular_bytes_capped(cfile, "c", max_bytes=audit.MAX_ALLOWED_CAP_BYTES) == cert_bytes, "exact 64MiB cap")
            _expect_err(
                lambda: audit.read_regular_bytes_capped(cfile, "c", max_bytes=audit.MAX_ALLOWED_CAP_BYTES + 1),
                "INT_OUT_OF_RANGE",
                "over 64MiB cap",
            )
            _expect_err(lambda: audit.read_regular_bytes_capped(cfile, "c", max_bytes=len(cert_bytes) - 1), "FILE_TOO_LARGE", "max_bytes-1")

            hlink = root / "hlink.json"
            os.link(cfile, hlink)
            try:
                _expect_err(lambda: audit.write_regular_bytes_safe(hlink, b"tamper", "hlink"), "HARDLINK_FORBIDDEN", "hardlink write")
                _check(cfile.read_bytes() == cert_bytes, "hardlink refusal altered target")
            finally:
                hlink.unlink()

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
                local_sym = real_sub / "local_sym"
                os.symlink(real_sub, local_sym)
                os.environ["PWD"] = str(sym_dir / "nested")
                _expect_err(lambda: audit.verify_certificate_file(Path("c.json")), "SYMLINK_ANCESTOR_FORBIDDEN", "symlink PWD")
                os.environ["PWD"] = "/nonexistent_s39_pwd_dir"
                _expect_err(lambda: audit.read_regular_bytes_capped(Path("c.json"), "missing_pwd"), "CWD_UNAVAILABLE", "missing PWD")
                os.environ["PWD"] = "/tmp/bad_\udcff_pwd"
                _expect_err(lambda: audit.read_regular_bytes_capped(Path("c.json"), "spwd"), "INVALID_UTF8_SURROGATE", "surrogate PWD")
                os.environ["PWD"] = "rel/local_sym"
                _check(audit.read_regular_bytes_capped(Path(".") / "c.json", "relpwd") == cert_bytes, "relative PWD")
                os.environ["PWD"] = str(real_sub)
                _check(audit.read_regular_bytes_capped(Path("c.json"), "realpwd") == cert_bytes, "real PWD")
                os.environ.pop("PWD", None)
                _check(audit.read_regular_bytes_capped(Path("c.json"), "nopwd") == cert_bytes, "unset PWD")

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
                    (["--wr=--json"], "INVALID_CLI_ARGS"),
                    (["--write"], "INVALID_CLI_ARGS"),
                    (["--check"], "INVALID_CLI_ARGS"),
                    (["--unknown", "x"], "INVALID_CLI_ARGS"),
                ):
                    ebuf = io.StringIO()
                    with redirect_stderr(ebuf):
                        rc_b = audit.main(bad_argv)  # type: ignore[arg-type]
                    err_txt = ebuf.getvalue()
                    _check(rc_b == 2 and exp_code in err_txt, f"bad argv {bad_argv!r}: rc={rc_b} err={err_txt!r}")
                _check(not (real_sub / "--json").exists(), "--write --json / --write=--json created ./--json")

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

            p_def = subprocess.run([sys.executable, "-I", "-O", "-B", str(ROOT / "mozart_nth_diff_audit.py")], capture_output=True, timeout=60)
            _check(p_def.returncode == 0 and p_def.stdout == cert_bytes, "subprocess zero-arg mismatch")
            p_std = subprocess.run([sys.executable, "-I", "-O", "-B", str(ROOT / "mozart_nth_diff_audit.py"), "--standalone", "--json"], capture_output=True, timeout=60)
            _check(p_std.returncode == 0 and p_std.stdout == cert_bytes, "subprocess --standalone mismatch")
            p_pwd = subprocess.run(
                [sys.executable, "-I", "-O", "-B", str(ROOT / "mozart_nth_diff_audit.py"), "--check", "c.json"],
                cwd=str(real_sub),
                env={**os.environ, "PWD": str(sym_dir / "nested")},
                capture_output=True,
                text=True,
                timeout=60,
            )
            _check(p_pwd.returncode == 2 and "SYMLINK_ANCESTOR_FORBIDDEN" in p_pwd.stderr, f"subprocess symlink PWD: {p_pwd.stderr!r}")

    def test_04_live_renameat2_hardlink_and_concurrent_writer_stress(self) -> None:
        libc = ctypes.CDLL(None, use_errno=True)
        renameat2 = libc.renameat2
        renameat2.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
        renameat2.restype = ctypes.c_int

        with tempfile.TemporaryDirectory(prefix="s39_race_") as td:
            root = Path(td)
            victim = root / "victim.txt"
            victim_bytes = b"DO_NOT_LEAK_OR_CLOBBER\n"
            victim.write_bytes(victim_bytes)

            # Part A: >= 520-iter concurrent renameat2(RENAME_EXCHANGE) leaf + intermediate dir race
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
                    except oracle.MozartNthDiffError:
                        pass
                    try:
                        audit.write_regular_bytes_safe(real_dir / "target.json", b'{"ok":2}\n', "race_w")
                    except oracle.MozartNthDiffError:
                        pass
                    if victim.read_bytes() != victim_bytes:
                        clobbers += 1
            finally:
                stop_ev.set()
                t.join(timeout=5)

            _check(leaks == 0 and clobbers == 0, f"renameat2 race failed: leaks={leaks}, clobbers={clobbers}")
            _check(victim.read_bytes() == victim_bytes, "victim clobbered in renameat2 race")

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
                    except oracle.MozartNthDiffError as exc:
                        _check(exc.code == "HARDLINK_FORBIDDEN", f"unexpected hardlink error {exc.code}")
            finally:
                stop_hl.set()
                t_hl.join(timeout=5)
            _check(hl_clobbers[0] == 0 and links_created[0] > 0, f"hardlink race failed: clobbers={hl_clobbers[0]}")
            leftovers = [p.name for p in hl_dir.iterdir() if p.name.startswith(".s39.")]
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
            cw_leftovers = [p.name for p in cw_dir.iterdir() if p.name.startswith(".s39.")]
            _check(
                cw_errs == [] and burst_target.read_bytes() in valid_80 and cw_leftovers == [],
                f"80T burst errors={cw_errs} leftovers={cw_leftovers}",
            )


if __name__ == "__main__":
    unittest.main()
