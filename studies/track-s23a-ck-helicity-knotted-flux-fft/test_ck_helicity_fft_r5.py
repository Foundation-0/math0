#!/usr/bin/env python3
"""Adversarial & Mutation-Kill Test Suite for CK Helicity & Spectral FFT/NTT.

Zero external dependencies, zero bare asserts (100% python3 -O parity).
Fast Zone-B, TOCTOU, deleted-CWD, surrogate, hardlink, and tamper tests run first
to maximize mutation kill speed.
"""
from __future__ import annotations

import copy
import ctypes
from fractions import Fraction
import io
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import threading
from types import SimpleNamespace
import unittest
from unittest import mock

_THIS_DIR = str(Path(__file__).resolve().parent)
if _THIS_DIR not in sys.path:
    sys.path.insert(0, _THIS_DIR)

import ck_helicity_fft_audit as audit
import ck_helicity_fft_oracle as oracle


class _EvilInt(int):
    pass


class _EvilStr(str):
    pass


class _EvilFrac(Fraction):
    pass


class _EvilPath(type(Path("."))):
    pass


class _EvilDict(dict):
    pass


class _EvilList(list):
    pass


class Test01ZoneBPrimitives(unittest.TestCase):
    """Exact type, boundary, canonical-rational, JSON-depth/cycle, and digest guards."""

    def _expect_err(self, code: str, fn, *args, **kwargs) -> None:
        with self.assertRaises(oracle.CKHelicityError) as ctx:
            fn(*args, **kwargs)
        self.assertEqual(ctx.exception.code, code)

    def test_strict_bool_int_str_hex64_boundaries(self) -> None:
        self.assertTrue(oracle.require_bool(True, "b"))
        self.assertFalse(oracle.require_bool(False, "b"))
        self._expect_err("INVALID_BOOL", oracle.require_bool, 1, "b")
        self._expect_err("INVALID_BOOL", oracle.require_bool, "true", "b")

        self.assertEqual(oracle.require_int(0, "n", lo=0, hi=0), 0)
        self.assertEqual(oracle.require_int((1 << oracle.MAX_INT_BITS) - 1, "max"), (1 << oracle.MAX_INT_BITS) - 1)
        self._expect_err("INVALID_INT", oracle.require_int, True, "n")
        self._expect_err("INVALID_INT", oracle.require_int, _EvilInt(5), "n")
        self._expect_err("INVALID_INT", oracle.require_int, 1.0, "n")
        self._expect_err("INT_TOO_LARGE", oracle.require_int, 1 << oracle.MAX_INT_BITS, "n")
        self._expect_err("INVALID_BOUND", oracle.require_int, 5, "n", lo=True)
        self._expect_err("INVALID_BOUND", oracle.require_int, 5, "n", hi=True)
        self._expect_err("INT_OUT_OF_RANGE", oracle.require_int, -1, "n", lo=0)
        self._expect_err("INT_OUT_OF_RANGE", oracle.require_int, 6, "n", hi=5)

        self.assertEqual(oracle.require_str("abc", "s", max_len=3), "abc")
        self._expect_err("INVALID_STR", oracle.require_str, _EvilStr("abc"), "s")
        self._expect_err("STR_TOO_LONG", oracle.require_str, "abcd", "s", max_len=3)
        self._expect_err("INVALID_UNICODE", oracle.require_str, "\ud800", "s")

        h_ok = "0123456789abcdef" * 4
        self.assertEqual(oracle.require_hex64(h_ok, "h"), h_ok)
        self.assertTrue(oracle.constant_time_hex64_equal(h_ok, h_ok, "eq"))
        self.assertFalse(oracle.constant_time_hex64_equal(h_ok, "f" + h_ok[1:], "neq"))
        self._expect_err("INVALID_HEX64", oracle.require_hex64, "a" * 63, "h")
        self._expect_err("STR_TOO_LONG", oracle.require_hex64, "a" * 65, "h")
        self._expect_err("INVALID_HEX64", oracle.require_hex64, "A" * 64, "h")
        self._expect_err("INVALID_HEX64", oracle.require_hex64, "\u00e9" * 64, "h")
        self._expect_err("INVALID_UNICODE", oracle.require_hex64, "\ud800" * 64, "h")

    def test_canonical_rational_parser_and_formatter(self) -> None:
        self.assertEqual(oracle.parse_exact_rational(0), Fraction(0, 1))
        self.assertEqual(oracle.parse_exact_rational(-7), Fraction(-7, 1))
        self.assertEqual(oracle.parse_exact_rational(Fraction(3, 5)), Fraction(3, 5))
        self.assertEqual(oracle.parse_exact_rational("0"), Fraction(0, 1))
        self.assertEqual(oracle.parse_exact_rational("-13/7"), Fraction(-13, 7))
        self.assertEqual(oracle.parse_exact_rational((1 << oracle.MAX_INT_BITS) - 1), Fraction((1 << oracle.MAX_INT_BITS) - 1, 1))
        self.assertEqual(oracle.parse_exact_rational("1" + "0" * 250), Fraction(10 ** 250, 1))

        self._expect_err("RATIONAL_TOO_LARGE", oracle.parse_exact_rational, 1 << oracle.MAX_INT_BITS)
        self._expect_err("RATIONAL_TOO_LARGE", oracle.parse_exact_rational, Fraction(1 << oracle.MAX_INT_BITS, 1))
        self._expect_err("RATIONAL_TOO_LARGE", oracle.parse_exact_rational, Fraction(1, 1 << oracle.MAX_INT_BITS))
        self._expect_err("INVALID_RATIONAL_TYPE", oracle.parse_exact_rational, True)
        self._expect_err("INVALID_RATIONAL_TYPE", oracle.parse_exact_rational, 1.5)
        self._expect_err("INVALID_RATIONAL_TYPE", oracle.parse_exact_rational, _EvilFrac(1, 2))
        self._expect_err("INVALID_RATIONAL_TYPE", oracle.parse_exact_rational, _EvilStr("1/2"))
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "1" * (oracle.MAX_RATIONAL_CHARS + 1))
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "1\u00e9")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "1/2/3")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "007")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "-0")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "+5")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "1/02")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "1/0")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "3/1")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "1/a")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "a/2")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "1/")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "-")
        self._expect_err("NON_CANONICAL_RATIONAL", oracle.parse_exact_rational, "2/4")
        self._expect_err("NON_CANONICAL_RATIONAL", oracle.parse_exact_rational, "-6/9")
        old_max = oracle.MAX_RATIONAL_CHARS
        try:
            oracle.MAX_RATIONAL_CHARS = 700
            self._expect_err("RATIONAL_TOO_LARGE", oracle.parse_exact_rational, "9" * 620)
            self._expect_err("RATIONAL_TOO_LARGE", oracle.parse_exact_rational, "1/" + "9" * 620)
        finally:
            oracle.MAX_RATIONAL_CHARS = old_max

        self.assertEqual(oracle.format_rational(Fraction(5, 1)), "5")
        self.assertEqual(oracle.format_rational(Fraction(-5, 3)), "-5/3")
        self.assertEqual(oracle.format_rational(Fraction((1 << oracle.MAX_FORMAT_BITS) - 1, 1)), str((1 << oracle.MAX_FORMAT_BITS) - 1))
        self._expect_err("INVALID_RATIONAL_TYPE", oracle.format_rational, 5)  # type: ignore[arg-type]
        self._expect_err("INVALID_RATIONAL_TYPE", oracle.format_rational, _EvilFrac(1, 2))
        self._expect_err("RATIONAL_TOO_LARGE", oracle.format_rational, Fraction(1 << oracle.MAX_FORMAT_BITS, 1))
        self._expect_err("RATIONAL_TOO_LARGE", oracle.format_rational, Fraction(1, 1 << oracle.MAX_FORMAT_BITS))

    def test_iterative_json_validator_and_strict_parser(self) -> None:
        # Depth boundary: exactly MAX_JSON_DEPTH ok; MAX_JSON_DEPTH + 1 rejected
        ok_nested: list = []
        cur = ok_nested
        for _ in range(oracle.MAX_JSON_DEPTH):
            nxt: list = []
            cur.append(nxt)
            cur = nxt
        oracle.validate_json_tree_iterative(ok_nested)
        cur.append(0)
        self._expect_err("JSON_DEPTH_EXCEEDED", oracle.validate_json_tree_iterative, ok_nested)

        # 1,500-deep nesting blocked iteratively (no RecursionError)
        deep: list = []
        cur = deep
        for _ in range(1500):
            nxt = []
            cur.append(nxt)
            cur = nxt
        self._expect_err("JSON_DEPTH_EXCEEDED", oracle.validate_json_tree_iterative, deep)

        # Reference cycles in dict and list
        cyc_d: dict = {}
        cyc_d["self"] = cyc_d
        self._expect_err("JSON_CYCLE", oracle.validate_json_tree_iterative, cyc_d)
        cyc_l: list = []
        cyc_l.append(cyc_l)
        self._expect_err("JSON_CYCLE", oracle.validate_json_tree_iterative, cyc_l)

        # Shared non-cyclic DAG reference allowed
        shared = {"x": 1}
        oracle.validate_json_tree_iterative({"a": shared, "b": shared})

        # Int bit limit vs digit limit
        oracle.validate_json_tree_iterative({"ok_int": 10 ** 615, "none": None, "flag": True})
        self._expect_err("INT_TOO_LARGE", oracle.validate_json_tree_iterative, {"huge_bits": 1 << 2048})
        self._expect_err("INT_TOO_LARGE", oracle.validate_json_tree_iterative, {"huge_digits": 10 ** 616})

        # Forbidden container / primitive subclasses & floats
        self._expect_err("FORBIDDEN_JSON_TYPE", oracle.validate_json_tree_iterative, _EvilDict({"a": 1}))
        self._expect_err("FORBIDDEN_JSON_TYPE", oracle.validate_json_tree_iterative, _EvilList([1]))
        self._expect_err("FORBIDDEN_JSON_TYPE", oracle.validate_json_tree_iterative, {"x": 1.5})
        self._expect_err("INVALID_STR", oracle.validate_json_tree_iterative, {1: "bad_key"})  # type: ignore[dict-item]

        # Strict JSON text parser
        self.assertEqual(oracle.parse_strict_json_text("[1,2]", require_object=False), [1, 2])
        self._expect_err("INVALID_BOOL", oracle.parse_strict_json_text, "{}", require_object=1)  # type: ignore[arg-type]
        self._expect_err("JSON_NOT_OBJECT", oracle.parse_strict_json_text, "[1,2]", require_object=True)
        self._expect_err("DUPLICATE_JSON_KEY", oracle.parse_strict_json_text, '{"a":1,"\\u0061":2}')
        self._expect_err("FLOAT_FORBIDDEN", oracle.parse_strict_json_text, '{"x":1.5}')
        self._expect_err("NONFINITE_CONSTANT", oracle.parse_strict_json_text, '{"x":NaN}')
        self._expect_err("NONFINITE_CONSTANT", oracle.parse_strict_json_text, '{"x":Infinity}')
        self._expect_err("INVALID_JSON", oracle.parse_strict_json_text, '{"x":' + ("9" * 5000) + "}")
        self._expect_err("JSON_DEPTH_EXCEEDED", oracle.parse_strict_json_text, ("[" * 1500) + "0" + ("]" * 1500), require_object=False)
        self._expect_err("INVALID_JSON", oracle.parse_strict_json_text, '{"a":')


class Test02MathGuardsAndNegativeControls(unittest.TestCase):
    """Exact input validation & negative physics controls for Theorems 1, 2, and 3."""

    def _expect_err(self, code: str, fn, *args, **kwargs) -> None:
        with self.assertRaises(oracle.CKHelicityError) as ctx:
            fn(*args, **kwargs)
        self.assertEqual(ctx.exception.code, code)

    def test_theorem1_flux_tube_guards(self) -> None:
        res = oracle.evaluate_flux_tube_helicity("simple", [Fraction(1, 1)], [], [Fraction(0, 1)])
        self.assertEqual(res["ri_kinks_tested"], [0])
        self.assertTrue(res["ri_framing_invariant"])

        self._expect_err("INVALID_FLUXES", oracle.evaluate_flux_tube_helicity, "a", [], [], [])
        self._expect_err("INVALID_FLUXES", oracle.evaluate_flux_tube_helicity, "a", "bad", [], [])  # type: ignore[arg-type]
        self._expect_err("INVALID_TWISTS", oracle.evaluate_flux_tube_helicity, "a", [Fraction(1, 1)], [], [])
        self._expect_err("INVALID_TWISTS", oracle.evaluate_flux_tube_helicity, "a", [Fraction(1, 1)], [], "bad")  # type: ignore[arg-type]
        self._expect_err("INVALID_CROSSINGS", oracle.evaluate_flux_tube_helicity, "a", [Fraction(1, 1)], "bad", [Fraction(0, 1)])  # type: ignore[arg-type]
        self._expect_err("INVALID_CROSSING", oracle.evaluate_flux_tube_helicity, "a", [Fraction(1, 1)], [(0, 0)], [Fraction(0, 1)])  # type: ignore[list-item]
        self._expect_err("INVALID_CROSSING", oracle.evaluate_flux_tube_helicity, "a", [Fraction(1, 1)], ["bad"], [Fraction(0, 1)])  # type: ignore[list-item]
        self._expect_err("INVALID_CROSSING_SIGN", oracle.evaluate_flux_tube_helicity, "a", [Fraction(1, 1)], [(0, 0, 0)], [Fraction(0, 1)])
        self._expect_err("ODD_CROSSING_SUM", oracle.evaluate_flux_tube_helicity, "a", [Fraction(1, 1), Fraction(1, 1)], [(0, 1, 1)], [Fraction(0, 1), Fraction(0, 1)])
        self._expect_err("INVALID_RI_KINKS", oracle.evaluate_flux_tube_helicity, "a", [Fraction(1, 1)], [], [Fraction(0, 1)], ri_kinks=[1, 2])
        self._expect_err("INVALID_RI_KINKS", oracle.evaluate_flux_tube_helicity, "a", [Fraction(1, 1)], [], [Fraction(0, 1)], ri_kinks="bad")  # type: ignore[arg-type]
        self._expect_err("TORUS_NOT_COPRIME", oracle._torus_parallel_cable_crossings, 2, 4)

    def test_theorem2_ck_and_projector_guards(self) -> None:
        self.assertEqual(oracle.exact_integer_norm((1, 2, 2)), 3)
        self._expect_err("INVALID_WAVEVECTOR", oracle.exact_integer_norm, (1, 2))  # type: ignore[arg-type]
        self._expect_err("INVALID_WAVEVECTOR", oracle.exact_integer_norm, "123")  # type: ignore[arg-type]
        self._expect_err("ZERO_WAVEVECTOR", oracle.exact_integer_norm, (0, 0, 0))
        self._expect_err("NON_PYTHAGOREAN_WAVEVECTOR", oracle.exact_integer_norm, (1, 1, 1))

        self._expect_err("EMPTY_SPECTRUM", oracle.evaluate_torus_field_energy_helicity, "e", [])
        self._expect_err("EMPTY_SPECTRUM", oracle.evaluate_torus_field_energy_helicity, "e", "bad")  # type: ignore[arg-type]
        _, _, pp, pm = oracle.helical_projectors_exact((1, 0, 0))
        bp = oracle.qmat_vec(pp, (oracle.QC0, oracle.qc(1), oracle.QC0))
        bm = oracle.qmat_vec(pm, (oracle.QC0, oracle.qc(1), oracle.QC0))
        self._expect_err("DUPLICATE_MODE", oracle.evaluate_torus_field_energy_helicity, "d", [((1, 0, 0), bp), ((1, 0, 0), bp)])
        self._expect_err("DUPLICATE_MODE", oracle.evaluate_torus_field_energy_helicity, "d", [((1, 0, 0), bp), ((-1, 0, 0), bp)])
        self._expect_err("NON_SOLENOIDAL_FIELD", oracle.evaluate_torus_field_energy_helicity, "ns", [((1, 0, 0), (oracle.QC1, oracle.QC0, oracle.QC0))])

        res_minus = oracle.evaluate_torus_field_energy_helicity("minus_beltrami", [((1, 0, 0), bm)])
        self.assertTrue(res_minus["woltjer_arnold_saturated"])
        self.assertTrue(res_minus["is_minimal_beltrami_ck_state"])
        self.assertEqual(res_minus["helicity_H"], "-1")
        res_mixed1 = oracle.evaluate_torus_field_energy_helicity("single_shell_mixed", [((1, 0, 0), oracle.qv_add(bp, bm))])
        self.assertFalse(res_mixed1["is_minimal_beltrami_ck_state"])
        self.assertFalse(res_mixed1["woltjer_arnold_saturated"])

        s1 = {0: oracle.QC1, 2: oracle.qc(2)}
        self.assertEqual(oracle._series_add(s1, {2: oracle.qc(-2)}), {0: oracle.QC1})
        self.assertEqual(oracle._series_sub(s1, {2: oracle.qc(2)}), {0: oracle.QC1})
        self.assertEqual(oracle._series_scale(oracle.QC0, s1), {})
        self.assertEqual(oracle._p3_add({(0, 0, 0): Fraction(1)}, {(0, 0, 0): Fraction(-1)}), {})
        self.assertEqual(oracle._p3_sub({(0, 0, 0): Fraction(1)}, {(0, 0, 0): Fraction(1)}), {})
        self.assertEqual(oracle._p3_scale(Fraction(0), {(0, 0, 0): Fraction(1)}), {})
        self.assertEqual(oracle._p3_int_face({(0, 1, 2): Fraction(1)}, 0, 1), Fraction(0))

    def test_theorem3_triad_and_fft_ntt_guards(self) -> None:
        t1_k = ((1, 2, 2), (-1, 2, -2), (0, -4, 0))
        _, _, ppk, _ = oracle.helical_projectors_exact(t1_k[0])
        _, _, ppp, _ = oracle.helical_projectors_exact(t1_k[1])
        _, _, ppq, _ = oracle.helical_projectors_exact(t1_k[2])
        b_ok = (
            oracle.qmat_vec(ppk, (oracle.qc(3), oracle.QC0, oracle.QC0)),
            oracle.qmat_vec(ppp, (oracle.QC0, oracle.qc(3), oracle.QC0)),
            oracle.qmat_vec(ppq, (oracle.qc(4), oracle.QC0, oracle.QC0)),
        )
        u_ok = b_ok
        self._expect_err(
            "NEGATIVE_RESISTIVITY",
            oracle.verify_helical_triad_helicity_conservation,
            "neg_eta", t1_k, b_ok, u_ok, eta_resistivity=Fraction(-1, 10),
        )
        self._expect_err(
            "TRIAD_NOT_CLOSED",
            oracle.verify_helical_triad_helicity_conservation,
            "open", ((1, 2, 2), (1, 2, 2), (0, -4, 0)), b_ok, u_ok,
        )
        b_bad = ((oracle.qc(1), oracle.qc(2), oracle.qc(2)), b_ok[1], b_ok[2])
        self._expect_err(
            "NON_SOLENOIDAL_FIELD",
            oracle.verify_helical_triad_helicity_conservation,
            "ns_b", t1_k, b_bad, u_ok,
        )
        self._expect_err("INVALID_FFT_LEN", oracle._fft1d_n4_qcomplex, [oracle.QC0, oracle.QC1])
        self._expect_err("INVALID_NTT_LEN", oracle.ntt_1d_mod, [], oracle.NTT_PRIME_1)
        self._expect_err("INVALID_NTT_LEN", oracle.ntt_1d_mod, [1, 2, 3], oracle.NTT_PRIME_1)
        self.assertEqual(oracle.crt_signed_pair((-42) % oracle.NTT_PRIME_1, (-42) % oracle.NTT_PRIME_2), -42)
        self.assertEqual(oracle.crt_signed_pair(42, 42), 42)


class Test03ZoneBFileIOHardlinksTOCTOUAndCLI(unittest.TestCase):
    """Hardened Zone-B file I/O: dir_fd TOCTOU, deleted CWD, surrogates, hardlinks, FIFOs, CLI."""

    def _expect_err(self, code: str, fn, *args, **kwargs) -> None:
        with self.assertRaises(oracle.CKHelicityError) as ctx:
            fn(*args, **kwargs)
        self.assertEqual(ctx.exception.code, code)

    def test_require_safe_path_and_file_io_adversarial(self) -> None:
        self._expect_err("INVALID_PATH_TYPE", audit.require_safe_path, "not_a_path")
        self._expect_err("INVALID_PATH_TYPE", audit.require_safe_path, _EvilPath("ok.json"))
        self._expect_err("INVALID_PATH", audit.require_safe_path, Path("bad\x00name"))
        self._expect_err("INVALID_UTF8_SURROGATE", audit.require_safe_path, Path("\ud800"))
        self._expect_err("INVALID_UTF8_SURROGATE", audit.require_safe_path, Path("dir/\ud800.json"))
        self._expect_err("NON_REGULAR_FILE", audit.require_safe_path, Path("/"))
        self._expect_err("NON_REGULAR_FILE", audit.require_safe_path, Path("."))
        self._expect_err("NON_REGULAR_FILE", audit.require_safe_path, Path(".."))
        self._expect_err("INVALID_WRITE_DATA", audit.write_regular_file_bytes, Path("/tmp/unused_s23a"), "str")  # type: ignore[arg-type]

        with tempfile.TemporaryDirectory(prefix="s23a_io_") as tmp:
            td = Path(tmp)
            real_dir = td / "real"
            real_dir.mkdir(mode=0o700)
            ok_file = real_dir / "ok.json"
            ok_file.write_bytes(b"{}\n")

            # Direct symlink, symlink ancestor, unnormalized sym_dir/../real/ok.json, missing ancestor
            sym_file = td / "sym.json"
            sym_file.symlink_to(ok_file)
            sym_dir = td / "sym_dir"
            sym_dir.symlink_to(real_dir)
            self._expect_err("SYMLINK_FORBIDDEN", audit.require_safe_path, sym_file)
            self._expect_err("SYMLINK_FORBIDDEN", audit.require_safe_path, sym_dir / "ok.json")
            self._expect_err("SYMLINK_FORBIDDEN", audit.require_safe_path, Path(f"{sym_dir}/../real/ok.json"))
            self._expect_err("SYMLINK_FORBIDDEN", audit.read_regular_file_bytes, sym_file)
            self._expect_err("SYMLINK_FORBIDDEN", audit.write_regular_file_bytes, sym_file, b"x")
            self._expect_err("FILE_IO_ERROR", audit.require_safe_path, td / "missing_dir" / "ok.json")
            self._expect_err("PATH_STAT_ERROR", audit.require_safe_path, ok_file / "child")

            # Valid non-existent leaf passes require_safe_path (for --write new file)
            self.assertEqual(audit.require_safe_path(real_dir / "brand_new.json"), real_dir / "brand_new.json")
            self.assertEqual(audit.require_safe_path(ok_file), ok_file)

            # Relative path inside symlinked PWD, clean PWD, unset PWD, and relative PWD
            old_cwd = os.getcwd()
            old_pwd = os.environ.get("PWD")
            try:
                os.chdir(real_dir)
                os.environ["PWD"] = str(sym_dir)
                self._expect_err("SYMLINK_FORBIDDEN", audit.require_safe_path, Path("ok.json"))
                os.environ["PWD"] = str(real_dir)
                self.assertEqual(audit.read_regular_file_bytes(Path("./ok.json")), b"{}\n")
                os.environ.pop("PWD", None)
                self.assertEqual(audit.read_regular_file_bytes(Path("ok.json")), b"{}\n")
                os.environ["PWD"] = "relative/pwd"
                self.assertEqual(audit.read_regular_file_bytes(Path("ok.json")), b"{}\n")
                rel_sym = real_dir / "local_sym"
                rel_sym.symlink_to(ok_file)
                self._expect_err("SYMLINK_FORBIDDEN", audit.require_safe_path, Path("local_sym"))
            finally:
                os.chdir(old_cwd)
                if old_pwd is None:
                    os.environ.pop("PWD", None)
                else:
                    os.environ["PWD"] = old_pwd

            # Missing file, directory, chmod 000, read-only dir write, FIFO (zero hang!)
            self._expect_err("FILE_READ_ERROR", audit.read_regular_file_bytes, td / "missing.json")
            self._expect_err("NON_REGULAR_FILE", audit.read_regular_file_bytes, real_dir)
            self._expect_err("NON_REGULAR_FILE", audit.write_regular_file_bytes, real_dir, b"x")

            no_perm = td / "noperm.json"
            no_perm.write_bytes(b"{}\n")
            os.chmod(no_perm, 0o000)
            ro_dir = td / "ro_dir"
            ro_dir.mkdir(mode=0o500)
            try:
                if os.geteuid() != 0:
                    self._expect_err("FILE_READ_ERROR", audit.read_regular_file_bytes, no_perm)
                    self._expect_err("FILE_WRITE_ERROR", audit.write_regular_file_bytes, ro_dir / "out.json", b"x")
            finally:
                os.chmod(no_perm, 0o600)
                os.chmod(ro_dir, 0o700)

            fifo = td / "pipe.fifo"
            os.mkfifo(fifo)
            self._expect_err("NON_REGULAR_FILE", audit.read_regular_file_bytes, fifo)
            self._expect_err("NON_REGULAR_FILE", audit.write_regular_file_bytes, fifo, b"x")

            if hasattr(os, "mkfifo"):
                nonreg_fifo = td / "nonreg_fifo"
                os.mkfifo(nonreg_fifo)
                self._expect_err("NON_REGULAR_FILE", audit.read_regular_file_bytes, nonreg_fifo)
                self._expect_err("NON_REGULAR_FILE", audit.write_regular_file_bytes, nonreg_fifo, b"x")

            if Path("/proc/kallsyms").exists():
                try:
                    audit.read_regular_file_bytes(Path("/proc/kallsyms"))
                except oracle.CKHelicityError as exc:
                    self.assertIn(exc.code, ("FILE_TOO_LARGE", "FILE_READ_ERROR"))

            # Exact boundary (== MAX_JSON_BYTES ok) vs oversized (> MAX_JSON_BYTES rejected)
            exact_max = td / "exact_max.json"
            exact_max.write_bytes(b"a" * oracle.MAX_JSON_BYTES)
            self.assertEqual(len(audit.read_regular_file_bytes(exact_max)), oracle.MAX_JSON_BYTES)
            big = td / "big.json"
            big.write_bytes(b"a" * (oracle.MAX_JSON_BYTES + 1))
            self._expect_err("FILE_TOO_LARGE", audit.read_regular_file_bytes, big)

            # Hardlink protection BEFORE any write/replace (original bytes stay 100% intact!)
            orig = td / "orig.json"
            orig.write_bytes(b"ORIGINAL_UNTOUCHED_BYTES\n")
            hard = td / "hard.json"
            os.link(orig, hard)
            self._expect_err("HARDLINK_FORBIDDEN", audit.write_regular_file_bytes, hard, b"CLOBBER\n")
            self.assertEqual(orig.read_bytes(), b"ORIGINAL_UNTOUCHED_BYTES\n")

            # Successful atomic regular write + shorter overwrite + zero stale temp files
            out_f = td / "out.json"
            audit.write_regular_file_bytes(out_f, b"hello_world\n")
            self.assertEqual(out_f.read_bytes(), b"hello_world\n")
            audit.write_regular_file_bytes(out_f, b"hi\n")
            self.assertEqual(out_f.read_bytes(), b"hi\n")
            self.assertEqual([p.name for p in td.glob(".ck_s23a_tmp_*")], [])

    def test_deleted_cwd_and_renameat2_toctou_resistance(self) -> None:
        # 1. Deleted-CWD fail-closed (in-process & live subprocess)
        old_cwd = os.getcwd()
        with tempfile.TemporaryDirectory(prefix="s23a_delcwd_") as tmp:
            doomed = Path(tmp) / "doomed"
            doomed.mkdir(mode=0o700)
            os.chdir(doomed)
            try:
                os.rmdir(doomed)
                self._expect_err("CWD_UNAVAILABLE", audit.require_safe_path, Path("c.json"))
                self._expect_err("CWD_UNAVAILABLE", audit.read_regular_file_bytes, Path("c.json"))
                proc = subprocess.run(
                    [sys.executable, "-I", "-B", str(Path(_THIS_DIR) / "ck_helicity_fft_audit.py"), "--check", "c.json"],
                    capture_output=True,
                    text=True,
                    check=False,
                )
                self.assertEqual(proc.returncode, 2)
                self.assertEqual(json.loads(proc.stderr)["error_code"], "CWD_UNAVAILABLE")
            finally:
                os.chdir(old_cwd)

        # 2. Live >= 500 concurrent renameat2(RENAME_EXCHANGE) TOCTOU read + write stress test (Linux only)
        if sys.platform == "linux":
            libc = ctypes.CDLL(None, use_errno=True)
            renameat2 = getattr(libc, "renameat2", None)
        else:
            renameat2 = None
        if renameat2 is not None:
            AT_FDCWD = -100
            RENAME_EXCHANGE = 2
            with tempfile.TemporaryDirectory(prefix="s23a_toctou_") as tmp:
                td = Path(tmp)
                canary_dir = td / "canary"
                canary_dir.mkdir(mode=0o700)
                canary_file = canary_dir / "data.json"
                canary_file.write_bytes(b"CANARY_DO_NOT_LEAK_OR_CLOBBER\n")

                safe_dir = td / "slot_a"
                safe_dir.mkdir(mode=0o700)
                (safe_dir / "data.json").write_bytes(b"SAFE_PAYLOAD\n")

                sym_slot = td / "slot_b"
                sym_slot.symlink_to(canary_dir)

                stop_ev = threading.Event()
                swaps = [0]
                p_a = os.fsencode(str(safe_dir))
                p_b = os.fsencode(str(sym_slot))

                def _swapper() -> None:
                    while not stop_ev.is_set() or swaps[0] < 600:
                        if renameat2(AT_FDCWD, p_a, AT_FDCWD, p_b, RENAME_EXCHANGE) == 0:
                            swaps[0] += 1
                        if stop_ev.is_set() and swaps[0] >= 600:
                            break

                t = threading.Thread(target=_swapper)
                t.start()
                try:
                    target = safe_dir / "data.json"
                    for i in range(600):
                        try:
                            got = audit.read_regular_file_bytes(target)
                            self.assertNotIn(b"CANARY", got)
                        except oracle.CKHelicityError as exc:
                            self.assertIn(exc.code, ("SYMLINK_FORBIDDEN", "PATH_STAT_ERROR", "FILE_READ_ERROR", "FILE_IO_ERROR"))
                        try:
                            audit.write_regular_file_bytes(target, f"SAFE_WRITE_{i}\n".encode("ascii"))
                        except oracle.CKHelicityError as exc:
                            self.assertIn(exc.code, ("SYMLINK_FORBIDDEN", "PATH_STAT_ERROR", "FILE_WRITE_ERROR", "FILE_IO_ERROR"))
                finally:
                    stop_ev.set()
                    t.join(timeout=5)

                self.assertGreaterEqual(swaps[0], 500)
                self.assertEqual(canary_file.read_bytes(), b"CANARY_DO_NOT_LEAK_OR_CLOBBER\n")

    def test_cli_argv_guards_and_error_json(self) -> None:
        bad_argvs: list[tuple[Any, str]] = [
            ("not_a_list", "INVALID_ARGV"),
            ([123], "INVALID_ARGV"),
            ([_EvilStr("--standalone")], "INVALID_ARGV"),
            (["\ud800"], "INVALID_UTF8_SURROGATE"),
            (["--check", "\ud800"], "INVALID_UTF8_SURROGATE"),
            (["--write=\ud800"], "INVALID_UTF8_SURROGATE"),
            (["--json", "--json"], "DUPLICATE_FLAG"),
            (["--standalone", "--standalone"], "CONFLICTING_MODE"),
            (["--standalone", "--check", "a.json"], "CONFLICTING_MODE"),
            (["--standalone", "--check=a.json"], "CONFLICTING_MODE"),
            (["--check", "a.json", "--write", "b.json"], "CONFLICTING_MODE"),
            (["--check"], "MISSING_PATH_ARG"),
            (["--write"], "MISSING_PATH_ARG"),
            (["--check", ""], "INVALID_PATH_ARG"),
            (["--write", ""], "INVALID_PATH_ARG"),
            (["--check", "--json"], "INVALID_PATH_ARG"),
            (["--write", "--json"], "INVALID_PATH_ARG"),
            (["--check=--json"], "INVALID_PATH_ARG"),
            (["--write=--json"], "INVALID_PATH_ARG"),
            (["--check="], "INVALID_PATH_ARG"),
            (["--write="], "INVALID_PATH_ARG"),
            (["--write", "-foo"], "INVALID_PATH_ARG"),
            (["--wr=--json"], "UNKNOWN_FLAG"),
            (["--unknown"], "UNKNOWN_FLAG"),
        ]
        with tempfile.TemporaryDirectory(prefix="s23a_cli_bad_") as tmp:
            old_cwd = os.getcwd()
            os.chdir(tmp)
            try:
                for argv, exp_code in bad_argvs:
                    buf_err = io.StringIO()
                    old_err = sys.stderr
                    try:
                        sys.stderr = buf_err
                        rc = audit.main(argv)
                    finally:
                        sys.stderr = old_err
                    self.assertEqual(rc, 2)
                    err_obj = json.loads(buf_err.getvalue())
                    self.assertFalse(err_obj["valid"])
                    self.assertEqual(err_obj["error_code"], exp_code)
                self.assertEqual(list(Path(tmp).iterdir()), [])
            finally:
                os.chdir(old_cwd)

        # Subprocess symlinked-PWD check on relative --check
        with tempfile.TemporaryDirectory(prefix="s23a_pwd_") as tmp:
            td = Path(tmp)
            real_dir = td / "real"
            real_dir.mkdir(mode=0o700)
            sym_dir = td / "sym"
            sym_dir.symlink_to(real_dir)
            (real_dir / "c.json").write_bytes(b"{}\n")
            proc = subprocess.run(
                [sys.executable, "-I", "-B", str(Path(_THIS_DIR) / "ck_helicity_fft_audit.py"), "--check", "c.json"],
                cwd=str(real_dir),
                env={"PATH": os.environ.get("PATH", ""), "PWD": str(sym_dir)},
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(proc.returncode, 2)
            self.assertEqual(json.loads(proc.stderr)["error_code"], "SYMLINK_FORBIDDEN")

    def test_darwin_system_root_alias_normalization(self) -> None:
        root_lnk = SimpleNamespace(st_mode=stat.S_IFLNK | 0o777, st_uid=0)
        root_dir = SimpleNamespace(st_mode=stat.S_IFDIR | 0o755, st_uid=0)
        user_lnk = SimpleNamespace(st_mode=stat.S_IFLNK | 0o777, st_uid=1000)

        def _fake_readlink(p: str) -> str:
            if p == "/var":
                return "private/var"
            if p == "/tmp":
                return "/private/tmp"
            if p == "/etc":
                return "private/etc"
            raise OSError("unexpected readlink")

        with (
            mock.patch.object(audit.sys, "platform", "darwin"),
            mock.patch.object(audit.os, "lstat", return_value=root_lnk),
            mock.patch.object(audit.os, "readlink", side_effect=_fake_readlink),
        ):
            self.assertEqual(
                audit._normalize_darwin_system_prefix(Path("/var/folders/xx/cert.json")),
                Path("/private/var/folders/xx/cert.json"),
            )
            self.assertEqual(
                audit._normalize_darwin_system_prefix(Path("/tmp/cert.json")),
                Path("/private/tmp/cert.json"),
            )
            self.assertEqual(
                audit._normalize_darwin_system_prefix(Path("/etc/cert.json")),
                Path("/private/etc/cert.json"),
            )
            self.assertEqual(
                audit._normalize_darwin_system_prefix(Path("/opt/cert.json")),
                Path("/opt/cert.json"),
            )
            self.assertEqual(
                audit._normalize_darwin_system_prefix(Path("a/var/folders/xx/cert.json")),
                Path("a/var/folders/xx/cert.json"),
            )
            self.assertEqual(
                audit._normalize_darwin_system_prefix(Path("/tmp"), allow_exact=True),
                Path("/private/tmp"),
            )
            self.assertEqual(
                audit._normalize_darwin_system_prefix(Path("/"), allow_exact=True),
                Path("/"),
            )
            self.assertEqual(audit._normalize_darwin_system_prefix(Path("/tmp")), Path("/tmp"))
            self.assertEqual(
                audit._normalize_darwin_system_prefix(Path("/tmp/../etc/passwd")),
                Path("/tmp/../etc/passwd"),
            )

            captured: list[list[str]] = []

            def _fake_step(start_fd: int, comps: list[str], label: str) -> int:
                captured.append(list(comps))
                return start_fd

            with mock.patch.object(audit, "_step_dir_fd_chain", side_effect=_fake_step):
                dfd, leaf = audit._open_parent_dir_fd(Path("/var/folders/xx/cert.json"))
                os.close(dfd)
                self.assertEqual(leaf, "cert.json")
                self.assertEqual(captured[-1], ["private", "var", "folders", "xx"])

                dfd2, leaf2 = audit._open_parent_dir_fd(Path("/var/folders/xx/evil_link/cert.json"))
                os.close(dfd2)
                self.assertEqual(leaf2, "cert.json")
                self.assertEqual(captured[-1], ["private", "var", "folders", "xx", "evil_link"])

                old_pwd = os.environ.get("PWD")
                try:
                    os.environ["PWD"] = "/tmp"
                    audit._check_logical_pwd_no_symlinks()
                    self.assertEqual(captured[-1], ["private", "tmp"])
                finally:
                    if old_pwd is None:
                        os.environ.pop("PWD", None)
                    else:
                        os.environ["PWD"] = old_pwd

        for bad_stat in (root_dir, user_lnk):
            with (
                mock.patch.object(audit.sys, "platform", "darwin"),
                mock.patch.object(audit.os, "lstat", return_value=bad_stat),
                mock.patch.object(audit.os, "readlink", side_effect=_fake_readlink),
            ):
                self.assertEqual(
                    audit._normalize_darwin_system_prefix(Path("/var/folders/xx/cert.json")),
                    Path("/var/folders/xx/cert.json"),
                )
        with (
            mock.patch.object(audit.sys, "platform", "darwin"),
            mock.patch.object(audit.os, "lstat", return_value=root_lnk),
            mock.patch.object(audit.os, "readlink", return_value="private/evil"),
        ):
            self.assertEqual(
                audit._normalize_darwin_system_prefix(Path("/var/folders/xx/cert.json")),
                Path("/var/folders/xx/cert.json"),
            )
        with (
            mock.patch.object(audit.sys, "platform", "darwin"),
            mock.patch.object(audit.os, "lstat", side_effect=OSError("no access")),
        ):
            self.assertEqual(
                audit._normalize_darwin_system_prefix(Path("/var/folders/xx/cert.json")),
                Path("/var/folders/xx/cert.json"),
            )
        with (
            mock.patch.object(audit.sys, "platform", "linux"),
            mock.patch.object(audit.os, "lstat", return_value=root_lnk),
            mock.patch.object(audit.os, "readlink", side_effect=_fake_readlink),
        ):
            self.assertEqual(
                audit._normalize_darwin_system_prefix(Path("/var/folders/xx/cert.json")),
                Path("/var/folders/xx/cert.json"),
            )


class Test04PayloadAndAuditTamperMatrix(unittest.TestCase):
    """Exhaustive tamper matrix killing every guard in validate_certificate_payload & independent_audit_payload."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.valid_cert = oracle.build_standalone_certificate()

    def _expect_err(self, code: str, fn, *args, **kwargs) -> None:
        with self.assertRaises(oracle.CKHelicityError) as ctx:
            fn(*args, **kwargs)
        self.assertEqual(ctx.exception.code, code)

    def _resign(self, cert: dict) -> dict:
        c = copy.deepcopy(cert)
        p_sha = oracle.sha256_hex(oracle.canonical_json_bytes(c["payload"]))
        c["payload_sha256"] = p_sha
        body = {
            "schema": c["schema"],
            "track_id": c["track_id"],
            "payload_sha256": p_sha,
            "payload": c["payload"],
        }
        c["certificate_sha256"] = oracle.sha256_hex(oracle.canonical_json_bytes(body))
        return c

    def test_validate_certificate_payload_tamper_cases(self) -> None:
        res_ok = oracle.validate_certificate_payload(self.valid_cert, full_replay=False)
        self.assertTrue(res_ok["valid"])
        self.assertFalse(res_ok["full_replay"])

        self._expect_err("CERT_NOT_DICT", oracle.validate_certificate_payload, [], full_replay=False)

        missing_k = copy.deepcopy(self.valid_cert)
        del missing_k["track_id"]
        self._expect_err("INVALID_CERT_KEYS", oracle.validate_certificate_payload, missing_k, full_replay=False)

        bad_schema = copy.deepcopy(self.valid_cert)
        bad_schema["schema"] = "wrong"
        self._expect_err("INVALID_SCHEMA", oracle.validate_certificate_payload, bad_schema, full_replay=False)

        bad_tid = copy.deepcopy(self.valid_cert)
        bad_tid["track_id"] = "wrong"
        self._expect_err("INVALID_TRACK_ID", oracle.validate_certificate_payload, bad_tid, full_replay=False)

        bad_payload_type = copy.deepcopy(self.valid_cert)
        bad_payload_type["payload"] = []
        self._expect_err("PAYLOAD_NOT_DICT", oracle.validate_certificate_payload, bad_payload_type, full_replay=False)

        bad_psha = copy.deepcopy(self.valid_cert)
        bad_psha["payload_sha256"] = ("0" if bad_psha["payload_sha256"][0] != "0" else "1") + bad_psha["payload_sha256"][1:]
        self._expect_err("PAYLOAD_SHA_MISMATCH", oracle.validate_certificate_payload, bad_psha, full_replay=False)

        bad_csha = copy.deepcopy(self.valid_cert)
        bad_csha["certificate_sha256"] = ("0" if bad_csha["certificate_sha256"][0] != "0" else "1") + bad_csha["certificate_sha256"][1:]
        self._expect_err("CERT_SHA_MISMATCH", oracle.validate_certificate_payload, bad_csha, full_replay=False)

        hollow = copy.deepcopy(self.valid_cert)
        hollow["payload"] = {}
        hollow = self._resign(hollow)
        self._expect_err("RECOMPUTATION_MISMATCH", oracle.validate_certificate_payload, hollow, full_replay=True)

    def test_independent_audit_payload_tamper_matrix(self) -> None:
        base_p = self.valid_cert["payload"]
        summary = audit.independent_audit_payload(base_p)
        self.assertTrue(summary["independent_audit_passed"])
        self.assertEqual(summary["torus_cables_checked"], 3)
        self.assertEqual(summary["ck_modes_checked"], 3)
        self.assertEqual(summary["projectors_checked"], 7)
        self.assertEqual(summary["triads_checked"], 3)

        def _check_tamper(code: str, mutator) -> None:
            p = copy.deepcopy(base_p)
            mutator(p)
            self._expect_err(code, audit.independent_audit_payload, p)

        # Theorem 1 tampers
        _check_tamper("AUDIT_T1_HOPF_FAILED", lambda p: p["theorem1_flux_tube_helicity"]["hopf_positive"].__setitem__("linking_matrix", [[0, 2], [2, 0]]))
        _check_tamper("AUDIT_T1_HOPF_FAILED", lambda p: p["theorem1_flux_tube_helicity"]["hopf_negative"].__setitem__("linking_matrix", [[0, 1], [1, 0]]))
        _check_tamper("AUDIT_T1_CHIRAL_FAILED", lambda p: p["theorem1_flux_tube_helicity"]["hopf_negative"].__setitem__("h_mutual", "5"))
        _check_tamper("AUDIT_T1_BORROMEAN_FAILED", lambda p: p["theorem1_flux_tube_helicity"]["borromean_rings"].__setitem__("linking_matrix", [[0, 1, 0], [1, 0, 0], [0, 0, 0]]))
        _check_tamper("AUDIT_T1_BORROMEAN_FAILED", lambda p: p["theorem1_flux_tube_helicity"]["borromean_rings"].__setitem__("h_mutual", "1"))
        _check_tamper("AUDIT_T1_TORUS_FAILED", lambda p: p["theorem1_flux_tube_helicity"]["torus_cables"][0].__setitem__("linking_matrix", [[0, 5], [5, 0]]))
        _check_tamper("AUDIT_T1_TORUS_FAILED", lambda p: p["theorem1_flux_tube_helicity"]["torus_cables"][0].__setitem__("torus_framing_matches_pq", False))
        _check_tamper("AUDIT_T1_CONTROL_FAILED", lambda p: p["theorem1_flux_tube_helicity"]["must_fail_odd_crossing_sum"].__setitem__("rejected", False))

        # Theorem 2 tampers
        _check_tamper("AUDIT_T2_CK_FAILED", lambda p: p["theorem2_ck_and_woltjer"]["cylindrical_ck_modes"][0].__setitem__("gamma_sq", "17"))
        _check_tamper("AUDIT_T2_CK_FAILED", lambda p: p["theorem2_ck_and_woltjer"]["cylindrical_ck_modes"][0].__setitem__("div_zero_exact", False))
        _check_tamper("AUDIT_T2_CK_FAILED", lambda p: p["theorem2_ck_and_woltjer"]["cylindrical_ck_modes"][0].__setitem__("curl_eq_lambda_b_exact", False))
        _check_tamper("AUDIT_T2_CONTROL_FAILED", lambda p: p["theorem2_ck_and_woltjer"]["must_fail_broken_dispersion"].__setitem__("residual_detected", False))
        _check_tamper("AUDIT_T2_WA_FAILED", lambda p: p["theorem2_ck_and_woltjer"]["woltjer_arnold_saturated"].__setitem__("woltjer_arnold_slack_2E_minus_lam1_absH", "1"))
        def _neg_slack(p: dict) -> None:
            wa = p["theorem2_ck_and_woltjer"]["woltjer_arnold_saturated"]
            wa["energy_E"] = "1"
            wa["helicity_H"] = "5"
            wa["woltjer_arnold_slack_2E_minus_lam1_absH"] = "-3"
        _check_tamper("AUDIT_T2_WA_FAILED", _neg_slack)
        def _unsat_beltrami(p: dict) -> None:
            wa = p["theorem2_ck_and_woltjer"]["woltjer_arnold_saturated"]
            wa["energy_E"] = "10"
            wa["helicity_H"] = "15"
            wa["woltjer_arnold_slack_2E_minus_lam1_absH"] = "5"
        _check_tamper("AUDIT_T2_WA_SAT_FAILED", _unsat_beltrami)
        _check_tamper("AUDIT_T2_VIRIAL_FAILED", lambda p: p["theorem2_ck_and_woltjer"]["chandrasekhar_fermi_virial"].__setitem__("pointwise_maxwell_virial_identity_zero", False))
        _check_tamper("AUDIT_T2_VIRIAL_FAILED", lambda p: p["theorem2_ck_and_woltjer"]["chandrasekhar_fermi_virial"].__setitem__("self_confined_R3_obstructed", False))

        # Theorem 3 tampers
        _check_tamper("AUDIT_T3_TRIAD_SUM", lambda p: p["theorem3_triads_and_fft"]["triads"][0].__setitem__("wavevectors", [[1, 2, 2], [1, 2, 2], [0, -4, 0]]))
        _check_tamper("AUDIT_T3_CONSERVATION", lambda p: p["theorem3_triads_and_fft"]["triads"][0].__setitem__("per_leg_ideal_dH_dt", ["1", "0", "0"]))
        _check_tamper("AUDIT_T3_CONSERVATION", lambda p: p["theorem3_triads_and_fft"]["triads"][0].__setitem__("ideal_helicity_conserved_exact", False))
        _check_tamper("AUDIT_T3_SPECTRAL", lambda p: p["theorem3_triads_and_fft"]["spectral_convolutions"]["qcomplex_fft3d_n4"].__setitem__("convolution_theorem_exact", False))
        _check_tamper("AUDIT_T3_SPECTRAL", lambda p: p["theorem3_triads_and_fft"]["spectral_convolutions"]["ntt_crt_3d"].__setitem__("n4_all_192_entries_exact_match", False))

    def test_file_level_canonical_byte_guards(self) -> None:
        raw = oracle.canonical_json_bytes(self.valid_cert) + b"\n"
        with tempfile.TemporaryDirectory(prefix="s23a_cert_") as tmp:
            td = Path(tmp)
            p_crlf = td / "crlf.json"
            p_crlf.write_bytes(raw.replace(b"\n", b"\r\n"))
            self._expect_err("CRLF_FORBIDDEN", audit.check_certificate_file, p_crlf)

            p_nolf = td / "nolf.json"
            p_nolf.write_bytes(raw[:-1])
            self._expect_err("MISSING_TRAILING_LF", audit.check_certificate_file, p_nolf)

            p_utf8 = td / "badutf8.json"
            p_utf8.write_bytes(b"\xff\xfe\n")
            self._expect_err("INVALID_UTF8", audit.check_certificate_file, p_utf8)

            p_pretty = td / "pretty.json"
            p_pretty.write_bytes((json.dumps(self.valid_cert, indent=2) + "\n").encode("ascii"))
            self._expect_err("NON_CANONICAL_BYTES", audit.check_certificate_file, p_pretty)


class Test99EndToEndTheoremsAndCLI(unittest.TestCase):
    """End-to-end exact physics checks and CLI roundtrip (--standalone, --write, --check)."""

    def test_all_three_theorems_and_cli_roundtrip(self) -> None:
        cert = oracle.build_standalone_certificate()
        p = cert["payload"]
        self.assertEqual(p["oracle_class"], "exact")
        self.assertEqual(p["novelty_classification"], "N1")
        self.assertTrue(p["zero_floats_exact_arithmetic"])

        # Theorem 1
        t1 = p["theorem1_flux_tube_helicity"]
        self.assertEqual(t1["unknot"]["h_total"], "0")
        self.assertEqual(t1["hopf_positive"]["h_mutual"], "5")
        self.assertEqual(t1["hopf_negative"]["h_mutual"], "-5")
        self.assertTrue(t1["hopf_chiral_antisymmetry"])
        self.assertEqual([tc["linking_matrix"][0][1] for tc in t1["torus_cables"]], [6, 10, 12])
        self.assertEqual(t1["whitehead_link"]["h_mutual"], "0")
        self.assertTrue(t1["law5_borromean_obstruction"]["abelian_u1_blind_to_brunnian_triple_linking"])

        # Theorem 2
        t2 = p["theorem2_ck_and_woltjer"]
        self.assertEqual(len(t2["cylindrical_ck_modes"]), 3)
        self.assertTrue(all(m["div_zero_exact"] and m["curl_eq_lambda_b_exact"] for m in t2["cylindrical_ck_modes"]))
        self.assertEqual(len(t2["pythagorean_helical_projectors"]), 7)
        self.assertTrue(all(pr["curl_eigen_exact"] and pr["real_sym6_symmetric"] for pr in t2["pythagorean_helical_projectors"]))
        self.assertEqual(t2["woltjer_arnold_saturated"]["woltjer_arnold_slack_2E_minus_lam1_absH"], "0")
        self.assertTrue(t2["woltjer_arnold_saturated"]["is_minimal_beltrami_ck_state"])
        self.assertEqual(t2["woltjer_arnold_strict_slack"]["woltjer_arnold_slack_2E_minus_lam1_absH"], "4558/27")
        self.assertEqual(t2["chandrasekhar_fermi_virial"]["cube_magnetic_energy_M"], "149/9")
        self.assertTrue(t2["chandrasekhar_fermi_virial"]["gauss_virial_cube_identity_exact"])

        # Theorem 3
        t3 = p["theorem3_triads_and_fft"]
        self.assertEqual(len(t3["triads"]), 3)
        self.assertTrue(all(tr["ideal_helicity_conserved_exact"] and tr["nontrivial_interscale_transfer"] for tr in t3["triads"]))
        self.assertTrue(t3["triads"][1]["velocity_is_non_solenoidal"])
        self.assertTrue(t3["triads"][2]["resistive_breaks_conservation"])
        self.assertTrue(t3["triads"][2]["resistive_spectral_matches"])
        sp = t3["spectral_convolutions"]
        self.assertTrue(sp["qcomplex_fft3d_n4"]["roundtrip_exact"])
        self.assertTrue(sp["qcomplex_fft3d_n4"]["parseval_exact"])
        self.assertTrue(sp["qcomplex_fft3d_n4"]["convolution_theorem_exact"])
        self.assertTrue(sp["ntt_crt_3d"]["n4_all_192_entries_exact_match"])
        self.assertTrue(sp["ntt_crt_3d"]["n8_roundtrip_p1_exact"])
        self.assertTrue(sp["ntt_crt_3d"]["n8_modular_parseval_p1_exact"])
        self.assertTrue(sp["ntt_crt_3d"]["n8_spotcheck_direct_match"])

        # CLI roundtrip (both space-separated and '=' syntax!)
        with tempfile.TemporaryDirectory(prefix="s23a_cli_") as tmp:
            cert_path = Path(tmp) / "cert.json"
            cert_path2 = Path(tmp) / "cert2.json"
            for argv, check_fn in [
                ([], lambda out: self.assertIn("OK " + oracle.SCHEMA_VERSION, out)),
                (["--standalone", "--json"], lambda out: self.assertEqual(json.loads(out)["payload_sha256"], cert["payload_sha256"])),
                (["--write", str(cert_path), "--json"], lambda out: self.assertTrue(json.loads(out)["written"])),
                (["--check", str(cert_path), "--json"], lambda out: self.assertTrue(json.loads(out)["valid"])),
                ([f"--write={cert_path2}", "--json"], lambda out: self.assertTrue(json.loads(out)["written"])),
                ([f"--check={cert_path2}", "--json"], lambda out: self.assertTrue(json.loads(out)["valid"])),
            ]:
                buf_out = io.StringIO()
                old_out = sys.stdout
                try:
                    sys.stdout = buf_out
                    rc = audit.main(argv)
                finally:
                    sys.stdout = old_out
                self.assertEqual(rc, 0)
                check_fn(buf_out.getvalue())


if __name__ == "__main__":
    unittest.main()
