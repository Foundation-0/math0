#!/usr/bin/env python3
"""Track S33 R5 Adversarial, Concurrency & 100% Mutation-Kill Test Suite.

Pure Python 3 standard library: zero external dependencies, zero bare asserts,
zero AST float literals, zero float() calls, zero RNG.
"""
from __future__ import annotations

import copy
import ctypes
from fractions import Fraction
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import unittest

_THIS_DIR = str(Path(__file__).resolve().parent)
if _THIS_DIR not in sys.path:
    sys.path.insert(0, _THIS_DIR)

import leonardo_codices_audit as audit
import leonardo_codices_oracle as oracle

# Runtime float obtained strictly from JSON parser (zero float literal / float() in AST)
_RUNTIME_FLOAT = json.loads("1.5")


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


class Test01ZoneBPrimitivesAndValidation(unittest.TestCase):
    """Exact type, boundary, canonical-rational, iterative JSON, and digest guards."""

    def _expect_err(self, code: str, fn, *args, **kwargs) -> None:
        with self.assertRaises(oracle.LeonardoError) as ctx:
            fn(*args, **kwargs)
        self.assertEqual(ctx.exception.code, code)

    def test_strict_bool_int_str_bytes_hex64_boundaries(self) -> None:
        self.assertTrue(oracle.require_bool(True, "b"))
        self.assertFalse(oracle.require_bool(False, "b"))
        self._expect_err("INVALID_BOOL", oracle.require_bool, 1, "b")
        self._expect_err("INVALID_BOOL", oracle.require_bool, "true", "b")

        self.assertEqual(oracle.require_int(0, "n", lo=0, hi=0), 0)
        self.assertEqual(oracle.require_int((1 << oracle.MAX_INT_BITS) - 1, "max"), (1 << oracle.MAX_INT_BITS) - 1)
        self._expect_err("INVALID_INT", oracle.require_int, True, "n")
        self._expect_err("INVALID_INT", oracle.require_int, _EvilInt(5), "n")
        self._expect_err("INVALID_INT", oracle.require_int, _RUNTIME_FLOAT, "n")
        self._expect_err("INT_TOO_LARGE", oracle.require_int, 1 << oracle.MAX_INT_BITS, "n")
        self._expect_err("INVALID_BOUND", oracle.require_int, 5, "n", lo=True)
        self._expect_err("INVALID_BOUND", oracle.require_int, 5, "n", hi=True)
        self._expect_err("INT_OUT_OF_RANGE", oracle.require_int, -1, "n", lo=0)
        self._expect_err("INT_OUT_OF_RANGE", oracle.require_int, 6, "n", hi=5)

        self.assertEqual(oracle.require_str("abc", "s", max_len=3), "abc")
        self._expect_err("INVALID_STR", oracle.require_str, _EvilStr("abc"), "s")
        self._expect_err("STR_TOO_LONG", oracle.require_str, "abcd", "s", max_len=3)
        self._expect_err("INT_OUT_OF_RANGE", oracle.require_str, "a", "s", max_len=oracle.HARD_MAX_BYTES_CAP + 1)
        self._expect_err("INVALID_UTF8_SURROGATE", oracle.require_str, "\ud800", "s")

        self.assertEqual(len(oracle.sha256_hex(b"ok")), 64)
        self._expect_err("INVALID_BYTES", oracle.sha256_hex, "not_bytes")

        h_ok = "0123456789abcdef" * 4
        self.assertEqual(oracle.require_hex64(h_ok, "h"), h_ok)
        self.assertTrue(oracle.constant_time_hex64_equal(h_ok, h_ok, "eq"))
        self.assertFalse(oracle.constant_time_hex64_equal(h_ok, "f" + h_ok[1:], "neq"))
        self._expect_err("INVALID_HEX64", oracle.require_hex64, "a" * 63, "h")
        self._expect_err("STR_TOO_LONG", oracle.require_hex64, "a" * 65, "h")
        self._expect_err("INVALID_HEX64", oracle.require_hex64, "A" * 64, "h")
        self._expect_err("INVALID_HEX64", oracle.require_hex64, "\u00e9" * 64, "h")
        self._expect_err("INVALID_UTF8_SURROGATE", oracle.require_hex64, "\ud800" * 64, "h")

    def test_canonical_rational_parser_and_formatter(self) -> None:
        self.assertEqual(oracle.parse_exact_rational(0), Fraction(0, 1))
        self.assertEqual(oracle.parse_exact_rational(-7), Fraction(-7, 1))
        self.assertEqual(oracle.parse_exact_rational(Fraction(3, 5)), Fraction(3, 5))
        self.assertEqual(oracle.parse_exact_rational("0"), Fraction(0, 1))
        self.assertEqual(oracle.parse_exact_rational("-13/7"), Fraction(-13, 7))
        self.assertEqual(oracle.parse_exact_rational((1 << oracle.MAX_INT_BITS) - 1), Fraction((1 << oracle.MAX_INT_BITS) - 1, 1))
        self.assertEqual(
            oracle.parse_exact_rational("1" + "0" * (oracle.MAX_RATIONAL_CHARS - 1)),
            Fraction(10 ** (oracle.MAX_RATIONAL_CHARS - 1), 1),
        )

        self._expect_err("RATIONAL_TOO_LARGE", oracle.parse_exact_rational, 1 << oracle.MAX_INT_BITS)
        self._expect_err("RATIONAL_TOO_LARGE", oracle.parse_exact_rational, Fraction(1 << oracle.MAX_INT_BITS, 1))
        self._expect_err("RATIONAL_TOO_LARGE", oracle.parse_exact_rational, Fraction(1, 1 << oracle.MAX_INT_BITS))
        self._expect_err("INVALID_RATIONAL_TYPE", oracle.parse_exact_rational, True)
        self._expect_err("INVALID_RATIONAL_TYPE", oracle.parse_exact_rational, _RUNTIME_FLOAT)
        self._expect_err("INVALID_RATIONAL_TYPE", oracle.parse_exact_rational, _EvilFrac(1, 2))
        self._expect_err("INVALID_RATIONAL_TYPE", oracle.parse_exact_rational, _EvilStr("1/2"))
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "1" * (oracle.MAX_RATIONAL_CHARS + 1))
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "1/2/3")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "-")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "\u00b2")  # Unicode superscript digit
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "\u0661\u0662")  # Arabic-Indic digits
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "\u2460")  # Circled digit
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "a")       # ASCII non-digit
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "007")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "-0")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "+5")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "1/02")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "1/0")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "3/1")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "1/a")
        self._expect_err("INVALID_RATIONAL_STR", oracle.parse_exact_rational, "1/")
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
        self.assertEqual(oracle.format_rational(Fraction(-0, 1)), "0")
        self.assertEqual(oracle.format_rational(Fraction(-5, 3)), "-5/3")
        self.assertEqual(oracle.format_rational(Fraction((1 << oracle.MAX_FORMAT_BITS) - 1, 1)), str((1 << oracle.MAX_FORMAT_BITS) - 1))
        self._expect_err("INVALID_RATIONAL_TYPE", oracle.format_rational, 5)
        self._expect_err("INVALID_RATIONAL_TYPE", oracle.format_rational, _EvilFrac(1, 2))
        self._expect_err("RATIONAL_TOO_LARGE", oracle.format_rational, Fraction(1 << oracle.MAX_FORMAT_BITS, 1))
        self._expect_err("RATIONAL_TOO_LARGE", oracle.format_rational, Fraction(1, 1 << oracle.MAX_FORMAT_BITS))

    def test_iterative_json_validator_and_strict_parser(self) -> None:
        ok_nested: list = []
        cur = ok_nested
        for _ in range(oracle.MAX_JSON_DEPTH):
            nxt: list = []
            cur.append(nxt)
            cur = nxt
        oracle.validate_json_tree_iterative(ok_nested)
        cur.append(0)
        self._expect_err("JSON_DEPTH_EXCEEDED", oracle.validate_json_tree_iterative, ok_nested)

        deep: list = []
        cur = deep
        for _ in range(1500):
            nxt = []
            cur.append(nxt)
            cur = nxt
        self._expect_err("JSON_DEPTH_EXCEEDED", oracle.validate_json_tree_iterative, deep)

        cyc_d: dict = {}
        cyc_d["self"] = cyc_d
        self._expect_err("JSON_CYCLE", oracle.validate_json_tree_iterative, cyc_d)
        cyc_l: list = []
        cyc_l.append(cyc_l)
        self._expect_err("JSON_CYCLE", oracle.validate_json_tree_iterative, cyc_l)

        shared = {"x": 1}
        oracle.validate_json_tree_iterative({"a": shared, "b": shared})

        oracle.validate_json_tree_iterative({"ok_int": 10 ** 615, "none": None, "flag": True})
        self._expect_err("INT_TOO_LARGE", oracle.validate_json_tree_iterative, {"huge_bits": 1 << 2048})
        self._expect_err("INT_TOO_LARGE", oracle.validate_json_tree_iterative, {"huge_digits": 10 ** 616})
        self._expect_err("INT_TOO_LARGE", oracle.canonical_json_bytes, {"x": 10 ** 4300})

        self._expect_err("FORBIDDEN_JSON_TYPE", oracle.validate_json_tree_iterative, _EvilDict({"a": 1}))
        self._expect_err("FORBIDDEN_JSON_TYPE", oracle.validate_json_tree_iterative, _EvilList([1]))
        self._expect_err("FORBIDDEN_JSON_TYPE", oracle.validate_json_tree_iterative, {"x": _RUNTIME_FLOAT})
        self._expect_err("INVALID_STR", oracle.validate_json_tree_iterative, {1: "bad_key"})

        self.assertEqual(oracle.parse_strict_json_text("[1,2]", require_object=False), [1, 2])
        self._expect_err("INVALID_BOOL", oracle.parse_strict_json_text, "{}", require_object=1)  # type: ignore[arg-type]
        self._expect_err("INT_OUT_OF_RANGE", oracle.parse_strict_json_text, "{}", max_bytes=oracle.HARD_MAX_BYTES_CAP + 1)
        self._expect_err("JSON_NOT_OBJECT", oracle.parse_strict_json_text, "[1,2]", require_object=True)
        self._expect_err("DUPLICATE_JSON_KEY", oracle.parse_strict_json_text, '{"a":1,"\\u0061":2}')
        self._expect_err("FLOAT_FORBIDDEN", oracle.parse_strict_json_text, '{"x":1.5}')
        self._expect_err("NONFINITE_CONSTANT", oracle.parse_strict_json_text, '{"x":NaN}')
        self._expect_err("NONFINITE_CONSTANT", oracle.parse_strict_json_text, '{"x":Infinity}')
        self._expect_err("INVALID_JSON", oracle.parse_strict_json_text, '{"x":' + ("9" * 5000) + "}")
        self._expect_err("JSON_DEPTH_EXCEEDED", oracle.parse_strict_json_text, ("[" * 1500) + "0" + ("]" * 1500), require_object=False)
        self._expect_err("INVALID_JSON", oracle.parse_strict_json_text, '{"a":')


class Test02PublicMathAPIAndNegativeControls(unittest.TestCase):
    """Strict validation and algebraic edge/negative checks across all 5 pillars."""

    def _expect_err(self, code: str, fn, *args, **kwargs) -> None:
        with self.assertRaises(oracle.LeonardoError) as ctx:
            fn(*args, **kwargs)
        self.assertEqual(ctx.exception.code, code)

    def test_linear_algebra_bareiss_and_sylvester_guards(self) -> None:
        # Singular, asymmetric, hyperbolic 2x2 pair pivot, and invalid shapes
        self.assertEqual(oracle.bareiss_det_exact([[1, 2], [2, 4]]), Fraction(0, 1))
        self.assertEqual(oracle.bareiss_det_exact([[0, 1], [1, 0]]), Fraction(-1, 1))
        self._expect_err("INVALID_MATRIX", oracle.bareiss_det_exact, [])
        self._expect_err("INVALID_MATRIX", oracle.bareiss_det_exact, "bad")  # type: ignore[arg-type]
        self._expect_err("INVALID_MATRIX", oracle.bareiss_det_exact, _EvilList([[1]]))
        self._expect_err("INVALID_MATRIX", oracle.bareiss_det_exact, [[1, 2], [3]])
        self._expect_err("INVALID_MATRIX", oracle.bareiss_det_exact, ["ab", "cd"])  # type: ignore[list-item]

        self._expect_err("INVALID_VECTOR", oracle.solve_linear_exact, [[1]], "1")  # type: ignore[arg-type]
        self._expect_err("INVALID_VECTOR", oracle.solve_linear_exact, [[1]], [1, 2])
        self._expect_err("SINGULAR_MATRIX", oracle.solve_linear_exact, [[1, 2], [2, 4]], [1, 2])

        self._expect_err("ASYMMETRIC_MATRIX", oracle.sylvester_inertia_exact, [[1, 2], [0, 1]])
        # Off-diagonal-only hyperbolic matrix [[0, 1], [1, 0]] exercises pair-pivot branch
        hyp = oracle.sylvester_inertia_exact([[0, 1], [1, 0]])
        self.assertEqual((hyp["n_pos"], hyp["n_neg"], hyp["n_zero"]), (1, 1, 0))
        self.assertTrue(hyp["congruence_verified"])
        # Zero matrix exercises all-zero remaining block
        z2 = oracle.sylvester_inertia_exact([[0, 0], [0, 0]])
        self.assertEqual((z2["n_pos"], z2["n_neg"], z2["n_zero"]), (0, 0, 2))
        self.assertTrue(z2["congruence_verified"])
        # Pivot-swap diagonal branch [[0, 0], [0, 3]]
        sw = oracle.sylvester_inertia_exact([[0, 0], [0, 3]])
        self.assertEqual((sw["n_pos"], sw["n_neg"], sw["n_zero"]), (1, 0, 1))
        self.assertTrue(sw["congruence_verified"])

    def test_pillars_1_to_5_public_api_guards(self) -> None:
        # Pillar 1: zero quadratic coeff (c_2=0, c_3=0) -> not straight hypotenuse
        flat_zero = oracle.evaluate_pitcher_snapshot_poly([1, 2, 0], 10)
        self.assertFalse(flat_zero["is_straight_hypotenuse"])
        self.assertEqual(flat_zero["hypotenuse_slope_dy_over_dx"], "non_constant")
        self._expect_err("INVALID_TRAJECTORY", oracle.evaluate_pitcher_snapshot_poly, [1, 2], 10)
        self._expect_err("INVALID_TRAJECTORY", oracle.evaluate_pitcher_snapshot_poly, "123", 10)  # type: ignore[arg-type]
        self._expect_err("NONPOSITIVE_GRAVITY", oracle.evaluate_pitcher_snapshot_poly, [0, 0, 1], 0)

        # Pillar 2: Rayleigh-Lamb and square helper guards
        self.assertEqual(oracle.rayleigh_lamb_omega_sq(2, 0, 1), Fraction(12, 1))
        self._expect_err("INT_OUT_OF_RANGE", oracle.rayleigh_lamb_omega_sq, 1, 0)
        self._expect_err("NEGATIVE_DENSITY_RATIO", oracle.rayleigh_lamb_omega_sq, 2, -1)
        self._expect_err("NEGATIVE_SURFACE_TENSION", oracle.rayleigh_lamb_omega_sq, 2, 0, -1)
        self.assertIsNone(oracle._is_rational_square(Fraction(-4, 1)))
        self.assertIsNone(oracle._is_rational_square(Fraction(1, 4)))
        self.assertEqual(oracle._is_rational_square(Fraction(9, 1)), 3)

        # Pillar 3: Reciprocal bridge guards
        self._expect_err("NEGATIVE_FRICTION", oracle.verify_reciprocal_bridge_at_friction, Fraction(-1, 10))

        # Pillar 4: Branching exponent & Kirchhoff-Schur guards
        self.assertEqual(oracle.generalized_branching_exponent(2, 2, 2), Fraction(2, 1))
        self._expect_err("INT_OUT_OF_RANGE", oracle.generalized_branching_exponent, 0, 2, 2)
        one_lvl = oracle.kirchhoff_schur_binary_tree_conductance([Fraction(3, 1)])
        self.assertEqual(one_lvl["effective_resistance_R_eff"], "1/3")
        self.assertTrue(one_lvl["schur_matches_series_parallel"])
        six_lvl = oracle.kirchhoff_schur_binary_tree_conductance([1, 1, 1, 1, 1, 1])
        self.assertEqual(six_lvl["effective_resistance_R_eff"], "63/32")
        self.assertTrue(six_lvl["schur_matches_series_parallel"])
        self._expect_err("INVALID_CONDUCTANCES", oracle.kirchhoff_schur_binary_tree_conductance, [])
        self._expect_err("INVALID_CONDUCTANCES", oracle.kirchhoff_schur_binary_tree_conductance, "123")  # type: ignore[arg-type]
        self._expect_err("TREE_TOO_DEEP", oracle.kirchhoff_schur_binary_tree_conductance, [1, 1, 1, 1, 1, 1, 1])
        self._expect_err("NONPOSITIVE_CONDUCTANCE", oracle.kirchhoff_schur_binary_tree_conductance, [1, 0])

        # Pillar 5: Chebyshev, F_p irreducibility, Ferrari helper, and aerial screw guards
        self.assertEqual(oracle.chebyshev_u_poly(0), [1])
        self.assertEqual(oracle.chebyshev_u_poly(1), [0, 2])
        self.assertEqual(oracle._fp_trim([0, 0], 5), [])
        self.assertEqual(oracle._fp_trim([1, 0], 5), [1])
        self.assertEqual(oracle._divisors_pos(0), [1])
        self.assertEqual(oracle._find_rational_root_cubic([Fraction(0), Fraction(1), Fraction(0), Fraction(1)]), Fraction(0))
        self.assertIsNone(oracle._find_rational_root_cubic([Fraction(-1), Fraction(-2), Fraction(0), Fraction(4)]))
        self.assertFalse(oracle.is_irreducible_mod_prime([-1, 0, 1], 5))  # x^2 - 1 reducible mod 5
        self._expect_err("INVALID_POLY", oracle.is_irreducible_mod_prime, [1], 5)
        self._expect_err("INVALID_POLY", oracle.is_irreducible_mod_prime, "12", 5)  # type: ignore[arg-type]
        self._expect_err("NON_PRIME_MODULUS", oracle.is_irreducible_mod_prime, [1, 1], 9)
        self._expect_err("LEADING_COEFF_VANISHES_MOD_P", oracle.is_irreducible_mod_prime, [1, 5], 5)

        self._expect_err("NONPOSITIVE_SCALING", oracle.evaluate_aerial_screw_isolift, 0, 1, 1)
        self._expect_err("NONPOSITIVE_SCALING", oracle.evaluate_aerial_screw_isolift, 1, 0, 1)
        self._expect_err("NONPOSITIVE_SCALING", oracle.evaluate_aerial_screw_isolift, 1, 1, 0)


class Test03ZoneBFileIOHardlinksTOCTOUAndCLI(unittest.TestCase):
    """Hardened Zone-B file I/O: dir_fd TOCTOU, hardlink race, deleted CWD, surrogates, CLI."""

    def _expect_err(self, code: str, fn, *args, **kwargs) -> None:
        with self.assertRaises(oracle.LeonardoError) as ctx:
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
        self._expect_err("NON_REGULAR_FILE", audit.require_safe_path, Path("a/.."))
        self._expect_err("INVALID_WRITE_DATA", audit.write_regular_file_bytes, Path("/tmp/unused_s33"), "str")  # type: ignore[arg-type]
        self._expect_err("INT_OUT_OF_RANGE", audit.read_regular_file_bytes, Path("/tmp/unused_s33"), max_bytes=oracle.HARD_MAX_BYTES_CAP + 1)
        self._expect_err("INT_OUT_OF_RANGE", audit.read_regular_file_bytes, Path("/tmp/unused_s33"), max_bytes=1 << 100)

        with tempfile.TemporaryDirectory(prefix="s33_io_") as tmp:
            td = Path(tmp)
            real_dir = td / "real"
            real_dir.mkdir(mode=0o700)
            ok_file = real_dir / "ok.json"
            ok_file.write_bytes(b"{}\n")

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

            self.assertEqual(audit.require_safe_path(real_dir / "brand_new.json"), real_dir / "brand_new.json")
            self.assertEqual(audit.require_safe_path(ok_file), ok_file)

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
                os.environ["PWD"] = ""
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

            if Path("/dev/null").exists():
                self._expect_err("NON_REGULAR_FILE", audit.read_regular_file_bytes, Path("/dev/null"))
                self._expect_err("NON_REGULAR_FILE", audit.write_regular_file_bytes, Path("/dev/null"), b"x")

            if Path("/proc/kallsyms").exists():
                try:
                    audit.read_regular_file_bytes(Path("/proc/kallsyms"))
                except oracle.LeonardoError as exc:
                    self.assertIn(exc.code, ("FILE_TOO_LARGE", "FILE_READ_ERROR"))

            exact_max = td / "exact_max.json"
            exact_max.write_bytes(b"a" * oracle.MAX_JSON_BYTES)
            self.assertEqual(len(audit.read_regular_file_bytes(exact_max)), oracle.MAX_JSON_BYTES)
            big = td / "big.json"
            big.write_bytes(b"a" * (oracle.MAX_JSON_BYTES + 1))
            self._expect_err("FILE_TOO_LARGE", audit.read_regular_file_bytes, big)

            orig = td / "orig.json"
            orig.write_bytes(b"ORIGINAL_UNTOUCHED_BYTES\n")
            hard = td / "hard.json"
            os.link(orig, hard)
            self._expect_err("HARDLINK_FORBIDDEN", audit.write_regular_file_bytes, hard, b"CLOBBER\n")
            self.assertEqual(orig.read_bytes(), b"ORIGINAL_UNTOUCHED_BYTES\n")

            out_f = td / "out.json"
            audit.write_regular_file_bytes(out_f, b"hello_world\n")
            self.assertEqual(out_f.read_bytes(), b"hello_world\n")
            audit.write_regular_file_bytes(out_f, b"hi\n")
            self.assertEqual(out_f.read_bytes(), b"hi\n")
            self.assertEqual([p.name for p in td.glob(".s33_leonardo_tmp_*")], [])

    def test_deleted_cwd_renameat2_toctou_and_hardlink_races(self) -> None:
        # 1. Deleted-CWD fail-closed
        old_cwd = os.getcwd()
        with tempfile.TemporaryDirectory(prefix="s33_delcwd_") as tmp:
            doomed = Path(tmp) / "doomed"
            doomed.mkdir(mode=0o700)
            os.chdir(doomed)
            try:
                os.rmdir(doomed)
                self._expect_err("CWD_UNAVAILABLE", audit.require_safe_path, Path("c.json"))
                self._expect_err("CWD_UNAVAILABLE", audit.read_regular_file_bytes, Path("c.json"))
                proc = subprocess.run(
                    [sys.executable, "-I", "-B", str(Path(_THIS_DIR) / "leonardo_codices_audit.py"), "--check", "c.json"],
                    capture_output=True,
                    text=True,
                    check=False,
                )
                self.assertEqual(proc.returncode, 2)
                self.assertEqual(json.loads(proc.stderr)["error_code"], "CWD_UNAVAILABLE")
            finally:
                os.chdir(old_cwd)

        # 2. Live >= 500 concurrent renameat2(RENAME_EXCHANGE) swaps across 550 read+write cycles
        libc = ctypes.CDLL(None, use_errno=True)
        renameat2 = getattr(libc, "renameat2", None)
        if renameat2 is not None:
            AT_FDCWD = -100
            RENAME_EXCHANGE = 2
            with tempfile.TemporaryDirectory(prefix="s33_toctou_") as tmp:
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
                    for i in range(550):
                        try:
                            got = audit.read_regular_file_bytes(target)
                            self.assertNotIn(b"CANARY", got)
                        except oracle.LeonardoError as exc:
                            self.assertIn(exc.code, ("SYMLINK_FORBIDDEN", "PATH_STAT_ERROR", "FILE_READ_ERROR", "FILE_IO_ERROR"))
                        try:
                            audit.write_regular_file_bytes(target, f"SAFE_WRITE_{i}\n".encode("ascii"))
                        except oracle.LeonardoError as exc:
                            self.assertIn(exc.code, ("SYMLINK_FORBIDDEN", "PATH_STAT_ERROR", "FILE_WRITE_ERROR", "FILE_IO_ERROR"))
                finally:
                    stop_ev.set()
                    t.join(timeout=5)

                self.assertGreaterEqual(swaps[0], 500)
                self.assertEqual(canary_file.read_bytes(), b"CANARY_DO_NOT_LEAK_OR_CLOBBER\n")
                self.assertEqual([p.name for p in safe_dir.glob(".s33_leonardo_tmp_*")], [])

        # 3. Live >= 400 concurrent os.link / os.unlink hardlink write race (0 victim clobbers!)
        with tempfile.TemporaryDirectory(prefix="s33_hlrace_") as tmp:
            td = Path(tmp)
            victim = td / "victim.json"
            victim.write_bytes(b"VICTIM_INODE_IMMUTABLE\n")
            target = td / "target.json"
            stop_hl = threading.Event()

            def _hl_racer() -> None:
                while not stop_hl.is_set():
                    try:
                        os.unlink(target)
                    except OSError:
                        pass
                    try:
                        os.link(victim, target)
                    except OSError:
                        pass

            th = threading.Thread(target=_hl_racer)
            th.start()
            try:
                for i in range(420):
                    try:
                        audit.write_regular_file_bytes(target, f"NEW_INODE_{i}\n".encode("ascii"))
                    except oracle.LeonardoError as exc:
                        self.assertIn(exc.code, ("HARDLINK_FORBIDDEN", "FILE_WRITE_ERROR"))
            finally:
                stop_hl.set()
                th.join(timeout=5)
            self.assertEqual(victim.read_bytes(), b"VICTIM_INODE_IMMUTABLE\n")
            self.assertEqual([p.name for p in td.glob(".s33_leonardo_tmp_*")], [])

            # 4) 16-thread concurrent writer stress (distinct targets + same target) & EEXIST/fstat guards
            mt_errors: list[str] = []
            mt_lock = threading.Lock()
            distinct_dir = td / "mt_distinct"
            distinct_dir.mkdir(mode=0o700)

            def _distinct_worker(tid: int) -> None:
                p = distinct_dir / f"worker_{tid}.json"
                for k in range(40):
                    data = f"T{tid}_K{k}\n".encode("ascii")
                    try:
                        audit.write_regular_file_bytes(p, data)
                    except Exception as exc:
                        with mt_lock:
                            mt_errors.append(f"distinct_t{tid}_k{k}:{type(exc).__name__}:{exc}")

            threads = [threading.Thread(target=_distinct_worker, args=(t,)) for t in range(16)]
            for th_w in threads:
                th_w.start()
            for th_w in threads:
                th_w.join(timeout=15)
            self.assertEqual(mt_errors, [])
            for tid in range(16):
                self.assertEqual((distinct_dir / f"worker_{tid}.json").read_bytes(), f"T{tid}_K39\n".encode("ascii"))
            self.assertEqual([p.name for p in distinct_dir.glob(".s33_leonardo_tmp_*")], [])

            same_dir = td / "mt_same"
            same_dir.mkdir(mode=0o700)
            shared_target = same_dir / "shared.json"
            valid_payloads = {f"SHARED_T{tid}_K{k}\n".encode("ascii") for tid in range(16) for k in range(40)}

            def _same_worker(tid: int) -> None:
                for k in range(40):
                    data = f"SHARED_T{tid}_K{k}\n".encode("ascii")
                    try:
                        audit.write_regular_file_bytes(shared_target, data)
                    except Exception as exc:
                        with mt_lock:
                            mt_errors.append(f"same_t{tid}_k{k}:{type(exc).__name__}:{exc}")

            threads = [threading.Thread(target=_same_worker, args=(t,)) for t in range(16)]
            for th_w in threads:
                th_w.start()
            for th_w in threads:
                th_w.join(timeout=15)
            self.assertEqual(mt_errors, [])
            self.assertIn(shared_target.read_bytes(), valid_payloads)
            self.assertEqual([p.name for p in same_dir.glob(".s33_leonardo_tmp_*")], [])

            # EEXIST retry succeeds on collision and fails cleanly on retry exhaustion
            orig_token = audit.secrets.token_hex
            orig_open = audit.os.open
            orig_fstat = audit.os.fstat
            try:
                calls = {"n": 0}
                def _collide_once(p_arg, flags, *a, **kw):
                    if isinstance(p_arg, str) and p_arg.startswith(".s33_leonardo_tmp_") and calls["n"] == 0:
                        calls["n"] += 1
                        raise FileExistsError("simulated collision")
                    return orig_open(p_arg, flags, *a, **kw)
                audit.os.open = _collide_once  # type: ignore[assignment]
                audit.write_regular_file_bytes(same_dir / "retry_ok.json", b"RETRY_OK\n")
                self.assertEqual((same_dir / "retry_ok.json").read_bytes(), b"RETRY_OK\n")

                def _always_collide(p_arg, flags, *a, **kw):
                    if isinstance(p_arg, str) and p_arg.startswith(".s33_leonardo_tmp_"):
                        raise FileExistsError("permanent collision")
                    return orig_open(p_arg, flags, *a, **kw)
                audit.os.open = _always_collide  # type: ignore[assignment]
                self._expect_err("TEMP_RETRY_EXHAUSTED", audit.write_regular_file_bytes, same_dir / "retry_fail.json", b"NO\n")

                audit.os.open = orig_open  # type: ignore[assignment]
                class _FakeStat:
                    st_nlink = 2
                audit.os.fstat = lambda _fd: _FakeStat()  # type: ignore[assignment]
                self._expect_err("HARDLINK_FORBIDDEN", audit.write_regular_file_bytes, same_dir / "tmp_hl.json", b"NO\n")
            finally:
                audit.secrets.token_hex = orig_token
                audit.os.open = orig_open
                audit.os.fstat = orig_fstat
            self.assertEqual([p.name for p in same_dir.glob(".s33_leonardo_tmp_*")], [])

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
        with tempfile.TemporaryDirectory(prefix="s33_cli_bad_") as tmp:
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

        with tempfile.TemporaryDirectory(prefix="s33_pwd_") as tmp:
            td = Path(tmp)
            real_dir = td / "real"
            real_dir.mkdir(mode=0o700)
            sym_dir = td / "sym"
            sym_dir.symlink_to(real_dir)
            (real_dir / "c.json").write_bytes(b"{}\n")
            proc = subprocess.run(
                [sys.executable, "-I", "-B", str(Path(_THIS_DIR) / "leonardo_codices_audit.py"), "--check", "c.json"],
                cwd=str(real_dir),
                env={"PATH": os.environ.get("PATH", ""), "PWD": str(sym_dir)},
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(proc.returncode, 2)
            self.assertEqual(json.loads(proc.stderr)["error_code"], "SYMLINK_FORBIDDEN")


class Test04PayloadAndSecondaryAuditTamperMatrix(unittest.TestCase):
    """Exhaustive tamper matrix killing every guard in validate_certificate_payload & secondary_algebraic_audit."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.valid_cert = oracle.build_standalone_certificate()

    def _expect_err(self, code: str, fn, *args, **kwargs) -> None:
        with self.assertRaises(oracle.LeonardoError) as ctx:
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

    def test_validate_certificate_payload_tampers(self) -> None:
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
        self._expect_err("INVALID_PAYLOAD_KEYS", oracle.validate_certificate_payload, hollow, full_replay=False)

        for field, bad_val, exp_code in [
            ("oracle_class", "approx", "INVALID_PAYLOAD_META"),
            ("novelty_classification", "N2", "INVALID_PAYLOAD_META"),
            ("zero_floats_exact_arithmetic", False, "INVALID_PAYLOAD_META"),
            ("all_verified", False, "INVALID_PAYLOAD_META"),
            ("pillar1_arundel_motion", [], "INVALID_PILLAR_TYPE"),
        ]:
            t_meta = copy.deepcopy(self.valid_cert)
            t_meta["payload"][field] = bad_val
            t_meta = self._resign(t_meta)
            self._expect_err(exp_code, oracle.validate_certificate_payload, t_meta, full_replay=False)

        unver = copy.deepcopy(self.valid_cert)
        unver["payload"]["pillar1_arundel_motion"]["pillar_verified"] = False
        unver = self._resign(unver)
        self._expect_err("PILLAR_NOT_VERIFIED", oracle.validate_certificate_payload, unver, full_replay=False)

        bool_int = copy.deepcopy(self.valid_cert)
        bool_int["payload"]["pillar2_leicester_bubble"]["hopf_bifurcation_4d"]["subcritical_straight_rise"]["hermite_inertia"]["n_neg"] = False
        bool_int = self._resign(bool_int)
        self._expect_err("BOOL_IN_NON_BOOL_FIELD", oracle.validate_certificate_payload, bool_int, full_replay=False)

        bool_list = copy.deepcopy(self.valid_cert)
        bool_list["payload"]["pillar5_lunes_aerial_screw_myth"]["squarable_lunes_5"][0]["ratio_m_n"][1] = True
        bool_list = self._resign(bool_list)
        self._expect_err("BOOL_IN_LIST", oracle.validate_certificate_payload, bool_list, full_replay=False)

        bool_nested = copy.deepcopy(self.valid_cert)
        bool_nested["payload"]["pillar1_arundel_motion"]["discrete_galileo_continuous_k2"][0]["N"] = True
        bool_nested = self._resign(bool_nested)
        self._expect_err("BOOL_IN_NON_BOOL_FIELD", oracle.validate_certificate_payload, bool_nested, full_replay=False)

        # Structurally valid re-signed payload with altered witness value hits RECOMPUTATION_MISMATCH on full_replay=True
        altered = copy.deepcopy(self.valid_cert)
        altered["payload"]["pillar1_arundel_motion"]["four_interval_diagnostics"]["centered_r2"] = "1/2"
        altered = self._resign(altered)
        self.assertTrue(oracle.validate_certificate_payload(altered, full_replay=False)["valid"])
        self._expect_err("RECOMPUTATION_MISMATCH", oracle.validate_certificate_payload, altered, full_replay=True)

    def test_secondary_algebraic_audit_tamper_matrix(self) -> None:
        base_p = self.valid_cert["payload"]
        sec = audit.secondary_algebraic_audit(base_p)
        self.assertTrue(sec["secondary_audit_passed"])
        self.assertEqual(sec["pillars_checked"], 5)

        self._expect_err("AUDIT_PAYLOAD_TYPE", audit.secondary_algebraic_audit, [])
        self._expect_err("AUDIT_SCHEMA_ERROR", audit.secondary_algebraic_audit, {"all_verified": True})
        self._expect_err("AUDIT_SCHEMA_ERROR", audit.secondary_algebraic_audit, {"all_verified": True, "pillar1_arundel_motion": None})
        self._expect_err(
            "AUDIT_SCHEMA_ERROR",
            audit.secondary_algebraic_audit,
            {"all_verified": True, "pillar1_arundel_motion": {"pitcher_snapshot_45deg": []}},
        )

        def _tamper(code: str, mutator) -> None:
            p = copy.deepcopy(base_p)
            mutator(p)
            self._expect_err(code, audit.secondary_algebraic_audit, p)

        _tamper("AUDIT_ALL_VERIFIED_FALSE", lambda p: p.__setitem__("all_verified", False))

        # Pillar 1 tampers
        _tamper("AUDIT_P1_45DEG", lambda p: p["pillar1_arundel_motion"]["pitcher_snapshot_45deg"].__setitem__("is_45_degree_equatione_di_moti", False))
        _tamper("AUDIT_P1_CUBIC", lambda p: p["pillar1_arundel_motion"]["must_fail_cubic_jerk"].__setitem__("is_straight_hypotenuse", True))
        _tamper("AUDIT_P1_GALILEO", lambda p: p["pillar1_arundel_motion"]["discrete_galileo_continuous_k2"][0].__setitem__("all_determinants_zero", False))
        _tamper("AUDIT_P1_GALILEO", lambda p: p["pillar1_arundel_motion"].__setitem__("discrete_galileo_continuous_k2", []))
        _tamper("INVALID_INT", lambda p: p["pillar1_arundel_motion"]["discrete_galileo_continuous_k2"][0].__setitem__("N", True))
        _tamper("AUDIT_P1_BWD_GALILEO", lambda p: p["pillar1_arundel_motion"]["uniform_backward_difference"]["galileo_k2"][0].__setitem__("first_det", "3"))
        _tamper("AUDIT_P1_BWD_GALILEO", lambda p: p["pillar1_arundel_motion"]["uniform_backward_difference"]["galileo_k2"][0].__setitem__("N", 99))
        _tamper("AUDIT_P1_BWD_LEONARDO", lambda p: p["pillar1_arundel_motion"]["uniform_backward_difference"]["leonardo_2k"][0].__setitem__("first_det", "5"))
        _tamper("AUDIT_P1_BWD_LEONARDO", lambda p: p["pillar1_arundel_motion"]["uniform_backward_difference"]["leonardo_2k"][0].__setitem__("N", 99))
        _tamper("AUDIT_P1_FWD_GALILEO", lambda p: p["pillar1_arundel_motion"]["uniform_forward_difference"]["galileo_k2"][0].__setitem__("first_det", "-3"))
        _tamper("AUDIT_P1_FWD_GALILEO", lambda p: p["pillar1_arundel_motion"]["uniform_forward_difference"]["galileo_k2"][0].__setitem__("N", 99))
        _tamper("AUDIT_P1_FWD_LEONARDO", lambda p: p["pillar1_arundel_motion"]["uniform_forward_difference"]["leonardo_2k"][0].__setitem__("first_det", "-3"))
        _tamper("AUDIT_P1_FWD_LEONARDO", lambda p: p["pillar1_arundel_motion"]["uniform_forward_difference"]["leonardo_2k"][0].__setitem__("N", 99))

        # Pillar 2 tampers
        _tamper("AUDIT_P2_VACUUM_L7", lambda p: p["pillar2_leicester_bubble"].__setitem__("vacuum_resonance_modes", [5]))
        _tamper("INVALID_INT", lambda p: p["pillar2_leicester_bubble"].__setitem__("vacuum_resonance_modes", [True]))
        _tamper("AUDIT_P2_SIGMA_ZERO", lambda p: p["pillar2_leicester_bubble"].__setitem__("sigma_zero_collapse_all_zero", False))
        _tamper("AUDIT_P2_RESONANCE_LEN", lambda p: p["pillar2_leicester_bubble"]["positive_rational_resonances_l3_to_l10"].pop())
        _tamper("AUDIT_P2_RESONANCE_DUP", lambda p: p["pillar2_leicester_bubble"]["positive_rational_resonances_l3_to_l10"].__setitem__(1, copy.deepcopy(p["pillar2_leicester_bubble"]["positive_rational_resonances_l3_to_l10"][0])))
        _tamper("INVALID_INT", lambda p: p["pillar2_leicester_bubble"]["positive_rational_resonances_l3_to_l10"][0].__setitem__("l", True))
        _tamper("AUDIT_P2_TAU_NONPOS", lambda p: p["pillar2_leicester_bubble"]["positive_rational_resonances_l3_to_l10"][0].__setitem__("tau_lk", "0"))
        _tamper("AUDIT_P2_RESONANCE_EQ", lambda p: p["pillar2_leicester_bubble"]["positive_rational_resonances_l3_to_l10"][0].__setitem__("omega_l_sq", "71"))
        _tamper("AUDIT_P2_HOPF_SUB", lambda p: p["pillar2_leicester_bubble"]["hopf_bifurcation_4d"]["subcritical_straight_rise"].__setitem__("hurwitz_d3", "0"))
        _tamper("AUDIT_P2_HOPF_CRIT", lambda p: p["pillar2_leicester_bubble"]["hopf_bifurcation_4d"]["critical_hopf_threshold"].__setitem__("hurwitz_d3", "1"))
        _tamper("AUDIT_P2_HOPF_SUP", lambda p: p["pillar2_leicester_bubble"]["hopf_bifurcation_4d"]["supercritical_oscillatory"].__setitem__("hurwitz_d3", "0"))
        _tamper("AUDIT_P2_HOPF_INERTIA", lambda p: p["pillar2_leicester_bubble"]["hopf_bifurcation_4d"]["subcritical_straight_rise"]["hermite_inertia"].__setitem__("n_pos", 3))
        _tamper("INVALID_INT", lambda p: p["pillar2_leicester_bubble"]["hopf_bifurcation_4d"]["subcritical_straight_rise"]["hermite_inertia"].__setitem__("n_neg", False))

        # Pillar 3 tampers
        _tamper("AUDIT_P3_DESCARTES", lambda p: p["pillar3_atlanticus_bridge_domes"]["da_vinci_domes_descartes_obstruction"][0].__setitem__("descartes_defect_half_turns", "1/2"))
        _tamper("AUDIT_P3_DESCARTES", lambda p: p["pillar3_atlanticus_bridge_domes"].__setitem__("da_vinci_domes_descartes_obstruction", []))
        _tamper("INVALID_INT", lambda p: p["pillar3_atlanticus_bridge_domes"]["da_vinci_domes_descartes_obstruction"][0].__setitem__("degree", True))
        _tamper("AUDIT_P3_TORUS_LEN", lambda p: p["pillar3_atlanticus_bridge_domes"]["euler_torus_tilings_11"].pop())
        _tamper("AUDIT_P3_TORUS_CHI", lambda p: p["pillar3_atlanticus_bridge_domes"]["euler_torus_tilings_11"][0].__setitem__("F", 2))
        _tamper("AUDIT_P3_TORUS_CHI", lambda p: p["pillar3_atlanticus_bridge_domes"]["euler_torus_tilings_11"][0].__setitem__("chi", 1))
        _tamper("INVALID_INT", lambda p: p["pillar3_atlanticus_bridge_domes"]["euler_torus_tilings_11"][0].__setitem__("V", True))
        _tamper("AUDIT_P3_SPHERE_CHI", lambda p: p["pillar3_atlanticus_bridge_domes"]["euler_sphere_cages"][0].__setitem__("F", 5))
        _tamper("AUDIT_P3_SPHERE_CHI", lambda p: p["pillar3_atlanticus_bridge_domes"]["euler_sphere_cages"][0].__setitem__("chi", 0))
        _tamper("AUDIT_P3_SPHERE_CHI", lambda p: p["pillar3_atlanticus_bridge_domes"].__setitem__("euler_sphere_cages", []))
        _tamper("INVALID_INT", lambda p: p["pillar3_atlanticus_bridge_domes"]["euler_sphere_cages"][0].__setitem__("V", True))
        _tamper("AUDIT_P3_BRIDGE_MU", lambda p: p["pillar3_atlanticus_bridge_domes"]["reciprocal_bridge_equilibrium_threshold"].__setitem__("mu_min", "1/2"))
        _tamper("AUDIT_P3_BRIDGE_EQ", lambda p: p["pillar3_atlanticus_bridge_domes"]["reciprocal_bridge_equilibrium_threshold"].__setitem__("equilibrium_residual_zero", False))
        _tamper("AUDIT_P3_FARKAS_MU", lambda p: p["pillar3_atlanticus_bridge_domes"]["reciprocal_bridge_farkas_collapse_low_mu"].__setitem__("farkas_vTg_strictly_negative", False))
        _tamper("AUDIT_P3_BEAM_DEL", lambda p: p["pillar3_atlanticus_bridge_domes"]["reciprocal_bridge_central_beam_removal"].__setitem__("catastrophic_collapse_certified", False))

        # Pillar 4 tampers
        _tamper("AUDIT_P4_EXPONENTS", lambda p: p["pillar4_trattato_branching_trees"]["variational_exponents"].__setitem__("turbulent_p5_q2_m3", "5/2"))
        _tamper("AUDIT_P4_DOMINANCE", lambda p: p["pillar4_trattato_branching_trees"]["symmetric_split_poiseuille_dominance"].__setitem__("C_murray_cubed", "64"))
        _tamper("AUDIT_P4_SCHUR_GAIN", lambda p: p["pillar4_trattato_branching_trees"]["kirchhoff_schur_4level_vascular"].__setitem__("conductance_gain_ratio", "3"))
        _tamper("AUDIT_P4_SCHUR_GAIN", lambda p: p["pillar4_trattato_branching_trees"]["kirchhoff_schur_4level_vascular"]["naive_alpha2_uniform_pipe"].__setitem__("n_levels", 3))
        _tamper("INVALID_INT", lambda p: p["pillar4_trattato_branching_trees"]["kirchhoff_schur_4level_vascular"]["naive_alpha2_uniform_pipe"].__setitem__("n_levels", True))

        # Pillar 5 tampers
        _tamper("AUDIT_P5_LUNES_LEN", lambda p: p["pillar5_lunes_aerial_screw_myth"]["squarable_lunes_5"].pop())
        _tamper("AUDIT_P5_LUNES_CONSTRUCT", lambda p: p["pillar5_lunes_aerial_screw_myth"]["squarable_lunes_5"][0].__setitem__("ruler_compass_constructible", False))
        _tamper("AUDIT_P5_LUNES_CONSTRUCT", lambda p: p["pillar5_lunes_aerial_screw_myth"]["squarable_lunes_5"][0].__setitem__("deg_in_y", 0))
        _tamper("AUDIT_P5_LUNES_CONSTRUCT", lambda p: p["pillar5_lunes_aerial_screw_myth"]["squarable_lunes_5"][0].__setitem__("ratio_m_n", [1, 1]))
        _tamper("INVALID_INT", lambda p: p["pillar5_lunes_aerial_screw_myth"]["squarable_lunes_5"][0].__setitem__("deg_in_y", True))
        _tamper("AUDIT_P5_HIPP_PI", lambda p: p["pillar5_lunes_aerial_screw_myth"]["zero_pi_dissections"]["hippocrates_2_1_lune"].__setitem__("pi_coeff", "1"))
        _tamper("AUDIT_P5_ROSETTE_PI", lambda p: p["pillar5_lunes_aerial_screw_myth"]["zero_pi_dissections"]["leonardo_atlanticus_4_lunes"].__setitem__("pi_coeff", "1"))
        _tamper("AUDIT_P5_GALOIS_41", lambda p: p["pillar5_lunes_aerial_screw_myth"]["galois_obstruction_4_1"].__setitem__("ruler_compass_impossible", False))
        _tamper("AUDIT_P5_GALOIS_41", lambda p: p["pillar5_lunes_aerial_screw_myth"]["galois_obstruction_4_1"].__setitem__("degree", 2))
        _tamper("AUDIT_P5_GALOIS_71", lambda p: p["pillar5_lunes_aerial_screw_myth"]["galois_obstruction_7_1"].__setitem__("ruler_compass_impossible", False))
        _tamper("AUDIT_P5_GALOIS_71", lambda p: p["pillar5_lunes_aerial_screw_myth"]["galois_obstruction_7_1"].__setitem__("degree", 4))
        _tamper("AUDIT_P5_SCREW", lambda p: p["pillar5_lunes_aerial_screw_myth"]["aerial_screw_isolift_2506_10223"].__setitem__("jhu_power_drop_in_42_to_43_pct_band", False))
        _tamper("AUDIT_P5_MYTH", lambda p: p["pillar5_lunes_aerial_screw_myth"]["cs13_myth_audit"].__setitem__("attributed_to_leonardo_in_authentic_codices", True))

    def test_file_level_canonical_byte_guards(self) -> None:
        raw = oracle.canonical_json_bytes(self.valid_cert) + b"\n"
        with tempfile.TemporaryDirectory(prefix="s33_cert_") as tmp:
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


class Test99EndToEndPillarsAndCLI(unittest.TestCase):
    """End-to-end verification of all 5 pillars and CLI roundtrip."""

    def test_all_five_pillars_and_cli_roundtrip(self) -> None:
        cert = oracle.build_standalone_certificate()
        p = cert["payload"]
        self.assertTrue(p["all_verified"])
        self.assertEqual(p["oracle_class"], "exact")
        self.assertEqual(p["novelty_classification"], "N1")

        # Pillar 1
        p1 = p["pillar1_arundel_motion"]
        self.assertTrue(p1["pillar_verified"])
        self.assertEqual(p1["four_interval_diagnostics"]["centered_r2"], "8000/8091")
        self.assertEqual([r["first_det"] for r in p1["discrete_galileo_continuous_k2"]], ["0", "0", "0", "0"])
        self.assertEqual([r["first_det"] for r in p1["uniform_backward_difference"]["galileo_k2"]], ["2", "2", "2", "2"])
        self.assertEqual([r["first_det"] for r in p1["uniform_backward_difference"]["leonardo_2k"]], ["4", "8", "16", "32"])
        self.assertEqual([r["first_det"] for r in p1["uniform_forward_difference"]["galileo_k2"]], ["-2", "-2", "-2", "-2"])
        self.assertEqual([r["first_det"] for r in p1["uniform_forward_difference"]["leonardo_2k"]], ["-2", "-4", "-8", "-16"])

        # Pillar 2
        p2 = p["pillar2_leicester_bubble"]
        self.assertTrue(p2["pillar_verified"])
        self.assertEqual(p2["vacuum_resonance_modes"], [7])
        self.assertEqual([r["tau_lk"] for r in p2["positive_rational_resonances_l3_to_l10"]], ["10/9", "2/7", "46/27", "23/60", "2/77", "10/7"])

        # Pillar 3
        p3 = p["pillar3_atlanticus_bridge_domes"]
        self.assertTrue(p3["pillar_verified"])
        self.assertEqual(p3["reciprocal_bridge_equilibrium_threshold"]["mu_min"], "1/3")
        self.assertEqual(p3["reciprocal_bridge_farkas_collapse_low_mu"]["farkas_vTg"], "-2")
        self.assertEqual(p3["reciprocal_bridge_farkas_collapse_zero_mu"]["farkas_vTg"], "-8")

        # Pillar 4
        p4 = p["pillar4_trattato_branching_trees"]
        self.assertTrue(p4["pillar_verified"])
        self.assertEqual(p4["symmetric_split_poiseuille_dominance"]["exact_cubic_gap"], "10")
        self.assertEqual(p4["kirchhoff_schur_4level_vascular"]["conductance_gain_ratio"], "15/4")

        # Pillar 5
        p5 = p["pillar5_lunes_aerial_screw_myth"]
        self.assertTrue(p5["pillar_verified"])
        self.assertEqual(p5["squarable_lunes_5"][3]["ferrari_resolvent_rational_root"], "1/8")
        self.assertEqual(p5["squarable_lunes_5"][4]["ferrari_resolvent_rational_root"], "1/8")
        self.assertEqual(p5["galois_obstruction_4_1"]["poly_in_x_asc"], [-1, -2, 0, 4])
        self.assertEqual(p5["galois_obstruction_7_1"]["poly_in_4x2_asc"], [-6, -12, 46, -62, 37, -10, 1])

        # CLI roundtrip (default, --standalone, --write, --check, and '=' syntax)
        with tempfile.TemporaryDirectory(prefix="s33_cli_") as tmp:
            cp1 = Path(tmp) / "c1.json"
            cp2 = Path(tmp) / "c2.json"
            for argv, check_fn in [
                ([], lambda out: self.assertIn("OK " + oracle.SCHEMA_VERSION, out)),
                (["--standalone", "--json"], lambda out: self.assertEqual(json.loads(out)["payload_sha256"], cert["payload_sha256"])),
                (["--write", str(cp1), "--json"], lambda out: self.assertTrue(json.loads(out)["written"])),
                (["--check", str(cp1), "--json"], lambda out: self.assertTrue(json.loads(out)["valid"])),
                ([f"--write={cp2}", "--json"], lambda out: self.assertTrue(json.loads(out)["written"])),
                ([f"--check={cp2}", "--json"], lambda out: self.assertTrue(json.loads(out)["valid"])),
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
