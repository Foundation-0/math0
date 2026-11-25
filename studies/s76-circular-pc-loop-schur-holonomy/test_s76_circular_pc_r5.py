#!/usr/bin/env python3
"""Aletheia R5 Adversarial, Zone-B, Lean-Gate & Mutation-Killer Test Suite for Track S76.

100% pure Python 3 stdlib, zero bare asserts, zero AST floats, zero .isdigit(),
zero random imports, CI chmod-644 compatible.
"""
from __future__ import annotations

import ast
import copy
import errno
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
import unittest
from unittest import mock

_THIS_DIR = Path(__file__).resolve().parent
if str(_THIS_DIR) not in sys.path:
    sys.path.insert(0, str(_THIS_DIR))

import s76_circular_pc_tomography as oracle  # noqa: E402
import verify_s76_circular_pc as verifier  # noqa: E402


class _IntSub(int):
    pass


class _StrSub(str):
    pass


class _ListSub(list):
    pass


class _DictSub(dict):
    pass


class _PathSub(type(Path())):
    pass


def _resign_cert(cert: dict) -> dict:
    c = copy.deepcopy(cert)
    p_sha = oracle.sha256_hex(oracle.canonical_json_bytes(c["payload"]))
    c["payload_sha256"] = p_sha
    env = {
        "schema_version": c["schema_version"],
        "track_id": c["track_id"],
        "payload_sha256": p_sha,
        "payload": c["payload"],
    }
    c["certificate_sha256"] = oracle.sha256_hex(oracle.canonical_json_bytes(env))
    return c


class Test01StaticHygiene(unittest.TestCase):
    def test_ast_and_text_hygiene(self) -> None:
        trust_files = (
            "s76_circular_pc_tomography.py",
            "verify_s76_circular_pc.py",
            "test_s76_circular_pc_r5.py",
        )
        for fname in trust_files:
            raw = (_THIS_DIR / fname).read_bytes()
            self.assertNotIn(b"\r", raw, fname)
            src = raw.decode("utf-8", "strict")
            self.assertNotIn("/" + "home/", src, fname)
            self.assertNotIn("/dev/" + "null", src, fname)
            tree = ast.parse(src, filename=fname)
            for node in ast.walk(tree):
                self.assertNotIsInstance(node, ast.Assert, fname)
                if isinstance(node, ast.Constant):
                    self.assertNotIsInstance(node.value, float, fname)
                if isinstance(node, ast.Call):
                    if isinstance(node.func, ast.Name):
                        self.assertNotIn(node.func.id, ("float", "eval", "exec"), fname)
                    if isinstance(node.func, ast.Attribute):
                        self.assertNotEqual(node.func.attr, "isdigit", fname)
                if isinstance(node, ast.Import):
                    for alias in node.names:
                        self.assertNotEqual(alias.name, "random", fname)
                if isinstance(node, ast.ImportFrom):
                    self.assertNotEqual(node.module, "random", fname)

        cap_src = (_THIS_DIR / "s76_live_anchor_capture.py").read_text(encoding="utf-8")
        self.assertNotIn("/" + "home/", cap_src)
        self.assertNotIn("/dev/" + "null", cap_src)
        for node in ast.walk(ast.parse(cap_src)):
            self.assertNotIsInstance(node, ast.Assert)

    def test_disk_json_artifacts_strict_zero_float_canonical(self) -> None:
        for fname in ("s76_circularep_live_anchor.json", "s76_circular_pc_certificate.json"):
            raw = verifier.read_regular_bytes_capped(_THIS_DIR / fname, fname)
            obj = verifier.parse_strict_json_bytes(raw, fname, require_canonical=True)
            self.assertIs(type(obj), dict)


class Test02OraclePrimitivesAndAlgebra(unittest.TestCase):
    def _assert_s76(self, code: str, fn, *args, **kwargs) -> None:
        with self.assertRaises(oracle.S76Error) as ctx:
            fn(*args, **kwargs)
        self.assertEqual(ctx.exception.code, code)

    def test_type_and_hex_guards(self) -> None:
        self.assertIs(oracle.require_bool(True, "b"), True)
        self.assertIs(oracle.require_bool(False, "b"), False)
        for bad in (0, 1, "true", None):
            self._assert_s76("INVALID_BOOL", oracle.require_bool, bad, "b")

        self.assertEqual(oracle.require_exact_int(5, "x", lo=5, hi=5), 5)
        self._assert_s76("INVALID_INT", oracle.require_exact_int, True, "x")
        self._assert_s76("INVALID_INT", oracle.require_exact_int, _IntSub(5), "x")
        self._assert_s76("INT_OUT_OF_RANGE", oracle.require_exact_int, 4, "x", lo=5)
        self._assert_s76("INT_OUT_OF_RANGE", oracle.require_exact_int, 6, "x", hi=5)
        big_ok = (1 << oracle.MAX_INT_BITS) - 1
        self.assertEqual(oracle.require_exact_int(big_ok, "x"), big_ok)
        self._assert_s76("INT_TOO_LARGE", oracle.require_exact_int, 1 << oracle.MAX_INT_BITS, "x")

        self.assertEqual(oracle.require_exact_str("abc", "s"), "abc")
        self._assert_s76("INVALID_STR", oracle.require_exact_str, _StrSub("a"), "s")
        self._assert_s76("INVALID_UTF8_SURROGATE", oracle.require_exact_str, "\ud800", "s")

        h64 = "0123456789abcdef" * 4
        self.assertEqual(oracle.require_hex64(h64, "h"), h64)
        self._assert_s76("INVALID_HEX", oracle.require_hex64, h64[:-1], "h")
        self._assert_s76("INVALID_HEX", oracle.require_hex64, "A" + h64[1:], "h")
        self._assert_s76("INVALID_HEX", oracle.require_hex_len, "g" * 40, 40, "h")

        self.assertTrue(oracle.is_ascii_digits("0123456789"))
        self.assertFalse(oracle.is_ascii_digits(""))
        self.assertFalse(oracle.is_ascii_digits("12a"))
        self.assertFalse(oracle.is_ascii_digits("\u00b2"))

    def test_validate_strict_json_tree_edges(self) -> None:
        shared = [1, 2]
        oracle.validate_strict_json_tree({"a": shared, "b": shared, "n": None, "t": True, "s": "ok"})

        # Exact max_depth passes (depth == MAX_JSON_DEPTH); max_depth + 1 fails
        nested: list = []
        cur = nested
        for _ in range(oracle.MAX_JSON_DEPTH):
            nxt: list = []
            cur.append(nxt)
            cur = nxt
        oracle.validate_strict_json_tree(nested)
        cur.append(0)
        self._assert_s76("JSON_DEPTH_EXCEEDED", oracle.validate_strict_json_tree, nested)

        # Exact MAX_INT_BITS passes inside tree; MAX_INT_BITS + 1 fails
        oracle.validate_strict_json_tree((1 << oracle.MAX_INT_BITS) - 1)

        # Cycles
        cyc_l: list = []
        cyc_l.append(cyc_l)
        self._assert_s76("JSON_CYCLE", oracle.validate_strict_json_tree, cyc_l)
        cyc_d: dict = {}
        cyc_d["self"] = cyc_d
        self._assert_s76("JSON_CYCLE", oracle.validate_strict_json_tree, cyc_d)

        # Bad types, subclasses, oversized int, surrogate key/value
        self._assert_s76("INT_TOO_LARGE", oracle.validate_strict_json_tree, 1 << oracle.MAX_INT_BITS)
        self._assert_s76("INVALID_UTF8_SURROGATE", oracle.validate_strict_json_tree, {"k": "\ud800"})
        self._assert_s76("INVALID_UTF8_SURROGATE", oracle.validate_strict_json_tree, {"\ud800": 1})
        self._assert_s76("INVALID_STR", oracle.validate_strict_json_tree, {1: "a"})
        for bad in ((1, 2), b"abc", _IntSub(1), _StrSub("a"), _ListSub([1]), _DictSub({"a": 1})):
            self._assert_s76("INVALID_JSON_TYPE", oracle.validate_strict_json_tree, bad)

    def test_q_str_dec_and_decimal_parser(self) -> None:
        self.assertEqual(oracle.q_str(Fraction(4, 1)), "4")
        self.assertEqual(oracle.q_str(Fraction(-3, 2)), "-3/2")
        self.assertEqual(oracle.dec_from_q(Fraction(1, 200), 2), "0.01")
        self.assertEqual(oracle.dec_from_q(Fraction(1, 300), 2), "0.00")
        self.assertEqual(oracle.dec_from_q(Fraction(-1, 1000), 2), "0.00")
        self.assertEqual(oracle.dec_from_q(Fraction(-3, 200), 2), "-0.02")
        self.assertEqual(oracle.dec_from_q(Fraction(5, 2), 0), "3")
        self.assertEqual(oracle.dec_from_q(Fraction(-5, 2), 0), "-3")
        self.assertEqual(oracle.dec_from_q(Fraction(0, 1), 0), "0")

        self.assertEqual(oracle.parse_decimal_or_sci_to_q("1.25", "x"), Fraction(5, 4))
        self.assertEqual(oracle.parse_decimal_or_sci_to_q("+1.25", "x"), Fraction(5, 4))
        self.assertEqual(oracle.parse_decimal_or_sci_to_q("-1.25", "x"), Fraction(-5, 4))
        self.assertEqual(oracle.parse_decimal_or_sci_to_q("42", "x"), Fraction(42, 1))
        self.assertEqual(oracle.parse_decimal_or_sci_to_q("1.5e-2", "x"), Fraction(3, 200))
        self.assertEqual(oracle.parse_decimal_or_sci_to_q("1.5E+2", "x"), Fraction(150, 1))
        self.assertEqual(oracle.parse_decimal_or_sci_to_q("2e200", "x"), Fraction(2 * (10 ** 200), 1))
        self.assertEqual(oracle.parse_decimal_or_sci_to_q("2e-200", "x"), Fraction(2, 10 ** 200))
        for bad in ("", " 1.0", "1.0 ", "1e2e3", "1e", "1e00001", "1e201", "1e-201", "1.2.3", ".5", "5.", "abc"):
            self._assert_s76("INVALID_DECIMAL", oracle.parse_decimal_or_sci_to_q, bad, "x")

    def test_exact_q_linear_algebra_and_inertia(self) -> None:
        # q_det with pivot swap and singular case
        swap_m = [[Fraction(0), Fraction(2)], [Fraction(3), Fraction(1)]]
        self.assertEqual(oracle.q_det(swap_m), Fraction(-6))
        sing_m = [[Fraction(1), Fraction(2)], [Fraction(2), Fraction(4)]]
        self.assertEqual(oracle.q_det(sing_m), Fraction(0))

        # q_solve with pivot swap and singular rejection
        sol = oracle.q_solve(swap_m, [[Fraction(4)], [Fraction(5)]])
        self.assertEqual(sol, [[Fraction(1)], [Fraction(2)]])
        self._assert_s76("SINGULAR_MATRIX", oracle.q_solve, sing_m, [[Fraction(1)], [Fraction(2)]])

        # q_sylvester_inertia: diag swap, negative diag, 2x2 off-diag with pi!=k & pj!=k+1 + Schur update, all-zero
        diag_swap = [
            [Fraction(0), Fraction(0), Fraction(0)],
            [Fraction(0), Fraction(3), Fraction(0)],
            [Fraction(0), Fraction(0), Fraction(-2)],
        ]
        self.assertEqual(oracle.q_sylvester_inertia(diag_swap), [1, 1, 1])

        # 4x4: row/col 0 all zero -> triggers pi != k (pi=1), pj != k+1 (pj=3), and Schur update on remaining rows
        off_4 = [
            [Fraction(0), Fraction(0), Fraction(0), Fraction(0)],
            [Fraction(0), Fraction(0), Fraction(0), Fraction(2)],
            [Fraction(0), Fraction(0), Fraction(0), Fraction(1)],
            [Fraction(0), Fraction(2), Fraction(1), Fraction(0)],
        ]
        self.assertEqual(oracle.q_sylvester_inertia(off_4), [1, 1, 2])
        # 4x4 full-rank 2x2 off-diagonal with nontrivial Schur update:
        # [[0,0,1,2],[0,0,2,1],[1,2,0,0],[2,1,0,0]] -> det = (1-4)^2 = 9, inertia [2,2,0]
        off_full = [
            [Fraction(0), Fraction(0), Fraction(1), Fraction(2)],
            [Fraction(0), Fraction(0), Fraction(2), Fraction(1)],
            [Fraction(1), Fraction(2), Fraction(0), Fraction(0)],
            [Fraction(2), Fraction(1), Fraction(0), Fraction(0)],
        ]
        self.assertEqual(oracle.q_sylvester_inertia(off_full), [2, 2, 0])
        self.assertEqual(oracle.q_sylvester_inertia(oracle.q_zeros(3, 3)), [0, 0, 3])

    def test_pillar_helper_boolops(self) -> None:
        self.assertTrue(oracle.check_ep_bias_row_match(Fraction(1, 2), Fraction(1, 2), Fraction(0)))
        self.assertFalse(oracle.check_ep_bias_row_match(Fraction(1, 3), Fraction(1, 2), Fraction(0)))
        self.assertFalse(oracle.check_ep_bias_row_match(Fraction(1, 2), Fraction(1, 2), Fraction(1)))

        self.assertTrue(oracle.check_non_normal_overshoot(Fraction(2), Fraction(2), Fraction(2), Fraction(1, 2)))
        self.assertFalse(oracle.check_non_normal_overshoot(Fraction(1), Fraction(2), Fraction(2), Fraction(1, 2)))
        self.assertFalse(oracle.check_non_normal_overshoot(Fraction(2), Fraction(1), Fraction(2), Fraction(1, 2)))
        self.assertFalse(oracle.check_non_normal_overshoot(Fraction(2), Fraction(2), Fraction(1), Fraction(1, 2)))
        self.assertFalse(oracle.check_non_normal_overshoot(Fraction(2), Fraction(2), Fraction(2), Fraction(1)))

        self.assertTrue(oracle.check_curl_oscillation_bracket(Fraction(1, 4), Fraction(3, 4), Fraction(2), Fraction(-1)))
        self.assertFalse(oracle.check_curl_oscillation_bracket(Fraction(3, 4), Fraction(3, 4), Fraction(2), Fraction(-1)))
        self.assertFalse(oracle.check_curl_oscillation_bracket(Fraction(1, 4), Fraction(2), Fraction(2), Fraction(-1)))
        self.assertFalse(oracle.check_curl_oscillation_bracket(Fraction(1, 4), Fraction(3, 4), Fraction(2), Fraction(0)))

    def test_pillar4_anchor_tamper_kills(self) -> None:
        raw = verifier.read_regular_bytes_capped(_THIS_DIR / "s76_circularep_live_anchor.json", "anchor")
        base = verifier.parse_strict_json_bytes(raw, "anchor", require_canonical=True)
        out = oracle.certify_pillar4_live_anchor(base)
        self.assertEqual(out["shipped_solved_count"], 269)
        self.assertEqual(out["complex_dominant_count"], 39)

        self._assert_s76("INVALID_ANCHOR", oracle.certify_pillar4_live_anchor, [])

        def mutate_and_expect(code: str, fn) -> None:
            bad = copy.deepcopy(base)
            fn(bad)
            self._assert_s76(code, oracle.certify_pillar4_live_anchor, bad)

        mutate_and_expect("INVALID_ANCHOR_SCHEMA", lambda d: d.__setitem__("schema_version", "bad"))
        mutate_and_expect("INVALID_ANCHOR_SCHEMA", lambda d: d.__setitem__("track_id", "bad"))
        mutate_and_expect("INVALID_ANCHOR", lambda d: d["upstream"].__setitem__("repo", "other"))
        mutate_and_expect("INVALID_ANCHOR", lambda d: d["upstream"].__setitem__("arxiv_id", "0000.00000"))
        mutate_and_expect("PARITY_MISMATCH", lambda d: d["float32_parity"]["parity"].__setitem__("iters", 43))
        mutate_and_expect("PARITY_MISMATCH", lambda d: d["float32_parity"]["parity"].__setitem__("max_abs_du_free_sci", "1.0e-05"))
        mutate_and_expect("PARITY_MISMATCH", lambda d: d["float32_parity"]["parity"].__setitem__("max_ep_grad_norm_err_sci", "1.0e-04"))
        mutate_and_expect("COUNT_MISMATCH", lambda d: d["tomography_300_puzzles"].__setitem__("stalled_count", 1))
        mutate_and_expect("PARITY_MISMATCH", lambda d: d["tomography_300_puzzles"].__setitem__("ref_solved_count", 268))
        mutate_and_expect("PARITY_MISMATCH", lambda d: d["tomography_300_puzzles"].__setitem__("ref_converged_wrong_count", 30))
        mutate_and_expect("PARITY_MISMATCH", lambda d: d["tomography_300_puzzles"]["rho_first_128_test"].__setitem__("median_dec6", "0.200000"))
        mutate_and_expect("COUNT_MISMATCH", lambda d: d["tomography_300_puzzles"]["equilibrium_spectra"].__setitem__("real_dominant_count", 260))
        mutate_and_expect("SPECTRAL_BOUND_FAIL", lambda d: d["tomography_300_puzzles"]["equilibrium_spectra"].__setitem__("rho_max_dec6", "1.000000"))
        mutate_and_expect("SPECTRAL_BOUND_FAIL", lambda d: d["tomography_300_puzzles"]["equilibrium_spectra"].__setitem__("norm2_max_dec6", "1.000000"))
        mutate_and_expect("SPECTRAL_BOUND_FAIL", lambda d: d["tomography_300_puzzles"]["equilibrium_spectra"].__setitem__("non_normality_median_dec6", "2.000000"))
        mutate_and_expect("SCHUR_ANCHOR_FAIL", lambda d: d["tomography_300_puzzles"]["loop_schur_and_hessian_512x512"].__setitem__("max_schur_identity_abs_err_sci", "1.0e-12"))
        mutate_and_expect("SCHUR_ANCHOR_FAIL", lambda d: d["tomography_300_puzzles"]["loop_schur_and_hessian_512x512"].__setitem__("g_loop_lambda_max_lo_dec6", "1.000000"))
        mutate_and_expect("SCHUR_ANCHOR_FAIL", lambda d: d["tomography_300_puzzles"]["loop_schur_and_hessian_512x512"].__setitem__("g_loop_lambda_max_hi_dec6", "1.195321"))
        mutate_and_expect("GD_CLIFF_FAIL", lambda d: d["tomography_300_puzzles"]["plain_gd_eta_0p8_cliff"].__setitem__("diverged_count", 123))
        mutate_and_expect("GD_CLIFF_FAIL", lambda d: d["tomography_300_puzzles"]["plain_gd_eta_0p8_cliff"].__setitem__("converged_with_lmax_le_2p5", 175))
        mutate_and_expect("CURL_BIAS_FAIL", lambda d: d["tomography_300_puzzles"]["power_iter_60_curl_bias"].__setitem__("real_dom_median_rel_err_sci", "0.0e+00"))
        mutate_and_expect("CURL_BIAS_FAIL", lambda d: d["tomography_300_puzzles"]["power_iter_60_curl_bias"].__setitem__("complex_dom_median_rel_err_dec6", "0.001000"))
        mutate_and_expect("ADJOINT_CANCEL_FAIL", lambda d: d["ep_gradient_tomography"]["test-0016"].__setitem__("gloop_adjoint_cancel_max_abs_err_sci", "1.0e-14"))
        mutate_and_expect("EP_ORDER_FAIL", lambda d: d["ep_gradient_tomography"]["test-0016"]["exact_phase_beta_sweep"][4].__setitem__("one_sided_rel_err_dec8", "0.01000000"))
        mutate_and_expect("EP_ORDER_FAIL", lambda d: d["ep_gradient_tomography"]["test-0016"]["exact_phase_beta_sweep"][4].__setitem__("one_sided_rel_err_dec8", "0.03000000"))
        mutate_and_expect("EP_ORDER_FAIL", lambda d: d["ep_gradient_tomography"]["test-0016"]["exact_phase_beta_sweep"][4].__setitem__("centered_rel_err_dec8", "0.00040000"))
        mutate_and_expect("EP_ORDER_FAIL", lambda d: d["ep_gradient_tomography"]["test-0016"]["exact_phase_beta_sweep"][4].__setitem__("centered_rel_err_dec8", "0.00070000"))
        mutate_and_expect("EP_BLOWUP_FAIL", lambda d: d["ep_gradient_tomography"]["test-0016"]["truncated_free_phase_sweep"][0]["beta_rows"][4].__setitem__("nosub_rel_err_dec6", "1.000000"))
        mutate_and_expect("EP_BLOWUP_FAIL", lambda d: d["ep_gradient_tomography"]["test-0016"]["truncated_free_phase_sweep"][0]["beta_rows"][4].__setitem__("sub_rel_err_dec6", "1000.000000"))
        mutate_and_expect("EP_BLOWUP_FAIL", lambda d: d["ep_gradient_tomography"]["test-0016"]["truncated_free_phase_sweep"][2]["beta_rows"][4].__setitem__("sub_rel_err_dec6", "5.000000"))
        mutate_and_expect("EP_BLOWUP_FAIL", lambda d: d["ep_gradient_tomography"]["test-0016"]["truncated_free_phase_sweep"][0]["beta_rows"][4].__setitem__("centered_rel_err_dec6", "0.010000"))
        mutate_and_expect("EP_BLOWUP_FAIL", lambda d: d["ep_gradient_tomography"]["test-0016"]["truncated_free_phase_sweep"][2]["beta_rows"][4].__setitem__("centered_rel_err_dec6", "0.010000"))
        mutate_and_expect("SOLVED_WRONG_SEP_FAIL", lambda d: d["tomography_300_puzzles"]["solved_vs_wrong_separation"].__setitem__("wrong_median_rho_dec6", "0.157705"))

        # Exact boundary PASS cases (kill <= -> < boundary mutants)
        b_r128 = copy.deepcopy(base)
        b_r128["tomography_300_puzzles"]["rho_first_128_test"]["median_dec6"] = "0.165898"
        oracle.certify_pillar4_live_anchor(b_r128)
        for ratio_val, field, denom in (
            ("0.00450000", "one_sided_rel_err_dec8", "0.00100000"),
            ("0.00550000", "one_sided_rel_err_dec8", "0.00100000"),
            ("0.02400000", "centered_rel_err_dec8", "0.00100000"),
            ("0.02600000", "centered_rel_err_dec8", "0.00100000"),
        ):
            b_ep = copy.deepcopy(base)
            b_ep["ep_gradient_tomography"]["test-0016"]["exact_phase_beta_sweep"][4][field] = ratio_val
            b_ep["ep_gradient_tomography"]["test-0016"]["exact_phase_beta_sweep"][5][field] = denom
            oracle.certify_pillar4_live_anchor(b_ep)


class Test03ZoneBIOAndParsers(unittest.TestCase):
    def _assert_s76(self, code: str, fn, *args, **kwargs) -> None:
        with self.assertRaises(oracle.S76Error) as ctx:
            fn(*args, **kwargs)
        self.assertEqual(ctx.exception.code, code)

    def test_path_and_darwin_normalization(self) -> None:
        self._assert_s76("INVALID_PATH_TYPE", verifier._require_concrete_path, "/tmp/a", "p")
        self._assert_s76("INVALID_PATH_TYPE", verifier._require_concrete_path, _PathSub("/tmp/a"), "p")
        self._assert_s76("INVALID_UTF8_SURROGATE", verifier._require_concrete_path, Path("/tmp/\ud800"), "p")
        self._assert_s76("NUL_BYTE_FORBIDDEN", verifier._require_concrete_path, Path("/tmp/a\x00b"), "p")

        fake_lnk = os.stat_result((stat.S_IFLNK | 0o777, 1, 1, 1, 0, 0, 0, 0, 0, 0))
        fake_nonroot = os.stat_result((stat.S_IFLNK | 0o777, 1, 1, 1, 1000, 0, 0, 0, 0, 0))
        fake_dir = os.stat_result((stat.S_IFDIR | 0o755, 1, 1, 1, 0, 0, 0, 0, 0, 0))

        with mock.patch.object(verifier.sys, "platform", "linux"), mock.patch.object(
            verifier.os, "lstat", return_value=fake_lnk
        ), mock.patch.object(verifier.os, "readlink", return_value="private/tmp"):
            self.assertEqual(verifier._normalize_darwin_system_prefix(Path("/tmp/a")), Path("/tmp/a"))

        with mock.patch.object(verifier.sys, "platform", "darwin"):
            self.assertEqual(verifier._normalize_darwin_system_prefix(Path("/usr/bin")), Path("/usr/bin"))
            with mock.patch.object(verifier.os, "lstat", return_value=fake_lnk), mock.patch.object(
                verifier.os, "readlink", return_value="private/tmp"
            ):
                self.assertEqual(verifier._normalize_darwin_system_prefix(Path("x/tmp/a")), Path("x/tmp/a"))
                self.assertEqual(verifier._normalize_darwin_system_prefix(Path("/tmp/../a")), Path("/tmp/../a"))
                self.assertEqual(verifier._normalize_darwin_system_prefix(Path("/tmp"), allow_exact=False), Path("/tmp"))
                self.assertEqual(verifier._normalize_darwin_system_prefix(Path("/tmp"), allow_exact=True), Path("/private/tmp"))
                self.assertEqual(verifier._normalize_darwin_system_prefix(Path("/tmp/x")), Path("/private/tmp/x"))
            with mock.patch.object(verifier.os, "lstat", return_value=fake_lnk), mock.patch.object(
                verifier.os, "readlink", return_value="/private/var"
            ):
                self.assertEqual(verifier._normalize_darwin_system_prefix(Path("/var/x")), Path("/private/var/x"))
            with mock.patch.object(verifier.os, "lstat", return_value=fake_lnk), mock.patch.object(
                verifier.os, "readlink", return_value="/evil/tmp"
            ):
                self.assertEqual(verifier._normalize_darwin_system_prefix(Path("/tmp/x")), Path("/tmp/x"))
            with mock.patch.object(verifier.os, "lstat", return_value=fake_nonroot), mock.patch.object(
                verifier.os, "readlink", return_value="private/tmp"
            ):
                self.assertEqual(verifier._normalize_darwin_system_prefix(Path("/tmp/x")), Path("/tmp/x"))
            with mock.patch.object(verifier.os, "lstat", return_value=fake_dir), mock.patch.object(
                verifier.os, "readlink", return_value="private/tmp"
            ):
                self.assertEqual(verifier._normalize_darwin_system_prefix(Path("/tmp/x")), Path("/tmp/x"))
            with mock.patch.object(verifier.os, "lstat", side_effect=OSError(errno.ENOENT, "no")):
                self.assertEqual(verifier._normalize_darwin_system_prefix(Path("/tmp/x")), Path("/tmp/x"))

    def test_safe_cwd_and_pwd_checks(self) -> None:
        with mock.patch.object(verifier.Path, "cwd", side_effect=OSError(errno.ENOENT, "gone")):
            self._assert_s76("CWD_UNAVAILABLE", verifier._safe_cwd, "lbl")

        with tempfile.TemporaryDirectory() as td:
            real_d = Path(td) / "real"
            real_d.mkdir()
            link_d = Path(td) / "link"
            link_d.symlink_to(real_d)
            old_cwd = os.getcwd()
            try:
                os.chdir(real_d)
                with mock.patch.dict(os.environ, {"PWD": "relative"}):
                    verifier._check_pwd_no_symlinks("lbl")
                with mock.patch.dict(os.environ, {"PWD": "/nonexistent_s76_dir_xyz"}):
                    verifier._check_pwd_no_symlinks("lbl")
                with mock.patch.dict(os.environ, {"PWD": str(Path(td))}):
                    verifier._check_pwd_no_symlinks("lbl")
                with mock.patch.object(verifier.os, "environ", {"PWD": "/tmp/\x00bad"}):
                    self._assert_s76("NUL_BYTE_FORBIDDEN", verifier._check_pwd_no_symlinks, "lbl")
                with mock.patch.dict(os.environ, {"PWD": str(link_d)}):
                    self._assert_s76("SYMLINK_ANCESTOR_FORBIDDEN", verifier._check_pwd_no_symlinks, "lbl")
                with mock.patch.dict(os.environ, {"PWD": str(real_d)}):
                    verifier._check_pwd_no_symlinks("lbl")
                    with mock.patch.object(verifier.os, "open", side_effect=OSError(errno.EACCES, "denied")):
                        self._assert_s76("CWD_UNAVAILABLE", verifier._check_pwd_no_symlinks, "lbl")
                    orig_open = os.open

                    def fail_step(path, flags, *a, **kw):
                        if path != "/":
                            raise OSError(errno.EACCES, "denied")
                        return orig_open(path, flags, *a, **kw)

                    with mock.patch.object(verifier.os, "open", side_effect=fail_step):
                        self._assert_s76("CWD_UNAVAILABLE", verifier._check_pwd_no_symlinks, "lbl")
            finally:
                os.chdir(old_cwd)

    def test_read_and_write_zone_b_adversarial(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            f_ok = root / "ok.bin"
            verifier.write_regular_bytes_safe(f_ok, b"hello", "ok")
            self.assertEqual(stat.S_IMODE(os.lstat(f_ok).st_mode), 0o600)
            self.assertEqual(verifier.read_regular_bytes_capped(f_ok, "ok", max_bytes=5), b"hello")
            self._assert_s76("FILE_TOO_LARGE", verifier.read_regular_bytes_capped, f_ok, "ok", max_bytes=4)
            self._assert_s76("INT_OUT_OF_RANGE", verifier.read_regular_bytes_capped, f_ok, "ok", max_bytes=0)
            self._assert_s76("INT_OUT_OF_RANGE", verifier.read_regular_bytes_capped, f_ok, "ok", max_bytes=verifier.MAX_ALLOWED_CAP_BYTES + 1)

            # Growing stream exceeds cap even if fstat reports small size
            small_st = os.stat_result((stat.S_IFREG | 0o600, 1, 1, 1, 0, 0, 2, 0, 0, 0))
            with mock.patch.object(verifier.os, "fstat", return_value=small_st):
                self._assert_s76("FILE_TOO_LARGE", verifier.read_regular_bytes_capped, f_ok, "ok", max_bytes=3)

            # fstat st_size > max_bytes rejects BEFORE os.read even on an empty 0-byte file
            empty_f = root / "empty.bin"
            verifier.write_regular_bytes_safe(empty_f, b"", "empty")
            big_st = os.stat_result((stat.S_IFREG | 0o600, 1, 1, 1, 0, 0, 999, 0, 0, 0))
            with mock.patch.object(verifier.os, "fstat", return_value=big_st):
                self._assert_s76("FILE_TOO_LARGE", verifier.read_regular_bytes_capped, empty_f, "empty", max_bytes=10)

            # Relative path read & write
            old_cwd = os.getcwd()
            try:
                os.chdir(root)
                with mock.patch.dict(os.environ, {"PWD": str(root)}):
                    verifier.write_regular_bytes_safe(Path("sub/nested/rel.bin"), b"xyz", "rel")
                    self.assertEqual(verifier.read_regular_bytes_capped(Path("sub/nested/rel.bin"), "rel"), b"xyz")
            finally:
                os.chdir(old_cwd)

            # Non-regular leaf paths (and direct _open_dir_chain rejection of "..")
            self._assert_s76("NOT_A_REGULAR_FILE", verifier.read_regular_bytes_capped, Path("/"), "root")
            self._assert_s76("NOT_A_REGULAR_FILE", verifier._open_dir_chain, root / "..", "dotdot", create_parents=False)
            self._assert_s76("NOT_A_REGULAR_FILE", verifier.read_regular_bytes_capped, root / "..", "dotdot")
            self._assert_s76("NOT_A_REGULAR_FILE", verifier.read_regular_bytes_capped, root / "sub", "dir")
            self._assert_s76("NOT_A_REGULAR_FILE", verifier.write_regular_bytes_safe, root / "sub", b"x", "dir")
            self._assert_s76("INVALID_PAYLOAD_BYTES", verifier.write_regular_bytes_safe, f_ok, "str", "bad")

            # FIFO non-blocking rejection (read and write)
            fifo = root / "pipe.fifo"
            os.mkfifo(fifo)
            self._assert_s76("NOT_A_REGULAR_FILE", verifier.read_regular_bytes_capped, fifo, "fifo")
            self._assert_s76("NOT_A_REGULAR_FILE", verifier.write_regular_bytes_safe, fifo, b"x", "fifo")

            # Symlink leaf & ancestor (read and write)
            sym_leaf = root / "sym_leaf"
            sym_leaf.symlink_to(f_ok)
            self._assert_s76("SYMLINK_FORBIDDEN", verifier.read_regular_bytes_capped, sym_leaf, "sym")
            self._assert_s76("SYMLINK_FORBIDDEN", verifier.write_regular_bytes_safe, sym_leaf, b"x", "sym")

            sym_dir = root / "sym_dir"
            sym_dir.symlink_to(root / "sub")
            self._assert_s76("SYMLINK_FORBIDDEN", verifier.read_regular_bytes_capped, sym_dir / "a", "symd")
            self._assert_s76("SYMLINK_FORBIDDEN", verifier.write_regular_bytes_safe, sym_dir / "a", b"x", "symd")

            # Hardlink (st_nlink == 2) on read and write
            hl = root / "hardlink"
            os.link(f_ok, hl)
            self._assert_s76("HARDLINK_FORBIDDEN", verifier.read_regular_bytes_capped, hl, "hl")
            self._assert_s76("HARDLINK_FORBIDDEN", verifier.write_regular_bytes_safe, hl, b"x", "hl")
            os.unlink(hl)

            # Missing file read error (must NOT create missing parent dir!) & root open error & os.read error
            self._assert_s76("FILE_READ_ERROR", verifier.read_regular_bytes_capped, root / "missing.bin", "miss")
            self._assert_s76("FILE_READ_ERROR", verifier.read_regular_bytes_capped, root / "nodir" / "x", "missd")
            self.assertFalse((root / "nodir").exists())
            with mock.patch.object(verifier.os, "open", side_effect=OSError(errno.EACCES, "denied")):
                self._assert_s76("FILE_READ_ERROR", verifier.read_regular_bytes_capped, f_ok, "rd")
                self._assert_s76("FILE_WRITE_ERROR", verifier.write_regular_bytes_safe, f_ok, b"x", "wr")
            with mock.patch.object(verifier.os, "read", side_effect=OSError(errno.EIO, "io")):
                self._assert_s76("FILE_READ_ERROR", verifier.read_regular_bytes_capped, f_ok, "rd")

            # Atomic overwrite + partial os.write + FileExistsError retry + mkdir FileExistsError race
            orig_write = os.write
            calls = {"w": 0}

            def partial_write(fd, buf):
                calls["w"] += 1
                if calls["w"] == 1:
                    return orig_write(fd, buf[:2])
                return orig_write(fd, buf)

            with mock.patch.object(verifier.os, "write", side_effect=partial_write):
                verifier.write_regular_bytes_safe(f_ok, b"abcdef", "part")
            self.assertEqual(verifier.read_regular_bytes_capped(f_ok, "part"), b"abcdef")

            orig_open = os.open
            state = {"n": 0}

            def open_retry_once(path, flags, *a, **kw):
                if isinstance(path, str) and path.startswith(".s76.") and state["n"] == 0:
                    state["n"] += 1
                    raise FileExistsError()
                return orig_open(path, flags, *a, **kw)

            with mock.patch.object(verifier.os, "open", side_effect=open_retry_once):
                verifier.write_regular_bytes_safe(f_ok, b"retry", "retry")
            self.assertEqual(verifier.read_regular_bytes_capped(f_ok, "retry"), b"retry")

            # Temp slots exhausted & temp open OSError & lstat OSError
            def open_always_exists(path, flags, *a, **kw):
                if isinstance(path, str) and path.startswith(".s76."):
                    raise FileExistsError()
                return orig_open(path, flags, *a, **kw)

            with mock.patch.object(verifier.os, "open", side_effect=open_always_exists):
                self._assert_s76("FILE_WRITE_ERROR", verifier.write_regular_bytes_safe, f_ok, b"x", "exh")

            nospc_calls = {"n": 0}

            def open_enospc(path, flags, *a, **kw):
                if isinstance(path, str) and path.startswith(".s76."):
                    nospc_calls["n"] += 1
                    raise OSError(errno.ENOSPC, "full")
                return orig_open(path, flags, *a, **kw)

            with mock.patch.object(verifier.os, "open", side_effect=open_enospc):
                self._assert_s76("FILE_WRITE_ERROR", verifier.write_regular_bytes_safe, f_ok, b"x", "nospc")
            self.assertEqual(nospc_calls["n"], 1)

            with mock.patch.object(verifier.os, "lstat", side_effect=OSError(errno.EACCES, "denied")):
                self._assert_s76("FILE_WRITE_ERROR", verifier.write_regular_bytes_safe, f_ok, b"x", "lst")

            # mkdir race (FileExistsError -> reopen succeeds; OSError fails immediately without second open; EACCES on parent does not call mkdir)
            race_dir = root / "racedir"
            orig_mkdir = os.mkdir
            race_flag = {"first": True}

            def open_race(path, flags, *a, **kw):
                if path == "racedir" and race_flag["first"]:
                    race_flag["first"] = False
                    raise OSError(errno.ENOENT, "enoent")
                return orig_open(path, flags, *a, **kw)

            race_dir.mkdir()
            with mock.patch.object(verifier.os, "open", side_effect=open_race), mock.patch.object(
                verifier.os, "mkdir", side_effect=FileExistsError()
            ):
                verifier.write_regular_bytes_safe(race_dir / "f.bin", b"ok", "race")
            self.assertEqual(verifier.read_regular_bytes_capped(race_dir / "f.bin", "race"), b"ok")

            with mock.patch.object(verifier.os, "mkdir", side_effect=OSError(errno.EACCES, "denied")):
                with self.assertRaises(oracle.S76Error) as mk_ctx:
                    verifier.write_regular_bytes_safe(root / "newd1" / "f", b"x", "mk")
                self.assertEqual(mk_ctx.exception.code, "FILE_WRITE_ERROR")
                self.assertIn("mkdir failed", mk_ctx.exception.detail)

            def open_parent_eacces(path, flags, *a, **kw):
                if path == "noacc":
                    raise OSError(errno.EACCES, "denied")
                return orig_open(path, flags, *a, **kw)

            with mock.patch.object(verifier.os, "open", side_effect=open_parent_eacces), mock.patch.object(
                verifier.os, "mkdir"
            ) as mk_spy:
                self._assert_s76("FILE_WRITE_ERROR", verifier.write_regular_bytes_safe, root / "noacc" / "f", b"x", "ea")
                mk_spy.assert_not_called()

            def open_reopen_fail(path, flags, *a, **kw):
                if path == "newd2":
                    raise OSError(errno.ENOENT, "enoent")
                return orig_open(path, flags, *a, **kw)

            with mock.patch.object(verifier.os, "open", side_effect=open_reopen_fail), mock.patch.object(
                verifier.os, "mkdir", side_effect=orig_mkdir
            ):
                self._assert_s76("FILE_WRITE_ERROR", verifier.write_regular_bytes_safe, root / "newd2" / "f", b"x", "re")

            # Short write 0, fchmod/fsync/replace OSError, temp nlink altered, unlink OSError cleanup
            with mock.patch.object(verifier.os, "write", return_value=0):
                self._assert_s76("FILE_WRITE_ERROR", verifier.write_regular_bytes_safe, f_ok, b"x", "sw0")
            with mock.patch.object(verifier.os, "fchmod", side_effect=OSError(errno.EPERM, "perm")):
                self._assert_s76("FILE_WRITE_ERROR", verifier.write_regular_bytes_safe, f_ok, b"x", "fch")
            with mock.patch.object(verifier.os, "fsync", side_effect=OSError(errno.EIO, "io")):
                self._assert_s76("FILE_WRITE_ERROR", verifier.write_regular_bytes_safe, f_ok, b"x", "fsy")
            bad_nlink = os.stat_result((stat.S_IFREG | 0o600, 1, 1, 2, 0, 0, 1, 0, 0, 0))
            with mock.patch.object(verifier.os, "fstat", return_value=bad_nlink):
                self._assert_s76("HARDLINK_FORBIDDEN", verifier.write_regular_bytes_safe, f_ok, b"x", "nl")
            # Put mocked-unlink test in its own subdir so leftovers check for 16T stress is exact
            rep_dir = root / "rep_fail"
            rep_dir.mkdir()
            with mock.patch.object(verifier.os, "replace", side_effect=OSError(errno.EXDEV, "xdev")), mock.patch.object(
                verifier.os, "unlink", side_effect=OSError(errno.ENOENT, "gone")
            ):
                self._assert_s76("FILE_WRITE_ERROR", verifier.write_regular_bytes_safe, rep_dir / "f.bin", b"x", "rep")

            # 16T concurrent stress test
            conc_dir = root / "conc_dir"
            conc_dir.mkdir()
            conc_f = conc_dir / "concurrent.bin"
            errs: list[BaseException] = []

            def worker(idx: int) -> None:
                try:
                    data = f"worker-{idx:02d}\n".encode("ascii")
                    for _ in range(8):
                        verifier.write_regular_bytes_safe(conc_f, data, "conc")
                        got = verifier.read_regular_bytes_capped(conc_f, "conc")
                        if not got.startswith(b"worker-"):
                            errs.append(ValueError("corrupt read"))
                except BaseException as exc:  # pragma: no cover
                    errs.append(exc)

            threads = [threading.Thread(target=worker, args=(i,)) for i in range(16)]
            for t in threads:
                t.start()
            for t in threads:
                t.join()
            self.assertEqual(errs, [])
            leftovers = [p.name for p in conc_dir.iterdir() if p.name.startswith(".s76.") and p.name.endswith(".tmp")]
            self.assertEqual(leftovers, [])

    def test_strict_json_and_rational_parsers(self) -> None:
        self.assertEqual(verifier._parse_bounded_int("0"), 0)
        self.assertEqual(verifier._parse_bounded_int("-42"), -42)
        self.assertEqual(len(str(verifier._parse_bounded_int("9" * oracle.MAX_INT_DIGITS))), oracle.MAX_INT_DIGITS)
        self._assert_s76("INVALID_INT_TOKEN", verifier._parse_bounded_int, "12a")
        self._assert_s76("INT_TOO_LARGE", verifier._parse_bounded_int, "9" * (oracle.MAX_INT_DIGITS + 1))
        self._assert_s76("NONCANONICAL_INT", verifier._parse_bounded_int, "01")
        self._assert_s76("NONCANONICAL_INT", verifier._parse_bounded_int, "-0")
        with mock.patch.object(oracle, "MAX_INT_DIGITS", 3000):
            max_bits_ok = (1 << oracle.MAX_INT_BITS) - 1
            self.assertEqual(verifier._parse_bounded_int(str(max_bits_ok)), max_bits_ok)
            self._assert_s76("INT_TOO_LARGE", verifier._parse_bounded_int, str(1 << oracle.MAX_INT_BITS))

        self.assertEqual(verifier.parse_strict_json_bytes(b'{"a":1}\n'), {"a": 1})
        self.assertEqual(verifier.parse_strict_json_bytes(b'{ "a" : 1 }', require_canonical=False), {"a": 1})
        self._assert_s76("INVALID_BYTES", verifier.parse_strict_json_bytes, '{"a":1}\n')
        self._assert_s76("BOM_FORBIDDEN", verifier.parse_strict_json_bytes, b'\xef\xbb\xbf{"a":1}\n')
        self._assert_s76("CRLF_FORBIDDEN", verifier.parse_strict_json_bytes, b'{"a":1}\r\n')
        self._assert_s76("INVALID_UTF8", verifier.parse_strict_json_bytes, b"\xff")
        self._assert_s76("FLOAT_FORBIDDEN", verifier.parse_strict_json_bytes, b'{"a":1.0}\n')
        self._assert_s76("NONFINITE_JSON_CONSTANT", verifier.parse_strict_json_bytes, b'{"a":NaN}\n')
        self._assert_s76("DUPLICATE_JSON_KEY", verifier.parse_strict_json_bytes, b'{"a":1,"a":2}\n')
        self._assert_s76("INVALID_JSON", verifier.parse_strict_json_bytes, b"{bad")
        self._assert_s76("INVALID_ROOT_TYPE", verifier.parse_strict_json_bytes, b"[1]\n")
        self._assert_s76("NONCANONICAL_JSON", verifier.parse_strict_json_bytes, b'{"a": 1}\n', require_canonical=True)

        self.assertEqual(verifier.parse_canonical_rational_str("0", "q"), Fraction(0))
        self.assertEqual(verifier.parse_canonical_rational_str("-3/4", "q"), Fraction(-3, 4))
        for bad, code in (
            ("", "INVALID_RATIONAL"),
            ("1/2/3", "INVALID_RATIONAL"),
            ("1/-2", "INVALID_RATIONAL"),
            ("3/1", "NONCANONICAL_RATIONAL"),
            ("1/0", "NONCANONICAL_RATIONAL"),
            ("2/4", "NONCANONICAL_RATIONAL"),
        ):
            self._assert_s76(code, verifier.parse_canonical_rational_str, bad, "q")


class Test05LeanGates(unittest.TestCase):
    def _assert_s76(self, code: str, fn, *args, **kwargs) -> None:
        with self.assertRaises(oracle.S76Error) as ctx:
            fn(*args, **kwargs)
        self.assertEqual(ctx.exception.code, code)

    def test_strip_and_static_gate(self) -> None:
        lean_src = (_THIS_DIR / "CircularPCLoopSchur.lean").read_text(encoding="utf-8")
        verifier.static_gate_lean4_source(lean_src)

        # Comments, nested comments, '/' and '-' non-comments, EOF comment
        stripped = verifier._strip_lean4_for_static_gate(
            "/- outer / - /- sorry -/ -/ -- axiom\n"
            "def x := a / b - c\n"
            "-- eof comment"
        )
        self.assertNotIn("sorry", stripped)
        self.assertNotIn("axiom", stripped)
        self.assertIn("a / b - c", stripped)
        self._assert_s76("LEAN4_UNTERMINATED_LEX", verifier._strip_lean4_for_static_gate, "/- unclosed")

        self._assert_s76("LEAN4_BAD_CHARS", verifier.static_gate_lean4_source, lean_src + "\r")
        self._assert_s76("LEAN4_BAD_CHARS", verifier.static_gate_lean4_source, lean_src + "\x00")

        for escape in (
            "\nsorry\n",
            "\nadmit\n",
            "\naxiom bad : Prop\n",
            "\nunsafe def u := 0\n",
            "\ntheorem t : True := by native_decide\n",
            "\ndef s := sorryAx\n",
            "\nset_option debug.skipKernelTC true\n",
            "\nset_option debug.byAsSorry true\n",
            "\n@[extern \"c_fn\"] def f : Nat := 0\n",
            "\nattribute [implemented_by f] g\n",
            "\n@[csimp] theorem c : True := trivial\n",
            "\nopaque hidden : Nat := 0\n",
            "\npartial def loop : Nat := loop\n",
            "\ndef ok := 1; partial def loop : Nat := loop\n",
            "\ntheorem t : True := by decide +native\n",
            "\nprivate theorem _e_multi : 1 = 1 := by decide -revert +native\n",
            "\nprivate theorem _e_plus : 1 = 1 := by decide +revert +native\n",
            "\ntheorem t : 1 = 1 := by decide (revert := true) +native\n",
            "\ntheorem t : 1 = 1 := by decide (config := myCfg)\n",
            "\ndef cfg : DecideConfig := {}\n",
            "\ntheorem t : True := by decide (native := !false)\n",
            "\ntheorem t : True := by decide (native := (true))\n",
            "\n#eval 1 + 1\n",
            "\n#reduce 1\n",
            "\n#exit\n",
            "\n#print Nat\n",
            "\nimport Mathlib\n",
            "\nimport Lean\n",
            "\nmacro \"bad\" : term => `(sorry)\n",
            "\nmacro_rules | `(bad) => `(sorry)\n",
            "\nelab \"bad\" : command => pure ()\n",
            "\nsyntax \"bad\" : term\n",
            '\ndef x := s!"{(by sorry : String)}"\n',
            '\ndef x := f!"{(by sorry : String)}"\n',
            '\ndef x := r"\\"\n',
            "\ntheorem t : False := by «sorry»\n",
        ):
            self._assert_s76("LEAN4_TRUST_ESCAPE", verifier.static_gate_lean4_source, lean_src + escape)

        self._assert_s76(
            "LEAN4_MISSING_THEOREM",
            verifier.static_gate_lean4_source,
            lean_src.replace("theorem loop_schur_2node_metric_exact", "theorem renamed_thm"),
        )
        self._assert_s76(
            "LEAN4_MISSING_PRINT_AXIOMS",
            verifier.static_gate_lean4_source,
            lean_src.replace("#print axioms CircularPCLoopSchur.loop_schur_2node_metric_exact", ""),
        )

    def test_resolve_and_verify_lean_live_and_mocked(self) -> None:
        live = verifier.verify_lean4_file_live(_THIS_DIR / "CircularPCLoopSchur.lean")
        self.assertEqual(live["theorems_verified"], len(oracle.LEAN_THEOREM_NAMES))
        self.assertIn("4.36.0", live["lean_version"])

        with tempfile.TemporaryDirectory() as td:
            fake_bin = Path(td) / "lean"
            fake_bin.write_text("#!/bin/sh\n", encoding="utf-8")
            os.chmod(fake_bin, 0o700)
            noexec_bin = Path(td) / "lean_noexec"
            noexec_bin.write_text("#!/bin/sh\n", encoding="utf-8")
            os.chmod(noexec_bin, 0o600)
            dir_bin = Path(td) / "lean_dir"
            dir_bin.mkdir(mode=0o700)
            with mock.patch.dict(os.environ, {"ALETHEIA_LEAN_BIN": str(fake_bin)}):
                self.assertEqual(verifier.resolve_lean_binary(), str(fake_bin))
            with mock.patch.dict(os.environ, {"ALETHEIA_LEAN_BIN": str(Path(td) / "missing")}):
                self._assert_s76("LEAN_BINARY_UNAVAILABLE", verifier.resolve_lean_binary)
            with mock.patch.dict(os.environ, {"ALETHEIA_LEAN_BIN": str(noexec_bin)}):
                self._assert_s76("LEAN_BINARY_UNAVAILABLE", verifier.resolve_lean_binary)
            with mock.patch.dict(os.environ, {"ALETHEIA_LEAN_BIN": str(dir_bin)}):
                self._assert_s76("LEAN_BINARY_UNAVAILABLE", verifier.resolve_lean_binary)

            # Fallback via shutil.which (exec vs non-exec) and Path.home() (dir / non-exec / exec)
            env_no = {k: v for k, v in os.environ.items() if k != "ALETHEIA_LEAN_BIN"}
            with mock.patch.dict(os.environ, env_no, clear=True):
                with mock.patch.object(verifier.shutil, "which", return_value=str(fake_bin)):
                    self.assertEqual(verifier.resolve_lean_binary(), str(fake_bin))
                home_d = Path(td) / "h"
                (home_d / ".local" / "bin" / "lean").mkdir(parents=True)
                (home_d / ".elan" / "bin").mkdir(parents=True)
                elan_lean = home_d / ".elan" / "bin" / "lean"
                elan_lean.write_text("#!/bin/sh\n", encoding="utf-8")
                os.chmod(elan_lean, 0o600)
                with mock.patch.object(verifier.shutil, "which", return_value=str(noexec_bin)), mock.patch.object(
                    verifier.Path, "home", return_value=home_d
                ):
                    self._assert_s76("LEAN_BINARY_UNAVAILABLE", verifier.resolve_lean_binary)
                os.chmod(elan_lean, 0o700)
                with mock.patch.object(verifier.shutil, "which", return_value=None), mock.patch.object(
                    verifier.Path, "home", return_value=home_d
                ):
                    self.assertEqual(verifier.resolve_lean_binary(), str(elan_lean))
                os.unlink(elan_lean)
                with mock.patch.object(verifier.shutil, "which", return_value=None), mock.patch.object(
                    verifier.Path, "home", return_value=home_d
                ):
                    self._assert_s76("LEAN_BINARY_UNAVAILABLE", verifier.resolve_lean_binary)

            # Bad UTF-8 lean file & live end-to-end multi-flag +native exploit regressions
            bad_utf8 = Path(td) / "bad.lean"
            bad_utf8.write_bytes(b"\xff\xfe")
            self._assert_s76("INVALID_UTF8", verifier.verify_lean4_file_live, bad_utf8)
            base_lean = (_THIS_DIR / "CircularPCLoopSchur.lean").read_text(encoding="utf-8")
            for idx_e, exploit_tail in enumerate((
                "\nprivate theorem _e_multi : 1 = 1 := by decide -revert +native\n",
                "\nprivate theorem _e_plus : 1 = 1 := by decide +revert +native\n",
            )):
                exp_p = Path(td) / f"exploit_{idx_e}.lean"
                exp_p.write_text(base_lean + exploit_tail, encoding="utf-8")
                self._assert_s76("LEAN4_TRUST_ESCAPE", verifier.verify_lean4_file_live, exp_p)

        lean_path = _THIS_DIR / "CircularPCLoopSchur.lean"
        ok_ver = subprocess.CompletedProcess(["lean", "--version"], 0, "Lean (version 4.36.0, x86_64)\n", "")

        def run_mock(ver_res, comp_res):
            seq = [ver_res, comp_res]

            def side_eff(*a, **kw):
                item = seq.pop(0)
                if isinstance(item, BaseException):
                    raise item
                return item

            return mock.patch.object(verifier.subprocess, "run", side_effect=side_eff)

        with run_mock(OSError("no"), ok_ver):
            self._assert_s76("LEAN_EXEC_ERROR", verifier.verify_lean4_file_live, lean_path)
        with run_mock(subprocess.CompletedProcess(["lean"], 0, "Lean (version 4.10.0)\n", ""), ok_ver):
            self._assert_s76("LEAN_VERSION_MISMATCH", verifier.verify_lean4_file_live, lean_path)
        with run_mock(subprocess.CompletedProcess(["lean"], 1, "Lean (version 4.36.0)\n", ""), ok_ver):
            self._assert_s76("LEAN_VERSION_MISMATCH", verifier.verify_lean4_file_live, lean_path)
        with run_mock(ok_ver, subprocess.TimeoutExpired(["lean"], 120)):
            self._assert_s76("LEAN_EXEC_ERROR", verifier.verify_lean4_file_live, lean_path)
        with run_mock(ok_ver, subprocess.CompletedProcess(["lean"], 1, "", "")):
            self._assert_s76("LEAN_COMPILE_FAIL", verifier.verify_lean4_file_live, lean_path)
        with run_mock(ok_ver, subprocess.CompletedProcess(["lean"], 0, "", "err")):
            self._assert_s76("LEAN_STDERR_NONEMPTY", verifier.verify_lean4_file_live, lean_path)
        with run_mock(ok_ver, subprocess.CompletedProcess(["lean"], 0, "warning: unused\n", "")):
            self._assert_s76("LEAN_WARNING_FORBIDDEN", verifier.verify_lean4_file_live, lean_path)
        with run_mock(ok_ver, subprocess.CompletedProcess(["lean"], 0, "weird line\n", "")):
            self._assert_s76("LEAN_UNEXPECTED_STDOUT", verifier.verify_lean4_file_live, lean_path)

        # Mixed: no-axioms line + empty [] + wrapped multiline [propext,\n Quot.sound] -> PASS
        lines_ok = [f"'{oracle.LEAN_THEOREM_NAMES[0]}' does not depend on any axioms", ""]
        lines_ok.append(f"'{oracle.LEAN_THEOREM_NAMES[1]}' depends on axioms: []")
        lines_ok.append(f"'{oracle.LEAN_THEOREM_NAMES[2]}' depends on axioms: [propext,")
        lines_ok.append("  ,")
        lines_ok.append("  Quot.sound]")
        for t in oracle.LEAN_THEOREM_NAMES[3:]:
            lines_ok.append(f"'{t}' depends on axioms: [propext, Quot.sound]")
        with run_mock(ok_ver, subprocess.CompletedProcess(["lean"], 0, "\n".join(lines_ok) + "\n", "")):
            res = verifier.verify_lean4_file_live(lean_path)
            self.assertEqual(res["theorems_verified"], len(oracle.LEAN_THEOREM_NAMES))

        # Unterminated wrapped bracket & duplicate theorem lines rejected
        with run_mock(ok_ver, subprocess.CompletedProcess(["lean"], 0, f"'{oracle.LEAN_THEOREM_NAMES[0]}' depends on axioms: [propext,\n", "")):
            self._assert_s76("LEAN_UNEXPECTED_STDOUT", verifier.verify_lean4_file_live, lean_path)
        dup_none = f"'{oracle.LEAN_THEOREM_NAMES[0]}' does not depend on any axioms\n" * 2
        with run_mock(ok_ver, subprocess.CompletedProcess(["lean"], 0, dup_none, "")):
            self._assert_s76("LEAN_DUPLICATE_THEOREM", verifier.verify_lean4_file_live, lean_path)
        dup_dep = f"'{oracle.LEAN_THEOREM_NAMES[0]}' depends on axioms: [propext]\n" * 2
        with run_mock(ok_ver, subprocess.CompletedProcess(["lean"], 0, dup_dep, "")):
            self._assert_s76("LEAN_DUPLICATE_THEOREM", verifier.verify_lean4_file_live, lean_path)

        bad_ax = f"'{oracle.LEAN_THEOREM_NAMES[0]}' depends on axioms: [Classical.choice]\n"
        with run_mock(ok_ver, subprocess.CompletedProcess(["lean"], 0, bad_ax, "")):
            self._assert_s76("LEAN_FORBIDDEN_AXIOM", verifier.verify_lean4_file_live, lean_path)

        with run_mock(ok_ver, subprocess.CompletedProcess(["lean"], 0, "\n".join(lines_ok[:-1]) + "\n", "")):
            self._assert_s76("LEAN_THEOREM_SET_MISMATCH", verifier.verify_lean4_file_live, lean_path)


class Test04SecondaryAuditReplayAndCLI(unittest.TestCase):
    def setUp(self) -> None:
        raw = verifier.read_regular_bytes_capped(_THIS_DIR / "s76_circular_pc_certificate.json", "cert")
        self.cert = verifier.parse_strict_json_bytes(raw, "cert", require_canonical=True)

    def _assert_s76(self, code: str, fn, *args, **kwargs) -> None:
        with self.assertRaises(oracle.S76Error) as ctx:
            fn(*args, **kwargs)
        self.assertEqual(ctx.exception.code, code)

    def test_y_full_replay_and_fr0_pass(self) -> None:
        r_full = verifier.verify_certificate_dict(self.cert, full_replay=True)
        self.assertTrue(r_full["valid"])
        self.assertTrue(r_full["full_replay"])
        self.assertIn("lean_live", r_full)

        r_fr0 = verifier.verify_certificate_dict(self.cert, full_replay=False)
        self.assertTrue(r_fr0["valid"])
        self.assertFalse(r_fr0["full_replay"])
        self.assertNotIn("lean_live", r_fr0)

        self._assert_s76("INVALID_BOOL", verifier.verify_certificate_dict, self.cert, full_replay=1)
        self._assert_s76("INVALID_CERT_TYPE", verifier.verify_certificate_dict, [], full_replay=False)
        self._assert_s76("INVALID_PAYLOAD_TYPE", verifier.secondary_audit_payload, [])

    def test_envelope_hash_and_full_replay_mismatch(self) -> None:
        bad_schema = copy.deepcopy(self.cert)
        bad_schema["schema_version"] = "bad"
        self._assert_s76("SCHEMA_MISMATCH", verifier.verify_certificate_dict, bad_schema, full_replay=False)

        bad_tid = copy.deepcopy(self.cert)
        bad_tid["track_id"] = "bad"
        self._assert_s76("SCHEMA_MISMATCH", verifier.verify_certificate_dict, bad_tid, full_replay=False)

        bad_psha = copy.deepcopy(self.cert)
        bad_psha["payload_sha256"] = "0" * 64
        self._assert_s76("PAYLOAD_SHA_MISMATCH", verifier.verify_certificate_dict, bad_psha, full_replay=False)

        bad_csha = copy.deepcopy(self.cert)
        bad_csha["certificate_sha256"] = "0" * 64
        self._assert_s76("CERT_SHA_MISMATCH", verifier.verify_certificate_dict, bad_csha, full_replay=False)

        # Valid re-signed cert with altered pinned hash passes FR0, killed by FR1
        fr1_only = copy.deepcopy(self.cert)
        fr1_only["payload"]["pinned_artifacts"]["lakefile_sha256"] = "0" * 64
        fr1_only = _resign_cert(fr1_only)
        self.assertTrue(verifier.verify_certificate_dict(fr1_only, full_replay=False)["valid"])
        cached_lean = {
            "lean_version": "Lean (version 4.36.0)",
            "theorems_verified": len(oracle.LEAN_THEOREM_NAMES),
            "lean_source_sha256": self.cert["payload"]["pinned_artifacts"]["lean_source_sha256"],
        }
        with mock.patch.object(verifier, "verify_lean4_file_live", return_value=cached_lean):
            self._assert_s76("FULL_REPLAY_MISMATCH", verifier.verify_certificate_dict, fr1_only, full_replay=True)

    def test_secondary_audit_exhaustive_tamper_kills(self) -> None:
        def tamper(code: str, fn) -> None:
            c = copy.deepcopy(self.cert)
            fn(c["payload"])
            self._assert_s76(code, verifier.secondary_audit_payload, c["payload"])
            # Also confirm re-signed FR0 catches it
            resigned = _resign_cert(c)
            self._assert_s76(code, verifier.verify_certificate_dict, resigned, full_replay=False)

        tamper("INVALID_SCHEMA_KEYS", lambda p: p.__setitem__("extra", 1))
        tamper("INVALID_SCHEMA_DICT", lambda p: p.__setitem__("pinned_artifacts", []))
        tamper("SCHEMA_MISMATCH", lambda p: p.__setitem__("schema_version", "bad"))
        tamper("SCHEMA_MISMATCH", lambda p: p.__setitem__("track_id", "bad"))
        tamper("SCHEMA_MISMATCH", lambda p: p.__setitem__("oracle_class", "bad"))
        tamper("SCHEMA_MISMATCH", lambda p: p.__setitem__("novelty_classification", "N0"))
        tamper("SCHEMA_MISMATCH", lambda p: p["pinned_artifacts"].__setitem__("lean_source", "x.lean"))
        tamper("SCHEMA_MISMATCH", lambda p: p["pinned_artifacts"].__setitem__("lean_toolchain", "bad"))
        tamper("SCHEMA_MISMATCH", lambda p: p["pinned_artifacts"].__setitem__("live_anchor_file", "bad.json"))
        tamper("THEOREM_LIST_MISMATCH", lambda p: p["pinned_artifacts"].__setitem__("lean_theorem_names", []))
        tamper("THEOREM_LIST_MISMATCH", lambda p: p["pinned_artifacts"].__setitem__("lean_theorem_names", {k: 0 for k in oracle.LEAN_THEOREM_NAMES}))
        tamper("THEOREM_LIST_MISMATCH", lambda p: p["pinned_artifacts"]["lean_theorem_names"].__setitem__(0, "bad"))

        # Pillar 1
        tamper("PILLAR1_FALSE", lambda p: p["pillar1_loop_schur_and_holonomy"]["l2_noncommuting_2x2"].__setitem__("loop_schur_identity_exact", False))
        tamper("PILLAR1_ALGEBRA_MISMATCH", lambda p: p["pillar1_loop_schur_and_holonomy"]["l2_noncommuting_2x2"].__setitem__("det_h_q", "1"))
        tamper("PILLAR1_ALGEBRA_MISMATCH", lambda p: p["pillar1_loop_schur_and_holonomy"]["l2_noncommuting_2x2"].__setitem__("det_g_loop_q", "1"))
        tamper("PILLAR1_ALGEBRA_MISMATCH", lambda p: (p["pillar1_loop_schur_and_holonomy"]["l2_noncommuting_2x2"].__setitem__("det_h_q", "0"), p["pillar1_loop_schur_and_holonomy"]["l2_noncommuting_2x2"].__setitem__("det_imm_q", "0")))
        tamper("INVALID_INERTIA", lambda p: p["pillar1_loop_schur_and_holonomy"]["l2_noncommuting_2x2"].__setitem__("g_loop_inertia", [2, 0]))
        tamper("INVALID_INERTIA", lambda p: p["pillar1_loop_schur_and_holonomy"]["l2_noncommuting_2x2"].__setitem__("g_loop_inertia", "123"))
        tamper("INERTIA_MISMATCH", lambda p: p["pillar1_loop_schur_and_holonomy"]["l2_noncommuting_2x2"].__setitem__("g_loop_inertia", [1, 1, 0]))

        # Pillar 2
        tamper("PILLAR2_RANGE", lambda p: p["pillar2_ep_bias_and_truncation"].__setitem__("theta_q", "1"))
        tamper("PILLAR2_IFT_MISMATCH", lambda p: p["pillar2_ep_bias_and_truncation"].__setitem__("exact_ift_grad_q", "1"))
        tamper("PILLAR2_ROWS", lambda p: p["pillar2_ep_bias_and_truncation"].__setitem__("exact_phase_rows", []))
        tamper("PILLAR2_ROWS", lambda p: p["pillar2_ep_bias_and_truncation"].__setitem__("exact_phase_rows", "abc"))
        tamper("PILLAR2_FALSE", lambda p: p["pillar2_ep_bias_and_truncation"]["exact_phase_rows"][0].__setitem__("bias_matches_formula", False))
        tamper("PILLAR2_BIAS_MISMATCH", lambda p: (
            p["pillar2_ep_bias_and_truncation"]["exact_phase_rows"][0].__setitem__("beta_q", "0"),
            p["pillar2_ep_bias_and_truncation"]["exact_phase_rows"][0].__setitem__("one_sided_bias_q", "0"),
            p["pillar2_ep_bias_and_truncation"]["exact_phase_rows"][0].__setitem__("one_sided_q", "27/4"),
        ))
        tamper("PILLAR2_BIAS_MISMATCH", lambda p: (
            p["pillar2_ep_bias_and_truncation"]["exact_phase_rows"][0].__setitem__("centered_bias_q", "1"),
            p["pillar2_ep_bias_and_truncation"]["exact_phase_rows"][0].__setitem__("centered_q", "31/4"),
        ))
        tamper("PILLAR2_BIAS_MISMATCH", lambda p: p["pillar2_ep_bias_and_truncation"]["exact_phase_rows"][0].__setitem__("one_sided_q", "0"))
        tamper("PILLAR2_BIAS_MISMATCH", lambda p: p["pillar2_ep_bias_and_truncation"]["exact_phase_rows"][0].__setitem__("centered_q", "0"))
        tamper(
            "PILLAR2_BIAS_MISMATCH",
            lambda p: (
                p["pillar2_ep_bias_and_truncation"]["exact_phase_rows"][0].__setitem__("one_sided_bias_q", "1"),
                p["pillar2_ep_bias_and_truncation"]["exact_phase_rows"][0].__setitem__("one_sided_q", "31/4"),
            ),
        )
        tamper("PILLAR2_TRUNC_MISMATCH", lambda p: (
            p["pillar2_ep_bias_and_truncation"].__setitem__("truncated_free_delta0_q", "0"),
            p["pillar2_ep_bias_and_truncation"].__setitem__("truncated_free_e0_q", "0"),
            p["pillar2_ep_bias_and_truncation"].__setitem__("truncated_free_grad_q", "0"),
        ))
        tamper("PILLAR2_TRUNC_MISMATCH", lambda p: (
            p["pillar2_ep_bias_and_truncation"].__setitem__("truncated_free_e0_q", "1"),
            p["pillar2_ep_bias_and_truncation"].__setitem__("truncated_free_grad_q", "-301/100"),
        ))
        tamper("PILLAR2_TRUNC_MISMATCH", lambda p: p["pillar2_ep_bias_and_truncation"].__setitem__("truncated_free_grad_q", "0"))
        tamper("PILLAR2_ROWS", lambda p: p["pillar2_ep_bias_and_truncation"].__setitem__("truncated_phase_rows", []))
        tamper("PILLAR2_ROWS", lambda p: p["pillar2_ep_bias_and_truncation"].__setitem__("truncated_phase_rows", "abc"))
        tamper("PILLAR2_BLOWUP_MISMATCH", lambda p: p["pillar2_ep_bias_and_truncation"]["truncated_phase_rows"][0].__setitem__("beta_q", "0"))
        tamper("PILLAR2_BLOWUP_MISMATCH", lambda p: p["pillar2_ep_bias_and_truncation"]["truncated_phase_rows"][2].__setitem__("nosub_inherited_abs_err_q", "1/10"))
        tamper("PILLAR2_BLOWUP_MISMATCH", lambda p: p["pillar2_ep_bias_and_truncation"]["truncated_phase_rows"][2].__setitem__("sub_converged_nudge_abs_err_q", "1/10"))
        tamper("PILLAR2_BLOWUP_MISMATCH", lambda p: p["pillar2_ep_bias_and_truncation"]["truncated_phase_rows"][0].__setitem__("centered_inherited_abs_err_q", "0"))
        tamper("PILLAR2_POLE_MISMATCH", lambda p: p["pillar2_ep_bias_and_truncation"].__setitem__("centered_pole_cancelled_beta_invariant", False))
        tamper("PILLAR2_POLE_MISMATCH", lambda p: p["pillar2_ep_bias_and_truncation"]["truncated_phase_rows"][1].__setitem__("centered_inherited_abs_err_q", "1/2"))

        # Pillar 3
        tamper("PILLAR3_GD_MISMATCH", lambda p: p["pillar3_krein_bifurcation_nonnormal_curl"]["contractive_gd_cliff"].__setitem__("rho_q", "0"))
        tamper("PILLAR3_GD_MISMATCH", lambda p: p["pillar3_krein_bifurcation_nonnormal_curl"]["contractive_gd_cliff"].__setitem__("rho_q", "1"))
        tamper("PILLAR3_GD_MISMATCH", lambda p: p["pillar3_krein_bifurcation_nonnormal_curl"]["contractive_gd_cliff"].__setitem__("det_h_q", "0"))
        tamper("PILLAR3_GD_MISMATCH", lambda p: (
            p["pillar3_krein_bifurcation_nonnormal_curl"]["contractive_gd_cliff"].__setitem__("lambda_max_h_q", "2"),
            p["pillar3_krein_bifurcation_nonnormal_curl"]["contractive_gd_cliff"].__setitem__("plain_gd_eta_crit_q", "1"),
        ))
        tamper("PILLAR3_GD_MISMATCH", lambda p: p["pillar3_krein_bifurcation_nonnormal_curl"]["contractive_gd_cliff"].__setitem__("plain_gd_eta_crit_q", "1"))
        tamper("PILLAR3_BIF_MISMATCH", lambda p: p["pillar3_krein_bifurcation_nonnormal_curl"]["critical_bifurcation_shadow"].__setitem__("det_h_q", "1"))
        tamper("PILLAR3_BIF_MISMATCH", lambda p: p["pillar3_krein_bifurcation_nonnormal_curl"]["critical_bifurcation_shadow"].__setitem__("shadow_vector_in_ker_jr", False))
        tamper("PILLAR3_BIF_MISMATCH", lambda p: p["pillar3_krein_bifurcation_nonnormal_curl"]["critical_bifurcation_shadow"].__setitem__("shadow_vector_in_ker_hpc", False))
        tamper("PILLAR3_KREIN_MISMATCH", lambda p: p["pillar3_krein_bifurcation_nonnormal_curl"]["krein_lagrangian_inertia"].__setitem__("contractive_det_k_q", "0"))
        tamper("PILLAR3_KREIN_MISMATCH", lambda p: p["pillar3_krein_bifurcation_nonnormal_curl"]["krein_lagrangian_inertia"].__setitem__("bifurcation_det_k_q", "1"))
        tamper("PILLAR3_NN_MISMATCH", lambda p: p["pillar3_krein_bifurcation_nonnormal_curl"]["non_normal_transient_amplification"].__setitem__("spectral_radius_q", "1"))
        tamper("PILLAR3_NN_MISMATCH", lambda p: p["pillar3_krein_bifurcation_nonnormal_curl"]["non_normal_transient_amplification"].__setitem__("overshoot_t1_to_t3_then_decay_t10", False))
        tamper("PILLAR3_NN_MISMATCH", lambda p: p["pillar3_krein_bifurcation_nonnormal_curl"]["non_normal_transient_amplification"]["norm_sq_e2_by_step"].__setitem__("t1", "1"))
        tamper("PILLAR3_NN_MISMATCH", lambda p: p["pillar3_krein_bifurcation_nonnormal_curl"]["non_normal_transient_amplification"]["norm_sq_e2_by_step"].__setitem__("t2", "1"))
        tamper("PILLAR3_NN_MISMATCH", lambda p: p["pillar3_krein_bifurcation_nonnormal_curl"]["non_normal_transient_amplification"]["norm_sq_e2_by_step"].__setitem__("t3", "1"))
        tamper("PILLAR3_NN_MISMATCH", lambda p: p["pillar3_krein_bifurcation_nonnormal_curl"]["non_normal_transient_amplification"]["norm_sq_e2_by_step"].__setitem__("t10", "1"))
        tamper("PILLAR3_CURL_MISMATCH", lambda p: p["pillar3_krein_bifurcation_nonnormal_curl"]["elliptic_complex_curl_obstruction"].__setitem__("strict_oscillation_bracket", False))
        tamper("PILLAR3_CURL_MISMATCH", lambda p: p["pillar3_krein_bifurcation_nonnormal_curl"]["elliptic_complex_curl_obstruction"].__setitem__("norm_sq_e1_q", "73/100"))
        tamper("PILLAR3_CURL_MISMATCH", lambda p: p["pillar3_krein_bifurcation_nonnormal_curl"]["elliptic_complex_curl_obstruction"].__setitem__("norm_sq_e2_q", "73/100"))
        tamper("PILLAR3_CURL_MISMATCH", lambda p: p["pillar3_krein_bifurcation_nonnormal_curl"]["elliptic_complex_curl_obstruction"].__setitem__("rho_sq_q", "1"))
        tamper("PILLAR3_CURL_MISMATCH", lambda p: p["pillar3_krein_bifurcation_nonnormal_curl"]["elliptic_complex_curl_obstruction"].__setitem__("skew_curl_entry_q", "0"))

        # Pillar 4
        tamper("PILLAR4_MISMATCH", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("upstream_repo", "other"))
        tamper("INVALID_HEX", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("upstream_commit_sha", "z" * 40))
        tamper("PILLAR4_FALSE", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("float32_parity_verified", False))
        tamper("PILLAR4_COUNTS", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("shipped_converged_wrong_count", 30))
        tamper("PILLAR4_DEC", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("shipped_solved_pct_dec2", "89.00"))
        tamper("PILLAR4_DEC", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("complex_dominant_pct_dec2", "12.00"))
        tamper("PILLAR4_BOUND", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("eq_rho_max_dec6", "1.000000"))
        tamper("PILLAR4_BOUND", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("eq_norm2_max_dec6", "1.000000"))
        tamper("PILLAR4_BOUND", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("non_normality_median_dec4", "1.0000"))
        tamper("PILLAR4_BOUND", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("non_normality_max_dec4", "1.5000"))
        tamper("PILLAR4_BOUND", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("wrong_vs_solved_median_rho_pct_dec2", "0.00"))
        tamper("PILLAR4_BOUND", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("loop_schur_300_max_abs_err_sci", "1.0e-12"))
        tamper("PILLAR4_BOUND", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("g_loop_softening_max_dec4", "1.0000"))
        tamper("PILLAR4_BOUND", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("power_iter_complex_vs_real_error_ratio_dec0", "100000000"))
        tamper("PILLAR4_GD_FMT", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("plain_gd_eta_0p8_converged_le_2p5_exact", "176/176/999"))
        tamper("PILLAR4_GD_FMT", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("plain_gd_eta_0p8_converged_le_2p5_exact", "a/176"))
        tamper("PILLAR4_GD_FMT", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("plain_gd_eta_0p8_converged_le_2p5_exact", "176/b"))
        tamper("PILLAR4_GD_BOUND", lambda p: (
            p["pillar4_live_circularep_anchor"].__setitem__("plain_gd_eta_0p8_converged_le_2p5_exact", "0/0"),
            p["pillar4_live_circularep_anchor"].__setitem__("plain_gd_eta_0p8_diverged_gt_2p5_exact", "97/300"),
        ))
        tamper("PILLAR4_GD_BOUND", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("plain_gd_eta_0p8_converged_le_2p5_exact", "175/176"))
        tamper("PILLAR4_GD_FMT", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("plain_gd_eta_0p8_diverged_gt_2p5_exact", "97/124/999"))
        tamper("PILLAR4_GD_FMT", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("plain_gd_eta_0p8_diverged_gt_2p5_exact", "a/124"))
        tamper("PILLAR4_GD_FMT", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("plain_gd_eta_0p8_diverged_gt_2p5_exact", "97/b"))
        tamper("PILLAR4_GD_BOUND", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("plain_gd_eta_0p8_diverged_gt_2p5_exact", "0/124"))
        tamper("PILLAR4_GD_BOUND", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("plain_gd_eta_0p8_diverged_gt_2p5_exact", "125/124"))
        tamper("PILLAR4_GD_BOUND", lambda p: p["pillar4_live_circularep_anchor"].__setitem__("plain_gd_eta_0p8_diverged_gt_2p5_exact", "97/123"))
        tamper("PILLAR4_EP_BOUND", lambda p: p["pillar4_live_circularep_anchor"]["ep_gradient_summary"]["test-0016"].__setitem__("exact_1s_ratio_0p01_over_0p002_dec2", "4.00"))
        tamper("PILLAR4_EP_BOUND", lambda p: p["pillar4_live_circularep_anchor"]["ep_gradient_summary"]["test-0016"].__setitem__("exact_1s_ratio_0p01_over_0p002_dec2", "6.00"))
        tamper("PILLAR4_EP_BOUND", lambda p: p["pillar4_live_circularep_anchor"]["ep_gradient_summary"]["test-0016"].__setitem__("exact_centered_ratio_0p01_over_0p002_dec2", "23.00"))
        tamper("PILLAR4_EP_BOUND", lambda p: p["pillar4_live_circularep_anchor"]["ep_gradient_summary"]["test-0016"].__setitem__("exact_centered_ratio_0p01_over_0p002_dec2", "27.00"))
        tamper("PILLAR4_EP_BOUND", lambda p: p["pillar4_live_circularep_anchor"]["ep_gradient_summary"]["test-0016"].__setitem__("t10_beta_0p0005_nosub_err_dec4", "1.0000"))
        tamper("PILLAR4_EP_BOUND", lambda p: p["pillar4_live_circularep_anchor"]["ep_gradient_summary"]["test-0016"].__setitem__("t10_beta_0p0005_sub_err_dec2", "1000.00"))
        tamper("PILLAR4_EP_BOUND", lambda p: p["pillar4_live_circularep_anchor"]["ep_gradient_summary"]["test-0016"].__setitem__("default_E1e6_beta_0p0005_sub_err_dec4", "5.0000"))
        tamper("PILLAR4_EP_BOUND", lambda p: p["pillar4_live_circularep_anchor"]["ep_gradient_summary"]["test-0016"].__setitem__("t10_beta_0p0005_centered_err_dec4", "0.0000"))
        tamper("PILLAR4_EP_BOUND", lambda p: p["pillar4_live_circularep_anchor"]["ep_gradient_summary"]["test-0016"].__setitem__("t10_beta_0p0005_centered_err_dec4", "0.0100"))
        tamper("PILLAR4_EP_BOUND", lambda p: p["pillar4_live_circularep_anchor"]["ep_gradient_summary"]["test-0016"].__setitem__("default_E1e6_beta_0p0005_centered_err_dec4", "0.0000"))
        tamper("PILLAR4_EP_BOUND", lambda p: p["pillar4_live_circularep_anchor"]["ep_gradient_summary"]["test-0016"].__setitem__("default_E1e6_beta_0p0005_centered_err_dec4", "0.0100"))
        tamper("PILLAR4_EP_BOUND", lambda p: p["pillar4_live_circularep_anchor"]["ep_gradient_summary"]["test-0016"].__setitem__("centered_advantage_vs_nosub_t10_dec1", "100.0"))

        # Exact boundary PASS cases on secondary_audit_payload (kill <= -> < mutants)
        for field, val in (
            ("exact_1s_ratio_0p01_over_0p002_dec2", "4.50"),
            ("exact_1s_ratio_0p01_over_0p002_dec2", "5.50"),
            ("exact_centered_ratio_0p01_over_0p002_dec2", "24.00"),
            ("exact_centered_ratio_0p01_over_0p002_dec2", "26.00"),
        ):
            ok_p = copy.deepcopy(self.cert["payload"])
            ok_p["pillar4_live_circularep_anchor"]["ep_gradient_summary"]["test-0016"][field] = val
            self.assertTrue(verifier.secondary_audit_payload(ok_p)["secondary_audit_passed"])

    def test_load_track_artifacts_errors(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "s76_circularep_live_anchor.json").write_bytes((_THIS_DIR / "s76_circularep_live_anchor.json").read_bytes())
            (root / "lean-toolchain").write_bytes(b"\xff\xfe")
            self._assert_s76("INVALID_UTF8", verifier._load_track_artifacts, root)
            (root / "lean-toolchain").write_bytes(b"leanprover/lean4:v4.10.0\n")
            self._assert_s76("TOOLCHAIN_MISMATCH", verifier._load_track_artifacts, root)

    def test_z_cli_modes_and_rejections(self) -> None:
        def run_cli(argv) -> tuple[int, str, str]:
            out_buf = io.StringIO()
            err_buf = io.StringIO()
            with mock.patch.object(verifier.sys, "stdout", out_buf), mock.patch.object(verifier.sys, "stderr", err_buf):
                rc = verifier.main(argv)
            return rc, out_buf.getvalue(), err_buf.getvalue()

        with tempfile.TemporaryDirectory() as td:
            out_p = Path(td) / "cert.json"
            # Run real live Lean 4.36.0 end-to-end via CLI --check, then reuse exact live receipt for flag variants
            rc, out, err = run_cli(["--check", str(_THIS_DIR / "s76_circular_pc_certificate.json"), "--json"])
            self.assertEqual((rc, err), (0, ""))
            chk_obj = json.loads(out)
            self.assertTrue(chk_obj["valid"])
            live_receipt = chk_obj["lean_live"]

            with mock.patch.object(verifier, "verify_lean4_file_live", return_value=live_receipt):
                rc, out, err = run_cli(["--write", str(out_p), "--json"])
                self.assertEqual((rc, err), (0, ""))
                self.assertEqual(stat.S_IMODE(os.lstat(out_p).st_mode), 0o600)
                w_obj = json.loads(out)
                self.assertTrue(w_obj["written"])

                rc, out, err = run_cli(["--write=" + str(out_p)])
                self.assertEqual((rc, err), (0, ""))
                self.assertTrue(out.startswith("WROTE "))

                rc, out, err = run_cli(["--check=" + str(out_p)])
                self.assertEqual((rc, err), (0, ""))
                self.assertTrue(out.startswith("OK "))

                rc, out, err = run_cli(["--standalone"])
                self.assertEqual((rc, err), (0, ""))
                self.assertEqual(out.encode("ascii"), (_THIS_DIR / "s76_circular_pc_certificate.json").read_bytes())

                rc, out, err = run_cli([])
                self.assertEqual((rc, err), (0, ""))
                self.assertTrue(out.startswith("OK "))

                rc, out, err = run_cli(["--json"])
                self.assertEqual((rc, err), (0, ""))
                self.assertTrue(json.loads(out)["valid"])

                with mock.patch.object(verifier.sys, "argv", ["verify_s76_circular_pc.py", "--json"]):
                    rc, out, err = run_cli(None)
                    self.assertEqual((rc, err), (0, ""))
                    self.assertTrue(json.loads(out)["valid"])

            # Error paths
            bad_cases = [
                (123, "INVALID_ARGV"),
                (["--json", "--json"], "DUPLICATE_FLAG"),
                (["--standalone", "--check", str(out_p)], "CONFLICTING_MODE"),
                (["--check", str(out_p), "--standalone"], "CONFLICTING_MODE"),
                (["--check", str(out_p), "--write=" + str(out_p)], "CONFLICTING_MODE"),
                (["--check"], "MISSING_PATH_ARG"),
                (["--check", ""], "INVALID_PATH_ARG"),
                (["--check", "-bad"], "INVALID_PATH_ARG"),
                (["--check="], "INVALID_PATH_ARG"),
                (["--write=-bad"], "INVALID_PATH_ARG"),
                (["--unknown"], "UNKNOWN_FLAG"),
                (["--check\x00"], "NUL_BYTE_FORBIDDEN"),
                (["--check", "a\x00b"], "NUL_BYTE_FORBIDDEN"),
                (["--check", "\ud800"], "INVALID_UTF8_SURROGATE"),
            ]
            for bad_argv, code in bad_cases:
                rc, out, err = run_cli(bad_argv)
                self.assertEqual(rc, 2, f"argv={bad_argv!r}")
                self.assertEqual(out, "")
                self.assertEqual(json.loads(err)["code"], code)
            # Direct _parse_cli_args checks ensure NUL in path arg and default mode string
            self._assert_s76("NUL_BYTE_FORBIDDEN", verifier._parse_cli_args, ["--check", "a\x00b"])
            self.assertEqual(verifier._parse_cli_args([])["mode"], "default")


if __name__ == "__main__":
    unittest.main()
