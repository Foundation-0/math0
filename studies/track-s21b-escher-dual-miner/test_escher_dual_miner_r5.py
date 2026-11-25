#!/usr/bin/env python3
"""Assertion-free R5 adversarial & mutation-killing test suite for Track S21b (R3).

Zero bare asserts (immune to python3 -O). Covers:
  - Full Zone-B strict I/O battery (scalars, canonical lowest-terms rationals, hex64,
    containers, JSON depth/size/floats/constants/dup-keys/surrogates, exact Path type /
    subclass rejection, symlink/ancestor/NUL/CRLF/ENAMETOOLONG paths)
  - Operator 1 (Drawing Hands / Print Gallery): live disk extraction of Track S20d &
    Foundation-0/aletheia-corpus (rejecting `{}` stubs even with matching pins!),
    separate claimed-vs-artifact binding checks across Pillars 1-3, exact-Q MiB rounding,
    strict vs hollow semantic destruction verifiers (incl. RuntimeError/RecursionError),
    callable hook guards, and constructive central-void obstructions
  - Operator 2 (Sky & Water): Markdown table/section parser (escaped pipes, backticks,
    LaTeX math, colon/paren/EOL headers, mixed-verdict preservation, slash-composite atomic
    ID accounting), linear-time bounded defect-span isolator & multi-line passing-tail
    stripper, 6-family obstruction classifier, exact-Q marginal dual-cut coverage matrix,
    greedy trajectory, and exhaustive minimal hitting set solver
  - Parameterized live-disk parity verification on a realistic hermetic tempdir fixture
    (plus fail-closed `{}` stub tamper tests & pin-validation guards)
  - Certificate verification tamper controls, in-memory verify_certificate_dict, and CLI
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence
import copy
from fractions import Fraction
import hashlib
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

_HERE = Path(__file__).resolve().parent
if str(_HERE) not in sys.path:
    sys.path.insert(0, str(_HERE))

import escher_dual_miner_audit as audit
import escher_dual_miner_oracle as emo


def _check(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"R5_CHECK_FAILED: {msg}")


def _expect_error(code: str, fn: object, *args: object, **kwargs: object) -> None:
    if not callable(fn):
        raise RuntimeError("R5_HARNESS_ERROR: fn must be callable")
    try:
        fn(*args, **kwargs)
    except emo.EscherMinerError as exc:
        if exc.code != code:
            raise RuntimeError(f"Expected EscherMinerError({code}), got {exc.code} ({exc.detail})") from exc
        return
    raise RuntimeError(f"Expected EscherMinerError({code}), but call succeeded")


class _IntSub(int):
    pass


class _StrSub(str):
    pass


class _DictSub(dict):
    pass


class _ListSub(list):
    pass


class _FracSub(Fraction):
    pass


class _PathSub(type(Path("."))):
    pass


class _LyingSeq(Sequence):
    def __getitem__(self, idx: int) -> int:
        return 1

    def __len__(self) -> int:
        return 1


class _LyingMap(Mapping):
    def __getitem__(self, key: str) -> int:
        return 1

    def __iter__(self):
        return iter(("a",))

    def __len__(self) -> int:
        return 1


def _flip_hex(digest: str) -> str:
    return ("0" if digest[0] != "0" else "1") + digest[1:]


def _make_signed_cert(payload: dict[str, object], extra: dict[str, object] | None = None) -> dict[str, object]:
    p_sha = emo.canonical_sha256(payload)
    body: dict[str, object] = {"payload": payload, "payload_sha256": p_sha}
    if extra is not None:
        body.update(extra)
    body["certificate_sha256"] = emo.canonical_sha256(body)
    return body


class TestZoneBStrictIO(unittest.TestCase):
    def test_scalars_canonical_fractions_and_hex64(self) -> None:
        _check(emo.MAX_JSON_DEPTH == 64, "MAX_JSON_DEPTH")
        _check(emo.MAX_JSON_BYTES == 2_000_000, "MAX_JSON_BYTES")
        _check(emo.MAX_INT_BITS == 2048, "MAX_INT_BITS")
        _check(emo.MAX_INT_DIGITS == 620, "MAX_INT_DIGITS")
        _check(emo.MAX_EVIDENCE_CHARS == 32_768, "MAX_EVIDENCE_CHARS")
        _check(emo.MIB_BYTES == 1_048_576, "MIB_BYTES")
        _check(audit.SCHEMA_VERSION == "aletheia.track_s21b.escher_self_application_dual_miner.v1", "SCHEMA_VERSION")
        _check(audit.TRACK_ID == "track-s21b-escher-self-application-dual-miner", "TRACK_ID")

        _check(emo.require_str("", "s") == "", "empty str ok by default")
        _check(emo.require_str("ok", "s", non_empty=True) == "ok", "non-empty str")
        _expect_error("EMPTY_STR", emo.require_str, "", "s", non_empty=True)
        _expect_error("INVALID_STR_TYPE", emo.require_str, _StrSub("a"), "s")
        _expect_error("INVALID_STR_TYPE", emo.require_str, 123, "s")
        _expect_error("INVALID_UTF8_SURROGATE", emo.require_str, chr(0xD800), "s")

        _check(emo.require_bool(True, "b") is True, "bool True")
        _check(emo.require_bool(False, "b") is False, "bool False")
        _expect_error("INVALID_BOOL_TYPE", emo.require_bool, 1, "b")
        _expect_error("INVALID_BOOL_TYPE", emo.require_bool, "true", "b")

        max_ok = (1 << 2048) - 1
        _check(emo.require_int(max_ok, "n") == max_ok, "2048-bit boundary ok")
        _check(emo.require_int(-max_ok, "n") == -max_ok, "-2048-bit boundary ok")
        _expect_error("INT_BIT_LIMIT_EXCEEDED", emo.require_int, 1 << 2048, "n")
        _expect_error("INT_BIT_LIMIT_EXCEEDED", emo.require_int, 10**5000, "n")
        _expect_error("INVALID_INT_TYPE", emo.require_int, True, "n")
        _expect_error("INVALID_INT_TYPE", emo.require_int, _IntSub(1), "n")
        _check(emo.require_int(5, "n", min_value=5, max_value=5) == 5, "exact min/max ok")
        _expect_error("INT_BELOW_MIN", emo.require_int, 4, "n", min_value=5)
        _expect_error("INT_ABOVE_MAX", emo.require_int, 6, "n", max_value=5)

        # Canonical lowest-terms rationals
        _check(emo.require_exact_fraction(0, "q") == Fraction(0, 1), "int 0")
        _check(emo.require_exact_fraction(-3, "q") == Fraction(-3, 1), "int frac")
        _check(emo.require_exact_fraction(Fraction(6, 8), "q") == Fraction(3, 4), "Fraction")
        _check(emo.require_exact_fraction("0", "q") == Fraction(0, 1), "str 0")
        _check(emo.require_exact_fraction("-7/4", "q") == Fraction(-7, 4), "str frac")
        _check(emo.require_exact_fraction("1" + "0" * 615, "q") == Fraction(10**615, 1), "616-digit canonical int ok")
        _check(emo._parse_bounded_int_str("0" * 619 + "1", "b") == 1, "bounded int 620 digits ok")
        _expect_error("INT_BIT_LIMIT_EXCEEDED", emo._parse_bounded_int_str, "9" * 620, "b")
        _expect_error("INVALID_INT_LITERAL", emo._parse_bounded_int_str, "", "b")
        _expect_error("INVALID_INT_LITERAL", emo._parse_bounded_int_str, "-", "b")
        _expect_error("INVALID_INT_LITERAL", emo._parse_bounded_int_str, "1_0", "b")
        _expect_error("INVALID_INT_LITERAL", emo._parse_bounded_int_str, "\u0661", "b")
        _expect_error("INT_DIGIT_LIMIT_EXCEEDED", emo._parse_bounded_int_str, "9" * 621, "b")
        _check(emo.fmt_q(Fraction(5, 1)) == "5", "fmt_q int")
        _check(emo.fmt_q(Fraction(3, 4)) == "3/4", "fmt_q frac")

        # Non-canonical rational rejections
        for bad_q in ("007", "-0", "-01", "00", "3/1", "0/1", "0/5", "2/4", "-4/6", "01/2", "1/02", "-0/3"):
            _expect_error("NON_CANONICAL_RATIONAL", emo.require_exact_fraction, bad_q, "q")

        _expect_error("INVALID_FRACTION_TYPE", emo.require_exact_fraction, json.loads("1.5"), "q")
        _expect_error("INVALID_FRACTION_TYPE", emo.require_exact_fraction, True, "q")
        _expect_error("INVALID_FRACTION_TYPE", emo.require_exact_fraction, _FracSub(1, 2), "q")
        _expect_error("INT_BIT_LIMIT_EXCEEDED", emo.require_exact_fraction, Fraction(10**5000, 1), "q")
        _expect_error("INT_BIT_LIMIT_EXCEEDED", emo.require_exact_fraction, Fraction(1, 10**5000), "q")
        _expect_error("INVALID_INT_LITERAL", emo.require_exact_fraction, "", "q")
        _expect_error("INVALID_INT_LITERAL", emo.require_exact_fraction, "-", "q")
        _expect_error("INVALID_INT_LITERAL", emo.require_exact_fraction, "\u0661", "q")
        _expect_error("INVALID_INT_LITERAL", emo.require_exact_fraction, " 1", "q")
        _expect_error("INT_DIGIT_LIMIT_EXCEEDED", emo.require_exact_fraction, "9" * 621, "q")
        _expect_error("INT_BIT_LIMIT_EXCEEDED", emo.require_exact_fraction, "9" * 620, "q")
        _expect_error("NON_POSITIVE_DENOMINATOR", emo.require_exact_fraction, "1/0", "q")
        _expect_error("NON_POSITIVE_DENOMINATOR", emo.require_exact_fraction, "1/-2", "q")
        _expect_error("INVALID_FRACTION_STR", emo.require_exact_fraction, "1/2/3", "q")

        good_a = "0123456789abcdef" * 4
        good_b = _flip_hex(good_a)
        _check(emo.constant_time_hex64_equal(good_a, good_a), "hex64 eq")
        _check(not emo.constant_time_hex64_equal(good_a, good_b), "hex64 neq")
        _expect_error("INVALID_HEX64_LEN", emo.require_hex64_ascii, "a" * 63, "h")
        _expect_error("INVALID_HEX64_LEN", emo.require_hex64_ascii, "a" * 65, "h")
        _expect_error("INVALID_HEX64_CHAR", emo.require_hex64_ascii, "A" * 64, "h")
        _expect_error("INVALID_HEX64_CHAR", emo.constant_time_hex64_equal, "\u00e9" * 64, good_a)
        _expect_error("INVALID_UTF8_SURROGATE", emo.constant_time_hex64_equal, good_a, chr(0xD800) * 64)

        good_40 = "0123456789abcdef" * 2 + "01234567"
        _check(emo.require_hex40_ascii(good_40, "g") == good_40, "hex40 ok")
        _expect_error("INVALID_HEX40_LEN", emo.require_hex40_ascii, "a" * 39, "g")
        _expect_error("INVALID_HEX40_LEN", emo.require_hex40_ascii, "a" * 41, "g")
        _expect_error("INVALID_HEX40_CHAR", emo.require_hex40_ascii, "A" * 40, "g")

    def test_containers_json_and_paths(self) -> None:
        _check(emo.require_exact_dict({"a": 1}, "d") == {"a": 1}, "dict ok")
        _expect_error("INVALID_DICT_TYPE", emo.require_exact_dict, _DictSub({"a": 1}), "d")
        _expect_error("INVALID_DICT_TYPE", emo.require_exact_dict, _LyingMap(), "d")
        _expect_error("INVALID_STR_TYPE", emo.require_exact_dict, {1: "a"}, "d")
        _expect_error("INVALID_UTF8_SURROGATE", emo.require_exact_dict, {chr(0xD800): 1}, "d")

        _check(emo.require_exact_list([], "l") == [], "empty list ok")
        _check(emo.require_exact_list([1], "l", non_empty=True) == [1], "non-empty list ok")
        _expect_error("EMPTY_LIST", emo.require_exact_list, [], "l", non_empty=True)
        _expect_error("INVALID_LIST_TYPE", emo.require_exact_list, _ListSub([1]), "l")
        _expect_error("INVALID_LIST_TYPE", emo.require_exact_list, _LyingSeq(), "l")

        emo.validate_json_value({"n": None, "b": True, "i": 1, "s": "x", "l": [1, 2]}, max_depth=2)
        _expect_error("JSON_DEPTH_EXCEEDED", emo.validate_json_value, {"a": {"b": 1}}, max_depth=1)
        _expect_error("UNSUPPORTED_JSON_TYPE", emo.validate_json_value, {"f": json.loads("1.25")})
        _expect_error("UNSUPPORTED_JSON_TYPE", emo.validate_json_value, (1, 2))
        _expect_error("INVALID_UTF8_SURROGATE", emo.validate_json_value, {"x": chr(0xD800)})
        _expect_error("INVALID_UTF8_SURROGATE", emo.validate_json_value, {chr(0xDC00): 1})
        cyc: dict[str, object] = {}
        cyc["self"] = cyc
        _expect_error("JSON_DEPTH_EXCEEDED", emo.validate_json_value, cyc)

        _check(emo.parse_strict_json_text('{"k":1}') == {"k": 1}, "strict json obj")
        _check(emo.parse_strict_json_text("[1,2]", require_object=False) == [1, 2], "strict json list")
        _expect_error("INVALID_BOOL_TYPE", emo.parse_strict_json_text, "[1,2]", require_object=0)
        _expect_error("JSON_ROOT_NOT_OBJECT", emo.parse_strict_json_text, "[1,2]", require_object=True)
        _expect_error("JSON_DUPLICATE_KEY", emo.parse_strict_json_text, '{"a":1,"a":2}')
        _expect_error("JSON_FLOAT_FORBIDDEN", emo.parse_strict_json_text, '{"x":1.0}')
        _expect_error("JSON_CONSTANT_FORBIDDEN", emo.parse_strict_json_text, '{"x":NaN}')
        _expect_error("INT_DIGIT_LIMIT_EXCEEDED", emo.parse_strict_json_text, '{"x":' + "9" * 5000 + "}")
        _expect_error("JSON_SYNTAX_ERROR", emo.parse_strict_json_text, "{bad")
        _expect_error("JSON_TOO_LARGE", emo.parse_strict_json_text, '{"a":"' + "x" * 20 + '"}', max_bytes=16)
        _check(emo.parse_strict_json_text('{"a":1}', max_bytes=7) == {"a": 1}, "exact max_bytes ok")
        _expect_error("INVALID_UTF8_SURROGATE", emo.parse_strict_json_text, '{"a":"\\ud800"}')

        # Exact pathlib.Path type enforcement (rejects Path subclasses)
        _expect_error("INVALID_PATH_TYPE", emo.require_no_symlink_path, "not-a-path")
        _expect_error("INVALID_PATH_TYPE", emo.require_no_symlink_path, _PathSub("."))
        _expect_error("INVALID_PATH_NUL", emo.require_no_symlink_path, Path("a\x00b"))
        _expect_error("INVALID_UTF8_SURROGATE", emo.require_no_symlink_path, Path(chr(0xD800)))
        for bad_pwd in (chr(0xD800), "a\x00b"):
            with patch.object(emo.os, "environ", {"PWD": bad_pwd}):
                emo.require_no_symlink_path(Path("relative_safe_name.json"))
        _expect_error("FILE_NOT_FOUND", emo.read_strict_utf8_file, Path("a" * 5000))
        _expect_error("FILE_NOT_FOUND", emo.read_strict_utf8_file, Path("."))
        _expect_error("FILE_NOT_FOUND", emo.read_strict_utf8_file, Path("/"))

        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            real = root / "ok.txt"
            real.write_bytes(b"hello\n")
            raw, text = emo.read_strict_utf8_file(real, max_bytes=6)
            _check(raw == b"hello\n" and text == "hello\n", "exact file size ok")
            _expect_error("FILE_TOO_LARGE", emo.read_strict_utf8_file, real, max_bytes=5)

            sym = root / "link.txt"
            sym.symlink_to(real)
            _expect_error("SYMLINK_FORBIDDEN", emo.read_strict_utf8_file, sym)

            sub = root / "realdir"
            sub.mkdir()
            (sub / "f.txt").write_bytes(b"ok\n")
            nested = sub / "nested"
            nested.mkdir()
            (nested / "g.txt").write_bytes(b"ok\n")
            symdir = root / "linkdir"
            symdir.symlink_to(sub)
            _expect_error("SYMLINK_ANCESTOR_FORBIDDEN", emo.read_strict_utf8_file, symdir / "f.txt")

            # Relative paths under symlinked PWD (direct & nested) refused, absolute & unrelated PWD allowed
            old_cwd = os.getcwd()
            old_pwd = os.environ.get("PWD")
            try:
                os.chdir(sub)
                os.environ["PWD"] = str(symdir)
                _expect_error("SYMLINK_ANCESTOR_FORBIDDEN", emo.require_no_symlink_path, Path("f.txt"))
                emo.require_no_symlink_path(real)  # absolute path unaffected by symlinked PWD
                os.chdir(nested)
                os.environ["PWD"] = str(symdir / "nested")
                _expect_error("SYMLINK_ANCESTOR_FORBIDDEN", emo.require_no_symlink_path, Path("g.txt"))
                os.environ["PWD"] = str(symdir)  # stale PWD != cwd must not falsely reject
                emo.require_no_symlink_path(Path("g.txt"))
                raw_rel, txt_rel = emo.read_strict_utf8_file(Path("g.txt"))
                _check(raw_rel == b"ok\n" and txt_rel == "ok\n", "relative read_strict_utf8_file ok")
                os.environ["PWD"] = str(root / "nonexistent_pwd")
                emo.require_no_symlink_path(Path("g.txt"))
            finally:
                os.chdir(old_cwd)
                if old_pwd is None:
                    os.environ.pop("PWD", None)
                else:
                    os.environ["PWD"] = old_pwd

            _expect_error("FILE_NOT_FOUND", emo.read_strict_utf8_file, root / "missing.txt")
            _expect_error("FILE_NOT_FOUND", emo.read_strict_utf8_file, sub)

            # Scratch FIFO inside TemporaryDirectory fails closed without blocking
            fifo_path = root / "scratch.fifo"
            os.mkfifo(fifo_path)
            _expect_error("FILE_NOT_FOUND", emo.read_strict_utf8_file, fifo_path)

            # Unreadable file (chmod 000) fails closed with FILE_READ_ERROR (zero raw PermissionError)
            unreadable = root / "unreadable.json"
            unreadable.write_bytes(b"{}\n")
            os.chmod(unreadable, 0)
            try:
                if os.geteuid() != 0:
                    _expect_error("FILE_READ_ERROR", emo.read_strict_utf8_file, unreadable)
                    err_un = io.StringIO()
                    with patch.object(sys, "stderr", err_un):
                        rc_un = audit.main(["--check", str(unreadable)])
                    _check(rc_un == 1 and "FAIL FILE_READ_ERROR" in err_un.getvalue(), "CLI chmod 000 fails closed")
            finally:
                os.chmod(unreadable, 0o600)

            # Virtual procfs streaming read cap (st_size==0 must still enforce max_bytes)
            proc_kallsyms = Path("/proc/kallsyms")
            if proc_kallsyms.is_file():
                _expect_error("FILE_TOO_LARGE", emo.read_strict_utf8_file, proc_kallsyms, max_bytes=64)

            # Atomic dir_fd O_NOFOLLOW TOCTOU / OSError branches
            import errno as _errno
            with patch.object(emo.os, "open", side_effect=OSError(_errno.EACCES, "denied")):
                _expect_error("FILE_READ_ERROR", emo._open_regular_file_nofollow, real)
            real_open = os.open
            call_n = {"n": 0}
            def _eloop_dir(p_arg: str, flags: int, *a: object, **kw: object) -> int:
                call_n["n"] += 1
                if call_n["n"] == 2:
                    raise OSError(_errno.ELOOP, "symlink dir")
                return real_open(p_arg, flags, *a, **kw)
            with patch.object(emo.os, "open", side_effect=_eloop_dir):
                _expect_error("SYMLINK_ANCESTOR_FORBIDDEN", emo._open_regular_file_nofollow, sub / "f.txt")
            def _eloop_leaf(p_arg: str, flags: int, *a: object, **kw: object) -> int:
                if p_arg == "ok.txt":
                    raise OSError(_errno.ELOOP, "symlink leaf")
                return real_open(p_arg, flags, *a, **kw)
            with patch.object(emo.os, "open", side_effect=_eloop_leaf):
                _expect_error("SYMLINK_FORBIDDEN", emo._open_regular_file_nofollow, real)
            with patch.object(emo.os, "fstat", side_effect=OSError(_errno.EIO, "fstat io")):
                _expect_error("FILE_READ_ERROR", emo.read_strict_utf8_file, real)
            with patch.object(emo.os, "read", side_effect=OSError(_errno.EIO, "read io")):
                _expect_error("FILE_READ_ERROR", emo.read_strict_utf8_file, real)
            # Multi-chunk streaming cap test (emulating st_size=0 virtual file > byte_limit)
            fake_st = os.stat(real)
            fake_zero_st = type(fake_st)((fake_st.st_mode, 0, 0, 0, 0, 0, 0, 0, 0, 0))
            with patch.object(emo.os, "fstat", return_value=fake_zero_st):
                _expect_error("FILE_TOO_LARGE", emo.read_strict_utf8_file, real, max_bytes=3)

            crlf = root / "crlf.txt"
            crlf.write_bytes(b"a\r\nb\n")
            _expect_error("CR_LINE_ENDINGS_FORBIDDEN", emo.read_strict_utf8_file, crlf)

            bad_utf8 = root / "bad.bin"
            bad_utf8.write_bytes(b"\xff\xfe")
            _expect_error("INVALID_UTF8", emo.read_strict_utf8_file, bad_utf8)


class TestOperator1SelfApplication(unittest.TestCase):
    def test_mib_rounding_bindings_and_provenance_edges(self) -> None:
        ok_r = emo.check_exact_mib_rounding(1_048_576, 100)
        _check(ok_r["within_half_ulp"] is True and ok_r["abs_residual_q"] == "0", "exact 1 MiB")
        exact_half = emo.check_exact_mib_rounding(1_048_576 + 5242, 100)
        _check(exact_half["within_half_ulp"] is True, "just under 1/200")
        over_half = emo.check_exact_mib_rounding(1_048_576 + 5243, 100)
        _check(over_half["within_half_ulp"] is False, "just over 1/200")
        _expect_error("INT_BELOW_MIN", emo.check_exact_mib_rounding, -1, 0)
        _expect_error("INT_BELOW_MIN", emo.check_exact_mib_rounding, 0, -1)

        b_ok = emo.verify_prose_artifact_bindings([
            {
                "id": "r1",
                "kind": "integer_range_binding",
                "claimed_count": 3,
                "claimed_min": 1,
                "claimed_max": 5,
                "artifact_count": 3,
                "artifact_min": 1,
                "artifact_max": 5,
            },
            {
                "id": "c1",
                "kind": "c_allocation_table",
                "claimed_hot_bytes": 10,
                "claimed_cache_limit_bytes": 10,
                "claimed_fits_cache": True,
                "allocated_arrays": [
                    {"name": "a", "bytes": 10, "hot_read": True},
                    {"name": "b", "bytes": 5, "hot_read": False},
                ],
            },
        ])
        _check(b_ok["passed"] is True, "bindings pass")
        for bad_rec in (
            {"id": "x", "kind": "integer_range_binding", "claimed_count": 2, "claimed_min": 1, "claimed_max": 5, "artifact_count": 3, "artifact_min": 1, "artifact_max": 5},
            {"id": "x", "kind": "integer_range_binding", "claimed_count": 3, "claimed_min": 2, "claimed_max": 5, "artifact_count": 3, "artifact_min": 1, "artifact_max": 5},
            {"id": "x", "kind": "integer_range_binding", "claimed_count": 3, "claimed_min": 1, "claimed_max": 4, "artifact_count": 3, "artifact_min": 1, "artifact_max": 5},
        ):
            _check(emo.verify_prose_artifact_bindings([bad_rec])["passed"] is False, "range mismatch")

        c_hot_bad = emo.verify_prose_artifact_bindings([{
            "id": "c_hot_bad",
            "kind": "c_allocation_table",
            "claimed_hot_bytes": 9,
            "claimed_cache_limit_bytes": 10,
            "claimed_fits_cache": True,
            "allocated_arrays": [{"name": "a", "bytes": 10, "hot_read": True}],
        }])
        _check(c_hot_bad["passed"] is False, "hot mismatch fails even if cache fit matches")
        c_fit_bad = emo.verify_prose_artifact_bindings([{
            "id": "c_fit_bad",
            "kind": "c_allocation_table",
            "claimed_hot_bytes": 11,
            "claimed_cache_limit_bytes": 10,
            "claimed_fits_cache": True,
            "allocated_arrays": [{"name": "a", "bytes": 11, "hot_read": True}],
        }])
        _check(c_fit_bad["passed"] is False, "cache fit mismatch fails even if hot bytes match")
        _expect_error("INVALID_INT_TYPE", emo.verify_prose_artifact_bindings, [{
            "id": "c_partial_fits",
            "kind": "c_allocation_table",
            "claimed_hot_bytes": 10,
            "claimed_fits_cache": True,
            "allocated_arrays": [{"name": "a", "bytes": 10, "hot_read": True}],
        }])
        _expect_error("INVALID_BOOL_TYPE", emo.verify_prose_artifact_bindings, [{
            "id": "c_partial_limit",
            "kind": "c_allocation_table",
            "claimed_hot_bytes": 10,
            "claimed_cache_limit_bytes": 10,
            "allocated_arrays": [{"name": "a", "bytes": 10, "hot_read": True}],
        }])
        _expect_error("DUPLICATE_ARRAY_NAME", emo.verify_prose_artifact_bindings, [{
            "id": "dup",
            "kind": "c_allocation_table",
            "claimed_hot_bytes": 2,
            "allocated_arrays": [
                {"name": "a", "bytes": 1, "hot_read": True},
                {"name": "a", "bytes": 1, "hot_read": True},
            ],
        }])
        _expect_error("UNKNOWN_BINDING_KIND", emo.verify_prose_artifact_bindings, [{"id": "u", "kind": "other"}])

        _check(emo.verify_provenance_claims([{
            "id": "s1",
            "kind": "spec_completeness",
            "required_clauses": ["a", "b"],
            "implemented_clauses": ["a"],
            "claimed_exact_spec_equivalence": False,
        }])["passed"] is True, "partial spec allowed when not claimed exact")
        _check(emo.verify_provenance_claims([{
            "id": "s2",
            "kind": "spec_completeness",
            "required_clauses": ["a", "b"],
            "implemented_clauses": ["a"],
            "claimed_exact_spec_equivalence": True,
        }])["passed"] is False, "partial spec rejected when claimed exact")
        _check(emo.verify_provenance_claims([{
            "id": "d1",
            "kind": "delivery_scope",
            "claimed_scope_tier": "production_deployment",
            "witnessed_scope_tier": "research_prototype",
        }])["passed"] is False, "scope overclaim rejected")
        _expect_error("UNKNOWN_SCOPE_TIER", emo.verify_provenance_claims, [{
            "id": "d2", "kind": "delivery_scope", "claimed_scope_tier": "bad", "witnessed_scope_tier": "research_prototype",
        }])
        _expect_error("UNKNOWN_SCOPE_TIER", emo.verify_provenance_claims, [{
            "id": "d3", "kind": "delivery_scope", "claimed_scope_tier": "research_prototype", "witnessed_scope_tier": "bad",
        }])
        for bad_m in (
            {"id": "m1", "kind": "metric_attribution", "claimed_subject": "A", "measured_subject": "A", "claimed_provenance": "same_experiment_measurement", "witness_provenance": "cross_experiment_anchor", "experiment_executed_for_claimed_subject": True},
            {"id": "m2", "kind": "metric_attribution", "claimed_subject": "A", "measured_subject": "B", "claimed_provenance": "same_experiment_measurement", "witness_provenance": "same_experiment_measurement", "experiment_executed_for_claimed_subject": True},
            {"id": "m3", "kind": "metric_attribution", "claimed_subject": "A", "measured_subject": "A", "claimed_provenance": "same_experiment_measurement", "witness_provenance": "same_experiment_measurement", "experiment_executed_for_claimed_subject": False},
            {"id": "m4", "kind": "metric_attribution", "claimed_subject": "A", "measured_subject": "B", "claimed_provenance": "cross_experiment_anchor", "witness_provenance": "unmeasured_hypothesis", "experiment_executed_for_claimed_subject": False},
        ):
            _check(emo.verify_provenance_claims([bad_m])["passed"] is False, f"bad metric {bad_m['id']}")
        _check(emo.verify_provenance_claims([{
            "id": "m5", "kind": "metric_attribution", "claimed_subject": "A", "measured_subject": "B",
            "claimed_provenance": "unmeasured_hypothesis", "witness_provenance": "unmeasured_hypothesis",
            "experiment_executed_for_claimed_subject": False,
        }])["passed"] is True, "unmeasured hypothesis allowed")
        _expect_error("UNKNOWN_METRIC_PROVENANCE", emo.verify_provenance_claims, [{
            "id": "m6", "kind": "metric_attribution", "claimed_subject": "A", "measured_subject": "A",
            "claimed_provenance": "bad", "witness_provenance": "cross_experiment_anchor", "experiment_executed_for_claimed_subject": True,
        }])
        _expect_error("UNKNOWN_METRIC_PROVENANCE", emo.verify_provenance_claims, [{
            "id": "m7", "kind": "metric_attribution", "claimed_subject": "A", "measured_subject": "A",
            "claimed_provenance": "cross_experiment_anchor", "witness_provenance": "bad", "experiment_executed_for_claimed_subject": True,
        }])
        _expect_error("UNKNOWN_PROVENANCE_KIND", emo.verify_provenance_claims, [{"id": "u", "kind": "other"}])

    def test_semantic_destruction_hooks_and_non_tautological_self_application(self) -> None:
        base = {
            "nested": {"m": {"k": 1}, "arr": [1], "h": "0" * 64, "h2": "a" * 64, "n": 5, "empty_d": {}, "empty_l": [], "scalar": 1},
            "sig": "0" * 64,
        }
        _expect_error("VERIFIER_NOT_CALLABLE", emo.run_semantic_destruction_gate, "nope", base, [{"id": "p", "op": "drop_required_field", "path": ["sig"]}])
        _expect_error("INVALID_VERIFIER_RETURN_TYPE", emo.run_semantic_destruction_gate, lambda w: 1, base, [{"id": "p", "op": "drop_required_field", "path": ["sig"]}])
        rej = emo.run_semantic_destruction_gate(lambda w: False, base, [{"id": "p", "op": "drop_required_field", "path": ["sig"]}])
        _check(rej["verdict"] == "VALID_WITNESS_REJECTED" and rej["passed"] is False, "always-false verifier rejected")

        # RuntimeError / RecursionError / ZeroDivisionError inside verifier_fn map cleanly to False
        def _boom_runtime(_w: dict[str, object]) -> bool:
            raise RuntimeError("boom")

        def _boom_recursion(_w: dict[str, object]) -> bool:
            raise RecursionError("deep")

        _check(emo._invoke_verifier_strict(_boom_runtime, base) is False, "RuntimeError -> False")
        _check(emo._invoke_verifier_strict(_boom_recursion, base) is False, "RecursionError -> False")

        # Non-callable hooks and missing required snapshot keys fail closed
        for fn in (emo.evaluate_s20d_self_application, emo.evaluate_corpus_self_application):
            _expect_error("INVALID_HOOK_CALLABLE", fn, bind_fn="bad")
            _expect_error("INVALID_HOOK_CALLABLE", fn, prov_fn="bad")
            _expect_error("INVALID_HOOK_CALLABLE", fn, destruct_fn="bad")
            _expect_error("MISSING_REQUIRED_KEY", fn, {"claimed": {}, "artifact": {}, "file_sha256": {}})

        d0 = emo._apply_semantic_destruction(base, {"op": "corrupt_pinned_hash", "path": ["nested", "h"]})
        _check(d0["nested"]["h"].startswith("1"), "flip 0 -> 1")
        da = emo._apply_semantic_destruction(base, {"op": "corrupt_pinned_hash", "path": ["nested", "h2"]})
        _check(da["nested"]["h2"].startswith("0"), "flip a -> 0")

        _expect_error("DESTRUCTION_PATH_MISSING", emo._apply_semantic_destruction, base, {"op": "drop_required_field", "path": ["missing", "x"]})
        _expect_error("DESTRUCTION_PATH_MISSING", emo._apply_semantic_destruction, base, {"op": "drop_required_field", "path": ["nested", "scalar", "x", "y"]})
        _expect_error("DESTRUCTION_PARENT_NOT_DICT", emo._apply_semantic_destruction, {"a": 1}, {"op": "drop_required_field", "path": ["a", "b"]})
        _expect_error("DESTRUCTION_LEAF_MISSING", emo._apply_semantic_destruction, base, {"op": "drop_required_field", "path": ["nested", "nope"]})
        _expect_error("TARGET_NOT_NONEMPTY_DICT", emo._apply_semantic_destruction, base, {"op": "empty_mapping_field", "path": ["nested", "scalar"]})
        _expect_error("TARGET_NOT_NONEMPTY_DICT", emo._apply_semantic_destruction, base, {"op": "empty_mapping_field", "path": ["nested", "empty_d"]})
        _expect_error("TARGET_NOT_NONEMPTY_LIST", emo._apply_semantic_destruction, base, {"op": "replace_list_with_arbitrary_dict", "path": ["nested", "scalar"]})
        _expect_error("TARGET_NOT_NONEMPTY_LIST", emo._apply_semantic_destruction, base, {"op": "replace_list_with_arbitrary_dict", "path": ["nested", "empty_l"]})
        _expect_error("UNKNOWN_DESTRUCTION_OP", emo._apply_semantic_destruction, base, {"op": "bogus", "path": ["nested", "n"]})
        _expect_error("RESIGN_FIELD_MISSING", emo._apply_semantic_destruction, base, {"op": "invert_numeric_claim", "path": ["nested", "n"], "resign_hash_field": "missing_sig"})

        w, csha = emo._make_s20d_self_witness()
        strict = emo._strict_pinned_cert_verifier(csha, w["payload_sha256"])
        _check(strict(copy.deepcopy(w)) is True, "strict accepts valid")
        bad_p = copy.deepcopy(w)
        bad_p["payload_sha256"] = _flip_hex(w["payload_sha256"])
        bad_p_body = {k: v for k, v in bad_p.items() if k != "certificate_sha256"}
        bad_p_csha = emo.canonical_sha256(bad_p_body)
        bad_p["certificate_sha256"] = bad_p_csha
        _check(emo._strict_pinned_cert_verifier(bad_p_csha, w["payload_sha256"])(bad_p) is False, "strict rejects forged payload_sha")
        _check(emo._strict_pinned_cert_verifier(csha, _flip_hex(w["payload_sha256"]))(copy.deepcopy(w)) is False, "strict rejects expected_payload_sha mismatch")
        bad_c = copy.deepcopy(w)
        bad_c["certificate_sha256"] = _flip_hex(csha)
        _check(strict(bad_c) is False, "strict rejects cert_sha mismatch")
        _check(emo._strict_pinned_cert_verifier(_flip_hex(csha), w["payload_sha256"])(copy.deepcopy(w)) is False, "strict rejects expected_cert_sha mismatch")

        # Full Operator 1 outputs + witness_basis check
        op1a = emo.evaluate_s20d_self_application()
        _check(op1a["fixed_points_closed"] == 5 and op1a["central_void_count"] == 4, "S20d 5/9 closure")
        _check(op1a["pillar3_strict_survivals"] == 0 and op1a["pillar3_hollow_survivals"] == 4, "S20d P3")
        _check(op1a["internal_closure_share_q"] == "5/9" and op1a["irreducible_void_share_q"] == "4/9", "S20d Q")
        _check(all("witness_basis" in v for v in op1a["central_void"]), "S20d witness_basis tagged")

        # Non-tautology: mutating claimed vs artifact genuinely flips fixed points to closed=False
        for mut_key in ("cert_file_sha256", "payload_sha256", "certificate_sha256"):
            s_bad = copy.deepcopy(emo.PINNED_S20D_SNAPSHOT)
            s_bad["claimed"][mut_key] = "0" * 64
            res_bad = emo.evaluate_s20d_self_application(s_bad)
            _check(res_bad["pillar1_passed"] is False and res_bad["fixed_points"][0]["closed"] is False and res_bad["fixed_points_closed"] == 4, f"S20d digest drift {mut_key}")

        s_bad_p1 = copy.deepcopy(emo.PINNED_S20D_SNAPSHOT)
        s_bad_p1["claimed"]["family_max"] = 4
        res_bad_p1 = emo.evaluate_s20d_self_application(s_bad_p1)
        _check(res_bad_p1["pillar1_passed"] is False and res_bad_p1["fixed_points"][0]["closed"] is False, "S20d claimed != artifact range fails")

        s_bad_p2 = copy.deepcopy(emo.PINNED_S20D_SNAPSHOT)
        s_bad_p2["artifact"]["implemented_zone_b_clauses"].pop()
        _check(emo.evaluate_s20d_self_application(s_bad_p2)["pillar2_passed"] is False, "S20d missing AST clause fails")

        s_bad_runs = copy.deepcopy(emo.PINNED_S20D_SNAPSHOT)
        s_bad_runs["artifact"]["s19a_runs_sum"] = 335
        _check(emo.evaluate_s20d_self_application(s_bad_runs)["fixed_points"][4]["closed"] is False, "S20d runs drift fails")

        op1b = emo.evaluate_corpus_self_application()
        _check(op1b["fixed_points_closed"] == 6 and op1b["central_void_count"] == 4, "corpus 6/10 closure")
        _check(op1b["all_readme_mib_within_half_ulp"] is True, "all 8 README MiBs within 1/200")
        _check(op1b["pillar3_strict_survivals"] == 0 and op1b["pillar3_hollow_survivals"] == 2, "corpus P3")
        _check(op1b["inclusion_tower"]["strictly_increasing"] is True, "4-layer tower")
        _check(op1b["internal_closure_share_q"] == "3/5" and op1b["irreducible_void_share_q"] == "2/5", "corpus Q")
        _check(all("witness_basis" in v for v in op1b["central_void"]), "corpus witness_basis tagged")

        # Corpus non-tautology: README count drift, p1 drift, MiB drift, and EVERY tower condition!
        c_bad_readme = copy.deepcopy(emo.PINNED_CORPUS_SNAPSHOT)
        c_bad_readme["claimed"]["swarm_cutoff_seq"] = 999
        res_bad_rm = emo.evaluate_corpus_self_application(c_bad_readme)
        _check(res_bad_rm["pillar1_passed"] is False and res_bad_rm["fixed_points"][0]["closed"] is False, "corpus README drift fails")

        c_bad_p1 = copy.deepcopy(emo.PINNED_CORPUS_SNAPSHOT)
        c_bad_p1["claimed"]["compiled_bytes"] += 1
        res_bad_p1 = emo.evaluate_corpus_self_application(c_bad_p1)
        _check(res_bad_p1["pillar1_passed"] is False and res_bad_p1["fixed_points"][0]["closed"] is False, "corpus compiled bytes drift fails")

        c_bad_mib = copy.deepcopy(emo.PINNED_CORPUS_SNAPSHOT)
        c_bad_mib["claimed"]["total_centi_mib"] = 39900
        _check(emo.evaluate_corpus_self_application(c_bad_mib)["all_readme_mib_within_half_ulp"] is False, "corpus MiB drift fails")

        for field, val in (
            ("layer1_corpus_manifest_files", 2431),
            ("layer2_sha256sums_files", 2435),
            ("layer3_git_tracked_files", 2436),
            ("sha256sums_minus_manifest", []),
            ("manifest_excludes_self_and_sha256sums", False),
            ("sha256sums_excludes_self", False),
        ):
            c_bad_t = copy.deepcopy(emo.PINNED_CORPUS_SNAPSHOT)
            c_bad_t["artifact"]["inclusion_tower"][field] = val
            _check(emo.evaluate_corpus_self_application(c_bad_t)["inclusion_tower"]["strictly_increasing"] is False, f"tower {field}")

        # Fail-closed list validation on corpus snapshot fields (no raw KeyError/TypeError)
        c_drop_smm = copy.deepcopy(emo.PINNED_CORPUS_SNAPSHOT)
        del c_drop_smm["artifact"]["inclusion_tower"]["sha256sums_minus_manifest"]
        _expect_error("INVALID_LIST_TYPE", emo.evaluate_corpus_self_application, c_drop_smm)
        c_int_smm = copy.deepcopy(emo.PINNED_CORPUS_SNAPSHOT)
        c_int_smm["artifact"]["inclusion_tower"]["sha256sums_minus_manifest"] = 123
        _expect_error("INVALID_LIST_TYPE", emo.evaluate_corpus_self_application, c_int_smm)
        for section in ("claimed", "artifact"):
            c_int_tt = copy.deepcopy(emo.PINNED_CORPUS_SNAPSHOT)
            c_int_tt[section]["torus_tracks"] = 123
            _expect_error("INVALID_LIST_TYPE", emo.evaluate_corpus_self_application, c_int_tt)
            c_empty_tt = copy.deepcopy(emo.PINNED_CORPUS_SNAPSHOT)
            c_empty_tt[section]["torus_tracks"] = []
            _expect_error("EMPTY_LIST", emo.evaluate_corpus_self_application, c_empty_tt)

        # R3 honest git metadata guards (no fabrication when .git absent!)
        c_no_git = copy.deepcopy(emo.PINNED_CORPUS_SNAPSHOT)
        c_no_git["artifact"]["inclusion_tower"]["git_metadata_source"] = "unavailable_no_git_dir"
        c_no_git["artifact"]["inclusion_tower"]["layer3_git_tracked_files"] = None
        c_no_git["artifact"]["inclusion_tower"]["head_commit"] = None
        c_no_git["artifact"]["inclusion_tower"]["head_tree"] = None
        res_ng = emo.evaluate_corpus_self_application(c_no_git)
        _check(res_ng["inclusion_tower"]["strictly_increasing"] is False, "no-git cannot close 4-layer tower")
        _check(res_ng["inclusion_tower"]["layer3_git_tracked_files"] is None, "no-git l3 is None")
        _check(res_ng["inclusion_tower"]["head_commit"] is None and res_ng["inclusion_tower"]["head_tree"] is None, "no-git shas None")

        c_bad_src = copy.deepcopy(emo.PINNED_CORPUS_SNAPSHOT)
        c_bad_src["artifact"]["inclusion_tower"]["git_metadata_source"] = "fabricated"
        _expect_error("INVALID_GIT_METADATA_SOURCE", emo.evaluate_corpus_self_application, c_bad_src)

        c_unexp_git = copy.deepcopy(c_no_git)
        c_unexp_git["artifact"]["inclusion_tower"]["layer3_git_tracked_files"] = 2437
        _expect_error("UNEXPECTED_GIT_METADATA", emo.evaluate_corpus_self_application, c_unexp_git)


class TestOperator2DualComplexMiner(unittest.TestCase):
    def test_markdown_parser_mixed_verdicts_and_linear_classifier(self) -> None:
        row = r"| **AUDIT-T1** | 2026 | a | `\` `x|y` `$` $\alpha\|v\|$ | G1 | exact | N1 | **`VERIFIED`** | ok\ |"
        cells = emo.split_markdown_table_row(row)
        _check(len(cells) == 9 and cells[0] == "**AUDIT-T1**" and cells[8] == "ok\\", "9-col split")
        cells2 = emo.split_markdown_table_row("a|b\\")
        _check(cells2 == ["a", "b\\"], "no outer pipes + trailing backslash")
        _check(emo.split_markdown_table_row("| `$` | $u|v$ | `x|y` |") == ["`$`", "$u|v$", "`x|y`"], "math and backtick pipes preserved")
        _expect_error("INVALID_AUDIT_IDS_TYPE", emo.expand_atomic_audit_ids, "AUDIT-1")
        _expect_error("INVALID_AUDIT_IDS_TYPE", emo.expand_atomic_audit_ids, 123)

        # Mixed verdicts preserved & advisory/upgrade verdicts handled accurately
        _check(emo.extract_primary_verdict("**DUAL-CONTINENT `VERIFIED`** (`0`)") == "VERIFIED", "dual-continent")
        _check(emo.extract_primary_verdict("**`VERIFIED`** *(upgraded from `PARTIAL/FRAGILE`)*") == "VERIFIED", "upgraded verified")
        _check(emo.extract_primary_verdict("**`VERIFIED` (with routing advisory)**") == "VERIFIED", "verified advisory")
        _check(emo.extract_primary_verdict("`VERIFIED`") == "VERIFIED", "backtick verified")
        _check(emo.extract_primary_verdict("**`FALSIFIED`** (x)") == "FALSIFIED", "falsified")
        _check(emo.extract_primary_verdict("**`PARTIAL/FRAGILE`** (x)") == "PARTIAL/FRAGILE", "partial")
        _check(emo.extract_primary_verdict("**`VERIFIED` / `PARTIAL/FRAGILE`**") == "PARTIAL/FRAGILE", "mixed verified/partial")
        _check(emo.extract_primary_verdict("**`VERIFIED` / `FALSIFIED`**") == "FALSIFIED", "mixed verified/falsified")
        _check(emo.extract_primary_verdict("**`VERIFIED`** / **`PARTIAL/FRAGILE`**") == "PARTIAL/FRAGILE", "R3 separate-bold mixed partial")
        _check(emo.extract_primary_verdict("**`VERIFIED`** / **`FALSIFIED`**") == "FALSIFIED", "R3 separate-bold mixed falsified")
        _check(emo.extract_primary_verdict("**`VERIFIED`** / `PARTIAL/FRAGILE`") == "PARTIAL/FRAGILE", "R3 bold+backtick mixed partial")
        _check(emo.extract_primary_verdict("`VERIFIED` / `PARTIAL/FRAGILE`") == "PARTIAL/FRAGILE", "R3 backtick+backtick mixed partial")
        _check(emo.extract_primary_verdict("**`VERIFIED` (REPOS) / `1` PROSE-ONLY TYPO IN ISSUE BODY**") == "PARTIAL/FRAGILE", "real mixed prose typo")
        _expect_error("UNPARSEABLE_VERDICT", emo.extract_primary_verdict, "no verdict")
        _expect_error("UNKNOWN_VERDICT_TOKEN", emo.extract_primary_verdict, "**`BOGUS`**")
        _expect_error("UNKNOWN_VERDICT_TOKEN", emo.extract_primary_verdict, "`BOGUS`")
        _expect_error("UNKNOWN_VERDICT_TOKEN", emo.extract_primary_verdict, "**`VERIFIED`** / **`BOGUS`**")

        sample_md = "\n".join([
            "# Log",
            "| **AUDIT-T1** | 2026 | a | tgt | G1 | exact | N1 | **`VERIFIED`** | clean |",
            "| **AUDIT-T2** | 2026 | a | tgt | **`PARTIAL/FRAGILE`** (**HOWEVER** `10**5000` raw 4,300-digit crash. All other probes cleanly rejected!) |",
            "### AUDIT-S1 (Test Section 1)",
            "- **Verdict:** **`PARTIAL/FRAGILE`** (cites `foo.py:10` wrong line nit)",
            "### AUDIT-S2: Colon Section Header",
            "- **Verdict:** **`VERIFIED`** (0 defects)",
            "### AUDIT-S3",
            "- **Verdict:** **`VERIFIED`** (0 defects)",
            "## Pre-Registered Predictions",
            "| none |",
        ])
        parsed_all = emo.parse_audit_log_markdown(sample_md)
        _check([e["audit_id"] for e in parsed_all] == ["AUDIT-T1", "AUDIT-T2", "AUDIT-S1", "AUDIT-S2", "AUDIT-S3"], "all 5 parsed incl colon/EOL")
        parsed_filt = emo.parse_audit_log_markdown(sample_md, allowed_audit_ids=frozenset({"AUDIT-T2", "AUDIT-S1"}))
        _check([e["audit_id"] for e in parsed_filt] == ["AUDIT-T2", "AUDIT-S1"], "cutoff filtered")
        _expect_error("INVALID_ALLOWED_IDS_TYPE", emo.parse_audit_log_markdown, sample_md, allowed_audit_ids=["AUDIT-T1"])

        _expect_error("CR_LINE_ENDINGS_FORBIDDEN", emo.parse_audit_log_markdown, "a\r\nb")
        _expect_error("UNEXPECTED_TABLE_COLS", emo.parse_audit_log_markdown, "| **AUDIT-X** | a | b |")
        _expect_error(
            "DUPLICATE_AUDIT_ID",
            emo.parse_audit_log_markdown,
            "| **AUDIT-X** | 1 | 2 | 3 | **`VERIFIED`** |\n| **AUDIT-X** | 1 | 2 | 3 | **`VERIFIED`** |",
        )
        _expect_error("MALFORMED_SECTION_HEADER", emo.parse_audit_log_markdown, "### AUDIT-!")
        _expect_error("MISSING_SECTION_VERDICT", emo.parse_audit_log_markdown, "### AUDIT-S9\n- no verdict here")
        _expect_error(
            "DUPLICATE_AUDIT_ID",
            emo.parse_audit_log_markdown,
            "| **AUDIT-S9** | 1 | 2 | 3 | **`VERIFIED`** |\n### AUDIT-S9\n- **Verdict:** **`VERIFIED`**",
        )
        _expect_error("EMPTY_AUDIT_LOG", emo.parse_audit_log_markdown, "# Empty log\nno rows here")

        # Earliest split across literals & guarded regexes, multi-line tail stripping, size bound & linear speed
        ev_lit_and_re = "ok; **ONLY 1 defect** first; **HOWEVER** later `10**5000`. All other probes cleanly rejected!"
        span_re_first = emo.extract_defect_span("v", ev_lit_and_re)
        _check(span_re_first.startswith("**ONLY 1 defect**") and "All other probes" not in span_re_first, "regex earlier than literal")

        ev_multi = "passed stuff; **1 Defect:** later; **HOWEVER** earliest `10**5000` crash. All other 10/10 passed cleanly!"
        span = emo.extract_defect_span("v", ev_multi)
        _check(span.startswith("**1 Defect:**") and "All other 10/10" not in span, "earliest literal + ratio tail trim")
        _check(emo.classify_defect_span("v", ev_multi) == ["OBS_ZONEB_IO"], "classified from span")

        ev_re_earlier_than_re = "ok; **2 concrete defects** mid; **ONLY 1 defect** early cites `a.py:9`"
        _check(emo.extract_defect_span("v", ev_re_earlier_than_re).startswith("**2 concrete"), "earlier regex kept")

        ev_multiline_tail = "1 defect: cites `a.py:1` citation nit\nRemaining checks passed cleanly (bool, NaN, 10**5000)."
        _check(emo.classify_defect_span("v", ev_multiline_tail) == ["OBS_STALE_ANCHOR"], "multi-line Remaining checks stripped")

        # R3 inline passing-clause stripping before tail markers (S21B R3 item 3)
        _check(
            emo.classify_defect_span("v", "NaN handling passed cleanly; cites `a.py:1` citation nit") == ["OBS_STALE_ANCHOR"],
            "R3 pre-tail passing clause stripped without false OBS_ZONEB_IO",
        )
        _check(
            emo.classify_defect_span("v", "All bool/NaN probes cleanly rejected. Cites `a.py:1` citation nit.") == ["OBS_STALE_ANCHOR"],
            "R3 sentence passing clause stripped",
        )
        _check(
            emo.classify_defect_span("v", "cites `a.py:1` citation nit; accepts raw NaN")
            == ["OBS_ZONEB_IO", "OBS_STALE_ANCHOR"],
            "R3 neutral non-passing defect clause retained alongside override clause (kills And->Or BoolOp)",
        )
        _check(
            emo.classify_defect_span("v", "NaN handling passed cleanly but crashed on NaN") == ["OBS_ZONEB_IO"],
            "R3 defect-override word retains clause",
        )
        _check(
            "passed cleanly" in emo.extract_defect_span("v", "NaN handling passed cleanly").lower(),
            "R3 all-passing fallback preserves non-empty span",
        )

        ev_tail_ratio_before_lit = "cites `a.py:1` All other 5/5 ok. Remaining checks passed."
        _check("All other 5/5" not in emo.extract_defect_span("v", ev_tail_ratio_before_lit), "ratio cut earlier than literal tail")

        # Guarded regex family match (not hit by literal list)
        _check(emo.classify_defect_span("v", "accepts raw NaN input") == ["OBS_ZONEB_IO"], "guarded regex OBS_ZONEB_IO")
        _check(emo.classify_defect_span("v", "will forge signature") == ["OBS_HOLLOW_WITNESS"], "guarded regex OBS_HOLLOW_WITNESS")
        _check(emo.classify_defect_span("cites `a.py:1` citation fix", "plain note") == ["OBS_STALE_ANCHOR"], "vcol fallback")
        _expect_error("UNCLASSIFIED_NEGATIVE_AUDIT", emo.classify_defect_span, "plain", "no known defect keywords")
        # Anchor substring present ('nan' in 'banana') without word-boundary regex match must NOT classify!
        _expect_error("UNCLASSIFIED_NEGATIVE_AUDIT", emo.classify_defect_span, "plain", "banana note")

        # Exact MAX_EVIDENCE_CHARS boundary & ReDoS protection
        _check(len(emo.extract_defect_span("v", "a" * emo.MAX_EVIDENCE_CHARS)) == emo.MAX_EVIDENCE_CHARS + 2, "32768 exact ok")
        _expect_error("EVIDENCE_TOO_LARGE", emo.extract_defect_span, "v", "|" * (emo.MAX_EVIDENCE_CHARS + 1))
        _expect_error("EVIDENCE_TOO_LARGE", emo.classify_defect_span, "v", "|" * 100_000)
        _expect_error("EVIDENCE_TOO_LARGE", emo.split_markdown_table_row, "|" * (emo.MAX_EVIDENCE_CHARS + 1))

        t0 = time.perf_counter()
        _check(emo.classify_defect_span("cites `a.py:1`", "|" * emo.MAX_EVIDENCE_CHARS) == ["OBS_STALE_ANCHOR"], "32768 pipes classified")
        _check((time.perf_counter() - t0) < 1, "linear-time <1s on 32768 pipes")
        # Section boundary isolation (### and ## stop section capture cleanly)
        sec_md = "### AUDIT-B1\n- **Verdict:** **`VERIFIED`**\nbody1\n## Next Heading\n- **Verdict:** **`FALSIFIED`**\n### AUDIT-B2\n- **Verdict:** **`VERIFIED`**\nbody2\n"
        sec_parsed = emo.parse_audit_log_markdown(sec_md)
        _check(len(sec_parsed) == 2 and "FALSIFIED" not in sec_parsed[0]["evidence"] and "body2" not in sec_parsed[0]["evidence"], "section stops at ## and ###")
        # Inline passing clause stripping: keep defect override, drop pure passing clause
        _check("passed cleanly" not in emo._strip_passing_clauses("NaN passed cleanly; cites `a.py:1`"), "pure passing clause stripped")
        _check("defect" in emo._strip_passing_clauses("passed cleanly except 1 defect; cites `a.py:1`"), "defect override clause retained")

    def test_dual_complex_tomography_and_hitting_set(self) -> None:
        small = emo.compute_dual_complex_tomography(
            [
                {"audit_id": "A1", "verdict": "FALSIFIED", "families": ["OBS_ZONEB_IO", "OBS_HOLLOW_WITNESS"]},
                {"audit_id": "A2", "verdict": "PARTIAL/FRAGILE", "families": ["OBS_HOLLOW_WITNESS"]},
            ],
            total_audits=5,
            verified_count=3,
        )
        _check(small["minimal_hitting_set_size"] == 1, "min hitting set size 1")
        _check(small["minimal_hitting_sets"] == [["OBS_HOLLOW_WITNESS"]], "exact hitting set")
        _check(small["all_families_strictly_irreducible"] is False, "not all 6 needed")
        _check(small["rejection_rate_q"] == "2/5" and small["verified_rate_q"] == "3/5", "exact Q rates")

        _expect_error("DUPLICATE_NEG_AUDIT_ID", emo.compute_dual_complex_tomography, [
            {"audit_id": "A1", "verdict": "FALSIFIED", "families": ["OBS_ZONEB_IO"]},
            {"audit_id": "A1", "verdict": "FALSIFIED", "families": ["OBS_ZONEB_IO"]},
        ], total_audits=2, verified_count=0)
        _expect_error("INVALID_NEG_VERDICT", emo.compute_dual_complex_tomography, [
            {"audit_id": "A1", "verdict": "VERIFIED", "families": ["OBS_ZONEB_IO"]},
        ], total_audits=1, verified_count=0)
        _expect_error("UNKNOWN_OBSTRUCTION_FAMILY", emo.compute_dual_complex_tomography, [
            {"audit_id": "A1", "verdict": "FALSIFIED", "families": ["OBS_UNKNOWN"]},
        ], total_audits=1, verified_count=0)
        _expect_error("AUDIT_COUNT_PARTITION_MISMATCH", emo.compute_dual_complex_tomography, [
            {"audit_id": "A1", "verdict": "FALSIFIED", "families": ["OBS_ZONEB_IO"]},
        ], total_audits=5, verified_count=3)

        # Full Track S21b R2 real audit history invariants (329 ledger / 333 atomic / 232 verified / 97 negative)
        payload = emo.compute_escher_dual_miner_payload()
        op2 = payload["operator2_negative_space_dual_complex"]
        _check(op2["total_audits"] == 329 and op2["verified_count"] == 232, "329 total / 232 verified")
        _check(op2["negative_count"] == 97 and op2["falsified_count"] == 1 and op2["partial_fragile_count"] == 96, "97 neg")
        _check(op2["verified_rate_q"] == "232/329" and op2["rejection_rate_q"] == "97/329", "exact Q partition")
        _check(op2["atomic_id_accounting"]["atomic_audit_ids_count"] == 333, "333 atomic IDs")
        _check(op2["atomic_id_accounting"]["slash_composite_count"] == 3, "3 slash composites")
        _check(op2["minimal_hitting_set_size"] == 6 and op2["minimal_hitting_set_unique"] is True, "unique size 6")
        _check(op2["all_families_strictly_irreducible"] is True, "all 6 irreducible")
        _check(op2["total_family_assignments"] == 162 and op2["mean_families_per_negative_audit_q"] == "162/97", "multiplicity")
        _check(op2["greedy_marginal_trajectory"][-1]["cumulative_recall_q"] == "1", "greedy reaches 1")


class TestLiveDiskExtractionAndCLI(unittest.TestCase):
    def _build_realistic_mini_expedition(
        self,
        root: Path,
    ) -> tuple[dict[str, str], dict[str, str], frozenset[str], frozenset[str], str]:
        """Build a realistic hermetic Track S20d + aletheia-corpus + AUDIT_LOG fixture (zero `{}` stubs!)."""
        s20d = root / "track-s20d-claim-to-witness-tomography"
        s20d.mkdir(parents=True)

        checker_code = "\n".join([
            "import sys",
            f"sys.path.insert(0, {str(_HERE)!r})",
            "from escher_dual_miner_oracle import (",
            "    verify_prose_artifact_bindings,",
            "    verify_provenance_claims,",
            "    run_semantic_destruction_gate,",
            ")",
            "MAX_JSON_DEPTH = 64",
            "MAX_JSON_BYTES = 2000000",
            "MAX_INT_BITS = 2048",
            "MAX_INT_DIGITS = 620",
            "NON_CONST_SENTINEL = frozenset('ab')",
            "BOOL_SENTINEL = True",
            "def _require_valid_utf8_str(v): return v",
            "def require_str(v): return v",
            "def require_bool(v): return v",
            "def require_int(v): return v",
            "def require_exact_dict(v): return v",
            "def require_exact_list(v): return v",
            "def require_hex64_ascii(v): return v",
            "def constant_time_hex64_equal(a, b): return a == b",
            "def require_no_symlink_path(p): return p",
            "def read_strict_utf8_file(p): return p",
        ]) + "\n"
        (s20d / "claim_witness_checker.py").write_text(checker_code, encoding="utf-8")
        (s20d / "claim_witness_audit.py").write_text("X = 1\n", encoding="utf-8")
        (s20d / "test_claim_witness_r5.py").write_text("Y = 1\n", encoding="utf-8")

        s20d_payload = {
            "per_family_audit118a_sig_counts": {"f1": 0, "f2": 2},
            "live_escape_suite": {
                "negative_cases": [
                    {"escape_id": "E1", "blocking_findings_in_review": 1},
                    {"escape_id": "E2", "blocking_findings_in_review": 3},
                ],
            },
        }
        s20d_cert = _make_signed_cert(s20d_payload)
        s20d_cert_bytes = emo.canonical_json_bytes(s20d_cert) + b"\n"
        (s20d / "claim_witness_certificate.json").write_bytes(s20d_cert_bytes)
        s20d_cert_file_sha = hashlib.sha256(s20d_cert_bytes).hexdigest()

        s20d_report = "\n".join([
            "# Mini S20d Report",
            f"- File SHA-256: `{s20d_cert_file_sha}`",
            f"- `payload_sha256`: `{s20d_cert['payload_sha256']}`",
            f"- `certificate_sha256`: `{s20d_cert['certificate_sha256']}`",
            "Across `10` multi-continent verification runs spanning **`2` AI verifier families**, max single-family coverage `2/4 = 50%`.",
            "Yet **`2` live pull requests** received **`4` blocking findings** total (`1 + 3`).",
            "Hardening: MAX_JSON_DEPTH = 64, MAX_JSON_BYTES = 2_000_000, MAX_INT_BITS = 2048, MAX_INT_DIGITS = 620, "
            "zero floats on trust paths, zero bare `assert`s, strict `type()` checks, unpaired UTF-16 surrogate, "
            "ASCII-hex64 pre-check, symlink/NUL/CRLF.",
            "Verified: mutate and BoolOp checks passed.",
        ]) + "\n"
        (s20d / "CLAIM_WITNESS_TOMOGRAPHY_REPORT.md").write_text(s20d_report, encoding="utf-8")

        s20d_pins = {
            fn: hashlib.sha256((s20d / fn).read_bytes()).hexdigest()
            for fn in emo.REQUIRED_S20D_PIN_KEYS
        }

        # Realistic mini aletheia-corpus
        corp = root / "publish" / "aletheia-corpus"
        (corp / "torus-knot-analysis" / "track-s19a-torus-activity-tomography").mkdir(parents=True)
        (corp / "torus-knot-analysis" / "track-s19b-torus-content-weaving").mkdir(parents=True)
        (corp / "torus-knot-analysis" / "track-s19c-zone-b-fuzzer").mkdir(parents=True)
        (corp / "expedition" / "verification").mkdir(parents=True)
        (root / "verification").mkdir(parents=True)

        corp_md = "\n".join([
            "| **AUDIT-M1** | 2026 | a | t | **`VERIFIED`** |",
            "| **AUDIT-M2** | 2026 | a | t | **`FALSIFIED`** (**HOWEVER** `10**5000` raw crash) |",
        ]) + "\n"
        live_md = corp_md + "### AUDIT-M3: Colon Header\n- **Verdict:** **`PARTIAL/FRAGILE`** (cites `a.py:1` citation nit)\n"
        (corp / "expedition" / "verification" / "AUDIT_LOG.md").write_text(corp_md, encoding="utf-8")
        (root / "verification" / "AUDIT_LOG.md").write_text(live_md, encoding="utf-8")

        s19a_cert = _make_signed_cert({
            "pillar2_multifamily_catch_matrix": {
                "per_family": [{"family": "f1", "runs": 6}, {"family": "f2", "runs": 4}],
            },
        })
        s19b_cert = _make_signed_cert({"ok": True})
        s19c_cert = _make_signed_cert({"ok": True})
        (corp / "torus-knot-analysis" / "track-s19a-torus-activity-tomography" / "torus_activity_certificate.json").write_bytes(
            emo.canonical_json_bytes(s19a_cert) + b"\n"
        )
        (corp / "torus-knot-analysis" / "track-s19b-torus-content-weaving" / "torus_content_certificate.json").write_bytes(
            emo.canonical_json_bytes(s19b_cert) + b"\n"
        )
        (corp / "torus-knot-analysis" / "track-s19c-zone-b-fuzzer" / "zone_b_fuzzer_certificate.json").write_bytes(
            emo.canonical_json_bytes(s19c_cert) + b"\n"
        )

        # 6 sections each 1,048,576 B (exact 1.00 MiB) -> total 6.00 MiB
        mib = emo.MIB_BYTES
        sec_summary = {s: {"files": 1, "bytes": mib} for s in emo._CORPUS_SECTION_NAMES}
        scrub_obj = {
            "files_scanned": 6,
            "bytes_scanned": 6 * mib,
            "total_redactions": 2,
            "redacted_file_count": 1,
            "redactions_by_kind": {"bearer_token": 2},
            "rules_checked": ["bearer_token"],
            "benign_prose_or_placeholder_skipped_total": 1,
            "post_scrub_verification": {
                "live_secrets_remaining": 0,
                "max_file_path": "transcripts/a.jsonl",
                "max_file_bytes": mib,
            },
        }
        scrub_bytes = emo.canonical_json_bytes(scrub_obj) + b"\n"
        (corp / "SECRET_SCRUB_RECEIPT.json").write_bytes(scrub_bytes)
        scrub_sha = hashlib.sha256(scrub_bytes).hexdigest()

        readme_lines = [
            "# Mini Corpus",
            "- **Swarm Cutoff Seq:** `#10`",
            "- **Agents Archived:** `2`",
            "- **Compiled Corpus Files:** `6` (`6.00 MiB` uncompressed)",
            "- **Max Single File Size:** `1.00 MiB` (`transcripts/a.jsonl`, strictly `< 95 MiB`)",
            "- **Secret Scrubbing:** `2` tokens/fixtures redacted across `1` files; **`0` live secrets remaining**",
            "- **Torus-Knot Analysis Integrated:** `track-s19a, track-s19b`",
            "| Directory | Files | Uncompressed MiB | Contents |",
            "| --- | ---: | ---: | --- |",
        ]
        for sname in emo._CORPUS_SECTION_NAMES:
            readme_lines.append(f"| `{sname}/` | `1` | `1.00` | {sname} |")
        (corp / "README.md").write_text("\n".join(readme_lines) + "\n", encoding="utf-8")

        manifest_files = [
            {"path": "README.md", "size_bytes": 100},
            {"path": "tools/compile_aletheia_corpus.py", "size_bytes": 200},
            {"path": "expedition/a.txt", "size_bytes": mib},
            {"path": "publish-branches-index/a.txt", "size_bytes": mib},
            {"path": "swarm/a.txt", "size_bytes": mib},
            {"path": "tasks/a.txt", "size_bytes": mib},
            {"path": "torus-knot-analysis/a.txt", "size_bytes": mib},
            {"path": "transcripts/a.jsonl", "size_bytes": mib},
        ]
        manifest_obj = {
            "swarm_cutoff_seq": 10,
            "agents_archived": ["a1", "a2"],
            "total_files_in_manifest": len(manifest_files),
            "max_single_file_bytes": mib,
            "hard_max_file_bytes": 95 * mib,
            "secret_scrub_receipt_sha256": scrub_sha,
            "section_summary": sec_summary,
            "torus_tracks_integrated": ["track-s19a", "track-s19b"],
            "files": manifest_files,
        }
        (corp / "CORPUS_MANIFEST.json").write_bytes(emo.canonical_json_bytes(manifest_obj) + b"\n")

        # SHA256SUMS includes all manifest files + CORPUS_MANIFEST.json (and blank line for parser test)
        sha_lines = [f"{'a' * 64}  {entry['path']}" for entry in manifest_files]
        sha_lines.append(f"{'b' * 64}  CORPUS_MANIFEST.json")
        sha_lines.append("")
        (corp / "SHA256SUMS").write_text("\n".join(sha_lines) + "\n", encoding="utf-8")

        # Create real tracked files + real .git repo so live git metadata extraction runs with zero fabrication!
        (corp / "tools").mkdir(parents=True, exist_ok=True)
        (corp / "tools" / "compile_aletheia_corpus.py").write_text("# stub\n", encoding="utf-8")
        for rel_dir in ("expedition", "publish-branches-index", "swarm", "tasks", "torus-knot-analysis", "transcripts"):
            (corp / rel_dir).mkdir(parents=True, exist_ok=True)
        for rel_file in ("expedition/a.txt", "publish-branches-index/a.txt", "swarm/a.txt", "tasks/a.txt", "torus-knot-analysis/a.txt", "transcripts/a.jsonl"):
            (corp / rel_file).write_text("x\n", encoding="utf-8")
        subprocess.run(["git", "-C", str(corp), "init", "-q"], check=True)
        subprocess.run(
            ["git", "-C", str(corp), "add", "README.md", "CORPUS_MANIFEST.json", "SHA256SUMS", "tools/compile_aletheia_corpus.py",
             "expedition/a.txt", "publish-branches-index/a.txt", "swarm/a.txt", "tasks/a.txt", "torus-knot-analysis/a.txt", "transcripts/a.jsonl"],
            check=True,
        )
        git_env = {**os.environ, "GIT_AUTHOR_DATE": "2026-01-01T00:00:00Z", "GIT_COMMITTER_DATE": "2026-01-01T00:00:00Z"}
        subprocess.run(
            ["git", "-C", str(corp), "-c", "user.name=Test", "-c", "user.email=t@example.com", "commit", "-q", "-m", "init"],
            env=git_env,
            check=True,
        )

        corp_files = {
            "CORPUS_MANIFEST.json": corp / "CORPUS_MANIFEST.json",
            "SECRET_SCRUB_RECEIPT.json": corp / "SECRET_SCRUB_RECEIPT.json",
            "SHA256SUMS": corp / "SHA256SUMS",
            "README.md": corp / "README.md",
            "torus_activity_certificate.json": corp / "torus-knot-analysis" / "track-s19a-torus-activity-tomography" / "torus_activity_certificate.json",
            "torus_content_certificate.json": corp / "torus-knot-analysis" / "track-s19b-torus-content-weaving" / "torus_content_certificate.json",
            "zone_b_fuzzer_certificate.json": corp / "torus-knot-analysis" / "track-s19c-zone-b-fuzzer" / "zone_b_fuzzer_certificate.json",
            "corpus_audit_log": corp / "expedition" / "verification" / "AUDIT_LOG.md",
        }
        corp_pins = {k: hashlib.sha256(fp.read_bytes()).hexdigest() for k, fp in corp_files.items()}
        corp_ids = frozenset({"AUDIT-M1", "AUDIT-M2"})
        cutoff_ids = frozenset({"AUDIT-M1", "AUDIT-M2", "AUDIT-M3"})

        live_s20d = emo.extract_s20d_snapshot_from_dir(s20d, corpus_dir=corp)
        live_corp = emo.extract_corpus_snapshot_from_dir(corp)
        _check(live_corp["artifact"]["root_and_tools_bytes"] == 300, "root + tools bytes counted accurately")
        op1_s20d = emo.evaluate_s20d_self_application(live_s20d)
        op1_corp = emo.evaluate_corpus_self_application(live_corp)
        op2 = emo.compute_dual_complex_tomography(
            [
                {"audit_id": "AUDIT-M2", "verdict": "FALSIFIED", "families": ["OBS_ZONEB_IO"]},
                {"audit_id": "AUDIT-M3", "verdict": "PARTIAL/FRAGILE", "families": ["OBS_STALE_ANCHOR"]},
            ],
            total_audits=3,
            verified_count=1,
            atomic_id_summary=emo.expand_atomic_audit_ids(["AUDIT-M1", "AUDIT-M2", "AUDIT-M3"]),
        )
        mini_payload = {
            "verification_basis": "pinned_snapshot_replay_certified_by_live_disk_parity",
            "operator1_self_application_tomography": {
                "track_s20d_self_application": op1_s20d,
                "aletheia_corpus_self_application": op1_corp,
                "combined_fixed_points_closed": 11,
                "combined_fixed_points_total": 11,
                "combined_central_void_count": 8,
                "combined_internal_closure_share_q": "11/19",
                "combined_irreducible_void_share_q": "8/19",
                "temporal_horizon_corpus_audits": 2,
                "temporal_horizon_live_audits": 3,
                "temporal_horizon_post_corpus_delta": 1,
                "temporal_horizon_delta_ids": ["AUDIT-M3"],
            },
            "operator2_negative_space_dual_complex": op2,
        }
        return s20d_pins, corp_pins, corp_ids, cutoff_ids, emo.canonical_sha256(mini_payload)

    def test_live_extraction_fail_closed_on_stubs_and_guards(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            s20d_pins, corp_pins, corp_ids, cutoff_ids, pay_sha = self._build_realistic_mini_expedition(root)

            res = emo.verify_live_disk_parity(
                root,
                expected_s20d_pins=s20d_pins,
                expected_corp_pins=corp_pins,
                expected_corp_ids=corp_ids,
                expected_cutoff_ids=cutoff_ids,
                expected_payload_sha=pay_sha,
            )
            _check(res["live_parity_verified"] is True and res["live_extraction_verified"] is True, "mini live parity ok")
            _check(res["live_audits_matched"] == 3 and res["live_verified_count"] == 1, "live audit counts ok")
            _check(not (root / "track-s20d-claim-to-witness-tomography" / "__pycache__").exists(), "no pycache written")

            # Also test extract_s20d_snapshot_from_dir with corpus_dir=None
            snap_no_corp = emo.extract_s20d_snapshot_from_dir(root / "track-s20d-claim-to-witness-tomography")
            _check(snap_no_corp["artifact"]["s19a_runs_sum"] == 10, "s20d extract without corpus_dir")

            # R3 live git metadata extraction tests (no-.git honest unavailable, empty repo, empty index, symlink .git)
            no_git_dir = root / "no_git_dir"
            no_git_dir.mkdir()
            ng_meta = emo._extract_corpus_git_metadata(no_git_dir)
            _check(
                ng_meta["git_metadata_source"] == "unavailable_no_git_dir"
                and ng_meta["layer3_git_tracked_files"] is None
                and ng_meta["head_commit"] is None
                and ng_meta["head_tree"] is None,
                "R3 no-.git dir returns honest unavailable None metadata",
            )
            bad_git_dir = root / "empty_git_repo"
            bad_git_dir.mkdir()
            subprocess.run(["git", "-C", str(bad_git_dir), "init", "-q"], check=True)
            _expect_error("CORPUS_GIT_QUERY_FAILED", emo._extract_corpus_git_metadata, bad_git_dir)
            subprocess.run(
                ["git", "-C", str(bad_git_dir), "-c", "user.name=T", "-c", "user.email=t@example.com", "commit", "-q", "--allow-empty", "-m", "empty"],
                check=True,
            )
            _expect_error("CORPUS_GIT_EMPTY_INDEX", emo._extract_corpus_git_metadata, bad_git_dir)
            sym_git_parent = root / "sym_git_parent"
            sym_git_parent.mkdir()
            (sym_git_parent / ".git").symlink_to(bad_git_dir / ".git")
            _expect_error("SYMLINK_FORBIDDEN", emo._extract_corpus_git_metadata, sym_git_parent)

            # Empty / mismatched pins rejected fail-closed
            _expect_error("PIN_KEYS_MISMATCH", emo.verify_live_disk_parity, root, expected_s20d_pins={})
            _expect_error("PIN_KEYS_MISMATCH", emo.verify_live_disk_parity, root, expected_s20d_pins=s20d_pins, expected_corp_pins={})
            _expect_error("INVALID_PIN_SET", emo.verify_live_disk_parity, root, expected_s20d_pins=s20d_pins, expected_corp_pins=corp_pins, expected_corp_ids=["AUDIT-M1"])
            _expect_error("EMPTY_PIN_SET", emo.verify_live_disk_parity, root, expected_s20d_pins=s20d_pins, expected_corp_pins=corp_pins, expected_corp_ids=frozenset())
            _expect_error("EMPTY_PIN_SET", emo.verify_live_disk_parity, root, expected_s20d_pins=s20d_pins, expected_corp_pins=corp_pins, expected_corp_ids=corp_ids, expected_cutoff_ids=frozenset())

            # Every failure guard in verify_live_disk_parity & load_s20d_checker_readonly
            _expect_error("EXPEDITION_ROOT_NOT_DIR", emo.verify_live_disk_parity, root / "missing_dir")
            _expect_error("S20D_DIR_NOT_FOUND", emo.extract_s20d_snapshot_from_dir, root / "missing_s20d")
            _expect_error("CORPUS_DIR_NOT_FOUND", emo.extract_corpus_snapshot_from_dir, root / "missing_corp")
            _expect_error("S20D_CHECKER_NOT_FOUND", emo.load_s20d_checker_readonly, root / "verification")

            class _NullLoaderSpec:
                loader = None

            with patch.object(emo.importlib.util, "spec_from_file_location", return_value=None):
                _expect_error("S20D_IMPORT_FAILED", emo.load_s20d_checker_readonly, root / "track-s20d-claim-to-witness-tomography")
            with patch.object(emo.importlib.util, "spec_from_file_location", return_value=_NullLoaderSpec()):
                _expect_error("S20D_IMPORT_FAILED", emo.load_s20d_checker_readonly, root / "track-s20d-claim-to-witness-tomography")

            bad_s20d = dict(s20d_pins)
            bad_s20d["claim_witness_audit.py"] = "0" * 64
            _expect_error("LIVE_S20D_SHA_MISMATCH", emo.verify_live_disk_parity, root, expected_s20d_pins=bad_s20d, expected_corp_pins=corp_pins, expected_corp_ids=corp_ids, expected_cutoff_ids=cutoff_ids, expected_payload_sha=pay_sha)

            bad_corp = dict(corp_pins)
            bad_corp["README.md"] = "0" * 64
            _expect_error("LIVE_CORPUS_SHA_MISMATCH", emo.verify_live_disk_parity, root, expected_s20d_pins=s20d_pins, expected_corp_pins=bad_corp, expected_corp_ids=corp_ids, expected_cutoff_ids=cutoff_ids, expected_payload_sha=pay_sha)

            _expect_error("LIVE_CUTOFF_INCOMPLETE", emo.verify_live_disk_parity, root, expected_s20d_pins=s20d_pins, expected_corp_pins=corp_pins, expected_corp_ids=corp_ids, expected_cutoff_ids=cutoff_ids | frozenset({"AUDIT-MISSING"}), expected_payload_sha=pay_sha)
            _expect_error("CORPUS_AUDIT_LOG_MISMATCH", emo.verify_live_disk_parity, root, expected_s20d_pins=s20d_pins, expected_corp_pins=corp_pins, expected_corp_ids=frozenset({"AUDIT-M1"}), expected_cutoff_ids=cutoff_ids, expected_payload_sha=pay_sha)
            _expect_error("LIVE_PAYLOAD_PARITY_MISMATCH", emo.verify_live_disk_parity, root, expected_s20d_pins=s20d_pins, expected_corp_pins=corp_pins, expected_corp_ids=corp_ids, expected_cutoff_ids=cutoff_ids, expected_payload_sha=_flip_hex(pay_sha))

            # Trust-path AST syntax/assert/float & partial-clause extraction checks
            bad_syn = root / "bad_syn.py"
            bad_syn.write_text("def broken(:\n", encoding="utf-8")
            _expect_error("TRUST_PATH_SYNTAX_ERROR", emo._inspect_python_ast_trust_file, bad_syn)
            bad_assert = root / "bad_assert.py"
            bad_assert.write_text("assert True\n", encoding="utf-8")
            _expect_error("TRUST_PATH_BARE_ASSERT", emo._inspect_python_ast_trust_file, bad_assert)
            bad_float = root / "bad_float.py"
            bad_float.write_text("x = 1.5\n", encoding="utf-8")
            _expect_error("TRUST_PATH_FLOAT_CONST", emo._inspect_python_ast_trust_file, bad_float)
            bool_py = root / "bool_const.py"
            bool_py.write_text("MAX_JSON_DEPTH = True\n", encoding="utf-8")
            _, bool_consts, _ = emo._inspect_python_ast_trust_file(bool_py)
            _check("MAX_JSON_DEPTH" not in bool_consts, "bool constant excluded from int_consts")
            _check(emo._extract_s20d_implemented_clauses({}, set()) == ["zero_floats_trust_path", "zero_bare_asserts"], "partial AST clauses")

            # Direct _verify_cert_internal_hashes (with re-signed outer cert_sha for payload check!) & _parse_sha256sums_strict
            good_c = _make_signed_cert({"k": 1})
            bad_cp = copy.deepcopy(good_c)
            bad_cp["payload_sha256"] = "0" * 64
            bad_cp["certificate_sha256"] = emo.canonical_sha256({k: v for k, v in bad_cp.items() if k != "certificate_sha256"})
            _expect_error("EXTRACTED_CERT_HASH_MISMATCH", emo._verify_cert_internal_hashes, bad_cp, "t")
            bad_cc = copy.deepcopy(good_c)
            bad_cc["certificate_sha256"] = "0" * 64
            _expect_error("EXTRACTED_CERT_HASH_MISMATCH", emo._verify_cert_internal_hashes, bad_cc, "t")

            # Direct meta_claims_outside_cert & self_hash_excluded_from_cert negative checks (BoolOp killers)
            with tempfile.TemporaryDirectory() as td_void:
                rv = Path(td_void)
                self._build_realistic_mini_expedition(rv)
                s20d_v = rv / "track-s20d-claim-to-witness-tomography"
                rep_sha_v = hashlib.sha256((s20d_v / "CLAIM_WITNESS_TOMOGRAPHY_REPORT.md").read_bytes()).hexdigest()
                # Embed BOTH report SHA and "mutate" inside cert payload -> both void booleans must flip False!
                c_v = _make_signed_cert({
                    "per_family_audit118a_sig_counts": {"f1": 0, "f2": 2},
                    "live_escape_suite": {"negative_cases": [{"escape_id": "E1", "blocking_findings_in_review": 1}, {"escape_id": "E2", "blocking_findings_in_review": 3}]},
                    "embedded_report_sha": rep_sha_v,
                    "embedded_meta_word": "mutate",
                })
                (s20d_v / "claim_witness_certificate.json").write_bytes(emo.canonical_json_bytes(c_v) + b"\n")
                snap_v = emo.extract_s20d_snapshot_from_dir(s20d_v)
                _check(snap_v["artifact"]["self_hash_excluded_from_cert"] is False, "report sha inside cert flips self_hash_excluded False")
                _check(snap_v["artifact"]["meta_claims_outside_cert"] is False, "mutate inside cert flips meta_claims_outside False")

                # Report missing meta words (while cert has none) -> meta_claims_outside_cert must still flip False
                rv2 = Path(td_void) / "sub_no_meta"
                rv2.mkdir()
                self._build_realistic_mini_expedition(rv2)
                s20d_v2 = rv2 / "track-s20d-claim-to-witness-tomography"
                rep_p2 = s20d_v2 / "CLAIM_WITNESS_TOMOGRAPHY_REPORT.md"
                rep_p2.write_text(rep_p2.read_text(encoding="utf-8").replace("mutate", "checks").replace("BoolOp", "ops"), encoding="utf-8")
                snap_v2 = emo.extract_s20d_snapshot_from_dir(s20d_v2)
                _check(snap_v2["artifact"]["meta_claims_outside_cert"] is False, "missing meta words in report flips False")

                # Mocked self-hash collision in cert (with report hash excluded) -> self_hash_excluded_from_cert must flip False
                c_v2_txt = (s20d_v2 / "claim_witness_certificate.json").read_text(encoding="utf-8")
                embedded_hex = json.loads(c_v2_txt)["payload_sha256"]
                real_sha256 = hashlib.sha256
                class _FakeSha:
                    def hexdigest(self) -> str:
                        return embedded_hex
                def _sha_collide(data: bytes) -> object:
                    if data == (s20d_v2 / "claim_witness_certificate.json").read_bytes():
                        return _FakeSha()
                    return real_sha256(data)
                with patch.object(emo.hashlib, "sha256", side_effect=_sha_collide):
                    snap_v3 = emo.extract_s20d_snapshot_from_dir(s20d_v2)
                _check(snap_v3["artifact"]["self_hash_excluded_from_cert"] is False, "self-hash inside cert flips False")

            _expect_error("MALFORMED_SHA256SUMS_LINE", emo._parse_sha256sums_strict, "badline\n")
            _expect_error("DUPLICATE_SHA256SUMS_PATH", emo._parse_sha256sums_strict, f"{'a'*64}  x\n{'b'*64}  x\n")
            _expect_error("EMPTY_SHA256SUMS", emo._parse_sha256sums_strict, "\n\n")

        # Replacing real files with `{}` stubs fails closed even with matching pins
        for stub_target, exp_err in (
            ("s20d_cert_stub", "INVALID_DICT_TYPE"),
            ("s20d_empty_family", "S20D_CERT_PARSE_ERROR"),
            ("s20d_report_stub", "S20D_REPORT_PARSE_ERROR"),
            ("s20d_report_bad_sum", "S20D_REPORT_PARSE_ERROR"),
            ("s20d_report_no_clauses", "S20D_REPORT_PARSE_ERROR"),
            ("corp_manifest_stub", "INVALID_STR_TYPE"),
            ("corp_manifest_bad_scrub_sha", "CORPUS_MANIFEST_SCRUB_SHA_MISMATCH"),
            ("corp_manifest_no_torus", "CORPUS_MANIFEST_PARSE_ERROR"),
            ("corp_manifest_bad_count", "CORPUS_MANIFEST_COUNT_MISMATCH"),
            ("corp_readme_stub", "CORPUS_README_PARSE_ERROR"),
            ("corp_readme_empty_tracks", "CORPUS_README_PARSE_ERROR"),
            ("corp_readme_missing_row", "CORPUS_README_PARSE_ERROR"),
        ):
            with tempfile.TemporaryDirectory() as td2:
                r2 = Path(td2)
                s_pins, c_pins, c_ids, cut_ids, p_sha = self._build_realistic_mini_expedition(r2)
                s20d2 = r2 / "track-s20d-claim-to-witness-tomography"
                corp2 = r2 / "publish" / "aletheia-corpus"
                if stub_target == "s20d_cert_stub":
                    (s20d2 / "claim_witness_certificate.json").write_text("{}\n", encoding="utf-8")
                elif stub_target == "s20d_empty_family":
                    c_obj = _make_signed_cert({"per_family_audit118a_sig_counts": {}, "live_escape_suite": {"negative_cases": [{"blocking_findings_in_review": 1}]}})
                    (s20d2 / "claim_witness_certificate.json").write_bytes(emo.canonical_json_bytes(c_obj) + b"\n")
                elif stub_target == "s20d_report_stub":
                    (s20d2 / "CLAIM_WITNESS_TOMOGRAPHY_REPORT.md").write_text("# R\n", encoding="utf-8")
                elif stub_target == "s20d_report_bad_sum":
                    rep = (s20d2 / "CLAIM_WITNESS_TOMOGRAPHY_REPORT.md").read_text("utf-8").replace("`4` blocking findings", "`9` blocking findings")
                    (s20d2 / "CLAIM_WITNESS_TOMOGRAPHY_REPORT.md").write_text(rep, encoding="utf-8")
                elif stub_target == "s20d_report_no_clauses":
                    rep = (s20d2 / "CLAIM_WITNESS_TOMOGRAPHY_REPORT.md").read_text("utf-8")
                    rep = "\n".join(ln for ln in rep.splitlines() if not ln.startswith("Hardening:")) + "\n"
                    (s20d2 / "CLAIM_WITNESS_TOMOGRAPHY_REPORT.md").write_text(rep, encoding="utf-8")
                elif stub_target == "corp_manifest_stub":
                    (corp2 / "CORPUS_MANIFEST.json").write_text("{}\n", encoding="utf-8")
                elif stub_target == "corp_manifest_bad_scrub_sha":
                    m_obj = json.loads((corp2 / "CORPUS_MANIFEST.json").read_text("utf-8"))
                    m_obj["secret_scrub_receipt_sha256"] = "0" * 64
                    (corp2 / "CORPUS_MANIFEST.json").write_bytes(emo.canonical_json_bytes(m_obj) + b"\n")
                elif stub_target == "corp_manifest_no_torus":
                    m_obj = json.loads((corp2 / "CORPUS_MANIFEST.json").read_text("utf-8"))
                    m_obj["files"] = [f for f in m_obj["files"] if not f["path"].startswith("torus-knot-analysis/")]
                    (corp2 / "CORPUS_MANIFEST.json").write_bytes(emo.canonical_json_bytes(m_obj) + b"\n")
                elif stub_target == "corp_manifest_bad_count":
                    m_obj = json.loads((corp2 / "CORPUS_MANIFEST.json").read_text("utf-8"))
                    m_obj["total_files_in_manifest"] = 999
                    (corp2 / "CORPUS_MANIFEST.json").write_bytes(emo.canonical_json_bytes(m_obj) + b"\n")
                elif stub_target == "corp_readme_stub":
                    (corp2 / "README.md").write_text("{}\n", encoding="utf-8")
                elif stub_target == "corp_readme_empty_tracks":
                    rm = (corp2 / "README.md").read_text("utf-8").replace("`track-s19a, track-s19b`", "`,`")
                    (corp2 / "README.md").write_text(rm, encoding="utf-8")
                elif stub_target == "corp_readme_missing_row":
                    rm = "\n".join(ln for ln in (corp2 / "README.md").read_text("utf-8").splitlines() if not ln.startswith("| `swarm/`")) + "\n"
                    (corp2 / "README.md").write_text(rm, encoding="utf-8")

                # Recompute pins so SHA checks would pass if real extraction didn't fail closed!
                s_pins_new = {fn: hashlib.sha256((s20d2 / fn).read_bytes()).hexdigest() for fn in emo.REQUIRED_S20D_PIN_KEYS}
                c_map = {
                    "CORPUS_MANIFEST.json": corp2 / "CORPUS_MANIFEST.json",
                    "SECRET_SCRUB_RECEIPT.json": corp2 / "SECRET_SCRUB_RECEIPT.json",
                    "SHA256SUMS": corp2 / "SHA256SUMS",
                    "README.md": corp2 / "README.md",
                    "torus_activity_certificate.json": corp2 / "torus-knot-analysis" / "track-s19a-torus-activity-tomography" / "torus_activity_certificate.json",
                    "torus_content_certificate.json": corp2 / "torus-knot-analysis" / "track-s19b-torus-content-weaving" / "torus_content_certificate.json",
                    "zone_b_fuzzer_certificate.json": corp2 / "torus-knot-analysis" / "track-s19c-zone-b-fuzzer" / "zone_b_fuzzer_certificate.json",
                    "corpus_audit_log": corp2 / "expedition" / "verification" / "AUDIT_LOG.md",
                }
                c_pins_new = {k: hashlib.sha256(fp.read_bytes()).hexdigest() for k, fp in c_map.items()}
                _expect_error(
                    exp_err,
                    emo.verify_live_disk_parity,
                    r2,
                    expected_s20d_pins=s_pins_new,
                    expected_corp_pins=c_pins_new,
                    expected_corp_ids=c_ids,
                    expected_cutoff_ids=cut_ids,
                    expected_payload_sha=p_sha,
                )

    def test_certificate_verification_and_cli(self) -> None:
        cert = audit.build_certificate()
        vdict = audit.verify_certificate_dict(copy.deepcopy(cert))
        _check(vdict["valid"] is True, "in-memory verify_certificate_dict ok")

        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            good_path = root / "cert.json"
            good_path.write_bytes(emo.canonical_json_bytes(cert) + b"\n")
            vfile = audit.verify_certificate_file(good_path)
            _check(vfile["valid"] is True, "file verify ok")

            non_canon = root / "pretty.json"
            non_canon.write_text(json.dumps(cert, indent=2), encoding="utf-8")
            _expect_error("NON_CANONICAL_CERT_BYTES", audit.verify_certificate_file, non_canon)

            extra_key = copy.deepcopy(cert)
            extra_key["rogue"] = 1
            _expect_error("CERT_KEYS_MISMATCH", audit.verify_certificate_dict, extra_key)

            bad_psha = copy.deepcopy(cert)
            bad_psha["payload_sha256"] = "0" * 64
            _expect_error("PAYLOAD_SHA_MISMATCH", audit.verify_certificate_dict, bad_psha)

            bad_csha = copy.deepcopy(cert)
            bad_csha["certificate_sha256"] = "0" * 64
            _expect_error("CERTIFICATE_SHA_MISMATCH", audit.verify_certificate_dict, bad_csha)

            tampered_p = copy.deepcopy(cert)
            tampered_p["payload"]["operator2_negative_space_dual_complex"]["total_audits"] = 999
            tampered_p["payload_sha256"] = emo.canonical_sha256(tampered_p["payload"])
            body_p = {k: v for k, v in tampered_p.items() if k != "certificate_sha256"}
            tampered_p["certificate_sha256"] = emo.canonical_sha256(body_p)
            _expect_error("PAYLOAD_RECOMPUTATION_MISMATCH", audit.verify_certificate_dict, tampered_p)

            tampered_m = copy.deepcopy(cert)
            tampered_m["novelty_tier"] = "N2"
            body_m = {k: v for k, v in tampered_m.items() if k != "certificate_sha256"}
            tampered_m["certificate_sha256"] = emo.canonical_sha256(body_m)
            _expect_error("CERT_RECOMPUTATION_MISMATCH", audit.verify_certificate_dict, tampered_m)

            buf = io.StringIO()
            with patch.object(sys, "stdout", buf):
                rc = audit.main(["--standalone"])
            _check(rc == 0 and "OK track-s21b" in buf.getvalue(), "CLI standalone text")

            buf = io.StringIO()
            with patch.object(sys, "stdout", buf):
                rc = audit.main(["--standalone", "--json"])
            _check(rc == 0 and json.loads(buf.getvalue())["certificate_sha256"] == cert["certificate_sha256"], "CLI standalone json")

            buf = io.StringIO()
            with patch.object(sys, "stdout", buf):
                rc = audit.main(["--check", str(good_path)])
            _check(rc == 0 and "OK verified" in buf.getvalue(), "CLI check text")

            buf = io.StringIO()
            with patch.object(sys, "stdout", buf):
                rc = audit.main(["--check", str(good_path), "--json"])
            _check(rc == 0 and json.loads(buf.getvalue())["valid"] is True, "CLI check json")

            err = io.StringIO()
            with patch.object(sys, "stderr", err):
                rc = audit.main(["--check", str(non_canon)])
            _check(rc == 1 and "FAIL NON_CANONICAL_CERT_BYTES" in err.getvalue(), "CLI check fail")

            err = io.StringIO()
            with patch.object(sys, "stderr", err):
                rc = audit.main(["--live-disk", str(root / "missing_exp")])
            _check(rc == 1 and "FAIL EXPEDITION_ROOT_NOT_DIR" in err.getvalue(), "CLI live-disk fail")

            # Strict argv validation (non-list, non-str, str-subclass, surrogate all rc=1 cleanly)
            for bad_argv, expected_code in (
                ([123], "INVALID_STR_TYPE"),
                ([_StrSub("--check"), str(good_path)], "INVALID_STR_TYPE"),
                ([chr(0xD800)], "INVALID_UTF8_SURROGATE"),
                ("bad", "INVALID_ARGV_TYPE"),
                (("--standalone",), "INVALID_ARGV_TYPE"),
            ):
                eb = io.StringIO()
                with patch.object(sys, "stderr", eb):
                    rc_bad = audit.main(bad_argv)  # type: ignore[arg-type]
                _check(rc_bad == 1 and f"FAIL {expected_code}" in eb.getvalue(), f"CLI bad argv {expected_code}")

            # Live subprocess relative --check inside symlinked PWD fails closed with rc=1
            real_cwd = root / "real_cwd"
            real_cwd.mkdir()
            (real_cwd / "c.json").write_bytes(emo.canonical_json_bytes(cert) + b"\n")
            sym_cwd = root / "sym_cwd"
            sym_cwd.symlink_to(real_cwd)
            env_sym = {**os.environ, "PWD": str(sym_cwd)}
            proc_sym = subprocess.run(
                [sys.executable, "-I", "-O", "-B", "-W", "error", str(_HERE / "escher_dual_miner_audit.py"), "--check", "c.json"],
                cwd=sym_cwd,
                env=env_sym,
                capture_output=True,
                text=True,
                check=False,
            )
            _check(proc_sym.returncode == 1 and "SYMLINK_ANCESTOR_FORBIDDEN" in proc_sym.stderr, "live symlinked PWD rejected")

            fake_live = {"live_parity_verified": True, "payload_sha256": cert["payload_sha256"], "live_audits_matched": 329}
            with patch.object(audit, "verify_live_disk_parity", return_value=fake_live):
                buf = io.StringIO()
                with patch.object(sys, "stdout", buf):
                    rc = audit.main(["--live-disk", str(root)])
                _check(rc == 0 and "OK live-disk-parity" in buf.getvalue(), "CLI live-disk text")

                buf = io.StringIO()
                with patch.object(sys, "stdout", buf):
                    rc = audit.main(["--live-disk", str(root), "--json"])
                _check(rc == 0 and json.loads(buf.getvalue())["live_parity_verified"] is True, "CLI live-disk json")

        # Privacy-clean redaction & leak checks across all track files (one-way SHA-256 only)
        _check("AUDIT-REV-ASMA77-F060-REDACTED1" in emo.PINNED_CORP_AUDIT_IDS, "redacted corpus ID present")
        _check("AUDIT-REV-GRAVITY29-CONTINUUM1-REDACTED2" in emo.PINNED_POST_CORPUS_DELTA_IDS, "redacted delta ID present")
        _check(emo._normalize_audit_id("AUDIT-PUBLIC-OK") == "AUDIT-PUBLIC-OK", "public ID unchanged")
        forbidden_token_sha256 = frozenset({
            "121283d779f8012226729faecec1688603c86b4a5cf7c25387c77070a6c0120b",
            "604aa1b5c1e2533865e35df2817de10f57695939cf88436f175ba2c7c5731b1b",
            "bc44f286f7a1439d9128a868e7e1ca1f135e4e23e6c77ae19bf4e31404d90334",
            "16c8f95fe15d6c733ca9080db25d1846e3f1705e2dd5d35033a8ac546504aa94",
            "427237f4136c75721c04bc470b67118e9866600445e32d2a7accfc0a7bea0065",
        })
        forbidden_paths = (
            "/" + "home" + "/",
            "/" + "Users" + "/",
            "/" + "dev" + "/" + "null",
        )
        token_re = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*", re.ASCII)
        for p_item in sorted(_HERE.iterdir()):
            if p_item.is_file():
                body_lc = p_item.read_text(encoding="utf-8").lower()
                for needle in forbidden_paths:
                    _check(needle.lower() not in body_lc, f"path leak {needle!r} in {p_item.name}")
                seen_tokens: set[str] = set()
                for chain in token_re.findall(body_lc):
                    seen_tokens.add(chain)
                    parts = chain.split("-")
                    if len(parts) > 1:
                        for idx_p in range(len(parts)):
                            seen_tokens.add(parts[idx_p])
                            if idx_p + 1 < len(parts):
                                seen_tokens.add(parts[idx_p] + "-" + parts[idx_p + 1])
                for tok in seen_tokens:
                    _check(
                        hashlib.sha256(tok.encode("utf-8")).hexdigest() not in forbidden_token_sha256,
                        f"redacted private token hash match in {p_item.name}",
                    )

        committed = _HERE / "escher_dual_miner_certificate.json"
        if committed.is_file():
            _check(audit.verify_certificate_file(committed)["valid"] is True, "committed cert valid")


if __name__ == "__main__":
    suite = unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__])
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    raise SystemExit(0 if result.wasSuccessful() else 1)
