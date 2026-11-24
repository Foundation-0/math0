#!/usr/bin/env python3
"""
Pure-Z/Q Adversarial & Mutation-Complete Test Suite for
SU(2)_k Chern-Simons, Jones Polynomials, Poincare-Disk SL(2,Z), Exact NTT+CRT.

Zero bare `assert`s; independent Laurent Skein cross-checks on `kauffman_jones_from_pd`
outputs, SU(2)_k, and signed NTT+CRT cross-checks; full Zone-B hardening coverage
across oracle & CLI (atomic per-component `dir_fd` I/O, deleted CWD, equals-syntax CLI).
"""
from __future__ import annotations

from contextlib import redirect_stderr, redirect_stdout
import copy
from fractions import Fraction
import hashlib
import inspect
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

_HERE = Path(__file__).resolve().parent
if str(_HERE) not in sys.path:
    sys.path.insert(0, str(_HERE))

import jones_cs_poincare_ntt_audit as audit_cli
import jones_cs_poincare_ntt_oracle as oracle


class _IntSub(int):
    pass


class _StrSub(str):
    pass


class _ListSub(list):
    pass


class _DictSub(dict):
    pass


class _FracSub(Fraction):
    pass


def _rehash_cert(cert: dict[str, object]) -> dict[str, object]:
    out = copy.deepcopy(cert)
    payload_sha = oracle.sha256_canonical(out["payload"])
    out["payload_sha256"] = payload_sha
    out["certificate_sha256"] = oracle.sha256_canonical(
        {
            "schema_version": out["schema_version"],
            "track_id": out["track_id"],
            "payload_sha256": payload_sha,
        }
    )
    return out


def _independent_laurent_shift(poly: dict[int, int], shift: int, scale: int = 1) -> dict[int, int]:
    return {k + shift: v * scale for k, v in poly.items() if v * scale != 0}


def _independent_laurent_sum(*polys: dict[int, int]) -> dict[int, int]:
    out: dict[int, int] = {}
    for p in polys:
        for k, v in p.items():
            nv = out.get(k, 0) + v
            if nv == 0:
                out.pop(k, None)
            else:
                out[k] = nv
    return dict(sorted(out.items()))


class TestA_ConstantsAndZoneBPrimitives(unittest.TestCase):
    """Fast constant pins and complete Zone-B primitive & atomic fd I/O hardening tests."""

    def test_constants_and_defaults_pinned(self) -> None:
        self.assertEqual(oracle.SCHEMA_VERSION, "s23b-jones-cs-poincare-ntt-cert/v1")
        self.assertEqual(oracle.TRACK_ID, "TRACK-S23B")
        self.assertEqual(oracle.MAX_JSON_DEPTH, 64)
        self.assertEqual(oracle.MAX_JSON_BYTES, 2_000_000)
        self.assertEqual(oracle.MAX_INT_BITS, 2048)
        self.assertEqual(oracle.MAX_INT_DIGITS, 620)
        self.assertEqual(oracle.MAX_SEQ_LEN, 4096)
        self.assertEqual(oracle.NTT_PRIME_1, 998244353)
        self.assertEqual(oracle.NTT_PRIME_2, 469762049)
        self.assertEqual(oracle.NTT_PRIME_3, 1004535809)
        self.assertIs(inspect.signature(oracle.validate_certificate_payload).parameters["full_replay"].default, True)
        self.assertIs(inspect.signature(audit_cli.verify_certificate_file).parameters["full_replay"].default, True)

    def test_require_int_bool_str_seq_mapping_hex_fmt(self) -> None:
        self.assertEqual(oracle.require_int(0, lo=0, hi=0), 0)
        max_ok = (1 << oracle.MAX_INT_BITS) - 1
        self.assertEqual(oracle.require_int(max_ok), max_ok)
        self.assertEqual(oracle.require_int(-max_ok), -max_ok)

        for bad in (True, False, 1.0, "1", _IntSub(1), None):
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.require_int(bad)
            self.assertEqual(ctx.exception.code, "INVALID_INT_TYPE")
        for huge in (1 << oracle.MAX_INT_BITS, -(1 << oracle.MAX_INT_BITS), 10**5000):
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.require_int(huge)
            self.assertEqual(ctx.exception.code, "INT_BIT_LIMIT")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.require_int(4, lo=5)
        self.assertEqual(ctx.exception.code, "INT_BELOW_MIN")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.require_int(6, hi=5)
        self.assertEqual(ctx.exception.code, "INT_ABOVE_MAX")
        for bad_bound in (True, _IntSub(1), "1"):
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.require_int(5, lo=bad_bound)  # type: ignore[arg-type]
            self.assertEqual(ctx.exception.code, "INVALID_INT_BOUND")
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.require_int(5, hi=bad_bound)  # type: ignore[arg-type]
            self.assertEqual(ctx.exception.code, "INVALID_INT_BOUND")

        self.assertIs(oracle.require_bool(True), True)
        self.assertIs(oracle.require_bool(False), False)
        for bad in (1, 0, "true", None):
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.require_bool(bad)
            self.assertEqual(ctx.exception.code, "INVALID_BOOL_TYPE")

        self.assertEqual(oracle.require_str("a", min_len=1, max_len=1), "a")
        for bad in (1, _StrSub("a"), b"a"):
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.require_str(bad)
            self.assertEqual(ctx.exception.code, "INVALID_STR_TYPE")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.require_str("\ud800")
        self.assertEqual(ctx.exception.code, "INVALID_UTF8")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.require_str("", min_len=1)
        self.assertEqual(ctx.exception.code, "STR_TOO_SHORT")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.require_str("ab", max_len=1)
        self.assertEqual(ctx.exception.code, "STR_TOO_LONG")

        self.assertEqual(oracle.require_seq([1, 2], min_len=2, max_len=2), (1, 2))
        self.assertEqual(oracle.require_seq((1,), min_len=1, max_len=1), (1,))
        for bad in ("ab", {1, 2}, _ListSub([1])):
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.require_seq(bad)
            self.assertEqual(ctx.exception.code, "INVALID_SEQ_TYPE")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.require_seq([], min_len=1)
        self.assertEqual(ctx.exception.code, "SEQ_TOO_SHORT")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.require_seq([1, 2], max_len=1)
        self.assertEqual(ctx.exception.code, "SEQ_TOO_LONG")

        self.assertEqual(oracle.require_mapping({"k": 1}), {"k": 1})
        for bad in ([], _DictSub({"a": 1})):
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.require_mapping(bad)
            self.assertEqual(ctx.exception.code, "INVALID_MAPPING_TYPE")
        for bad in ({1: "a"}, {_StrSub("k"): 1}):
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.require_mapping(bad)
            self.assertEqual(ctx.exception.code, "NON_STR_KEY")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.require_mapping({"\ud800": 1})
        self.assertEqual(ctx.exception.code, "INVALID_UTF8")

        good_hex = "0123456789abcdef" * 4
        other_hex = "fedcba9876543210" * 4
        self.assertEqual(oracle.require_hex64_ascii(good_hex), good_hex)
        self.assertTrue(oracle.constant_time_hex64_equal(good_hex, good_hex))
        self.assertFalse(oracle.constant_time_hex64_equal(good_hex, other_hex))
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.require_hex64_ascii(123)
        self.assertEqual(ctx.exception.code, "INVALID_DIGEST_TYPE")
        for bad_len in ("0" * 63, "0" * 65):
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.require_hex64_ascii(bad_len)
            self.assertEqual(ctx.exception.code, "INVALID_DIGEST_LEN")
        for bad_ch in ("A" + "0" * 63, "é" + "0" * 63, "\ud800" + "0" * 63, "g" + "0" * 63):
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.require_hex64_ascii(bad_ch)
            self.assertEqual(ctx.exception.code, "INVALID_DIGEST_HEX")

        self.assertEqual(oracle.fmt_q(Fraction(7, 1)), "7")
        self.assertEqual(oracle.fmt_q(Fraction(-5, 7)), "-5/7")
        self.assertEqual(oracle.fmt_q(Fraction(max_ok, 1)), str(max_ok))
        self.assertEqual(oracle.fmt_q(Fraction(1, max_ok)), f"1/{max_ok}")
        for bad in (1, "1/2", _FracSub(1, 2)):
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.fmt_q(bad)  # type: ignore[arg-type]
            self.assertEqual(ctx.exception.code, "INVALID_FRACTION_TYPE")
        for huge_q in (Fraction(1 << oracle.MAX_INT_BITS, 1), Fraction(1, 1 << oracle.MAX_INT_BITS)):
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.fmt_q(huge_q)
            self.assertEqual(ctx.exception.code, "FRACTION_BIT_LIMIT")

        # _parse_capped_int_token direct boundary checks
        self.assertEqual(oracle._parse_capped_int_token("0" * 619 + "1"), 1)
        self.assertEqual(oracle._parse_capped_int_token(str(max_ok)), max_ok)
        for bad_tok in ("-", "١٢٣", "12a"):
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle._parse_capped_int_token(bad_tok)
            self.assertEqual(ctx.exception.code, "INVALID_INT_TOKEN")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle._parse_capped_int_token("0" * 620 + "1")
        self.assertEqual(ctx.exception.code, "INT_DIGIT_LIMIT")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle._parse_capped_int_token(str(1 << oracle.MAX_INT_BITS))
        self.assertEqual(ctx.exception.code, "INT_BIT_LIMIT")

    def test_json_and_atomic_path_io_zone_b(self) -> None:
        nested_ok: object = 1
        for _ in range(4):
            nested_ok = [nested_ok]
        oracle.validate_json_value(nested_ok, max_depth=4)
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.validate_json_value([nested_ok], max_depth=4)
        self.assertEqual(ctx.exception.code, "MAX_DEPTH_EXCEEDED")

        cyclic: list[object] = []
        cyclic.append(cyclic)
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.validate_json_value(cyclic)
        self.assertEqual(ctx.exception.code, "MAX_DEPTH_EXCEEDED")

        oracle.validate_json_value({"a": [True, False, None, (1 << oracle.MAX_INT_BITS) - 1, "ok"]})
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.validate_json_value({1: "x"})
        self.assertEqual(ctx.exception.code, "NON_STR_KEY")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.validate_json_value({"\ud800": "x"})
        self.assertEqual(ctx.exception.code, "INVALID_UTF8")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.validate_json_value({"a": "\ud800"})
        self.assertEqual(ctx.exception.code, "INVALID_UTF8")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.validate_json_value({"a": 1 << oracle.MAX_INT_BITS})
        self.assertEqual(ctx.exception.code, "INT_BIT_LIMIT")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.validate_json_value({"a": 1.5})
        self.assertEqual(ctx.exception.code, "FLOAT_FORBIDDEN")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.validate_json_value({"a": {1, 2}})
        self.assertEqual(ctx.exception.code, "UNSUPPORTED_JSON_TYPE")

        self.assertEqual(oracle.parse_strict_json_text("[1,2]", require_object=False), [1, 2])
        self.assertEqual(oracle.parse_strict_json_text('{"b":1,"a":2}'), {"b": 1, "a": 2})
        self.assertEqual(oracle.canonical_json_bytes({"b": 1, "a": 2}), b'{"a":2,"b":1}')
        self.assertEqual(
            oracle.sha256_canonical({"b": 1, "a": 2}),
            hashlib.sha256(b'{"a":2,"b":1}').hexdigest(),
        )
        exact_pad = "{}" + (" " * (oracle.MAX_JSON_BYTES - 2))
        self.assertEqual(oracle.parse_strict_json_text(exact_pad), {})
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.parse_strict_json_text(exact_pad + " ")
        self.assertEqual(ctx.exception.code, "JSON_TOO_LARGE")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.parse_strict_json_text(b"{}")  # type: ignore[arg-type]
        self.assertEqual(ctx.exception.code, "INVALID_JSON_INPUT")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.parse_strict_json_text("   ")
        self.assertEqual(ctx.exception.code, "EMPTY_JSON_INPUT")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.parse_strict_json_text('{"x":1.5}')
        self.assertEqual(ctx.exception.code, "JSON_FLOAT_FORBIDDEN")
        for tok in ("NaN", "Infinity", "-Infinity"):
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.parse_strict_json_text(f'{{"x":{tok}}}')
            self.assertEqual(ctx.exception.code, "JSON_CONSTANT_FORBIDDEN")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.parse_strict_json_text('{"a":1,"a":2}')
        self.assertEqual(ctx.exception.code, "JSON_DUPLICATE_KEY")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.parse_strict_json_text("[1,2]", require_object=True)
        self.assertEqual(ctx.exception.code, "JSON_ROOT_NOT_OBJECT")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.parse_strict_json_text("[1,2]", require_object=0)  # type: ignore[arg-type]
        self.assertEqual(ctx.exception.code, "INVALID_BOOL_TYPE")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.parse_strict_json_text("{bad")
        self.assertEqual(ctx.exception.code, "JSON_PARSE_ERROR")
        deep_json = "[" * 2000 + "]" * 2000
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.parse_strict_json_text(deep_json, require_object=False)
        self.assertIn(ctx.exception.code, ("MAX_DEPTH_EXCEEDED", "JSON_PARSE_ERROR"))

        class _EvilPath(type(Path())):
            pass

        for bad_path in ("/tmp/x", _EvilPath("/tmp/x")):
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.require_safe_path(bad_path)  # type: ignore[arg-type]
            self.assertEqual(ctx.exception.code, "INVALID_PATH_TYPE")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.require_safe_path(Path("bad\x00name"))
        self.assertEqual(ctx.exception.code, "INVALID_PATH_NUL")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.require_safe_path(Path("bad\ud800name"))
        self.assertEqual(ctx.exception.code, "INVALID_UTF8")

        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            real_file = root / "ok.json"
            oracle.safe_write_bytes(real_file, b'{"longer":123456}\n')
            self.assertEqual(oracle.load_safe_bytes(real_file), b'{"longer":123456}\n')
            oracle.safe_write_bytes(real_file, b'{"a":2}\n')
            self.assertEqual(oracle.load_safe_bytes(real_file), b'{"a":2}\n')
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.safe_write_bytes(real_file, "not-bytes")  # type: ignore[arg-type]
            self.assertEqual(ctx.exception.code, "INVALID_BYTES_TYPE")

            # Hardlink guard refuses BEFORE truncation
            hl_orig = root / "hl_orig.json"
            oracle.safe_write_bytes(hl_orig, b'{"keep":1}\n')
            hl_alias = root / "hl_alias.json"
            os.link(hl_orig, hl_alias)
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.safe_write_bytes(hl_alias, b'{"evil":9}\n')
            self.assertEqual(ctx.exception.code, "HARDLINK_FORBIDDEN")
            self.assertEqual(hl_orig.read_bytes(), b'{"keep":1}\n')
            hl_alias.unlink()

            # Non-regular scratch FIFO (no system device writes)
            if hasattr(os, "mkfifo"):
                nonreg_fifo = root / "nonreg_fifo"
                os.mkfifo(nonreg_fifo)
                with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                    oracle.safe_write_bytes(nonreg_fifo, b"{}\n")
                self.assertEqual(ctx.exception.code, "NON_REGULAR_FILE")
                with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                    oracle.load_safe_bytes(nonreg_fifo)
                self.assertEqual(ctx.exception.code, "NON_REGULAR_FILE")

            # Live /proc/kallsyms st_size==0 streaming cap probe
            kallsyms = Path("/proc/kallsyms")
            if kallsyms.exists() and not stat.S_ISLNK(os.lstat(kallsyms).st_mode):
                with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                    oracle.load_safe_bytes(kallsyms)
                self.assertIn(ctx.exception.code, ("FILE_TOO_LARGE", "FILE_READ_ERROR"))

            sym_file = root / "sym.json"
            sym_file.symlink_to(real_file)
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.require_safe_path(sym_file)
            self.assertEqual(ctx.exception.code, "SYMLINK_FORBIDDEN")
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.load_safe_bytes(sym_file)
            self.assertEqual(ctx.exception.code, "SYMLINK_FORBIDDEN")
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.safe_write_bytes(sym_file, b"{}\n")
            self.assertEqual(ctx.exception.code, "SYMLINK_FORBIDDEN")

            # Deterministic temp-file collision retry + ENAMETOOLONG lstat guard
            pre_tmp = root / f".s23b.{os.getpid()}.0.tmp"
            pre_tmp.write_bytes(b"preexisting")
            oracle.safe_write_bytes(real_file, b'{"retry":1}\n')
            self.assertEqual(oracle.load_safe_bytes(real_file), b'{"retry":1}\n')
            self.assertEqual(pre_tmp.read_bytes(), b"preexisting")
            pre_tmp.unlink()
            self.assertEqual([p.name for p in root.glob(".s23b.*.tmp")], [])
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.safe_write_bytes(root / ("a" * 300), b"{}\n")
            self.assertEqual(ctx.exception.code, "FILE_WRITE_ERROR")

            # Live concurrent os.link/os.unlink hardlink race (>= 400 writes -> 0 inode clobbers, 0 leftover temps)
            race_dir = root / "hl_race"
            race_dir.mkdir()
            race_target = race_dir / "target.json"
            race_victim = race_dir / "victim.json"
            oracle.safe_write_bytes(race_target, b'{"step":-1}\n')
            stop_race = threading.Event()
            links_created = [0]
            clobbers = [0]

            def _hardlink_attacker() -> None:
                while not stop_race.is_set():
                    try:
                        os.link(race_target, race_victim)
                        links_created[0] += 1
                    except OSError:
                        continue
                    try:
                        snap = race_victim.read_bytes()
                        for _ in range(8):
                            if race_victim.read_bytes() != snap:
                                clobbers[0] += 1
                    except OSError:
                        pass
                    finally:
                        try:
                            os.unlink(race_victim)
                        except OSError:
                            pass

            attacker = threading.Thread(target=_hardlink_attacker, daemon=True)
            attacker.start()
            try:
                for step in range(420):
                    new_payload = f'{{"step":{step}}}\n'.encode("ascii")
                    try:
                        oracle.safe_write_bytes(race_target, new_payload)
                    except oracle.JonesPoincareNTTError as exc:
                        self.assertEqual(exc.code, "HARDLINK_FORBIDDEN")
            finally:
                stop_race.set()
                attacker.join(timeout=5)
            self.assertEqual(clobbers[0], 0)
            self.assertGreater(links_created[0], 0)
            self.assertEqual([p.name for p in race_dir.glob(".s23b.*.tmp")], [])
            if race_victim.exists():
                race_victim.unlink()

            # Empty component paths ("/" and ".") and non-directory / missing intermediate ancestors
            self.assertEqual(oracle.require_safe_path(Path("/")), Path("/"))
            self.assertEqual(oracle.require_safe_path(Path(".")), Path("."))
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.load_safe_bytes(Path("/"))
            self.assertEqual(ctx.exception.code, "NON_REGULAR_FILE")
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.safe_write_bytes(Path("/"), b"{}\n")
            self.assertEqual(ctx.exception.code, "NON_REGULAR_FILE")
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.load_safe_bytes(real_file / "child.json")
            self.assertEqual(ctx.exception.code, "SYMLINK_FORBIDDEN")
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.load_safe_bytes(root / "missing_dir" / "f.json")
            self.assertEqual(ctx.exception.code, "FILE_READ_ERROR")
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.safe_write_bytes(root / "missing_dir" / "f.json", b"{}\n")
            self.assertEqual(ctx.exception.code, "FILE_WRITE_ERROR")
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.require_safe_path(root / ("a" * 300))
            self.assertEqual(ctx.exception.code, "FILE_READ_ERROR")

            real_dir = root / "sub"
            real_dir.mkdir()
            deep_dir = real_dir / "nested"
            deep_dir.mkdir()
            (real_dir / "f.json").write_bytes(b'{"k":1}\n')
            sym_dir = root / "sym_sub"
            sym_dir.symlink_to(real_dir)
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.load_safe_bytes(sym_dir / "f.json")
            self.assertEqual(ctx.exception.code, "SYMLINK_FORBIDDEN")
            # Raw unnormalized .. symlink traversal rejected
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.require_safe_path(sym_dir / ".." / "ok.json")
            self.assertEqual(ctx.exception.code, "SYMLINK_FORBIDDEN")

            orig_cwd = os.getcwd()
            orig_pwd = os.environ.get("PWD")
            try:
                os.chdir(real_dir)
                os.environ["PWD"] = str(sym_dir)
                with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                    oracle.require_safe_path(Path("f.json"))
                self.assertEqual(ctx.exception.code, "SYMLINK_FORBIDDEN")

                os.chdir(deep_dir)
                os.environ["PWD"] = str(sym_dir / "nested")
                with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                    oracle.require_safe_path(Path("f.json"))
                self.assertEqual(ctx.exception.code, "SYMLINK_FORBIDDEN")

                os.chdir(root)
                os.environ["PWD"] = str(sym_dir)
                self.assertEqual(oracle.require_safe_path(Path("ok.json")), Path("ok.json"))
                os.environ.pop("PWD", None)
                self.assertEqual(oracle.require_safe_path(Path("ok.json")), Path("ok.json"))

                # Deleted CWD fails closed with CWD_UNAVAILABLE (rc=2 on CLI, zero traceback)
                dead_dir = root / "dead_cwd"
                dead_dir.mkdir()
                os.chdir(dead_dir)
                os.environ["PWD"] = str(dead_dir)
                dead_dir.rmdir()
                with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                    oracle.require_safe_path(Path("rel.json"))
                self.assertEqual(ctx.exception.code, "CWD_UNAVAILABLE")
                for dead_argv in (["--check", "rel.json", "--no-replay"], ["--write", "rel.json"]):
                    out_buf = io.StringIO()
                    err_buf = io.StringIO()
                    with redirect_stdout(out_buf), redirect_stderr(err_buf):
                        rc = audit_cli.main(dead_argv)
                    self.assertEqual(rc, 2)
                    self.assertEqual(json.loads(err_buf.getvalue())["error_code"], "CWD_UNAVAILABLE")
                os.environ.pop("PWD", None)
                with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                    oracle.load_safe_bytes(Path("rel.json"))
                self.assertEqual(ctx.exception.code, "CWD_UNAVAILABLE")

                # Unreadable CWD (chmod 000): getcwd succeeds on Linux, open(".") fails -> CWD_UNAVAILABLE
                if os.geteuid() != 0:
                    no_read_cwd = root / "no_read_cwd"
                    no_read_cwd.mkdir()
                    os.chdir(no_read_cwd)
                    no_read_cwd.chmod(0o000)
                    try:
                        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                            oracle.require_safe_path(Path("rel.json"))
                        self.assertEqual(ctx.exception.code, "CWD_UNAVAILABLE")
                    finally:
                        no_read_cwd.chmod(0o700)
            finally:
                os.chdir(orig_cwd)
                if orig_pwd is None:
                    os.environ.pop("PWD", None)
                else:
                    os.environ["PWD"] = orig_pwd

            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.load_safe_bytes(root / "missing.json")
            self.assertEqual(ctx.exception.code, "FILE_READ_ERROR")
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.load_safe_bytes(real_dir)
            self.assertEqual(ctx.exception.code, "NON_REGULAR_FILE")

            fifo_path = root / "pipe.fifo"
            os.mkfifo(fifo_path)
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.load_safe_bytes(fifo_path)
            self.assertEqual(ctx.exception.code, "NON_REGULAR_FILE")
            for bad_out in (real_dir, fifo_path):
                with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                    oracle.safe_write_bytes(bad_out, b"{}\n")
                self.assertEqual(ctx.exception.code, "NON_REGULAR_FILE")

            big_file = root / "big.bin"
            big_file.write_bytes(b"a" * oracle.MAX_JSON_BYTES)
            self.assertEqual(len(oracle.load_safe_bytes(big_file)), oracle.MAX_JSON_BYTES)
            big_file.write_bytes(b"a" * (oracle.MAX_JSON_BYTES + 1))
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.load_safe_bytes(big_file)
            self.assertEqual(ctx.exception.code, "FILE_TOO_LARGE")

            if os.geteuid() != 0:
                unreadable = root / "unreadable.json"
                unreadable.write_bytes(b"{}\n")
                unreadable.chmod(0o000)
                ro_dir = root / "ro_dir"
                ro_dir.mkdir()
                ro_dir.chmod(0o500)
                try:
                    with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                        oracle.load_safe_bytes(unreadable)
                    self.assertEqual(ctx.exception.code, "FILE_READ_ERROR")
                    with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                        oracle.safe_write_bytes(ro_dir / "x.json", b"{}\n")
                    self.assertEqual(ctx.exception.code, "FILE_WRITE_ERROR")
                finally:
                    unreadable.chmod(0o600)
                    ro_dir.chmod(0o700)

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
            mock.patch.object(oracle.sys, "platform", "darwin"),
            mock.patch.object(oracle.os, "lstat", return_value=root_lnk),
            mock.patch.object(oracle.os, "readlink", side_effect=_fake_readlink),
        ):
            self.assertEqual(
                oracle._normalize_darwin_system_prefix(Path("/var/folders/xx/cert.json")),
                Path("/private/var/folders/xx/cert.json"),
            )
            self.assertEqual(
                oracle._normalize_darwin_system_prefix(Path("/tmp/cert.json")),
                Path("/private/tmp/cert.json"),
            )
            self.assertEqual(
                oracle._normalize_darwin_system_prefix(Path("/etc/cert.json")),
                Path("/private/etc/cert.json"),
            )
            self.assertEqual(
                oracle._normalize_darwin_system_prefix(Path("/opt/cert.json")),
                Path("/opt/cert.json"),
            )
            self.assertEqual(
                oracle._normalize_darwin_system_prefix(Path("a/var/folders/xx/cert.json")),
                Path("a/var/folders/xx/cert.json"),
            )
            self.assertEqual(
                oracle._normalize_darwin_system_prefix(Path("/tmp"), allow_exact=True),
                Path("/private/tmp"),
            )
            self.assertEqual(
                oracle._normalize_darwin_system_prefix(Path("/"), allow_exact=True),
                Path("/"),
            )
            self.assertEqual(oracle._normalize_darwin_system_prefix(Path("/tmp")), Path("/tmp"))
            self.assertEqual(
                oracle._normalize_darwin_system_prefix(Path("/tmp/../etc/passwd")),
                Path("/tmp/../etc/passwd"),
            )

            anchor, parts = oracle._validate_path_and_split(Path("/var/folders/xx/cert.json"))
            self.assertEqual(anchor, "/")
            self.assertEqual(parts, ("private", "var", "folders", "xx", "cert.json"))
            anchor2, parts2 = oracle._validate_path_and_split(Path("/var/folders/xx/evil_link/cert.json"))
            self.assertEqual(anchor2, "/")
            self.assertEqual(parts2, ("private", "var", "folders", "xx", "evil_link", "cert.json"))

            captured_pwd: list[tuple[str, ...]] = []

            def _fake_open_chain(anc: str, pts: tuple[str, ...], err_code: str, label: str) -> int:
                captured_pwd.append(pts)
                return os.open("/", os.O_RDONLY | os.O_DIRECTORY)

            old_pwd = os.environ.get("PWD")
            try:
                os.environ["PWD"] = "/tmp"
                with (
                    mock.patch.object(oracle.os.path, "realpath", return_value="/private/tmp"),
                    mock.patch.object(oracle, "_open_dir_chain", side_effect=_fake_open_chain),
                ):
                    anc_rel, pts_rel = oracle._validate_path_and_split(Path("cert.json"))
                self.assertEqual(anc_rel, ".")
                self.assertEqual(pts_rel, ("cert.json",))
                self.assertEqual(captured_pwd[-1], ("private", "tmp"))
            finally:
                if old_pwd is None:
                    os.environ.pop("PWD", None)
                else:
                    os.environ["PWD"] = old_pwd

        for bad_stat in (root_dir, user_lnk):
            with (
                mock.patch.object(oracle.sys, "platform", "darwin"),
                mock.patch.object(oracle.os, "lstat", return_value=bad_stat),
                mock.patch.object(oracle.os, "readlink", side_effect=_fake_readlink),
            ):
                self.assertEqual(
                    oracle._normalize_darwin_system_prefix(Path("/var/folders/xx/cert.json")),
                    Path("/var/folders/xx/cert.json"),
                )
        with (
            mock.patch.object(oracle.sys, "platform", "darwin"),
            mock.patch.object(oracle.os, "lstat", return_value=root_lnk),
            mock.patch.object(oracle.os, "readlink", return_value="private/evil"),
        ):
            self.assertEqual(
                oracle._normalize_darwin_system_prefix(Path("/var/folders/xx/cert.json")),
                Path("/var/folders/xx/cert.json"),
            )
        with (
            mock.patch.object(oracle.sys, "platform", "darwin"),
            mock.patch.object(oracle.os, "lstat", side_effect=OSError("no access")),
        ):
            self.assertEqual(
                oracle._normalize_darwin_system_prefix(Path("/var/folders/xx/cert.json")),
                Path("/var/folders/xx/cert.json"),
            )
        with (
            mock.patch.object(oracle.sys, "platform", "linux"),
            mock.patch.object(oracle.os, "lstat", return_value=root_lnk),
            mock.patch.object(oracle.os, "readlink", side_effect=_fake_readlink),
        ):
            self.assertEqual(
                oracle._normalize_darwin_system_prefix(Path("/var/folders/xx/cert.json")),
                Path("/var/folders/xx/cert.json"),
            )


class TestB_ExactAlgebraicPillarsAndIndependentCrossChecks(unittest.TestCase):
    """Independent Skein-relation, cyclotomic, Cayley, and NTT+CRT verification + guard kills."""

    def test_cyclotomic_and_qi_edge_guards(self) -> None:
        phi6 = oracle.cyclotomic_poly_q(6)
        self.assertEqual(phi6, [Fraction(1), Fraction(-1), Fraction(1)])
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle._poly_divmod_q([Fraction(1)], [Fraction(0)])
        self.assertEqual(ctx.exception.code, "POLY_ZERO_DIV")
        # Non-invertible element mod reducible polynomial (x - 1)(x + 1) = x^2 - 1
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.poly_inv_mod_q([Fraction(-1), Fraction(1)], [Fraction(-1), Fraction(0), Fraction(1)])
        self.assertEqual(ctx.exception.code, "POLY_NOT_INVERTIBLE")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle._pad_cyc_int([Fraction(1, 2)], 2)
        self.assertEqual(ctx.exception.code, "NON_INTEGRAL_CYCLOTOMIC")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle._qi_div((Fraction(1), Fraction(0)), (Fraction(0), Fraction(0)))
        self.assertEqual(ctx.exception.code, "QI_ZERO_DIV")

        # Exact Q[i] verification of T_D and T_D^-1 inverse identity across boundary & interior points
        t_d = (
            ((Fraction(-1), Fraction(2)), (Fraction(1), Fraction(0))),
            ((Fraction(-1), Fraction(0)), (Fraction(1), Fraction(2))),
        )
        t_d_inv = (
            ((Fraction(1), Fraction(2)), (Fraction(-1), Fraction(0))),
            ((Fraction(1), Fraction(0)), (Fraction(-1), Fraction(2))),
        )
        for w_pt in (
            (Fraction(0), Fraction(0)),
            (Fraction(1), Fraction(0)),
            (Fraction(-1), Fraction(0)),
            (Fraction(0), Fraction(1)),
            (Fraction(3, 5), Fraction(4, 5)),
        ):
            self.assertEqual(oracle._qi_mobius(t_d, oracle._qi_mobius(t_d_inv, w_pt)), w_pt)
            self.assertEqual(oracle._qi_mobius(t_d_inv, oracle._qi_mobius(t_d, w_pt)), w_pt)
        self.assertEqual(oracle._qi_mobius(t_d, (Fraction(0), Fraction(0))), (Fraction(1, 5), Fraction(-2, 5)))
        self.assertEqual(oracle._qi_mobius(t_d_inv, (Fraction(0), Fraction(0))), (Fraction(1, 5), Fraction(2, 5)))
        self.assertEqual(oracle._qi_mobius(t_d_inv, (Fraction(1), Fraction(0))), (Fraction(1), Fraction(0)))

    def test_jones_skein_relation_and_pd_guards(self) -> None:
        # Independent Jones Skein Relation: t^-1 V_{L_+} - t V_{L_-} == (t^(1/2) - t^(-1/2)) V_{L_0}
        # Triple 1: L_+ = trefoil (s1^3), L_- = unknot (s1^2 s1^-1), L_0 = positive Hopf link (s1^2)
        v_plus = oracle.kauffman_jones_from_pd(*oracle.braid_to_pd(2, [(1, 1), (1, 1), (1, 1)]))
        v_minus = oracle.kauffman_jones_from_pd(*oracle.braid_to_pd(2, [(1, 1), (1, 1), (1, -1)]))
        v_zero = oracle.kauffman_jones_from_pd(*oracle.braid_to_pd(2, [(1, 1), (1, 1)]))
        lhs = _independent_laurent_sum(
            _independent_laurent_shift(v_plus, -2, 1),
            _independent_laurent_shift(v_minus, 2, -1),
        )
        rhs = _independent_laurent_sum(
            _independent_laurent_shift(v_zero, 1, 1),
            _independent_laurent_shift(v_zero, -1, -1),
        )
        self.assertEqual(lhs, rhs)

        # Triple 2: L_+ = positive Hopf (s1^2), L_- = 2-unlink (s1 s1^-1), L_0 = unknot (s1)
        v_p2 = oracle.kauffman_jones_from_pd(*oracle.braid_to_pd(2, [(1, 1), (1, 1)]))
        v_m2 = oracle.kauffman_jones_from_pd(*oracle.braid_to_pd(2, [(1, 1), (1, -1)]))
        v_02 = oracle.kauffman_jones_from_pd(*oracle.braid_to_pd(2, [(1, 1)]))
        lhs2 = _independent_laurent_sum(
            _independent_laurent_shift(v_p2, -2, 1),
            _independent_laurent_shift(v_m2, 2, -1),
        )
        rhs2 = _independent_laurent_sum(
            _independent_laurent_shift(v_02, 1, 1),
            _independent_laurent_shift(v_02, -1, -1),
        )
        self.assertEqual(lhs2, rhs2)

        # PD / braid / torus / Kauffman guards
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.braid_to_pd(2, [(1, 0)])
        self.assertEqual(ctx.exception.code, "INVALID_CROSSING_SIGN")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.compute_linking_matrix([(1, 4, 2, 3)], [1, 1])
        self.assertEqual(ctx.exception.code, "PD_SIGN_LEN_MISMATCH")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.compute_linking_matrix([(1, 4, 2, 3)], [0])
        self.assertEqual(ctx.exception.code, "INVALID_CROSSING_SIGN")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.kauffman_jones_from_pd([(1, 4, 2, 3)], [1, 1])
        self.assertEqual(ctx.exception.code, "PD_SIGN_LEN_MISMATCH")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.kauffman_jones_from_pd([], [], free_loops=0)
        self.assertEqual(ctx.exception.code, "EMPTY_LINK_DIAGRAM")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.kauffman_jones_from_pd([(1, 4, 2, 3)], [0])
        self.assertEqual(ctx.exception.code, "INVALID_CROSSING_SIGN")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.torus_knot_jones_closed_form(2, 4)
        self.assertEqual(ctx.exception.code, "NON_COPRIME_TORUS")

        # Defensive odd Kauffman power & torus division guards via controlled unit hooks
        orig_mul = oracle._laurent_mul
        oracle._laurent_mul = lambda _a, _b: {1: 1}  # type: ignore[assignment]
        try:
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.kauffman_jones_from_pd([], [], free_loops=1)
            self.assertEqual(ctx.exception.code, "ODD_KAUFFMAN_POWER")
        finally:
            oracle._laurent_mul = orig_mul

        # Test odd-gcd bypass for torus_knot_jones_closed_form remainder guard
        orig_gcd = oracle.math.gcd
        oracle.math.gcd = lambda _a, _b: 1  # type: ignore[assignment]
        try:
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                oracle.torus_knot_jones_closed_form(2, 2)
            self.assertEqual(ctx.exception.code, "TORUS_DIVISION_REMAINDER")
        finally:
            oracle.math.gcd = orig_gcd

    def test_ntt_crt_signed_convolution_and_guards(self) -> None:
        # Signed negative+positive convolution matches naive O(N^2) identically
        a = [5, -17, 1000003, -9999991, 42]
        b = [-3, 888888, -7777777, 19]
        ntt_res = oracle.ntt_convolve_crt(a, b, primes=(oracle.NTT_PRIME_1, oracle.NTT_PRIME_2))
        naive_res = oracle.naive_convolve_exact(a, b, len(a) + len(b) - 2)
        self.assertEqual(ntt_res, naive_res)
        self.assertLess(min(ntt_res), 0)
        self.assertGreater(max(ntt_res), 0)

        # NTT & CRT guards
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.ntt_transform([1, 2, 3], oracle.NTT_PRIME_1, 3)
        self.assertEqual(ctx.exception.code, "INVALID_NTT_LEN")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.ntt_transform([1, 2, 3, 4], 7, 3)
        self.assertEqual(ctx.exception.code, "NTT_MOD_NOT_FRIENDLY")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.ntt_convolve_crt([1], [1], primes=(7, oracle.NTT_PRIME_1))
        self.assertEqual(ctx.exception.code, "UNSUPPORTED_NTT_PRIME")
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.ntt_convolve_crt([1], [1], primes=(oracle.NTT_PRIME_1, oracle.NTT_PRIME_1))
        self.assertEqual(ctx.exception.code, "DUPLICATE_NTT_PRIME")

        # Exact CRT dynamic range boundary: max_bound * 2 == M fails; max_bound * 2 < M passes
        m12 = oracle.NTT_PRIME_1 * oracle.NTT_PRIME_2
        half_m = m12 // 2
        self.assertEqual(oracle.ntt_convolve_crt([half_m], [1]), [half_m])
        self.assertEqual(oracle.ntt_convolve_crt([-half_m], [1]), [-half_m])
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.ntt_convolve_crt([half_m + 1], [1])
        self.assertEqual(ctx.exception.code, "CRT_DYNAMIC_RANGE_EXCEEDED")


class TestC_CertificateValidationAndCLI(unittest.TestCase):
    """Full certificate validation, tamper rejection matrix, flag-like CLI guard, and -I parity."""

    def test_real_certificate_and_all_tamper_rejections(self) -> None:
        cert_path = _HERE / "jones_cs_poincare_ntt_certificate.json"
        cert = oracle.parse_strict_json_text(cert_path.read_text("utf-8"), require_object=True)

        res_fast = audit_cli.verify_certificate_file(cert_path, full_replay=False)
        self.assertTrue(res_fast["valid"])
        self.assertFalse(res_fast["full_replay"])
        self.assertTrue(res_fast["all_theorems_passed"])

        # Non-bool full_replay rejected
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.validate_certificate_payload(cert, full_replay=1)  # type: ignore[arg-type]
        self.assertEqual(ctx.exception.code, "INVALID_BOOL_TYPE")

        # Envelope tampers
        c_extra = copy.deepcopy(cert)
        c_extra["extra"] = 1
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.validate_certificate_payload(c_extra, full_replay=False)
        self.assertEqual(ctx.exception.code, "INVALID_CERT_KEYS")

        c_schema = copy.deepcopy(cert)
        c_schema["schema_version"] = "wrong/v0"
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.validate_certificate_payload(c_schema, full_replay=False)
        self.assertEqual(ctx.exception.code, "INVALID_SCHEMA_VERSION")

        c_track = copy.deepcopy(cert)
        c_track["track_id"] = "WRONG"
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.validate_certificate_payload(c_track, full_replay=False)
        self.assertEqual(ctx.exception.code, "INVALID_TRACK_ID")

        c_psha = copy.deepcopy(cert)
        c_psha["payload_sha256"] = "0" * 64
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.validate_certificate_payload(c_psha, full_replay=False)
        self.assertEqual(ctx.exception.code, "PAYLOAD_SHA_MISMATCH")

        c_csha = copy.deepcopy(cert)
        c_csha["certificate_sha256"] = "0" * 64
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.validate_certificate_payload(c_csha, full_replay=False)
        self.assertEqual(ctx.exception.code, "CERT_SHA_MISMATCH")

        # Payload tampers (re-hashed so digest checks pass and semantic guards fire)
        tampers = [
            ("INVALID_PAYLOAD_KEYS", lambda p: p.update({"extra": 1})),
            ("INVALID_PAYLOAD_SCHEMA", lambda p: p.update({"schema_version": "bad"})),
            ("INVALID_PAYLOAD_TRACK", lambda p: p.update({"track_id": "BAD"})),
            ("INVALID_ARITHMETIC_MODE", lambda p: p.update({"arithmetic_mode": "float64"})),
            ("INVALID_NOVELTY_CLASS", lambda p: p.update({"novelty_classification": "N99"})),
            ("THEOREM_FAILED", lambda p: p["theorem1_jones_and_cs"].update({"all_passed": False})),
            ("THEOREM_FAILED", lambda p: p["theorem2_modular_and_poincare"].update({"all_passed": False})),
            ("THEOREM_FAILED", lambda p: p["theorem3_hecke_and_ntt"].update({"all_passed": False})),
            ("THEOREM_FAILED", lambda p: p.update({"all_theorems_passed": False})),
        ]
        for expected_code, mutate_fn in tampers:
            bad = copy.deepcopy(cert)
            mutate_fn(bad["payload"])
            bad = _rehash_cert(bad)
            with self.assertRaises(oracle.JonesPoincareNTTError, msg=expected_code) as ctx:
                oracle.validate_certificate_payload(bad, full_replay=False)
            self.assertEqual(ctx.exception.code, expected_code)

    def test_cli_modes_flag_like_guards_and_isolated_subprocess(self) -> None:
        cert_path = _HERE / "jones_cs_poincare_ntt_certificate.json"
        cert = oracle.parse_strict_json_text(cert_path.read_text("utf-8"), require_object=True)

        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            non_canon = root / "non_canon.json"
            non_canon.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                audit_cli.verify_certificate_file(non_canon, full_replay=False)
            self.assertEqual(ctx.exception.code, "NON_CANONICAL_CERT_BYTES")

            crlf = root / "crlf.json"
            crlf.write_bytes(oracle.canonical_json_bytes(cert) + b"\r\n")
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                audit_cli.verify_certificate_file(crlf, full_replay=False)
            self.assertEqual(ctx.exception.code, "CR_FORBIDDEN")

            bad_u8 = root / "bad_u8.json"
            bad_u8.write_bytes(b"\xff\xfe")
            with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
                audit_cli.verify_certificate_file(bad_u8, full_replay=False)
            self.assertEqual(ctx.exception.code, "INVALID_UTF8")

            # CLI --check --no-replay success & failure
            out_buf = io.StringIO()
            err_buf = io.StringIO()
            with redirect_stdout(out_buf), redirect_stderr(err_buf):
                rc = audit_cli.main(["--check", str(cert_path), "--no-replay"])
            self.assertEqual(rc, 0)
            self.assertEqual(json.loads(out_buf.getvalue())["file_sha256"], hashlib.sha256(cert_path.read_bytes()).hexdigest())

            out_buf = io.StringIO()
            err_buf = io.StringIO()
            with redirect_stdout(out_buf), redirect_stderr(err_buf):
                rc = audit_cli.main(["--check", str(non_canon), "--no-replay"])
            self.assertEqual(rc, 1)
            self.assertEqual(json.loads(err_buf.getvalue())["error_code"], "NON_CANONICAL_CERT_BYTES")

            # Flag-like & empty path arguments (space + equals syntax), conflicting flags, invalid argv
            for bad_argv, exp_rc, exp_code in (
                (["--check", "--json"], 2, "INVALID_CLI_ARGS"),
                (["--write", "--json"], 2, "INVALID_CLI_ARGS"),
                (["--check", "-bad"], 2, "INVALID_CLI_ARGS"),
                (["--write", "-bad"], 2, "INVALID_CLI_ARGS"),
                (["--check", ""], 2, "INVALID_CLI_ARGS"),
                (["--write", ""], 2, "INVALID_CLI_ARGS"),
                (["--check=--json"], 2, "INVALID_CLI_ARGS"),
                (["--write=--json"], 2, "INVALID_CLI_ARGS"),
                (["--check=-bad"], 2, "INVALID_CLI_ARGS"),
                (["--write=-bad"], 2, "INVALID_CLI_ARGS"),
                (["--check="], 2, "INVALID_CLI_ARGS"),
                (["--write="], 2, "INVALID_CLI_ARGS"),
                (["--standalone", "--no-replay"], 2, "INVALID_CLI_ARGS"),
                (["--write", str(root / "w.json"), "--no-replay"], 2, "INVALID_CLI_ARGS"),
                ("bad-argv", 2, "INVALID_CLI_ARGS"),
                ([123], 1, "INVALID_STR_TYPE"),
                ([_StrSub("--no-replay")], 1, "INVALID_STR_TYPE"),
                (["\ud800"], 1, "INVALID_UTF8"),
            ):
                out_buf = io.StringIO()
                err_buf = io.StringIO()
                with redirect_stdout(out_buf), redirect_stderr(err_buf):
                    rc = audit_cli.main(bad_argv)  # type: ignore[arg-type]
                self.assertEqual(rc, exp_rc, msg=str(bad_argv))
                self.assertEqual(json.loads(err_buf.getvalue())["error_code"], exp_code)

            # Confirm --write=--json and abbreviated --wr=--json NEVER create ./--json in CWD
            orig_cwd = os.getcwd()
            try:
                os.chdir(root)
                out_buf = io.StringIO()
                err_buf = io.StringIO()
                with redirect_stdout(out_buf), redirect_stderr(err_buf):
                    rc = audit_cli.main(["--write=--json"])
                self.assertEqual(rc, 2)
                self.assertEqual(json.loads(err_buf.getvalue())["error_code"], "INVALID_CLI_ARGS")
                self.assertFalse((root / "--json").exists())

                err_buf = io.StringIO()
                with redirect_stderr(err_buf):
                    with self.assertRaises(SystemExit) as sysex:
                        audit_cli.main(["--wr=--json"])
                self.assertEqual(sysex.exception.code, 2)
                self.assertFalse((root / "--json").exists())
            finally:
                os.chdir(orig_cwd)

            # Valid equals-syntax --check=PATH and sys.argv[1:] require_str path (argv=None)
            out_buf = io.StringIO()
            err_buf = io.StringIO()
            with redirect_stdout(out_buf), redirect_stderr(err_buf):
                rc = audit_cli.main([f"--check={cert_path}", "--no-replay"])
            self.assertEqual(rc, 0)
            self.assertTrue(json.loads(out_buf.getvalue())["valid"])

            orig_sys_argv = sys.argv
            try:
                sys.argv = ["prog", "\ud800"]
                out_buf = io.StringIO()
                err_buf = io.StringIO()
                with redirect_stdout(out_buf), redirect_stderr(err_buf):
                    rc = audit_cli.main(None)
                self.assertEqual(rc, 1)
                self.assertEqual(json.loads(err_buf.getvalue())["error_code"], "INVALID_UTF8")

                sys.argv = ["prog", "--check", str(cert_path), "--no-replay"]
                out_buf = io.StringIO()
                err_buf = io.StringIO()
                with redirect_stdout(out_buf), redirect_stderr(err_buf):
                    rc = audit_cli.main(None)
                self.assertEqual(rc, 0)
                self.assertTrue(json.loads(out_buf.getvalue())["valid"])
            finally:
                sys.argv = orig_sys_argv

            # Fast CLI --standalone & --write (space, equals, bare) + dir/FIFO/hardlink refusal
            orig_builder = audit_cli.build_certificate
            orig_default = audit_cli.DEFAULT_CERT_PATH
            audit_cli.build_certificate = lambda: cert  # type: ignore[assignment]
            audit_cli.DEFAULT_CERT_PATH = root / "default_written.json"
            try:
                out_buf = io.StringIO()
                err_buf = io.StringIO()
                with redirect_stdout(out_buf), redirect_stderr(err_buf):
                    rc = audit_cli.main(["--standalone", "--json"])
                self.assertEqual(rc, 0)
                self.assertEqual(out_buf.getvalue().encode("ascii"), cert_path.read_bytes())

                w_out = root / "written.json"
                out_buf = io.StringIO()
                err_buf = io.StringIO()
                with redirect_stdout(out_buf), redirect_stderr(err_buf):
                    rc = audit_cli.main(["--write", str(w_out)])
                self.assertEqual(rc, 0)
                self.assertTrue(json.loads(out_buf.getvalue())["written"])
                self.assertEqual(w_out.read_bytes(), cert_path.read_bytes())

                eq_out = root / "eq_written.json"
                out_buf = io.StringIO()
                err_buf = io.StringIO()
                with redirect_stdout(out_buf), redirect_stderr(err_buf):
                    rc = audit_cli.main([f"--write={eq_out}"])
                self.assertEqual(rc, 0)
                self.assertEqual(eq_out.read_bytes(), cert_path.read_bytes())

                out_buf = io.StringIO()
                err_buf = io.StringIO()
                with redirect_stdout(out_buf), redirect_stderr(err_buf):
                    rc = audit_cli.main(["--write"])
                self.assertEqual(rc, 0)
                self.assertEqual((root / "default_written.json").read_bytes(), cert_path.read_bytes())

                fifo = root / "out.fifo"
                os.mkfifo(fifo)
                for bad_out in (root, fifo):
                    out_buf = io.StringIO()
                    err_buf = io.StringIO()
                    with redirect_stdout(out_buf), redirect_stderr(err_buf):
                        rc = audit_cli.main(["--write", str(bad_out)])
                    self.assertEqual(rc, 1)
                    self.assertEqual(json.loads(err_buf.getvalue())["error_code"], "NON_REGULAR_FILE")
            finally:
                audit_cli.build_certificate = orig_builder
                audit_cli.DEFAULT_CERT_PATH = orig_default

            # Isolated -I -O -B subprocess from foreign cwd kills sys.path & __main__ mutants
            proc = subprocess.run(
                [sys.executable, "-I", "-O", "-B", str(_HERE / "jones_cs_poincare_ntt_audit.py"), "--check", str(cert_path), "--no-replay"],
                cwd=td,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertTrue(json.loads(proc.stdout)["valid"])


class TestZ_FullEndToEndReplay(unittest.TestCase):
    """End-to-end deterministic full replay across all 3 theorems & canonical replay tamper rejection."""

    def test_z_full_replay_and_canonical_mismatch(self) -> None:
        cert_path = _HERE / "jones_cs_poincare_ntt_certificate.json"
        cert = oracle.parse_strict_json_text(cert_path.read_text("utf-8"), require_object=True)

        bad_replay = copy.deepcopy(cert)
        bad_replay["payload"]["theorem3_hecke_and_ntt"]["delta_ramanujan_tau_N64"]["tau_64"] = 0
        bad_replay = _rehash_cert(bad_replay)
        with self.assertRaises(oracle.JonesPoincareNTTError) as ctx:
            oracle.validate_certificate_payload(bad_replay, full_replay=True)
        self.assertEqual(ctx.exception.code, "CANONICAL_REPLAY_MISMATCH")

        res_full = audit_cli.verify_certificate_file(cert_path, full_replay=True)
        self.assertTrue(res_full["valid"])
        self.assertTrue(res_full["full_replay"])
        self.assertTrue(res_full["all_theorems_passed"])


if __name__ == "__main__":
    unittest.main()
