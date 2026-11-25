"""Comprehensive R5 Test & Mutation-Kill Suite for Track S20e (Sokoban Coupled Farkas Duals).

Zero external dependencies, zero bare asserts, runs under `-I -B`, `-I -O -B`,
`-I -B -W error`, and `PYTHONHASHSEED=42 -I -B`.
"""
from __future__ import annotations

import copy
from fractions import Fraction
import io
import json
import os
from pathlib import Path
import stat
import sys
import tempfile
import unittest
from unittest.mock import patch

_THIS_DIR = str(Path(__file__).resolve().parent)
if _THIS_DIR not in sys.path:
    sys.path.insert(0, _THIS_DIR)

import sokoban_farkas_audit as audit
import sokoban_farkas_oracle as oracle


class _IntSub(int):
    pass


class _StrSub(str):
    pass


class _FracSub(Fraction):
    pass


class _PathSub(type(Path("."))):
    pass


class TestZoneBHardening(unittest.TestCase):
    """Exhaustive Zone-B fail-closed tests for exact types, bounds, JSON, and file I/O."""

    def test_require_int_and_bounds(self) -> None:
        self.assertEqual(oracle.require_int(0, "z", lo=0, hi=0), 0)
        self.assertEqual(oracle.require_int(-5, "n", lo=-5, hi=5), -5)
        for bad in (True, False, 1.0, "1", _IntSub(1), None):
            with self.assertRaises(oracle.AletheiaError) as ctx:
                oracle.require_int(bad, "bad")
            self.assertEqual(ctx.exception.code, "INVALID_INT_TYPE")
        self.assertEqual(oracle.require_int((1 << 2048) - 1, "max2048"), (1 << 2048) - 1)
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.require_int(1 << 2048, "big")
        self.assertEqual(ctx.exception.code, "INT_BIT_LIMIT")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.require_int(10**5000, "huge")
        self.assertEqual(ctx.exception.code, "INT_BIT_LIMIT")
        self.assertNotIn("000000", str(ctx.exception))
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.require_int(-(10**5000), "nhuge")
        self.assertEqual(ctx.exception.code, "INT_BIT_LIMIT")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.require_int(4, "lo_fail", lo=5)
        self.assertEqual(ctx.exception.code, "INT_BELOW_MIN")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.require_int(6, "hi_fail", hi=5)
        self.assertEqual(ctx.exception.code, "INT_ABOVE_MAX")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.require_int(1, "bad_lo", lo=True)  # type: ignore[arg-type]
        self.assertEqual(ctx.exception.code, "INVALID_BOUND_TYPE")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.require_int(1, "bad_hi", hi=True)  # type: ignore[arg-type]
        self.assertEqual(ctx.exception.code, "INVALID_BOUND_TYPE")

    def test_hex64_and_constant_time(self) -> None:
        good = "0123456789abcdef" * 4
        other = "fedcba9876543210" * 4
        self.assertTrue(oracle.constant_time_hex64_equal(good, good))
        self.assertFalse(oracle.constant_time_hex64_equal(good, other))
        for bad, code in (
            (123, "INVALID_DIGEST_TYPE"),
            (_StrSub(good), "INVALID_DIGEST_TYPE"),
            ("a" * 63, "INVALID_DIGEST_LEN"),
            ("a" * 65, "INVALID_DIGEST_LEN"),
            ("A" * 64, "INVALID_DIGEST_HEX"),
            ("\u00e9" * 64, "INVALID_DIGEST_HEX"),
            (chr(0xD800) * 64, "INVALID_DIGEST_HEX"),
        ):
            with self.assertRaises(oracle.AletheiaError) as ctx:
                oracle.constant_time_hex64_equal(bad, good)
            self.assertEqual(ctx.exception.code, code)

    def test_rationals_fmt_parse_and_ceil(self) -> None:
        self.assertEqual(oracle.fmt_q(Fraction(7, 1)), "7")
        self.assertEqual(oracle.fmt_q(Fraction(5, 3)), "5/3")
        self.assertEqual(oracle.parse_q(5), Fraction(5))
        self.assertEqual(oracle.parse_q(Fraction(-3, 2)), Fraction(-3, 2))
        self.assertEqual(oracle.parse_q("7/3"), Fraction(7, 3))
        self.assertEqual(oracle.parse_q("-4"), Fraction(-4))
        self.assertEqual(oracle.parse_q("9" * 616), Fraction(int("9" * 616)))
        self.assertEqual(oracle.ceil_q(Fraction(6, 3)), 2)
        self.assertEqual(oracle.ceil_q(Fraction(7, 3)), 3)
        self.assertEqual(oracle.ceil_q(Fraction(-7, 3)), -2)
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.fmt_q(_FracSub(1, 2))
        self.assertEqual(ctx.exception.code, "INVALID_FRACTION_TYPE")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.fmt_q(Fraction(10**5000, 1))
        self.assertEqual(ctx.exception.code, "FRACTION_BIT_LIMIT")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.fmt_q(Fraction(1, 10**5000))
        self.assertEqual(ctx.exception.code, "FRACTION_BIT_LIMIT")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.parse_q(Fraction(10**5000, 1))
        self.assertEqual(ctx.exception.code, "FRACTION_BIT_LIMIT")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.parse_q(Fraction(1, 10**5000))
        self.assertEqual(ctx.exception.code, "FRACTION_BIT_LIMIT")
        for bad, code in (
            (True, "INVALID_RATIONAL_TYPE"),
            (1.5, "INVALID_RATIONAL_TYPE"),
            (_FracSub(1, 2), "INVALID_RATIONAL_TYPE"),
            ("1/2/3", "INVALID_RATIONAL_STR"),
            ("1/0", "INVALID_RATIONAL_CANON"),
            ("1/-2", "INVALID_RATIONAL_CANON"),
            ("3/1", "INVALID_RATIONAL_CANON"),
            ("2/4", "INVALID_RATIONAL_CANON"),
            ("-0", "NON_CANONICAL_INT_STR"),
            ("007", "NON_CANONICAL_INT_STR"),
            ("01/2", "NON_CANONICAL_INT_STR"),
            ("", "INVALID_INT_STR"),
            ("-", "INVALID_INT_STR"),
            ("12a", "INVALID_INT_STR"),
            ("\u0661", "INVALID_INT_STR"),
            ("9" * 617, "INT_DIGIT_LIMIT"),
        ):
            with self.assertRaises(oracle.AletheiaError) as ctx:
                oracle.parse_q(bad)
            self.assertEqual(ctx.exception.code, code)

    def test_json_validation_and_strict_parser(self) -> None:
        self.assertEqual(oracle.parse_strict_json_text('{"a":[1,true,null,"ok"]}'), {"a": [1, True, None, "ok"]})
        self.assertEqual(oracle.parse_strict_json_text("[1,2]", require_object=False), [1, 2])
        oracle.validate_json_value([[0]], max_depth=2)
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.validate_json_value([[0]], max_depth=1)
        self.assertEqual(ctx.exception.code, "MAX_DEPTH_EXCEEDED")
        deep: object = 0
        for _ in range(1500):
            deep = [deep]
        cyc: list[object] = []
        cyc.append(cyc)
        for bad, code in (
            (deep, "MAX_DEPTH_EXCEEDED"),
            (cyc, "MAX_DEPTH_EXCEEDED"),
            ({1: "x"}, "NON_STR_KEY"),
            ({chr(0xD800): "x"}, "INVALID_UTF8"),
            ({"k": chr(0xD800)}, "INVALID_UTF8"),
            ({"k": 1.5}, "FLOAT_FORBIDDEN"),
            ({"k": _IntSub(1)}, "UNSUPPORTED_JSON_TYPE"),
            ({"k": (1, 2)}, "UNSUPPORTED_JSON_TYPE"),
        ):
            with self.assertRaises(oracle.AletheiaError) as ctx:
                oracle.validate_json_value(bad)
            self.assertEqual(ctx.exception.code, code)

        for raw, code in (
            (123, "INVALID_STR_TYPE"),
            ('{"s":"' + chr(0xD800) + '"}', "INVALID_UTF8"),
            ("   \n\t ", "EMPTY_JSON_INPUT"),
            ('{"x":1.5}', "JSON_FLOAT_FORBIDDEN"),
            ('{"x":NaN}', "JSON_CONSTANT_FORBIDDEN"),
            ('{"x":Infinity}', "JSON_CONSTANT_FORBIDDEN"),
            ('{"x":' + ("9" * 5000) + "}", "INT_DIGIT_LIMIT"),
            ('{"a":1,"a":2}', "JSON_DUPLICATE_KEY"),
            ("{bad", "JSON_SYNTAX_ERROR"),
            ("[1,2]", "JSON_ROOT_NOT_OBJECT"),
            ("[" * 100 + "0" + "]" * 100, "MAX_DEPTH_EXCEEDED"),
            ('{"s":"\\ud800"}', "INVALID_UTF8"),
        ):
            with self.assertRaises(oracle.AletheiaError) as ctx:
                oracle.parse_strict_json_text(raw)  # type: ignore[arg-type]
            self.assertEqual(ctx.exception.code, code)
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.parse_strict_json_text('{"a":1}', require_object=1)  # type: ignore[arg-type]
        self.assertEqual(ctx.exception.code, "INVALID_BOOL_TYPE")
        with patch.object(oracle, "MAX_JSON_BYTES", 7):
            self.assertEqual(oracle.parse_strict_json_text('{"a":1}'), {"a": 1})
            with self.assertRaises(oracle.AletheiaError) as ctx:
                oracle.parse_strict_json_text('{"a":12}')
            self.assertEqual(ctx.exception.code, "JSON_TOO_LARGE")

    def test_file_io_symlinks_fifo_crlf_and_errors(self) -> None:
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.require_no_symlink_path("not_a_path")  # type: ignore[arg-type]
        self.assertEqual(ctx.exception.code, "INVALID_PATH_TYPE")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.require_no_symlink_path(_PathSub("sub"))
        self.assertEqual(ctx.exception.code, "INVALID_PATH_TYPE")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.require_no_symlink_path(Path("bad\x00name"))
        self.assertEqual(ctx.exception.code, "INVALID_PATH_NUL")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.read_strict_utf8_file(Path("a" * 5000))
        self.assertEqual(ctx.exception.code, "FILE_NOT_FOUND")
        with patch.object(Path, "is_symlink", side_effect=OSError("stat_err")):
            with self.assertRaises(oracle.AletheiaError) as ctx:
                oracle.require_no_symlink_path(Path("x"))
            self.assertEqual(ctx.exception.code, "PATH_OS_ERROR")

        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            reg = root / "ok.json"
            reg.write_bytes(b'{"a":1}\n')
            raw, txt = oracle.read_strict_utf8_file(reg)
            self.assertEqual(raw, b'{"a":1}\n')
            self.assertEqual(txt, '{"a":1}\n')

            # Symlink target & symlink ancestor
            sym = root / "sym.json"
            sym.symlink_to(reg)
            with self.assertRaises(oracle.AletheiaError) as ctx:
                oracle.read_strict_utf8_file(sym)
            self.assertEqual(ctx.exception.code, "SYMLINK_FORBIDDEN")

            sub = root / "real_dir"
            sub.mkdir()
            (sub / "f.json").write_bytes(b'{"a":1}')
            sym_dir = root / "sym_dir"
            sym_dir.symlink_to(sub)
            with self.assertRaises(oracle.AletheiaError) as ctx:
                oracle.read_strict_utf8_file(sym_dir / "f.json")
            self.assertEqual(ctx.exception.code, "SYMLINK_ANCESTOR_FORBIDDEN")

            # Relative path with symlink component + '..' traversal
            old_cwd = Path.cwd()
            try:
                os.chdir(root)
                with self.assertRaises(oracle.AletheiaError) as ctx:
                    oracle.require_no_symlink_path(Path("sym_dir/../ok.json"))
                self.assertEqual(ctx.exception.code, "SYMLINK_ANCESTOR_FORBIDDEN")
            finally:
                os.chdir(old_cwd)

            # Missing, directory, FIFO (both read and write!), CR/CRLF, bad UTF-8, oversized
            with self.assertRaises(oracle.AletheiaError) as ctx:
                oracle.read_strict_utf8_file(root / "missing.json")
            self.assertEqual(ctx.exception.code, "FILE_NOT_FOUND")
            with self.assertRaises(oracle.AletheiaError) as ctx:
                oracle.read_strict_utf8_file(sub)
            self.assertEqual(ctx.exception.code, "NOT_REGULAR_FILE")
            fifo = root / "pipe.fifo"
            os.mkfifo(fifo)
            with self.assertRaises(oracle.AletheiaError) as ctx:
                oracle.read_strict_utf8_file(fifo)
            self.assertEqual(ctx.exception.code, "NOT_REGULAR_FILE")
            with self.assertRaises(oracle.AletheiaError) as ctx:
                audit.write_certificate_file(sub)
            self.assertEqual(ctx.exception.code, "NOT_REGULAR_FILE")
            with self.assertRaises(oracle.AletheiaError) as ctx:
                audit.write_certificate_file(fifo)
            self.assertEqual(ctx.exception.code, "NOT_REGULAR_FILE")

            crlf = root / "crlf.json"
            crlf.write_bytes(b'{"a":1}\r\n')
            with self.assertRaises(oracle.AletheiaError) as ctx:
                oracle.read_strict_utf8_file(crlf)
            self.assertEqual(ctx.exception.code, "CR_LINE_ENDINGS_FORBIDDEN")

            bad_u8 = root / "bad_u8.json"
            bad_u8.write_bytes(b"\xff\xfe")
            with self.assertRaises(oracle.AletheiaError) as ctx:
                oracle.read_strict_utf8_file(bad_u8)
            self.assertEqual(ctx.exception.code, "INVALID_UTF8")

            with patch.object(oracle, "MAX_JSON_BYTES", 8):
                self.assertEqual(oracle.read_strict_utf8_file(reg)[0], b'{"a":1}\n')
            with patch.object(oracle, "MAX_JSON_BYTES", 7):
                with self.assertRaises(oracle.AletheiaError) as ctx:
                    oracle.read_strict_utf8_file(reg)
                self.assertEqual(ctx.exception.code, "FILE_TOO_LARGE")

            # Read/write OSError wrapping
            unreadable = root / "noperm.json"
            unreadable.write_bytes(b'{"a":1}')
            with patch.object(Path, "read_bytes", side_effect=PermissionError("denied")):
                with self.assertRaises(oracle.AletheiaError) as ctx:
                    oracle.read_strict_utf8_file(unreadable)
                self.assertEqual(ctx.exception.code, "FILE_READ_ERROR")
            with patch.object(Path, "lstat", side_effect=PermissionError("stat_denied")):
                with self.assertRaises(oracle.AletheiaError) as ctx:
                    audit.write_certificate_file(root / "w_stat.json")
                self.assertEqual(ctx.exception.code, "FILE_WRITE_ERROR")
            with patch.object(Path, "write_bytes", side_effect=PermissionError("denied")):
                with patch.object(audit, "build_standalone_certificate", return_value={"ok": True}):
                    with self.assertRaises(oracle.AletheiaError) as ctx:
                        audit.write_certificate_file(root / "w.json")
                    self.assertEqual(ctx.exception.code, "FILE_WRITE_ERROR")


class TestPart3Mechanics(unittest.TestCase):
    """Exact coverage of every Part III hero ability, Goblin/Priest rule, and purple door rule."""

    def test_grid_and_key_errors(self) -> None:
        for bad_grid in (None, [], [123], ["###", "##"], ["###", "#?#", "###"]):
            with self.assertRaises(oracle.AletheiaError):
                oracle.Part3Oracle(bad_grid)  # type: ignore[arg-type]
        for bad_fn in (
            oracle.eval_iii14_coupled,
            oracle.eval_iii20_coupled,
            oracle.eval_iii21_coupled,
            oracle.eval_naive_unpartitioned_iii21,
        ):
            with self.assertRaises(oracle.AletheiaError) as ctx:
                bad_fn(None)  # type: ignore[arg-type]
            self.assertEqual(ctx.exception.code, "INVALID_ORACLE_STATE")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.verify_concrete_room_bound("NOPE", oracle.eval_iii14_coupled)
        self.assertEqual(ctx.exception.code, "UNKNOWN_ROOM")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.verify_concrete_room_bound("III-14", None)  # type: ignore[arg-type]
        self.assertEqual(ctx.exception.code, "INVALID_EVAL_FN")
        ps = oracle.Part3Oracle(["###", "#F#", "###"])
        with self.assertRaises(oracle.AletheiaError):
            ps.step("X")
        # Dead / no active hero state
        ps.obj[1][1] = None
        self.assertEqual(ps.step("R"), (False, False))

    def test_all_six_heroes_and_special_rules(self) -> None:
        # Fighter multi-push chain + blocked push
        pf = oracle.Part3Oracle(["#######", "#F**..#", "#######"])
        self.assertEqual(pf.step("R"), (True, False))
        self.assertEqual(pf.obj[1][2:5], ["F", "*", "*"])
        pf.step("R")
        before = [r[:] for r in pf.obj]
        pf.step("R")  # blocked by right wall
        self.assertEqual(pf.obj, before)

        # Thief pull + walk without behind moveable
        pt = oracle.Part3Oracle(["######", "#*T..#", "######"])
        pt.step("R")
        self.assertEqual(pt.obj[1][2:4], ["*", "T"])
        pt.step("L")  # blocked by crate
        self.assertEqual(pt.obj[1][3], "T")
        pt2 = oracle.Part3Oracle(["######", "#.T..#", "######"])
        pt2.step("R")
        self.assertEqual(pt2.obj[1][2:4], [None, "T"])

        # Wizard swap + static-stop walk + board-edge walk (no outer border!)
        pw = oracle.Part3Oracle(["W..*#", "....."])
        pw.step("R")
        self.assertEqual((pw.obj[0][0], pw.obj[0][3]), ("*", "W"))
        pw2 = oracle.Part3Oracle(["W..#", "...."])
        pw2.step("R")
        self.assertEqual(pw2.obj[0][1], "W")
        pw3 = oracle.Part3Oracle(["W...", "...."])
        pw3.step("R")
        self.assertEqual(pw3.obj[0][1], "W")

        # Priest immunity + orthogonal shield + Goblin mutual kill + Hero death
        pp = oracle.Part3Oracle(["######", "#P.O.#", "#.1..#", "######"])
        self.assertEqual(pp.step("R"), (True, False))  # P adjacent to O -> P survives & shields 1
        self.assertEqual(pp.obj[1][2], "P")
        self.assertEqual(pp.obj[2][2], "1")
        pg = oracle.Part3Oracle(["######", "#FO.O#", "######"])
        # Push O into O -> mutual kill
        pg2 = oracle.Part3Oracle(["#######", "#F.O.O#", "#######"])
        pg2.step("R")  # F moves adjacent to O -> F dies!
        self.assertEqual(pg2.obj[1][2], "CORPSE")
        pg3 = oracle.Part3Oracle(["#######", "#F*O.O#", "#######"])
        alive, _ = pg3.step("R")
        self.assertTrue(alive)
        self.assertIsNone(pg3.obj[1][4])
        self.assertIsNone(pg3.obj[1][5])

        # Druid # <-> *, O -> #, ally petrification vs Priest shield vs healer immunity
        pd = oracle.Part3Oracle(["#######", "#D*#O.#", "#######"])
        pd.step("R")  # * -> #
        self.assertEqual(pd.obj[1][2], "#")
        pd.step("R")  # # -> *
        self.assertEqual(pd.obj[1][2], "*")
        pd2 = oracle.Part3Oracle(["######", "#DO..#", "######"])
        alive, _ = pd2.step("R")  # wait: D starts adjacent to O -> dies at init! Test safe start:
        self.assertFalse(alive)
        pd3 = oracle.Part3Oracle(["######", "#D1..#", "######"])
        pd3.step("R")  # D petrifies unshielded 1 -> #
        self.assertEqual(pd3.obj[1][2], "#")
        pd4 = oracle.Part3Oracle(["######", "#D14.#", "######"])
        pd4.step("R")  # 4 shields 1 -> 1 stays 1!
        self.assertEqual(pd4.obj[1][2], "1")
        pd5 = oracle.Part3Oracle(["######", "#D4..#", "######"])
        pd5.step("R")  # Priest immune to Druid
        self.assertEqual(pd5.obj[1][2], "4")

        # Bard blocked rollback + purple door open/close/crush + cyclic 'A' switch
        pb = oracle.Part3Oracle(["######", "#B*.}#", "#..].#", "######"])
        before_b = [r[:] for r in pb.obj]
        pb.step("L")  # blocked by left wall -> rollback
        self.assertEqual(pb.obj, before_b)
        pb2 = oracle.Part3Oracle(["#######", "#B*}]G#", "#######"])
        pb2.step("R")  # moves * onto } -> door ] opens!
        self.assertIsNone(pb2.obj[1][4])
        self.assertEqual(pb2.floor[1][4], "PO")
        # Step onto open door while unweighing switch -> crushed!
        pb3 = oracle.Part3Oracle(["#######", "#.B}]G#", "#######"])
        pb3.step("R")  # B steps onto }, door opens
        pb3.step("R")  # B steps onto PO leaving } unweighed -> door slams shut crushing B!
        self.assertEqual(pb3.obj[1][4], "]")
        # Cyclic 'A' switch wrapping 6 -> 1
        pa = oracle.Part3Oracle(["#####", "#D1.#", "#####"])
        pa.step("A")
        self.assertEqual((pa.obj[1][1], pa.obj[1][2]), ("6", "F"))


class TestFarkasLPAndDeadlockEngine(unittest.TestCase):
    """Exact primal/dual Farkas LP verification, negative tampering tests, and deadlock cut checks."""

    def test_farkas_solver_validation_and_negative_controls(self) -> None:
        q_ok = oracle.QuotientGraph("q", 2, 1, (0,), ((1, 0, "A"),))
        cert = oracle.solve_coupled_farkas_lp(
            instance_id="tiny",
            action_classes=("A",),
            quotients=(q_ok,),
            cost_partition=({"A": Fraction(1)},),
        )
        res = audit.verify_coupled_farkas_certificate(cert)
        self.assertTrue(res["verified"])
        self.assertEqual(res["primal_q"], "1")

        # Solver input errors
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.solve_coupled_farkas_lp(instance_id=123, action_classes=("A",), quotients=(q_ok,), cost_partition=({},))  # type: ignore[arg-type]
        self.assertEqual(ctx.exception.code, "INVALID_FARKAS_INPUT")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.solve_coupled_farkas_lp(instance_id="e", action_classes=("A",), quotients=(q_ok,), cost_partition=("bad",))  # type: ignore[arg-type]
        self.assertEqual(ctx.exception.code, "INVALID_FARKAS_INPUT")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.solve_coupled_farkas_lp(instance_id="e", action_classes=("A",), quotients=("not_qg",), cost_partition=({},))  # type: ignore[arg-type]
        self.assertEqual(ctx.exception.code, "INVALID_QUOTIENT")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.solve_coupled_farkas_lp(instance_id="e", action_classes=(), quotients=(q_ok,), cost_partition=({},))
        self.assertEqual(ctx.exception.code, "INVALID_FARKAS_INPUT")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.solve_coupled_farkas_lp(instance_id="e", action_classes=("A", "A"), quotients=(q_ok,), cost_partition=({},))
        self.assertEqual(ctx.exception.code, "DUPLICATE_ACTION_CLASS")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.solve_coupled_farkas_lp(instance_id="e", action_classes=("A",), quotients=(q_ok,), cost_partition=({"A": Fraction(-1)},))
        self.assertEqual(ctx.exception.code, "NEGATIVE_WEIGHT")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.solve_coupled_farkas_lp(
                instance_id="e",
                action_classes=("A",),
                quotients=(q_ok, q_ok),
                cost_partition=({"A": Fraction(2, 3)}, {"A": Fraction(2, 3)}),
            )
        self.assertEqual(ctx.exception.code, "COST_PARTITION_EXCEEDS_ONE")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.solve_coupled_farkas_lp(
                instance_id="e",
                action_classes=("A",),
                quotients=(oracle.QuotientGraph("eg", 2, 1, (), ()),),
                cost_partition=({"A": Fraction(1)},),
            )
        self.assertEqual(ctx.exception.code, "EMPTY_GOALS")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.solve_coupled_farkas_lp(
                instance_id="e",
                action_classes=("A",),
                quotients=(oracle.QuotientGraph("ua", 2, 1, (0,), ((1, 0, "B"),)),),
                cost_partition=({"A": Fraction(1)},),
            )
        self.assertEqual(ctx.exception.code, "UNKNOWN_ACTION_CLASS")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.solve_coupled_farkas_lp(
                instance_id="e",
                action_classes=("A",),
                quotients=(oracle.QuotientGraph("unr", 2, 1, (0,), ()),),
                cost_partition=({"A": Fraction(1)},),
            )
        self.assertEqual(ctx.exception.code, "QUOTIENT_UNREACHABLE")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.solve_coupled_farkas_lp(
                instance_id="e",
                action_classes=("A",),
                quotients=(oracle.QuotientGraph("punr", 3, 1, (0,), ((1, 0, "A"),)),),
                cost_partition=({"A": Fraction(1)},),
            )
        self.assertEqual(ctx.exception.code, "QUOTIENT_PARTIAL_UNREACHABLE")
        # Non-tight partition (duality gap nonzero)
        q_short = oracle.QuotientGraph("qs", 2, 1, (0,), ((1, 0, "A"),))
        q_long = oracle.QuotientGraph("ql", 3, 2, (0,), ((2, 1, "A"), (1, 0, "A")))
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.solve_coupled_farkas_lp(
                instance_id="gap",
                action_classes=("A",),
                quotients=(q_short, q_long),
                cost_partition=({"A": Fraction(1, 2)}, {"A": Fraction(1, 2)}),
            )
        self.assertEqual(ctx.exception.code, "NONZERO_DUALITY_GAP")

    def test_independent_farkas_verifier_rejects_every_tamper(self) -> None:
        base = oracle.build_fractional_shared_action_certificate()
        self.assertTrue(audit.verify_coupled_farkas_certificate(base)["verified"])

        def _check_tamper(mutator, code: str) -> None:
            bad = copy.deepcopy(base)
            mutator(bad)
            with self.assertRaises(oracle.AletheiaError) as ctx:
                audit.verify_coupled_farkas_certificate(bad)
            self.assertEqual(ctx.exception.code, code)

        with self.assertRaises(oracle.AletheiaError):
            audit.verify_coupled_farkas_certificate([])  # type: ignore[arg-type]
        _check_tamper(lambda d: d.update(action_classes="SHARED"), "INVALID_LIST")
        _check_tamper(lambda d: d.update(action_classes=[]), "INVALID_ACTIONS")

        # Zero lambda and zero flow edge valid boundary tests (kills lv<=0 and fv<=0)
        q_zero_l = oracle.QuotientGraph("qz", 2, 1, (0,), ((1, 0, "A"), (1, 0, "UNUSED")))
        cert_zl = oracle.solve_coupled_farkas_lp(
            instance_id="zero_lambda",
            action_classes=("A", "UNUSED"),
            quotients=(q_zero_l,),
            cost_partition=({"A": Fraction(1), "UNUSED": Fraction(1)},),
        )
        cert_zl["quotients"][0]["dual_flow_edges"].append([1, "0"])
        self.assertTrue(audit.verify_coupled_farkas_certificate(cert_zl)["verified"])
        _check_tamper(lambda d: d.update(action_classes=["SHARED", "SHARED"]), "DUPLICATE_ACTION")
        _check_tamper(lambda d: d.update(quotients=[]), "EMPTY_QUOTIENTS")
        _check_tamper(lambda d: d["dual_lambda"].pop("SHARED"), "MISSING_LAMBDA")
        _check_tamper(lambda d: d["dual_lambda"].update(SHARED="-1"), "NEGATIVE_LAMBDA")
        _check_tamper(lambda d: d["quotients"][0].update(goals=[]), "EMPTY_GOALS")
        _check_tamper(lambda d: d["quotients"][0]["weights"].pop("SHARED"), "MISSING_WEIGHT")
        _check_tamper(lambda d: d["quotients"][0]["weights"].update(SHARED="-1/3"), "NEGATIVE_WEIGHT")
        _check_tamper(lambda d: d["quotients"][0]["primal_h"].pop(), "PRIMAL_H_LEN")
        _check_tamper(lambda d: d["quotients"][0]["primal_h"].__setitem__(0, "1"), "GOAL_POTENTIAL_NONZERO")
        _check_tamper(lambda d: d["quotients"][0].update(primal_start_q="99"), "PRIMAL_START_MISMATCH")
        _check_tamper(lambda d: d["quotients"][0]["edges"].__setitem__(0, [3, 2]), "EDGE_ARITY")
        _check_tamper(lambda d: d["quotients"][0]["edges"].__setitem__(0, [3, 2, "NOPE"]), "EDGE_ACTION_INVALID")
        _check_tamper(lambda d: d["quotients"][0]["primal_h"].__setitem__(2, "0"), "BELLMAN_INFEASIBLE")
        _check_tamper(lambda d: d["quotients"][0]["dual_flow_edges"].__setitem__(0, [0]), "FLOW_PAIR_ARITY")
        _check_tamper(lambda d: d["quotients"][0]["dual_flow_edges"].append([0, "1"]), "DUPLICATE_FLOW_EDGE")
        _check_tamper(lambda d: d["quotients"][0]["dual_flow_edges"].__setitem__(0, [0, "-1"]), "NEGATIVE_FLOW")
        _check_tamper(lambda d: d["quotients"][0]["dual_flow_edges"].__setitem__(0, [0, "2"]), "FLOW_CONSERVATION_FAIL")
        _check_tamper(lambda d: d["dual_lambda"].update(SHARED="1"), "DUAL_CAPACITY_EXCEEDED")
        _check_tamper(lambda d: d["quotients"][0]["weights"].update(SHARED="2/3"), "COST_PARTITION_SUM_GT_ONE")
        _check_tamper(lambda d: d["dual_lambda"].update(SHARED="3"), "STRONG_DUALITY_GAP")
        _check_tamper(lambda d: d.update(primal_objective_q="99"), "PRIMAL_OBJ_MISMATCH")
        _check_tamper(lambda d: d.update(dual_objective_q="99"), "DUAL_OBJ_MISMATCH")
        _check_tamper(lambda d: d.update(ceil_integer_bound=99), "CEIL_MISMATCH")

    def test_deadlock_certifier_and_verifier_tamper_controls(self) -> None:
        self.assertEqual(oracle.independent_bfs_distance(3, 0, (2,), ((0, 1), (1, 2))), 2)
        self.assertIsNone(oracle.independent_bfs_distance(2, 0, (1,), ()))
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.independent_bfs_distance(2, 0, None, ())  # type: ignore[arg-type]
        self.assertEqual(ctx.exception.code, "INVALID_GRAPH_CONTAINER")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.independent_bfs_distance(2, 0, (1,), ((0,),))  # type: ignore[arg-type]
        self.assertEqual(ctx.exception.code, "INVALID_EDGE")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.certify_farkas_deadlock(
                witness_id="bad_in",
                num_vertices=2,
                start=0,
                goals=None,  # type: ignore[arg-type]
                edges=(),
                one_entity_projections=(),
            )
        self.assertEqual(ctx.exception.code, "INVALID_DEADLOCK_INPUT")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.certify_farkas_deadlock(
                witness_id="bad_e",
                num_vertices=2,
                start=0,
                goals=(1,),
                edges=((0,),),  # type: ignore[arg-type]
                one_entity_projections=(),
            )
        self.assertEqual(ctx.exception.code, "INVALID_EDGE")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.certify_farkas_deadlock(
                witness_id="reach",
                num_vertices=2,
                start=0,
                goals=(1,),
                edges=((0, 1),),
                one_entity_projections=[],
            )
        self.assertEqual(ctx.exception.code, "NOT_DEADLOCK")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.certify_farkas_deadlock(
                witness_id="bad_proj",
                num_vertices=2,
                start=0,
                goals=(1,),
                edges=(),
                one_entity_projections=[{"name": "p", "num_vertices": 2, "start": 0, "goals": [1], "edges": []}],
            )
        self.assertEqual(ctx.exception.code, "PROJECTION_NOT_FINITE")

        base = oracle.certify_farkas_deadlock(
            witness_id="dl",
            num_vertices=3,
            start=0,
            goals=(2,),
            edges=((0, 1), (1, 0)),
            one_entity_projections=[{"name": "p1", "num_vertices": 2, "start": 0, "goals": [1], "edges": [[0, 1]]}],
        )
        self.assertTrue(audit.verify_deadlock_cut_certificate(base)["verified"])

        def _tamper_dl(mutator, code: str) -> None:
            bad = copy.deepcopy(base)
            mutator(bad)
            with self.assertRaises(oracle.AletheiaError) as ctx:
                audit.verify_deadlock_cut_certificate(bad)
            self.assertEqual(ctx.exception.code, code)

        _tamper_dl(lambda d: d.update(reachable_cut_set=[1]), "START_NOT_IN_CUT")
        _tamper_dl(lambda d: d.update(reachable_cut_set=[0, 1, 2]), "GOAL_IN_CUT")
        _tamper_dl(lambda d: d.update(edges=[[0]]), "EDGE_ARITY")
        _tamper_dl(lambda d: d["edges"].append([1, 2]), "CUT_NOT_CLOSED")
        _tamper_dl(lambda d: d.update(one_entity_projections=[]), "MISSING_PROJECTIONS")


class TestZZFrontierRoomsAndCLI(unittest.TestCase):
    """End-to-end verification of III-14 (24), III-20 (9), III-21 (30), deadlocks, controls, and CLI."""

    def test_evaluator_edge_states(self) -> None:
        # Degenerate missing-hero states return 0 safely
        empty14 = oracle.Part3Oracle(oracle.FRONTIER_CATALOG["III-14"]["grid"])
        for y in range(empty14.h):
            for x in range(empty14.w):
                if empty14.is_hero(empty14.obj[y][x]):
                    empty14.obj[y][x] = None
        self.assertEqual(oracle.eval_iii14_coupled(empty14)[0], 0)
        empty20 = oracle.Part3Oracle(oracle.FRONTIER_CATALOG["III-20"]["grid"])
        for y in range(empty20.h):
            for x in range(empty20.w):
                if empty20.is_hero(empty20.obj[y][x]):
                    empty20.obj[y][x] = None
        self.assertEqual(oracle.eval_iii20_coupled(empty20)[0], 0)
        empty21 = oracle.Part3Oracle(oracle.FRONTIER_CATALOG["III-21"]["grid"])
        for y in range(empty21.h):
            for x in range(empty21.w):
                if empty21.is_hero(empty21.obj[y][x]):
                    empty21.obj[y][x] = None
        self.assertEqual(oracle.eval_iii21_coupled(empty21)[0], 0)

        # Internal helper & state-cap boundary tests (kills M073..M079, M082, M083, BoolOp L1862)
        no_hero = oracle.Part3Oracle(("###", "#.#", "###"))
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle._require_active_slot(no_hero)
        self.assertEqual(ctx.exception.code, "MISSING_ACTIVE_HERO")
        oracle.require_pairwise_disjoint(({1}, {2}))
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle.require_pairwise_disjoint(({1, 2}, {2, 3}))
        self.assertEqual(ctx.exception.code, "BARRIERS_NOT_DISJOINT")

        n_s, _, _, _ = oracle._build_concrete_subproblem_graph(("#####", "#F..#", "#####"), max_states=3)
        self.assertEqual(n_s, 3)
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle._build_concrete_subproblem_graph(("#####", "#F..#", "#####"), max_states=2)
        self.assertEqual(ctx.exception.code, "SUBPROBLEM_STATE_CAP")

        d_w, r_w = oracle._concrete_bfs_shortest_win(("######", "#F..G#", "######"), max_states=3)
        self.assertEqual((d_w, r_w), (3, "RRR"))
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle._concrete_bfs_shortest_win(("######", "#F..G#", "######"), max_states=2)
        self.assertEqual(ctx.exception.code, "BFS_STATE_CAP")
        with self.assertRaises(oracle.AletheiaError) as ctx:
            oracle._concrete_bfs_shortest_win(("#####", "#F#G#", "#####"), max_states=10)
        self.assertEqual(ctx.exception.code, "SLICE_UNSOLVABLE")

        # Synthetic room route failure guards (ROUTE_DIED, ROUTE_NOT_WIN on not won AND on h_end != 0)
        syn_rooms = {
            "SYN_DIE": {
                "grid": ("#####", "#F.O#", "#####"),
                "reference_route": "R",
                "prior_1box_bounds": {},
                "proven_floor": 1,
                "shortest_known": 1,
            },
            "SYN_NOWIN": {
                "grid": ("#####", "#F.G#", "#####"),
                "reference_route": "R",
                "prior_1box_bounds": {},
                "proven_floor": 2,
                "shortest_known": 2,
            },
            "SYN_HEND": {
                "grid": ("####", "#FG#", "####"),
                "reference_route": "R",
                "prior_1box_bounds": {},
                "proven_floor": 1,
                "shortest_known": 1,
            },
        }
        with patch.dict(oracle.FRONTIER_CATALOG, syn_rooms):
            with self.assertRaises(oracle.AletheiaError) as ctx:
                oracle.verify_concrete_room_bound("SYN_DIE", lambda _: (0, {}))
            self.assertEqual(ctx.exception.code, "ROUTE_DIED")
            with self.assertRaises(oracle.AletheiaError) as ctx:
                oracle.verify_concrete_room_bound("SYN_NOWIN", lambda _: (0, {}))
            self.assertEqual(ctx.exception.code, "ROUTE_NOT_WIN")
            with self.assertRaises(oracle.AletheiaError) as ctx:
                oracle.verify_concrete_room_bound("SYN_HEND", lambda _: (1, {}))
            self.assertEqual(ctx.exception.code, "ROUTE_NOT_WIN")

        # Audit build_standalone_certificate internal invariant guards (M051, M052, M053)
        fake_ok = {
            "III-14": {"root_coupled_bound": 24, "bellman_1step_consistent": True, "residual_gap_to_floor": 20, "residual_gap_to_known": 24, "total_edges_checked": 1},
            "III-20": {"root_coupled_bound": 9, "bellman_1step_consistent": True, "residual_gap_to_floor": 68, "residual_gap_to_known": 75, "total_edges_checked": 1},
            "III-21": {"root_coupled_bound": 30, "bellman_1step_consistent": True, "residual_gap_to_floor": 240, "residual_gap_to_known": 286, "total_edges_checked": 1},
        }
        with patch.object(audit, "verify_concrete_room_bound", side_effect=lambda r, _fn: {**fake_ok[r], "root_coupled_bound": 99}):
            with self.assertRaises(oracle.AletheiaError) as ctx:
                audit.build_standalone_certificate()
            self.assertEqual(ctx.exception.code, "ROOT_FARKAS_CONCRETE_MISMATCH")
        with patch.object(audit, "verify_concrete_room_bound", side_effect=lambda r, _fn: {**fake_ok[r], "bellman_1step_consistent": False}):
            with self.assertRaises(oracle.AletheiaError) as ctx:
                audit.build_standalone_certificate()
            self.assertEqual(ctx.exception.code, "BELLMAN_CHECK_FAILED")
        with patch.object(audit, "verify_concrete_room_bound", side_effect=lambda r, _fn: fake_ok[r]):
            with patch.object(audit, "build_deadlock_and_coupling_witnesses", return_value={
                "iii14_bard_2crate_deadlock": oracle.certify_farkas_deadlock(witness_id="a", num_vertices=2, start=0, goals=(1,), edges=(), one_entity_projections=[{"name": "p", "num_vertices": 2, "start": 0, "goals": [1], "edges": [[0, 1]]}]),
                "iii20_goblin_ring_deadlock": oracle.certify_farkas_deadlock(witness_id="b", num_vertices=2, start=0, goals=(1,), edges=(), one_entity_projections=[{"name": "p", "num_vertices": 2, "start": 0, "goals": [1], "edges": [[0, 1]]}]),
                "iii21_wizard_alcove_deadlock": oracle.certify_farkas_deadlock(witness_id="c", num_vertices=2, start=0, goals=(1,), edges=(), one_entity_projections=[{"name": "p", "num_vertices": 2, "start": 0, "goals": [1], "edges": [[0, 1]]}]),
            }):
                with patch.object(audit, "verify_naive_must_fail_control", return_value={"correctly_falsified": False}):
                    with self.assertRaises(oracle.AletheiaError) as ctx:
                        audit.build_standalone_certificate()
                    self.assertEqual(ctx.exception.code, "MUST_FAIL_NOT_TRIGGERED")

        # Non-str argv guard in audit.main
        buf_e = io.StringIO()
        with patch("sys.stderr", buf_e):
            self.assertEqual(audit.main([123]), 2)  # type: ignore[list-item]
        self.assertEqual(json.loads(buf_e.getvalue())["error_code"], "INVALID_ARGV")

        # III-14 active Bard with need_w2c >= 1 -> a_sw == 2; need_w2c == 0 & weighed == 9 -> a_sw == 0
        p14 = oracle.Part3Oracle(oracle.FRONTIER_CATALOG["III-14"]["grid"])
        p14.step("A")
        self.assertEqual(oracle.eval_iii14_coupled(p14)[1]["a_sw"], 2)
        for x, y in oracle.TOPO["s9"]:
            p14.obj[y][x] = "*"
        self.assertEqual(oracle.eval_iii14_coupled(p14)[1]["w2c"], 0)
        self.assertEqual(oracle.eval_iii14_coupled(p14)[1]["a_sw"], 0)
        p14.obj[2][4] = None
        p14.obj[1][1] = "*"
        p14.step("A")
        self.assertEqual(oracle.eval_iii14_coupled(p14)[1]["a_sw"], 1)

    def test_z_all_rooms_deadlocks_cli_and_tamper_rejections(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            cpath = Path(td) / "cert.json"
            buf_out = io.StringIO()
            with patch("sys.stdout", buf_out):
                rc = audit.main(["--write", str(cpath), "--json"])
            self.assertEqual(rc, 0)
            w_res = json.loads(buf_out.getvalue())
            self.assertTrue(w_res["written"])

            raw_obj = json.loads(cpath.read_text(encoding="utf-8"))
            p = raw_obj["payload"]
            by_id = {row["room_id"]: row for row in p["summary_table"]}
            self.assertEqual(by_id["III-14"]["coupled_farkas_root"], 24)
            self.assertEqual(by_id["III-14"]["strict_gain_over_prior"], 3)
            self.assertEqual(by_id["III-20"]["coupled_farkas_root"], 9)
            self.assertEqual(by_id["III-20"]["strict_gain_over_prior"], 6)
            self.assertEqual(by_id["III-21"]["coupled_farkas_root"], 30)
            self.assertEqual(by_id["III-21"]["strict_gain_over_prior"], 9)
            self.assertEqual(p["farkas_certificates"]["FRAC_SHARED"]["primal_objective_q"], "4")
            self.assertEqual(
                [q["primal_start_q"] for q in p["farkas_certificates"]["FRAC_SHARED"]["quotients"]],
                ["5/3", "7/3"],
            )
            self.assertFalse(p["law2b_scope_and_residual_gaps"]["closes_global_frontier_optimality"])
            self.assertTrue(p["must_fail_naive_control"]["correctly_falsified"])
            self.assertEqual(p["must_fail_naive_control"]["bellman_violation_count"], 22)
            self.assertEqual(p["must_fail_naive_control"]["max_1step_drop"], 9)
            self.assertEqual(p["deadlock_witnesses"]["iii20_priest_escort_restoration_distance"], 9)
            self.assertEqual(len(p["deadlock_witnesses"]["iii20_priest_escort_witness_route"]), 9)
            for rid in ("III-14", "III-20", "III-21"):
                self.assertEqual(p["concrete_room_checks"][rid]["admissibility_violations"], 0)
                self.assertLessEqual(p["concrete_room_checks"][rid]["max_1step_drop"], 1)
                self.assertTrue(p["concrete_room_checks"][rid]["route_exact_win"])
                self.assertTrue(p["deadlock_independent_checks"][rid]["verified"])

            buf_out = io.StringIO()
            with patch("sys.stdout", buf_out):
                rc = audit.main(["--check", str(cpath)])
            self.assertEqual(rc, 0)
            self.assertIn("OK ", buf_out.getvalue())

            buf_out = io.StringIO()
            with patch("sys.stdout", buf_out):
                rc = audit.main(["--standalone", "--json"])
            self.assertEqual(rc, 0)
            standalone = json.loads(buf_out.getvalue())
            self.assertEqual(standalone["payload_sha256"], w_res["payload_sha256"])

            # Non-canonical bytes rejected
            nc = Path(td) / "noncanon.json"
            nc.write_text(json.dumps(raw_obj, indent=2) + "\n", encoding="utf-8")
            with self.assertRaises(oracle.AletheiaError) as ctx:
                audit.check_certificate_file(nc)
            self.assertEqual(ctx.exception.code, "NON_CANONICAL_CERT_BYTES")

            # Schema version mismatch
            bad_sv = copy.deepcopy(raw_obj)
            bad_sv["schema_version"] = "wrong"
            sv_p = Path(td) / "sv.json"
            sv_p.write_bytes(oracle.canonical_json_bytes(bad_sv) + b"\n")
            with self.assertRaises(oracle.AletheiaError) as ctx:
                audit.check_certificate_file(sv_p)
            self.assertEqual(ctx.exception.code, "SCHEMA_VERSION_MISMATCH")

            # Payload SHA mismatch
            bad_sha = copy.deepcopy(raw_obj)
            bad_sha["payload_sha256"] = "0" * 64
            sha_p = Path(td) / "sha.json"
            sha_p.write_bytes(oracle.canonical_json_bytes(bad_sha) + b"\n")
            with self.assertRaises(oracle.AletheiaError) as ctx:
                audit.check_certificate_file(sha_p)
            self.assertEqual(ctx.exception.code, "PAYLOAD_SHA_MISMATCH")

            # Missing farkas/deadlock/escort tamper (all rejected before recomputation!)
            miss_f = copy.deepcopy(raw_obj)
            miss_f["payload"]["farkas_certificates"].pop("III-14")
            miss_f["payload_sha256"] = oracle.canonical_sha256(miss_f["payload"])
            mf_p = Path(td) / "mf.json"
            mf_p.write_bytes(oracle.canonical_json_bytes(miss_f) + b"\n")
            with self.assertRaises(oracle.AletheiaError) as ctx:
                audit.check_certificate_file(mf_p)
            self.assertEqual(ctx.exception.code, "MISSING_FARKAS_CERT")

            miss_d = copy.deepcopy(raw_obj)
            miss_d["payload"]["deadlock_witnesses"].pop("iii14_bard_2crate_deadlock")
            miss_d["payload_sha256"] = oracle.canonical_sha256(miss_d["payload"])
            md_p = Path(td) / "md.json"
            md_p.write_bytes(oracle.canonical_json_bytes(miss_d) + b"\n")
            with self.assertRaises(oracle.AletheiaError) as ctx:
                audit.check_certificate_file(md_p)
            self.assertEqual(ctx.exception.code, "MISSING_DEADLOCK_WITNESS")

            for bad_r, code in (
                ("AAA", "INVALID_ESCORT_ROUTE"),
                ("RRRRRRRRR", "ESCORT_ROUTE_DIED"),
                ("AAAAAAAAA", "ESCORT_ROUTE_NOT_WIN"),
            ):
                bad_e = copy.deepcopy(raw_obj)
                bad_e["payload"]["deadlock_witnesses"]["iii20_priest_escort_witness_route"] = bad_r
                bad_e["payload_sha256"] = oracle.canonical_sha256(bad_e["payload"])
                ep = Path(td) / f"esc_{bad_r}.json"
                ep.write_bytes(oracle.canonical_json_bytes(bad_e) + b"\n")
                with self.assertRaises(oracle.AletheiaError) as ctx:
                    audit.check_certificate_file(ep)
                self.assertEqual(ctx.exception.code, code)

            # True == 1 forged payload (with recomputed payload_sha256 -> caught by recomputation!)
            forg = copy.deepcopy(raw_obj)
            forg["payload"]["summary_table"][0]["strict_gain_over_prior"] = True
            forg["payload_sha256"] = oracle.canonical_sha256(forg["payload"])
            forg_p = Path(td) / "forg.json"
            forg_p.write_bytes(oracle.canonical_json_bytes(forg) + b"\n")
            with patch.object(audit, "build_standalone_certificate", return_value=raw_obj):
                with self.assertRaises(oracle.AletheiaError) as ctx:
                    audit.check_certificate_file(forg_p)
                self.assertEqual(ctx.exception.code, "RECOMPUTATION_MISMATCH")

            # CLI fail-closed exit code 2 on error
            buf_err = io.StringIO()
            with patch("sys.stderr", buf_err):
                rc_err = audit.main(["--check", str(Path(td) / "does_not_exist.json")])
            self.assertEqual(rc_err, 2)
            self.assertEqual(json.loads(buf_err.getvalue())["error_code"], "FILE_NOT_FOUND")


if __name__ == "__main__":
    unittest.main()
