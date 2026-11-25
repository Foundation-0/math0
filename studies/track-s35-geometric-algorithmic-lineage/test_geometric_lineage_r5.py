#!/usr/bin/env python3
"""Track S35 Regression, Adversarial Zone-B, Concurrency/TOCTOU & Mutation-Killing Suite.

Zero bare asserts, zero floats, zero .isdigit(), zero external dependencies, zero math RNG.
"""
from __future__ import annotations

import ast
import copy
import ctypes
from fractions import Fraction
import io
import json
import os
from pathlib import Path
import stat
import sys
import tempfile
import threading
import unittest
from contextlib import redirect_stderr, redirect_stdout
from unittest import mock

_THIS_DIR = Path(__file__).resolve().parent
if str(_THIS_DIR) not in sys.path:
    sys.path.insert(0, str(_THIS_DIR))

import geometric_lineage_audit as aud  # noqa: E402
import geometric_lineage_oracle as orc  # noqa: E402


class _EvilPath(type(Path("."))):
    """Adversarial Path subclass rejected by _require_concrete_path."""


class _EvilInt(int):
    """Adversarial int subclass rejected by require_exact_int."""


class _EvilStr(str):
    """Adversarial str subclass rejected by _require_utf8_no_surrogate."""


class _EvilFrac(Fraction):
    """Adversarial Fraction subclass rejected by require_fraction."""


class _EvilDict(dict):
    """Adversarial dict subclass rejected by _validate_json_tree."""


class _EvilList(list):
    """Adversarial list subclass rejected by _validate_json_tree."""


class TestStaticHygieneAndPrimitives(unittest.TestCase):
    def test_zero_bare_asserts_floats_isdigit_across_track(self) -> None:
        for fname in (
            "geometric_lineage_oracle.py",
            "geometric_lineage_audit.py",
            "test_geometric_lineage_r5.py",
        ):
            src = (_THIS_DIR / fname).read_text(encoding="utf-8")
            tree = ast.parse(src)
            asserts = [n.lineno for n in ast.walk(tree) if isinstance(n, ast.Assert)]
            self.assertEqual(asserts, [], f"bare assert in {fname}: {asserts}")
            floats = [n.lineno for n in ast.walk(tree) if isinstance(n, ast.Constant) and type(n.value) is float]
            self.assertEqual(floats, [], f"float literal in {fname}: {floats}")
            float_calls = [
                n.lineno
                for n in ast.walk(tree)
                if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "float"
            ]
            self.assertEqual(float_calls, [], f"float() call in {fname}: {float_calls}")
            isdigit_calls = [
                n.lineno
                for n in ast.walk(tree)
                if isinstance(n, ast.Attribute) and n.attr == "isdigit"
            ]
            self.assertEqual(isdigit_calls, [], f".isdigit() call in {fname}: {isdigit_calls}")

    def test_oracle_primitives_decimal_q3_and_bareiss(self) -> None:
        # require_ok & require_bool
        orc.require_ok(True, "X", "ok")
        with self.assertRaises(orc.GeometricLineageError) as cm_c:
            orc.require_ok(1, "X", "bad")  # type: ignore[arg-type]
        self.assertEqual(cm_c.exception.code, "INVALID_CONDITION")
        with self.assertRaises(orc.GeometricLineageError) as cm_f:
            orc.require_ok(False, "FAIL_CODE", "msg")
        self.assertEqual(cm_f.exception.code, "FAIL_CODE")
        self.assertIs(orc.require_bool(False), False)
        with self.assertRaises(orc.GeometricLineageError) as cm_b:
            orc.require_bool(0)
        self.assertEqual(cm_b.exception.code, "INVALID_BOOL")

        # require_exact_int exact boundaries & bad bounds
        lim = 10**orc.MAX_INT_DIGITS
        self.assertEqual(orc.require_exact_int(lim - 1), lim - 1)
        self.assertEqual(orc.require_exact_int(-(lim - 1)), -(lim - 1))
        self.assertEqual(orc.require_exact_int(5, lo=5, hi=5), 5)
        for bad_i in (True, _EvilInt(1), "5"):
            with self.assertRaises(orc.GeometricLineageError) as cm:
                orc.require_exact_int(bad_i)
            self.assertEqual(cm.exception.code, "INVALID_INT")
        for huge_i in (lim, -lim, 10**4300):
            with self.assertRaises(orc.GeometricLineageError) as cm:
                orc.require_exact_int(huge_i)
            self.assertEqual(cm.exception.code, "INT_DIGIT_LIMIT")
        with self.assertRaises(orc.GeometricLineageError) as cm_lo:
            orc.require_exact_int(4, lo=5)
        self.assertEqual(cm_lo.exception.code, "INT_OUT_OF_RANGE")
        with self.assertRaises(orc.GeometricLineageError) as cm_hi:
            orc.require_exact_int(6, hi=5)
        self.assertEqual(cm_hi.exception.code, "INT_OUT_OF_RANGE")
        with self.assertRaises(orc.GeometricLineageError) as cm_blo:
            orc.require_exact_int(5, lo=True)  # type: ignore[arg-type]
        self.assertEqual(cm_blo.exception.code, "INVALID_BOUND")
        with self.assertRaises(orc.GeometricLineageError) as cm_bhi:
            orc.require_exact_int(5, hi=True)  # type: ignore[arg-type]
        self.assertEqual(cm_bhi.exception.code, "INVALID_BOUND")

        # require_fraction, format_rational, format_decimal (including -0.000000 suppression!)
        max_b = (1 << orc.MAX_RATIONAL_BITS) - 1
        over_b = 1 << orc.MAX_RATIONAL_BITS
        self.assertEqual(orc.require_fraction(Fraction(max_b, 1)), Fraction(max_b, 1))
        self.assertEqual(orc.require_fraction(Fraction(1, max_b)), Fraction(1, max_b))
        for bad_fr in (1, _EvilFrac(1, 2)):
            with self.assertRaises(orc.GeometricLineageError) as cm:
                orc.require_fraction(bad_fr)
            self.assertEqual(cm.exception.code, "INVALID_RATIONAL")
        for big_fr in (Fraction(over_b, 1), Fraction(1, over_b)):
            with self.assertRaises(orc.GeometricLineageError) as cm:
                orc.require_fraction(big_fr)
            self.assertEqual(cm.exception.code, "RATIONAL_BIT_LIMIT")

        self.assertEqual(orc.format_decimal(Fraction(-1, 10**9), 6), "0.000000")
        self.assertEqual(orc.format_decimal(Fraction(-5, 2), 0), "-3")
        self.assertEqual(orc.format_decimal(Fraction(1, 2), 0), "1")
        self.assertEqual(orc.format_decimal(Fraction(1, 4), 2), "0.25")
        self.assertEqual(orc.format_decimal(Fraction(-3, 8), 2), "-0.38")

        # q3_sign exhaustive branch & BoolOp coverage
        self.assertEqual(orc.q3_sign((Fraction(0), Fraction(0))), 0)
        self.assertEqual(orc.q3_sign((Fraction(0), Fraction(1))), 1)
        self.assertEqual(orc.q3_sign((Fraction(1), Fraction(0))), 1)
        self.assertEqual(orc.q3_sign((Fraction(0), Fraction(-1))), -1)
        self.assertEqual(orc.q3_sign((Fraction(-1), Fraction(0))), -1)
        self.assertEqual(orc.q3_sign((Fraction(2), Fraction(-1))), 1)   # 4 > 3
        self.assertEqual(orc.q3_sign((Fraction(1), Fraction(-1))), -1)  # 1 < 3
        self.assertEqual(orc.q3_sign((Fraction(-1), Fraction(1))), 1)   # 3 > 1
        self.assertEqual(orc.q3_sign((Fraction(-2), Fraction(1))), -1)  # 3 < 4

        # Bareiss pivot swap, singular matrix, and domain guards
        self.assertEqual(orc.bareiss_det_int([[0, 1], [1, 0]]), -1)
        self.assertEqual(orc.bareiss_det_int([[0, 0], [0, 1]]), 0)
        with self.assertRaises(orc.GeometricLineageError) as cm_em:
            orc.bareiss_det_int([])
        self.assertEqual(cm_em.exception.code, "EMPTY_MATRIX")
        with self.assertRaises(orc.GeometricLineageError) as cm_ns:
            orc.bareiss_det_int([[1, 2]])
        self.assertEqual(cm_ns.exception.code, "NON_SQUARE_MATRIX")
        with self.assertRaises(orc.GeometricLineageError) as cm_emf:
            orc.bareiss_det_fraction([])
        self.assertEqual(cm_emf.exception.code, "EMPTY_MATRIX")
        with self.assertRaises(orc.GeometricLineageError) as cm_nsf:
            orc.bareiss_det_fraction([[Fraction(1), Fraction(2)]])
        self.assertEqual(cm_nsf.exception.code, "NON_SQUARE_MATRIX")

    def test_pillar_helpers_and_negative_controls(self) -> None:
        # Cayley-Menger & perspective guards (5x4 matrix kills outer len==4 independently of inner row len==4!)
        with self.assertRaises(orc.GeometricLineageError) as cm_cm1:
            orc.cayley_menger_det_4pts([[Fraction(0)] * 4 for _ in range(5)])
        self.assertEqual(cm_cm1.exception.code, "INVALID_CM_DIM")
        with self.assertRaises(orc.GeometricLineageError) as cm_cm2:
            orc.cayley_menger_det_4pts([[Fraction(0)] * 3 for _ in range(4)])
        self.assertEqual(cm_cm2.exception.code, "INVALID_CM_DIM")
        with self.assertRaises(orc.GeometricLineageError) as cm_bc:
            orc._project_perspective((Fraction(1), Fraction(1), Fraction(0)), Fraction(5))
        self.assertEqual(cm_bc.exception.code, "BEHIND_CAMERA")
        with self.assertRaises(orc.GeometricLineageError) as cm_cr:
            orc._cross_ratio_1d(Fraction(1), Fraction(2), Fraction(2), Fraction(4))
        self.assertEqual(cm_cr.exception.code, "DEGENERATE_CROSS_RATIO")

        # SAT negative control: overlapping squares return False
        def _sq(x0: int, y0: int, x1: int, y1: int) -> tuple[tuple[orc.Q3Pair, orc.Q3Pair], ...]:
            return (
                ((Fraction(x0), Fraction(0)), (Fraction(y0), Fraction(0))),
                ((Fraction(x1), Fraction(0)), (Fraction(y0), Fraction(0))),
                ((Fraction(x1), Fraction(0)), (Fraction(y1), Fraction(0))),
                ((Fraction(x0), Fraction(0)), (Fraction(y1), Fraction(0))),
            )
        self.assertFalse(orc._q3_polygons_strictly_separated_sat(_sq(0, 0, 2, 2), _sq(1, 1, 3, 3)))
        self.assertTrue(orc._q3_polygons_strictly_separated_sat(_sq(0, 0, 2, 2), _sq(2, 0, 4, 2)))

        # Mondrian negative controls & flipped non-guillotine BoolOp kills
        with self.assertRaises(orc.GeometricLineageError) as cm_triv:
            orc.verify_mondrian_tiling(3, [(0, 0, 3, 3)])
        self.assertEqual(cm_triv.exception.code, "TRIVIAL_TILING")
        with self.assertRaises(orc.GeometricLineageError) as cm_cong:
            orc.verify_mondrian_tiling(4, [(0, 0, 4, 2), (0, 2, 4, 2)])
        self.assertEqual(cm_cong.exception.code, "CONGRUENT_TILES")
        with self.assertRaises(orc.GeometricLineageError) as cm_ov:
            orc.verify_mondrian_tiling(3, [(0, 0, 2, 2), (1, 1, 2, 1)])
        self.assertEqual(cm_ov.exception.code, "OVERLAPPING_TILES")
        with self.assertRaises(orc.GeometricLineageError) as cm_inc:
            orc.verify_mondrian_tiling(3, [(0, 0, 3, 1), (0, 1, 2, 2)])
        self.assertEqual(cm_inc.exception.code, "INCOMPLETE_TILING")

        # Vertical-only & horizontal-only guillotine positive controls (kills is_guillotine cut BoolOps!)
        self.assertTrue(orc.is_guillotine_tiling([(0, 0, 1, 2), (1, 0, 1, 2)], 0, 0, 2, 2))
        self.assertTrue(orc.is_guillotine_tiling([(0, 0, 2, 1), (0, 1, 2, 1)], 0, 0, 2, 2))
        # Vertical-cut guillotine split with non-guillotine left vs right half (kills BOTH halves of is_guillotine BoolOps!)
        ng_pin_7: list[orc.Rect] = [(0, 0, 1, 5), (1, 0, 6, 2), (4, 2, 3, 5), (0, 5, 4, 2), (1, 2, 3, 3)]
        # Right half non-guillotine, left strip guillotine:
        self.assertFalse(orc.is_guillotine_tiling([(0, 0, 2, 7)] + [(x + 2, y, w, h) for (x, y, w, h) in ng_pin_7], 0, 0, 9, 7))
        # Left half non-guillotine, right strip guillotine:
        self.assertFalse(orc.is_guillotine_tiling(ng_pin_7 + [(7, 0, 2, 7)], 0, 0, 9, 7))
        # Bottom half non-guillotine, top strip guillotine:
        self.assertFalse(orc.is_guillotine_tiling(ng_pin_7 + [(0, 7, 7, 2)], 0, 0, 7, 9))
        # Top half non-guillotine, bottom strip guillotine:
        self.assertFalse(orc.is_guillotine_tiling([(0, 0, 7, 2)] + [(x, y + 2, w, h) for (x, y, w, h) in ng_pin_7], 0, 0, 7, 9))
        # B&B positive control: n=3 with max_defect=2 returns False (a valid tiling DOES exist!)
        no_tiling, _ = orc.prove_no_mondrian_tiling_below(3, 2)
        self.assertFalse(no_tiling)

        # Riley structure tensor guards
        with self.assertRaises(orc.GeometricLineageError) as cm_g1:
            orc.discrete_structure_tensor([[1, 2, 3], [1, 2, 3]])
        self.assertEqual(cm_g1.exception.code, "GRID_TOO_SMALL")
        with self.assertRaises(orc.GeometricLineageError) as cm_g2:
            orc.discrete_structure_tensor([[1, 2], [1, 2], [1, 2]])
        self.assertEqual(cm_g2.exception.code, "GRID_TOO_SMALL")
        with self.assertRaises(orc.GeometricLineageError) as cm_rg:
            orc.discrete_structure_tensor([[1, 2, 3], [1, 2], [1, 2, 3]])
        self.assertEqual(cm_rg.exception.code, "RAGGED_GRID")


class TestParsersAuditAndTamperKills(unittest.TestCase):
    def test_strict_parsers_and_canonical_json_validation(self) -> None:
        # _parse_bounded_int: valid, boundaries, -0, leading zero, unicode digits, huge int
        self.assertEqual(aud._parse_bounded_int("0"), 0)
        self.assertEqual(aud._parse_bounded_int("10"), 10)
        self.assertEqual(aud._parse_bounded_int("-42"), -42)
        self.assertEqual(aud._parse_bounded_int("9" * aud.MAX_JSON_INT_DIGITS), int("9" * aud.MAX_JSON_INT_DIGITS))
        for bad_tok, code in (
            ("-0", "INVALID_JSON_INT"),
            ("-", "INVALID_JSON_INT"),
            ("", "INVALID_JSON_INT"),
            ("007", "INVALID_JSON_INT"),
            ("01", "INVALID_JSON_INT"),
            ("+1", "INVALID_JSON_INT"),
            ("1_0", "INVALID_JSON_INT"),
            ("\u0661", "INVALID_JSON_INT"),
            ("9" * (aud.MAX_JSON_INT_DIGITS + 1), "INT_DIGIT_LIMIT"),
        ):
            with self.assertRaises(orc.GeometricLineageError) as cm:
                aud._parse_bounded_int(bad_tok)
            self.assertEqual(cm.exception.code, code)

        # parse_exact_rational (includes den == 2 boundary to kill den >= 2 -> den > 2)
        self.assertEqual(aud.parse_exact_rational("0"), Fraction(0))
        self.assertEqual(aud.parse_exact_rational("1/2"), Fraction(1, 2))
        self.assertEqual(aud.parse_exact_rational("-5/7"), Fraction(-5, 7))
        for bad_r, code in (
            ("1/2/3", "INVALID_RATIONAL"),
            ("3/1", "INVALID_RATIONAL"),
            ("3/0", "INVALID_RATIONAL"),
            ("2/4", "NON_CANONICAL_RATIONAL"),
        ):
            with self.assertRaises(orc.GeometricLineageError) as cm:
                aud.parse_exact_rational(bad_r)
            self.assertEqual(cm.exception.code, code)

        # hex64
        good_h = "0123456789abcdef" * 4
        self.assertEqual(aud.require_hex64_lower_ascii(good_h), good_h)
        for bad_h in ("a" * 63, "A" * 64, "z" * 64, "\u00e9" * 64):
            with self.assertRaises(orc.GeometricLineageError) as cm:
                aud.require_hex64_lower_ascii(bad_h)
            self.assertEqual(cm.exception.code, "INVALID_HEX64")

        # parse_strict_json_text & canonical_json_bytes (including 10**4300, floats, cyclic dicts, exact cap)
        self.assertEqual(aud.parse_strict_json_text("[1,null,true,false]", require_object=False), [1, None, True, False])
        exact_s = '{"k":"' + ("a" * (aud.MAX_JSON_BYTES - 8)) + '"}'
        self.assertEqual(len(aud.parse_strict_json_text(exact_s, require_object=True)["k"]), aud.MAX_JSON_BYTES - 8)
        for bad_txt, code in (
            ("[1]", "JSON_ROOT_NOT_OBJECT"),
            ('{"a":1,"a":2}', "DUPLICATE_JSON_KEY"),
            ('{"a":1,"\\u0061":2}', "DUPLICATE_JSON_KEY"),
            ('{"x":1e2}', "FLOAT_LITERAL_FORBIDDEN"),
            ('{"x":NaN}', "NONFINITE_LITERAL_FORBIDDEN"),
            ('{"x":' + "9" * (aud.MAX_JSON_INT_DIGITS + 1) + "}", "INT_DIGIT_LIMIT"),
            ("{bad", "JSON_PARSE_ERROR"),
            ('{"a":' * (aud.MAX_JSON_DEPTH + 1) + "1" + "}" * (aud.MAX_JSON_DEPTH + 1), "JSON_DEPTH_LIMIT"),
            ('{"k":"' + ("a" * aud.MAX_JSON_BYTES) + '"}', "JSON_TOO_LARGE"),
        ):
            with self.assertRaises(orc.GeometricLineageError) as cm:
                aud.parse_strict_json_text(bad_txt, require_object=True)
            self.assertEqual(cm.exception.code, code)

        # canonical_json_bytes rejects 10**4300, -10**4300, cyclic dict, float/tuple, surrogates
        cyc: dict[str, Any] = {}
        cyc["self"] = cyc
        deep_ok: Any = 1
        for _ in range(aud.MAX_JSON_DEPTH):
            deep_ok = [deep_ok]
        self.assertTrue(aud.canonical_json_bytes(deep_ok).startswith(b"["))
        self.assertTrue(aud.canonical_json_bytes({"v": [None, True, False, 10**aud.MAX_JSON_INT_DIGITS - 1, -(10**aud.MAX_JSON_INT_DIGITS - 1)]}).startswith(b"{"))
        for bad_obj, code in (
            ({"x": 10**4300}, "INT_DIGIT_LIMIT"),
            ({"x": -(10**4300)}, "INT_DIGIT_LIMIT"),
            (cyc, "JSON_DEPTH_LIMIT"),
            ([deep_ok], "JSON_DEPTH_LIMIT"),
            ({"x": (1, 2)}, "FORBIDDEN_JSON_TYPE"),
            ({"x": "\ud800"}, "INVALID_UTF8_SURROGATE"),
            ({1: "a"}, "INVALID_STR"),
        ):
            with self.assertRaises(orc.GeometricLineageError) as cm:
                aud.canonical_json_bytes(bad_obj)
            self.assertEqual(cm.exception.code, code)

    def test_certificate_verification_and_secondary_audit_tamper_kills(self) -> None:
        cert = aud.build_standalone_certificate()
        self.assertTrue(cert["payload"]["summary"]["all_six_pillars_verified"])
        self.assertTrue(aud.verify_certificate_dict(cert, full_replay=True)["valid"])
        self.assertTrue(aud.verify_certificate_dict(cert, full_replay=False)["valid"])

        # Top-level structure & digest kills
        for bad_c, code in (
            ([], "INVALID_CERT_TYPE"),
            (dict(cert, extra=1), "INVALID_CERT_KEYS"),
            (dict(cert, schema_version="bad"), "INVALID_SCHEMA"),
            (dict(cert, track_id="bad"), "INVALID_TRACK_ID"),
            (dict(cert, payload=[1]), "INVALID_PAYLOAD_TYPE"),
        ):
            with self.assertRaises(orc.GeometricLineageError) as cm:
                aud.verify_certificate_dict(bad_c, full_replay=True)
            self.assertEqual(cm.exception.code, code)

        flip_p = ("0" if cert["payload_sha256"][0] != "0" else "1") + cert["payload_sha256"][1:]
        with self.assertRaises(orc.GeometricLineageError) as cm_ps:
            aud.verify_certificate_dict(dict(cert, payload_sha256=flip_p))
        self.assertEqual(cm_ps.exception.code, "PAYLOAD_SHA256_MISMATCH")

        flip_c = ("0" if cert["certificate_sha256"][0] != "0" else "1") + cert["certificate_sha256"][1:]
        with self.assertRaises(orc.GeometricLineageError) as cm_cs:
            aud.verify_certificate_dict(dict(cert, certificate_sha256=flip_c))
        self.assertEqual(cm_cs.exception.code, "CERT_SHA256_MISMATCH")

        # Re-signed tampered payload (portal_id changed -> rejected even at full_replay=False!)
        resigned = copy.deepcopy(cert)
        resigned["payload"]["portal_id"] = "TAMPERED"
        resigned["payload_sha256"] = aud._sha256_canonical(resigned["payload"])
        resigned["certificate_sha256"] = aud._sha256_canonical(
            {k: resigned[k] for k in ("schema_version", "track_id", "payload_sha256", "payload")}
        )
        with self.assertRaises(orc.GeometricLineageError) as cm_sec_tamper:
            aud.verify_certificate_dict(resigned, full_replay=False)
        self.assertEqual(cm_sec_tamper.exception.code, "SCHEMA_VALUE_MISMATCH")

        # full_replay=True detects oracle drift even when secondary_audit passes (kills full_replay branch!)
        with mock.patch.object(aud, "build_standalone_certificate", return_value=dict(cert, payload_sha256=flip_p)):
            with self.assertRaises(orc.GeometricLineageError) as cm_rep:
                aud.verify_certificate_dict(cert, full_replay=True)
            self.assertEqual(cm_rep.exception.code, "REPLAY_MISMATCH")

        # Direct secondary_audit_payload JSON-tree & bijective schema/leaf/keyset/length kills
        p_float = copy.deepcopy(cert["payload"])
        p_float["portal_id"] = json.loads("1.5")
        with self.assertRaises(orc.GeometricLineageError) as cm_fl:
            aud.secondary_audit_payload(p_float)
        self.assertEqual(cm_fl.exception.code, "FORBIDDEN_JSON_TYPE")

        for bad_sub, expected_code in (
            (_EvilStr("Portal-32"), "FORBIDDEN_JSON_TYPE"),
            (_EvilInt(1), "FORBIDDEN_JSON_TYPE"),
            (_EvilDict({"x": 1}), "FORBIDDEN_JSON_TYPE"),
            (_EvilList([1]), "FORBIDDEN_JSON_TYPE"),
            ("\ud800", "INVALID_UTF8_SURROGATE"),
            (10**4300, "INT_DIGIT_LIMIT"),
        ):
            p_sub = copy.deepcopy(cert["payload"])
            p_sub["portal_id"] = bad_sub
            with self.assertRaises(orc.GeometricLineageError) as cm_sub:
                aud.secondary_audit_payload(p_sub)
            self.assertEqual(cm_sub.exception.code, expected_code)

        # bool-vs-int type mismatch (1 == True in Python -> kills exact type(act) is type(exp) check!)
        p_bool_int = copy.deepcopy(cert["payload"])
        p_bool_int["pillar1_uccello_gauss_bonnet_stellated"]["all_verified"] = 1
        with self.assertRaises(orc.GeometricLineageError) as cm_bi:
            aud.secondary_audit_payload(p_bool_int)
        self.assertEqual(cm_bi.exception.code, "INVALID_SCHEMA_TYPE")

        # Extra dict key & extra list element kills
        p_extra_k = copy.deepcopy(cert["payload"])
        p_extra_k["extra_key"] = 1
        with self.assertRaises(orc.GeometricLineageError) as cm_ek:
            aud.secondary_audit_payload(p_extra_k)
        self.assertEqual(cm_ek.exception.code, "INVALID_SCHEMA_KEYS")

        p_extra_l = copy.deepcopy(cert["payload"])
        p_extra_l["pillar1_uccello_gauss_bonnet_stellated"]["mazzocchio_tori"].append(
            copy.deepcopy(p_extra_l["pillar1_uccello_gauss_bonnet_stellated"]["mazzocchio_tori"][0])
        )
        with self.assertRaises(orc.GeometricLineageError) as cm_el:
            aud.secondary_audit_payload(p_extra_l)
        self.assertEqual(cm_el.exception.code, "INVALID_SCHEMA_LIST")

        # Coordinated semantic mega-forgery rejected under full_replay=False
        p_mega = copy.deepcopy(cert["payload"])
        p_mega["pillar1_uccello_gauss_bonnet_stellated"]["mazzocchio_tori"][0].update({"V": 0, "E": 0, "F": 0, "chi": 0})
        p_mega["pillar1_uccello_gauss_bonnet_stellated"]["small_stellated_dodecahedron"].update({"V": 0, "E": 6, "F": 0})
        p_mega["pillar1_uccello_gauss_bonnet_stellated"]["all_verified"] = False
        p_mega["pillar4_mondrian_oeis_a276523"]["optimal_tilings_n3_to_n10"] = []
        p_mega["pillar4_mondrian_oeis_a276523"]["exhaustive_bb_lower_bounds_n3_to_n5"][0].update({"n": -999, "bb_nodes_explored": -1})
        p_mega["pillar5_riley_structure_tensor_moire"]["structure_tensor_cases"][2]["Jxy"] = 1
        with self.assertRaises(orc.GeometricLineageError):
            aud.secondary_audit_payload(p_mega)

        # Exhaustive walk: every nested dict extra key (51/51), every list length, every leaf (475/475), every container->scalar
        paths_dict: list[tuple[Any, ...]] = []
        paths_list: list[tuple[Any, ...]] = []
        paths_leaf: list[tuple[Any, ...]] = []

        def _collect(node: Any, path: tuple[Any, ...]) -> None:
            if type(node) is dict:
                paths_dict.append(path)
                for k, v in node.items():
                    _collect(v, path + (k,))
            elif type(node) is list:
                paths_list.append(path)
                for i_n, v in enumerate(node):
                    _collect(v, path + (i_n,))
            else:
                paths_leaf.append(path)

        _collect(cert["payload"], ())
        self.assertEqual(len(paths_dict), 51)
        self.assertEqual(len(paths_leaf), 475)

        def _get_parent(root_obj: Any, path: tuple[Any, ...]) -> Any:
            cur = root_obj
            for seg in path[:-1]:
                cur = cur[seg]
            return cur

        for dp in paths_dict:
            mut = copy.deepcopy(cert["payload"])
            tgt = mut if not dp else _get_parent(mut, dp)[dp[-1]]
            tgt["__forged_extra__"] = 1
            with self.assertRaises(orc.GeometricLineageError):
                aud.secondary_audit_payload(mut)
            if dp:
                mut2 = copy.deepcopy(cert["payload"])
                _get_parent(mut2, dp)[dp[-1]] = 0
                with self.assertRaises(orc.GeometricLineageError):
                    aud.secondary_audit_payload(mut2)

        for lp in paths_list:
            mut = copy.deepcopy(cert["payload"])
            tgt = _get_parent(mut, lp)[lp[-1]]
            tgt.append(copy.deepcopy(tgt[0]))
            with self.assertRaises(orc.GeometricLineageError):
                aud.secondary_audit_payload(mut)
            mut2 = copy.deepcopy(cert["payload"])
            _get_parent(mut2, lp)[lp[-1]] = 0
            with self.assertRaises(orc.GeometricLineageError):
                aud.secondary_audit_payload(mut2)

        for fp in paths_leaf:
            mut = copy.deepcopy(cert["payload"])
            parent = _get_parent(mut, fp)
            val = parent[fp[-1]]
            if type(val) is bool:
                parent[fp[-1]] = not val
            elif type(val) is int:
                parent[fp[-1]] = val + 1
            else:
                parent[fp[-1]] = val + "_X"
            with self.assertRaises(orc.GeometricLineageError):
                aud.secondary_audit_payload(mut)

        # Schema-safe secondary_audit_payload helper kills + all 6 pillars tamper kills + bool-as-int kills
        with self.assertRaises(orc.GeometricLineageError) as cm_nd:
            aud.secondary_audit_payload("not_dict")
        self.assertEqual(cm_nd.exception.code, "INVALID_PAYLOAD")
        with self.assertRaises(orc.GeometricLineageError) as cm_dk:
            aud._require_dict_key("x", "k", "lbl")
        self.assertEqual(cm_dk.exception.code, "INVALID_SCHEMA_DICT")
        with self.assertRaises(orc.GeometricLineageError) as cm_dk2:
            aud._require_dict_key({"k": []}, "k", "lbl")
        self.assertEqual(cm_dk2.exception.code, "INVALID_SCHEMA_DICT")
        with self.assertRaises(orc.GeometricLineageError) as cm_lk0:
            aud._require_list_key({}, "k", "lbl", min_len=1)
        self.assertEqual(cm_lk0.exception.code, "MISSING_FIELD")
        with self.assertRaises(orc.GeometricLineageError) as cm_lk1:
            aud._require_list_key({"k": "abcd"}, "k", "lbl", min_len=2)
        self.assertEqual(cm_lk1.exception.code, "INVALID_SCHEMA_LIST")
        with self.assertRaises(orc.GeometricLineageError) as cm_lk2:
            aud._require_list_key({"k": [1]}, "k", "lbl", min_len=2)
        self.assertEqual(cm_lk2.exception.code, "INVALID_SCHEMA_LIST")
        with self.assertRaises(orc.GeometricLineageError) as cm_ri0:
            aud._req_int_field({}, "k", "lbl")
        self.assertEqual(cm_ri0.exception.code, "MISSING_FIELD")
        with self.assertRaises(orc.GeometricLineageError) as cm_rb0:
            aud._req_bool_field({}, "k", "lbl")
        self.assertEqual(cm_rb0.exception.code, "MISSING_FIELD")

        def _tamper(mutator: Any, code: str) -> None:
            p = copy.deepcopy(cert["payload"])
            mutator(p)
            with self.assertRaises(orc.GeometricLineageError) as cm_t:
                aud.secondary_audit_payload(p)
            self.assertEqual(cm_t.exception.code, code)

        _tamper(lambda p: p.pop("pillar1_uccello_gauss_bonnet_stellated"), "MISSING_FIELD")
        _tamper(lambda p: p["pillar1_uccello_gauss_bonnet_stellated"]["mazzocchio_tori"].__setitem__(0, "bad"), "INVALID_SCHEMA_DICT")
        _tamper(lambda p: p["pillar1_uccello_gauss_bonnet_stellated"]["mazzocchio_tori"][0].__setitem__("chi", False), "INVALID_INT")
        _tamper(lambda p: p["pillar1_uccello_gauss_bonnet_stellated"]["mazzocchio_tori"][0].__setitem__("chi", 1), "AUDIT_P1_TORUS_CHI")
        _tamper(lambda p: p["pillar1_uccello_gauss_bonnet_stellated"]["mazzocchio_tori"][0].__setitem__("V", 99), "AUDIT_P1_TORUS_CHI")
        _tamper(lambda p: p["pillar1_uccello_gauss_bonnet_stellated"]["mazzocchio_tori"][0].__setitem__("gauss_bonnet_sum_over_2pi", "1"), "AUDIT_P1_GB")
        _tamper(lambda p: p["pillar1_uccello_gauss_bonnet_stellated"]["small_stellated_dodecahedron"].__setitem__("V", 13), "AUDIT_P1_SSD")
        _tamper(lambda p: p["pillar1_uccello_gauss_bonnet_stellated"]["small_stellated_dodecahedron"].__setitem__("genus", 3), "AUDIT_P1_SSD")
        _tamper(lambda p: p["pillar1_uccello_gauss_bonnet_stellated"]["platonic_dodecahedron_contrast"].__setitem__("genus", 1), "AUDIT_P1_DOD")
        _tamper(lambda p: p["pillar2_piero_cayley_menger_cross_ratio"]["cayley_menger"].__setitem__("unit_tetrahedron_det", "5"), "AUDIT_P2_UNIT")
        _tamper(lambda p: p["pillar2_piero_cayley_menger_cross_ratio"]["cayley_menger"].__setitem__("orthogonal_345_det", "1"), "AUDIT_P2_ORTH")
        _tamper(lambda p: p["pillar2_piero_cayley_menger_cross_ratio"]["cayley_menger"].__setitem__("coplanar_control_det", "1"), "AUDIT_P2_COP")
        _tamper(lambda p: p["pillar2_piero_cayley_menger_cross_ratio"]["perspective_cross_ratio_cases"].__setitem__(0, "bad"), "INVALID_SCHEMA_DICT")
        _tamper(lambda p: p["pillar2_piero_cayley_menger_cross_ratio"]["perspective_cross_ratio_cases"][0].__setitem__("cross_ratio_residual", "1"), "AUDIT_P2_CR")
        _tamper(lambda p: p["pillar2_piero_cayley_menger_cross_ratio"]["perspective_cross_ratio_cases"][0].__setitem__("affine_ratio_broken_by_perspective", False), "AUDIT_P2_AFF")
        _tamper(lambda p: p["pillar3_durer_melencolia_net_pentagon"]["melencolia_magic_square"].__setitem__("det", 1), "AUDIT_P3_DET")
        _tamper(lambda p: p["pillar3_durer_melencolia_net_pentagon"]["melencolia_magic_square"].__setitem__("top_left_3x3_minor_det", 135), "AUDIT_P3_MINOR")
        _tamper(lambda p: p["pillar3_durer_melencolia_net_pentagon"]["melencolia_magic_square"].__setitem__("exact_rank", 4), "AUDIT_P3_RANK")
        _tamper(lambda p: p["pillar3_durer_melencolia_net_pentagon"]["melencolia_magic_square"].__setitem__("trace", 33), "AUDIT_P3_TRACE")
        _tamper(lambda p: p["pillar3_durer_melencolia_net_pentagon"]["truncated_trapezohedron_net"].__setitem__("face_pairs_checked_sat", 27), "AUDIT_P3_NET_PAIRS")
        _tamper(lambda p: p["pillar3_durer_melencolia_net_pentagon"]["truncated_trapezohedron_net"].__setitem__("all_28_pairs_disjoint_interiors", False), "AUDIT_P3_NET_DISJ")
        _tamper(lambda p: p["pillar3_durer_melencolia_net_pentagon"]["pentagon_1525_error_proof"].__setitem__("P_at_lo", "0"), "AUDIT_P3_PENT_LO")
        _tamper(lambda p: p["pillar3_durer_melencolia_net_pentagon"]["pentagon_1525_error_proof"].__setitem__("P_at_separator", "0"), "AUDIT_P3_PENT_SEP")
        _tamper(lambda p: p["pillar4_mondrian_oeis_a276523"]["oeis_A276523_sequence"].__setitem__(0, 3), "AUDIT_P4_SEQ")
        _tamper(lambda p: p["pillar4_mondrian_oeis_a276523"]["exhaustive_bb_lower_bounds_n3_to_n5"].__setitem__(0, "bad"), "INVALID_SCHEMA_DICT")
        _tamper(lambda p: p["pillar4_mondrian_oeis_a276523"]["exhaustive_bb_lower_bounds_n3_to_n5"][0].__setitem__("certified_impossible", False), "AUDIT_P4_LB")
        _tamper(lambda p: p["pillar5_riley_structure_tensor_moire"]["structure_tensor_cases"].__setitem__(0, "bad"), "INVALID_SCHEMA_DICT")
        _tamper(lambda p: p["pillar5_riley_structure_tensor_moire"]["structure_tensor_cases"][0].__setitem__("Jxy", 1), "AUDIT_P5_JXY")
        _tamper(lambda p: p["pillar5_riley_structure_tensor_moire"]["structure_tensor_cases"][2].__setitem__("Jxy", 0), "AUDIT_P5_JXY")
        _tamper(lambda p: p["pillar5_riley_structure_tensor_moire"]["moire_n12_q_sqrt3"].__setitem__("beat_frequency_abs_f1_minus_f2", 2), "AUDIT_P5_BEAT")
        _tamper(lambda p: p["pillar5_riley_structure_tensor_moire"]["moire_n12_q_sqrt3"].__setitem__("sub_nyquist_fold_N_minus_sum", 4), "AUDIT_P5_ALIAS")
        _tamper(lambda p: p["pillar6_lewitt_burnside_kolmogorov"]["incomplete_open_cubes"].__setitem__("total_q3_subgraphs_searched", 4095), "AUDIT_P6_TOTAL")
        _tamper(lambda p: p["pillar6_lewitt_burnside_kolmogorov"]["incomplete_open_cubes"].__setitem__("connected_3d_spanning_proper", 2365), "AUDIT_P6_VALID")
        _tamper(lambda p: p["pillar6_lewitt_burnside_kolmogorov"]["incomplete_open_cubes"].__setitem__("O_orbits_total", 121), "AUDIT_P6_O")
        _tamper(lambda p: p["pillar6_lewitt_burnside_kolmogorov"]["incomplete_open_cubes"].__setitem__("Oh_orbits_total", 76), "AUDIT_P6_OH")
        _tamper(lambda p: p["pillar6_lewitt_burnside_kolmogorov"]["incomplete_open_cubes"].__setitem__("chiral_enantiomorphic_pairs", 44), "AUDIT_P6_CHIRAL")
        _tamper(lambda p: p["pillar6_lewitt_burnside_kolmogorov"]["incomplete_open_cubes"].__setitem__("O_burnside_fix_sum", 2927), "AUDIT_P6_BURN_O")
        _tamper(lambda p: p["pillar6_lewitt_burnside_kolmogorov"]["incomplete_open_cubes"].__setitem__("Oh_burnside_fix_sum", 3695), "AUDIT_P6_BURN_OH")
        _tamper(lambda p: p["pillar6_lewitt_burnside_kolmogorov"]["wall_drawing_compression"].__setitem__("wd118_n50_segments", 1224), "AUDIT_P6_WD118")
        _tamper(lambda p: p["summary"].__setitem__("all_six_pillars_verified", False), "AUDIT_SUMMARY_ALL")
        _tamper(lambda p: p["summary"].__setitem__("pillar_count", 5), "AUDIT_SUMMARY_CNT")
        _tamper(lambda p: p["summary"].__setitem__("float_count_on_trust_path", 1), "AUDIT_SUMMARY_FLT")
        _tamper(lambda p: p["summary"].__setitem__("bare_assert_count", 1), "AUDIT_SUMMARY_ASS")
        _tamper(lambda p: p["summary"].__setitem__("rng_calls", 1), "AUDIT_SUMMARY_RNG")


class TestZoneBIOConcurrencyAndCLI(unittest.TestCase):
    def test_zone_b_io_paths_caps_symlinks_pwd_hardlinks_and_deleted_cwd(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            nested = root / "sub1" / "sub2" / "cert.json"

            # Atomic write creates missing parent dirs with 0o600 file mode
            w_res = aud.write_certificate_file(nested)
            self.assertTrue(w_res["written"])
            self.assertEqual(stat.S_IMODE(os.lstat(nested).st_mode), 0o600)
            c_res = aud.check_certificate_file(nested)
            self.assertTrue(c_res["valid"])
            self.assertEqual(w_res["file_sha256"], c_res["file_sha256"])

            # Concrete path, NUL, surrogate, and max_bytes cap (1<<100 -> typed error)
            with self.assertRaises(orc.GeometricLineageError) as cm_ep:
                aud.read_regular_bytes_capped(_EvilPath(str(nested)))
            self.assertEqual(cm_ep.exception.code, "INVALID_PATH_TYPE")
            with self.assertRaises(orc.GeometricLineageError) as cm_nul:
                aud.read_regular_bytes_capped(Path("a\x00b"))
            self.assertEqual(cm_nul.exception.code, "NUL_BYTE_FORBIDDEN")
            with self.assertRaises(orc.GeometricLineageError) as cm_sur:
                aud.read_regular_bytes_capped(Path("bad\ud800.json"))
            self.assertEqual(cm_sur.exception.code, "INVALID_UTF8_SURROGATE")
            with self.assertRaises(orc.GeometricLineageError) as cm_cap:
                aud.read_regular_bytes_capped(nested, "c", max_bytes=1 << 100)
            self.assertEqual(cm_cap.exception.code, "INT_OUT_OF_RANGE")

            # Root / dot / parent-dir targets rejected (including direct _open_dir_chain BoolOp kills!)
            for bad_dir in (Path("/"), Path("..")):
                with self.assertRaises(orc.GeometricLineageError) as cm_od:
                    aud._open_dir_chain(bad_dir, "d", create_parents=False)
                self.assertEqual(cm_od.exception.code, "NOT_A_REGULAR_FILE")
            for bad_dir in (Path("/"), Path("."), Path("..")):
                with self.assertRaises(orc.GeometricLineageError) as cm_d:
                    aud.read_regular_bytes_capped(bad_dir)
                self.assertEqual(cm_d.exception.code, "NOT_A_REGULAR_FILE")

            # Read missing parent dir -> FILE_READ_ERROR and must NOT create missing_dir (kills create_parents BoolOp!)
            missing_parent = root / "missing_dir"
            with self.assertRaises(orc.GeometricLineageError) as cm_mp:
                aud.read_regular_bytes_capped(missing_parent / "x.json")
            self.assertEqual(cm_mp.exception.code, "FILE_READ_ERROR")
            self.assertFalse(missing_parent.exists())

            # Direct leaf symlink & intermediate sym/../real rejected (both read and write)
            sym_leaf = root / "sym_leaf.json"
            sym_leaf.symlink_to(nested)
            with self.assertRaises(orc.GeometricLineageError) as cm_slr:
                aud.read_regular_bytes_capped(sym_leaf)
            self.assertEqual(cm_slr.exception.code, "SYMLINK_FORBIDDEN")
            with self.assertRaises(orc.GeometricLineageError) as cm_slw:
                aud.write_regular_bytes_safe(sym_leaf, b"x")
            self.assertEqual(cm_slw.exception.code, "SYMLINK_FORBIDDEN")

            sym_dir = root / "sym_dir"
            sym_dir.symlink_to(nested.parent)
            with self.assertRaises(orc.GeometricLineageError) as cm_sd:
                aud.read_regular_bytes_capped(Path(f"{sym_dir}/../sub2/cert.json"))
            self.assertEqual(cm_sd.exception.code, "SYMLINK_FORBIDDEN")
            with self.assertRaises(orc.GeometricLineageError) as cm_sdw:
                aud.write_regular_bytes_safe(sym_dir / "x.json", b"a")
            self.assertEqual(cm_sdw.exception.code, "SYMLINK_FORBIDDEN")

            # FIFO, directory, hardlink target, non-bytes payload, pre-replace temp st_nlink != 1
            fifo = root / "p.fifo"
            os.mkfifo(fifo)
            with self.assertRaises(orc.GeometricLineageError) as cm_fr:
                aud.read_regular_bytes_capped(fifo)
            self.assertEqual(cm_fr.exception.code, "NOT_A_REGULAR_FILE")
            with self.assertRaises(orc.GeometricLineageError) as cm_fw:
                aud.write_regular_bytes_safe(fifo, b"x")
            self.assertEqual(cm_fw.exception.code, "NOT_A_REGULAR_FILE")

            hl_a = root / "hl_a.json"
            hl_a.write_bytes(b"KEEP_ME\n")
            hl_b = root / "hl_b.json"
            os.link(hl_a, hl_b)
            with self.assertRaises(orc.GeometricLineageError) as cm_hl:
                aud.write_regular_bytes_safe(hl_b, b"CLOBBER\n")
            self.assertEqual(cm_hl.exception.code, "HARDLINK_FORBIDDEN")
            self.assertEqual(hl_a.read_bytes(), b"KEEP_ME\n")

            with self.assertRaises(orc.GeometricLineageError) as cm_nb:
                aud.write_regular_bytes_safe(root / "nb.json", "not_bytes")  # type: ignore[arg-type]
            self.assertEqual(cm_nb.exception.code, "INVALID_PAYLOAD_BYTES")

            # Pre-replace temp st_nlink != 1 check
            fake_st = mock.Mock(st_nlink=2)
            with mock.patch("os.fstat", return_value=fake_st):
                with self.assertRaises(orc.GeometricLineageError) as cm_tmp_hl:
                    aud.write_regular_bytes_safe(root / "tmp_hl_test.json", b"abc")
                self.assertEqual(cm_tmp_hl.exception.code, "HARDLINK_FORBIDDEN")
            self.assertFalse((root / "tmp_hl_test.json").exists())

            # Streaming cap: exact boundary succeeds, +1 fails
            exact_f = root / "exact.bin"
            exact_f.write_bytes(b"x" * 70000)
            self.assertEqual(len(aud.read_regular_bytes_capped(exact_f, "ex", max_bytes=70000)), 70000)
            with self.assertRaises(orc.GeometricLineageError) as cm_big:
                aud.read_regular_bytes_capped(exact_f, "ex", max_bytes=69999)
            self.assertEqual(cm_big.exception.code, "FILE_TOO_LARGE")

            # Relative paths, atomic PWD check (valid, symlinked, missing, empty), deleted-CWD
            orig_cwd = os.getcwd()
            try:
                os.chdir(nested.parent)
                with mock.patch.dict(os.environ, {"PWD": str(nested.parent)}, clear=False):
                    self.assertEqual(aud.read_regular_bytes_capped(Path("./cert.json")), nested.read_bytes())
                with mock.patch.dict(os.environ, {"PWD": ""}, clear=False):
                    self.assertEqual(aud.read_regular_bytes_capped(Path("cert.json")), nested.read_bytes())
                with mock.patch.dict(os.environ, {"PWD": str(sym_dir)}, clear=False):
                    with self.assertRaises(orc.GeometricLineageError) as cm_pwd:
                        aud.read_regular_bytes_capped(Path("cert.json"))
                    self.assertEqual(cm_pwd.exception.code, "SYMLINK_ANCESTOR_FORBIDDEN")
                with mock.patch.dict(os.environ, {"PWD": str(root / "no_such_pwd")}, clear=False):
                    with self.assertRaises(orc.GeometricLineageError) as cm_gpwd:
                        aud.read_regular_bytes_capped(Path("cert.json"))
                    self.assertEqual(cm_gpwd.exception.code, "CWD_UNAVAILABLE")

                doomed = root / "doomed_cwd"
                doomed.mkdir()
                os.chdir(doomed)
                doomed.rmdir()
                for cli_args in (["--check", "rel.json", "--json"], ["--write", "rel.json", "--json"]):
                    eb = io.StringIO()
                    with redirect_stderr(eb):
                        rc = aud.main(cli_args)
                    self.assertEqual(rc, 2)
                    self.assertEqual(json.loads(eb.getvalue())["error_code"], "CWD_UNAVAILABLE")
            finally:
                os.chdir(orig_cwd)

            # Unreadable chmod 000 dir & file (kills create_parents=True non-ENOENT error path too!)
            if os.geteuid() != 0:
                locked_dir = root / "locked_dir"
                locked_dir.mkdir()
                locked_dir.chmod(0)
                try:
                    with self.assertRaises(orc.GeometricLineageError) as cm_ld:
                        aud.write_regular_bytes_safe(locked_dir / "x.json", b"a")
                    self.assertEqual(cm_ld.exception.code, "FILE_WRITE_ERROR")
                finally:
                    locked_dir.chmod(0o755)

            # Format checks in check_certificate_file
            raw_v = nested.read_bytes()
            for fname, blob, code in (
                ("crlf.json", raw_v[:-1] + b"\r\n", "CRLF_FORBIDDEN"),
                ("nolf.json", raw_v[:-1], "MISSING_TRAILING_LF"),
                ("badu.json", b"\xff\xfe\n", "INVALID_UTF8"),
                ("nonc.json", b" " + raw_v, "NON_CANONICAL_BYTES"),
            ):
                p = root / fname
                p.write_bytes(blob)
                with self.assertRaises(orc.GeometricLineageError) as cm_fmt:
                    aud.check_certificate_file(p)
                self.assertEqual(cm_fmt.exception.code, code)

    def test_concurrency_16t_distinct_16t_same_80t_burst_and_renameat2_toctou(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            payload = b'{"ok":true}\n'

            # 16T distinct targets
            errs_d: list[Exception] = []
            def _w_dist(idx: int) -> None:
                try:
                    p = root / f"d_{idx}.json"
                    aud.write_regular_bytes_safe(p, payload)
                    if aud.read_regular_bytes_capped(p) != payload:
                        errs_d.append(RuntimeError("mismatch"))
                except Exception as exc:  # pragma: no cover
                    errs_d.append(exc)
            ts = [threading.Thread(target=_w_dist, args=(i,)) for i in range(16)]
            for t in ts:
                t.start()
            for t in ts:
                t.join()
            self.assertEqual(errs_d, [])

            # 16T same target
            same_p = root / "same.json"
            errs_s: list[Exception] = []
            def _w_same(idx: int) -> None:
                try:
                    aud.write_regular_bytes_safe(same_p, f'{{"id":{idx}}}\n'.encode("ascii"))
                except Exception as exc:  # pragma: no cover
                    errs_s.append(exc)
            ts = [threading.Thread(target=_w_same, args=(i,)) for i in range(16)]
            for t in ts:
                t.start()
            for t in ts:
                t.join()
            self.assertEqual(errs_s, [])
            self.assertIn(b'"id":', same_p.read_bytes())

            # 80T burst across 8 targets -> 0 errors, 0 leftover .tmp files
            errs_b: list[Exception] = []
            def _w_burst(idx: int) -> None:
                try:
                    aud.write_regular_bytes_safe(root / f"b_{idx % 8}.json", payload)
                except Exception as exc:  # pragma: no cover
                    errs_b.append(exc)
            ts = [threading.Thread(target=_w_burst, args=(i,)) for i in range(80)]
            for t in ts:
                t.start()
            for t in ts:
                t.join()
            self.assertEqual(errs_b, [])
            self.assertEqual([p.name for p in root.iterdir() if p.name.endswith(".tmp")], [])

            # Live renameat2(RENAME_EXCHANGE) >= 500 iterations on BOTH read & write
            libc = ctypes.CDLL("libc.so.6", use_errno=True)
            outside = root / "outside"
            outside.mkdir()
            canary = outside / "target.json"
            canary.write_bytes(b"CANARY_OUTSIDE\n")
            slot = root / "slot"
            slot.mkdir()
            (slot / "target.json").write_bytes(b"LEGIT_INSIDE\n")
            sym = root / "sym_swap"
            sym.symlink_to(outside)

            stop = threading.Event()
            b1 = os.fsencode(slot)
            b2 = os.fsencode(sym)
            def _swapper() -> None:
                while not stop.is_set():
                    libc.syscall(316, -100, b1, -100, b2, 2)  # SYS_renameat2, AT_FDCWD, RENAME_EXCHANGE

            sw = threading.Thread(target=_swapper, daemon=True)
            sw.start()
            leaks = 0
            clobbers = 0
            try:
                for _ in range(600):
                    try:
                        if aud.read_regular_bytes_capped(slot / "target.json") != b"LEGIT_INSIDE\n":
                            leaks += 1
                    except orc.GeometricLineageError:
                        pass
                    try:
                        aud.write_regular_bytes_safe(slot / "target.json", b"LEGIT_INSIDE\n")
                    except orc.GeometricLineageError:
                        pass
                    if canary.read_bytes() != b"CANARY_OUTSIDE\n":
                        clobbers += 1
            finally:
                stop.set()
                sw.join(timeout=2)
            self.assertEqual(leaks, 0)
            self.assertEqual(clobbers, 0)

            # Live hardlink race (>=500 iterations): concurrent os.link/os.unlink vs atomic write
            hl_dir = root / "hl_race"
            hl_dir.mkdir()
            hl_tgt = hl_dir / "target.json"
            hl_alias = hl_dir / "sentinel_alias.json"
            hl_tgt.write_bytes(b"INITIAL_SENTINEL\n")
            stop_hl = threading.Event()
            hl_clobbers = 0

            def _hl_racer() -> None:
                while not stop_hl.is_set():
                    try:
                        os.link(hl_tgt, hl_alias)
                    except OSError:
                        pass
                    try:
                        os.unlink(hl_alias)
                    except OSError:
                        pass

            hl_t = threading.Thread(target=_hl_racer, daemon=True)
            hl_t.start()
            try:
                for i_hl in range(600):
                    # Also test fixed-inode sentinel preservation across replace
                    pinned = hl_dir / f"pin_{i_hl % 4}.json"
                    try:
                        aud.write_regular_bytes_safe(hl_tgt, b"NEW_ATOMIC_BYTES\n")
                    except orc.GeometricLineageError:
                        pass
                    try:
                        if hl_alias.exists():
                            data_a = hl_alias.read_bytes()
                            if data_a not in (b"INITIAL_SENTINEL\n", b"NEW_ATOMIC_BYTES\n"):
                                hl_clobbers += 1
                    except OSError:
                        pass
                    if i_hl == 0:
                        pinned.write_bytes(b"PINNED_SENTINEL\n")
            finally:
                stop_hl.set()
                hl_t.join(timeout=2)
            self.assertEqual(hl_clobbers, 0)
            self.assertEqual([p.name for p in hl_dir.iterdir() if p.name.endswith(".tmp")], [])

    def test_cli_modes_space_and_equals_syntax_and_adversarial_argv(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            p1 = root / "c1.json"
            p2 = root / "c2.json"

            out_t = io.StringIO()
            with redirect_stdout(out_t):
                self.assertEqual(aud.main([]), 0)
            self.assertIn("OK ", out_t.getvalue())

            out_j = io.StringIO()
            with redirect_stdout(out_j):
                self.assertEqual(aud.main(["--standalone", "--json"]), 0)
            standalone_b = out_j.getvalue().encode("ascii")

            # Space syntax --write / --check AND equals syntax --write= / --check=
            out_w1 = io.StringIO()
            with redirect_stdout(out_w1):
                self.assertEqual(aud.main(["--write", str(p1), "--json"]), 0)
            self.assertEqual(p1.read_bytes(), standalone_b)

            out_c1 = io.StringIO()
            with redirect_stdout(out_c1):
                self.assertEqual(aud.main(["--check", str(p1), "--json"]), 0)
            self.assertTrue(json.loads(out_c1.getvalue())["valid"])

            out_w2 = io.StringIO()
            with redirect_stdout(out_w2):
                self.assertEqual(aud.main([f"--write={p2}", "--json"]), 0)
            self.assertEqual(p2.read_bytes(), standalone_b)

            out_c2 = io.StringIO()
            with redirect_stdout(out_c2):
                self.assertEqual(aud.main([f"--check={p2}", "--json"]), 0)
            self.assertTrue(json.loads(out_c2.getvalue())["valid"])

            # Adversarial CLI argv including --write --json, --write=--json, --check=--json (0 stray files!)
            bad_cases: list[tuple[Any, str]] = [
                ("bad", "INVALID_ARGV"),
                ([123], "INVALID_STR"),
                ([_EvilStr("--standalone")], "INVALID_STR"),
                (["\ud800"], "INVALID_UTF8_SURROGATE"),
                (["--json", "--json"], "DUPLICATE_FLAG"),
                (["--standalone", "--standalone"], "CONFLICTING_MODE"),
                (["--standalone", "--check", str(p1)], "CONFLICTING_MODE"),
                (["--standalone", f"--check={p1}"], "CONFLICTING_MODE"),
                (["--check"], "MISSING_PATH_ARG"),
                (["--write"], "MISSING_PATH_ARG"),
                (["--check", ""], "INVALID_PATH_ARG"),
                (["--check", "--json"], "INVALID_PATH_ARG"),
                (["--write", "--json"], "INVALID_PATH_ARG"),
                (["--check=--json"], "INVALID_PATH_ARG"),
                (["--write=--json"], "INVALID_PATH_ARG"),
                (["--write="], "INVALID_PATH_ARG"),
                (["--bogus"], "UNKNOWN_FLAG"),
            ]
            for bad_argv, code in bad_cases:
                eb = io.StringIO()
                with redirect_stderr(eb):
                    rc = aud.main(bad_argv)
                self.assertEqual(rc, 2)
                self.assertEqual(json.loads(eb.getvalue())["error_code"], code)
            self.assertFalse((root / "--json").exists())


if __name__ == "__main__":
    unittest.main()
