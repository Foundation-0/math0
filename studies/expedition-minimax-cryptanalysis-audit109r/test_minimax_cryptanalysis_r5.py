"""Assertion-free R5 adversarial, wrong-value, and mutation-killing test suite for
the MiniMax-AI/Research Cryptography Portal Clean-Room Audit.

Pure Python 3 stdlib. Zero floats in certified paths. Zero bare assert statements.
"""

import copy
from enum import IntEnum
from fractions import Fraction
import hashlib
import io
import json
import os
import sys
import tempfile
import unittest
from unittest import mock

_SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
if _SCRIPT_DIR not in sys.path:
    sys.path.insert(0, _SCRIPT_DIR)

import minimax_cryptanalysis_audit as a
import minimax_cryptanalysis_oracle as o


class _SampleIntEnum(IntEnum):
    ONE = 1


class TestMinimaxCryptanalysisR5(unittest.TestCase):
    def _assert_err(self, code, fn, *args, **kwargs):
        with self.assertRaises(o.MinimaxCryptError) as ctx:
            fn(*args, **kwargs)
        self.assertEqual(ctx.exception.code, code)

    def _make_challenge(self, idx, route="Route-A (synthetic)", first_blood=False):
        return {
            "sec": idx + 1,
            "n": 254,
            "m": 8,
            "t": 6,
            "k": 206,
            "mt": 48,
            "official_checker_output": 1,
            "rref_bit_identical": True,
            "g_is_irreducible": True,
            "route": route,
            "first_blood": first_blood,
        }

    def _build_synthetic_research_dir(self, root):
        """Construct a minimal synthetic MiniMax-AI/Research tree and return its measured SHA-256 map."""
        git_refs = os.path.join(root, ".git", "refs", "heads")
        os.makedirs(git_refs, exist_ok=True)
        with open(os.path.join(root, ".git", "HEAD"), "w", encoding="utf-8") as fh:
            fh.write("ref: refs/heads/main\n")
        with open(os.path.join(git_refs, "main"), "w", encoding="utf-8") as fh:
            fh.write(o.UPSTREAM_COMMIT + "\n")

        cdir = os.path.join(root, "Cryptography")
        lean_dir = os.path.join(cdir, "BentSum", "lean")
        os.makedirs(os.path.join(lean_dir, "BentSum"), exist_ok=True)
        lean_shas = {}
        lean_sample = (
            "-- clean comment mentioning sorry\n"
            "/- nested /- axiom -/ -/\n"
            'def raw_ok := r#"sorry decide +native Lean.ofReduceBool"#\n'
            "def ok := 1\n"
        )
        for rel in o.REQUIRED_LEAN_FILES:
            p = os.path.join(lean_dir, rel)
            raw_b = lean_sample.encode("utf-8")
            with open(p, "wb") as fh:
                fh.write(raw_b)
            lean_shas[rel] = hashlib.sha256(raw_b).hexdigest()

        snf_dir = os.path.join(cdir, "Blender", "artifacts", "snf_steering", "witnesses")
        os.makedirs(snf_dir, exist_ok=True)
        unsh = [
            [1, 0, 0, 0, 0, 0, 0, 0],
            [0, 1, 0, 0, 0, 0, 0, 0],
            [0, 0, 2, 0, 0, 0, 0, 0],
            [0, 0, 0, 2, 0, 0, 0, 0],
            [0, 0, 0, 0, 4, 0, 0, 0],
            [0, 0, 0, 0, 0, 4, 0, 0],
            [0, 0, 0, 0, 0, 0, 8, 0],
            [0, 0, 0, 0, 0, 0, 0, 8],
        ]
        sh_vecs = [
            [1, 2, 2, 2, 2, 2, 2, 2],
            [3, 1, 2, 2, 2, 2, 2, 2],
            [5, 3, 4, 2, 2, 2, 2, 2],
            [7, 5, 2, 4, 2, 2, 2, 2],
            [9, 7, 2, 2, 4, 2, 2, 2],
            [11, 9, 2, 2, 2, 4, 2, 2],
            [13, 11, 2, 2, 2, 2, 4, 2],
            [15, 13, 2, 2, 2, 2, 2, 4],
        ]
        snf_bytes = json.dumps({"unshifted_eqlen_eqcsum": unsh, "shifted_multi_eqlen_eqcsum": sh_vecs}).encode("utf-8")
        with open(os.path.join(snf_dir, "snf_audit_vectors.json"), "wb") as fh:
            fh.write(snf_bytes)

        bpaper = os.path.join(cdir, "Blender", "paper")
        os.makedirs(bpaper, exist_ok=True)
        with open(os.path.join(bpaper, "main.tex"), "w", encoding="utf-8") as fh:
            fh.write(
                "Proposition: global minimum within the two-step silent-carry healing family.\n"
                "Section 3.3: steer $W_0, W_2, W_4, W_6 \\in \\{x, \\neg x\\}$ to enter.\n"
            )

        tii_dir = os.path.join(cdir, "TII-McEliece", "artifacts", "goppa_key_recovery", "witnesses")
        os.makedirs(tii_dir, exist_ok=True)
        challenges = [
            self._make_challenge(
                i,
                route="Route-A (synthetic)" if i < 89 else "Route-B (synthetic)",
                first_blood=(i < 55),
            )
            for i in range(94)
        ]
        tii_bytes = json.dumps(
            {
                "total_solved": 94,
                "route_a_solved": 89,
                "route_b_solved": 5,
                "first_bloods": 55,
                "challenges": challenges,
            }
        ).encode("utf-8")
        with open(os.path.join(tii_dir, "verified_tii_94_summary.json"), "wb") as fh:
            fh.write(tii_bytes)

        return {
            "lean_file_sha256": lean_shas,
            "blender_snf_witness_sha256": hashlib.sha256(snf_bytes).hexdigest(),
            "tii_94_summary_sha256": hashlib.sha256(tii_bytes).hexdigest(),
        }

    def test_01_core_primitives_hygiene_and_linear_algebra(self):
        # Float/complex, non-str key, int subclass, depth cap, bit cap, and unsupported container rejection
        for bad in (1.5, complex(1, 2), {"a": 0.1}, {0.5: "a"}, [1, 2.0], (3.0,)):
            self._assert_err("FLOAT_FORBIDDEN", o.verify_no_floats, bad)
        for bad_k in ({8: 16}, {True: "a"}):
            self._assert_err("INVALID_KEY_TYPE", o.verify_no_floats, bad_k)
            self._assert_err("INVALID_KEY_TYPE", o.canonical_json_bytes, bad_k)
        for bad_t in ({1, 2}, b"abc", object(), {"s": {1}}, [b"x"], _SampleIntEnum.ONE):
            self._assert_err("INVALID_JSON_TYPE", o.verify_no_floats, bad_t)
            self._assert_err("INVALID_JSON_TYPE", o.canonical_json_bytes, bad_t)
        self._assert_err("INVALID_JSON_TYPE", o.canonical_json_bytes, {"q": Fraction(1, 2)})
        self._assert_err("INT_TOO_LARGE", o.verify_no_floats, {"big": 1 << (o.MAX_INT_BITS + 1)})
        o.verify_no_floats({"max_ok": (1 << o.MAX_INT_BITS) - 1})
        o.verify_no_floats({"a": {"b": 1}}, max_depth=2)
        self._assert_err("MAX_DEPTH_EXCEEDED", o.verify_no_floats, {"a": {"b": 1}}, max_depth=1)
        deep = {}
        cur = deep
        for _ in range(o.MAX_CONTAINER_DEPTH + 2):
            nxt = {}
            cur["a"] = nxt
            cur = nxt
        self._assert_err("MAX_DEPTH_EXCEEDED", o.verify_no_floats, deep)
        o.verify_no_floats({"k": [1, True, None, "s", Fraction(3, 7)]})

        # require_exact_int boundaries (including IntEnum rejection & bit cap)
        self._assert_err("INVALID_INT", o.require_exact_int, True, "x")
        self._assert_err("INVALID_INT", o.require_exact_int, _SampleIntEnum.ONE, "x")
        self._assert_err("INVALID_INT", o.require_exact_int, "1", "x")
        self._assert_err("INVALID_INT", o.require_exact_int, 1.0, "x")
        self._assert_err("INT_TOO_LARGE", o.require_exact_int, 1 << (o.MAX_INT_BITS + 1), "x")
        max_exact_int = (1 << o.MAX_INT_BITS) - 1
        self.assertEqual(o.require_exact_int(max_exact_int, "x"), max_exact_int)
        self.assertEqual(o.require_exact_int(-5, "x"), -5)
        self.assertEqual(o.require_exact_int(0, "x", min_value=0, max_value=3), 0)
        self.assertEqual(o.require_exact_int(3, "x", min_value=0, max_value=3), 3)
        self._assert_err("RANGE_ERROR", o.require_exact_int, -1, "x", min_value=0)
        self._assert_err("RANGE_ERROR", o.require_exact_int, 4, "x", max_value=3)

        # require_exact_bool, require_non_empty_str, require_hex_sha256, require_hex_sha1
        self.assertIs(o.require_exact_bool(True, "b"), True)
        self.assertIs(o.require_exact_bool(False, "b"), False)
        for bad_b in (0, 1, "true", None):
            self._assert_err("INVALID_BOOL", o.require_exact_bool, bad_b, "b")
        self.assertEqual(o.require_non_empty_str("ok", "s"), "ok")
        for bad_s in (123, "", "   ", " ok", "ok "):
            self._assert_err("INVALID_STR", o.require_non_empty_str, bad_s, "s")
        good_sha = "0123456789abcdef" * 4
        self.assertEqual(o.require_hex_sha256(good_sha, "h"), good_sha)
        for bad_h in ("a" * 63, "a" * 65, "A" * 64, "g" * 64, "0" * 64):
            self._assert_err("INVALID_SHA256", o.require_hex_sha256, bad_h, "h")
        self.assertEqual(o.require_hex_sha1(o.UPSTREAM_COMMIT, "c"), o.UPSTREAM_COMMIT)
        for bad_c in ("a" * 39, "a" * 41, "A" * 40, "g" * 40, "0" * 40):
            self._assert_err("INVALID_COMMIT", o.require_hex_sha1, bad_c, "c")

        # frac_str & format_exact_decimal (half-to-even ties and -0 guard)
        self._assert_err("INVALID_FRACTION", o.frac_str, 1)
        self._assert_err("INVALID_FRACTION", o.format_exact_decimal, 1)
        self._assert_err("RANGE_ERROR", o.format_exact_decimal, Fraction(1, 2), -1)
        self._assert_err("RANGE_ERROR", o.format_exact_decimal, Fraction(1, 2), 13)
        self.assertEqual(o.frac_str(Fraction(6, 4)), "3/2")
        self.assertEqual(o.format_exact_decimal(Fraction(1, 2), 0), "0")
        self.assertEqual(o.format_exact_decimal(Fraction(3, 2), 0), "2")
        self.assertEqual(o.format_exact_decimal(Fraction(5, 2), 0), "2")
        self.assertEqual(o.format_exact_decimal(Fraction(1, 4), 0), "0")
        self.assertEqual(o.format_exact_decimal(Fraction(3, 4), 0), "1")
        self.assertEqual(o.format_exact_decimal(Fraction(-1, 1000), 0), "0")
        self.assertEqual(o.format_exact_decimal(Fraction(-3, 2), 0), "-2")
        self.assertEqual(o.format_exact_decimal(Fraction(-5, 4), 2), "-1.25")

        # _strict_equal
        self.assertFalse(o._strict_equal(1, True))
        self.assertFalse(o._strict_equal({"a": 1}, {"a": 1, "b": 2}))
        self.assertFalse(o._strict_equal({"a": 1}, {"a": True}))
        self.assertFalse(o._strict_equal([1, 2], [1]))
        self.assertFalse(o._strict_equal([1], [True]))
        self.assertTrue(o._strict_equal({"a": [1, True]}, {"a": [1, True]}))

        # Operator label hygiene
        self._assert_err("INVALID_LABELS", o.enforce_operator_label_hygiene, "not_seq")
        self._assert_err("INVALID_LABELS", o.enforce_operator_label_hygiene, [])
        self._assert_err("METAPHOR_LABEL_REJECTED", o.enforce_operator_label_hygiene, ["valid_op", "quantum_leap_lift"])
        self.assertTrue(o.enforce_operator_label_hygiene(a.OPERATOR_LABELS)["passed"])

        # GF(2) polynomial Rabin irreducibility & inverse guards
        self.assertTrue(o._gf2_poly_is_irred_pow2(o.STANDARD_COLM_MOD128))
        self.assertFalse(o._gf2_poly_is_irred_pow2((1 << 128) | 1))
        self.assertFalse(o._gf2_poly_is_irred_pow2(0b1))  # deg 0
        self.assertFalse(o._gf2_poly_is_irred_pow2(0b1011))  # irreducible deg 3 (not power of 2)
        self.assertFalse(o._gf2_poly_is_irred_pow2(0b110))  # x*(x+1): passes x^4=x, fails half gcd
        self.assertFalse(o._gf2_poly_is_irred_pow2(0b110111011))  # product of two deg-4 irreducibles
        self.assertIsNone(o._gf2_poly_inv(0, o.STANDARD_COLM_MOD128))
        self.assertIsNone(o._gf2_poly_inv(3, (1 << 128) | 1))

        # Bareiss determinant edge cases
        self.assertEqual(o._bareiss_det_exact([[1, 2], [2, 4]]), 0)
        self.assertEqual(o._bareiss_det_exact([[0, 1], [1, 0]]), -1)
        self.assertEqual(o._bareiss_det_exact([[0, 1], [0, 2]]), 0)

        # 2-adic SNF validation & edge cases
        self._assert_err("RANGE_ERROR", o.snf_2adic_valuations_exact, [[1]], 1)
        self._assert_err("RANGE_ERROR", o.snf_2adic_valuations_exact, [[1]], 65)
        self._assert_err("INVALID_MATRIX", o.snf_2adic_valuations_exact, 42, 8)
        self._assert_err("INVALID_MATRIX", o.snf_2adic_valuations_exact, [], 8)
        self._assert_err("INVALID_MATRIX", o.snf_2adic_valuations_exact, [42], 8)
        self._assert_err("INVALID_MATRIX", o.snf_2adic_valuations_exact, [1], 8)
        self._assert_err("INVALID_MATRIX", o.snf_2adic_valuations_exact, [[]], 8)
        self._assert_err("INVALID_MATRIX", o.snf_2adic_valuations_exact, [[1, 2], "ab"], 8)
        self._assert_err("INVALID_MATRIX", o.snf_2adic_valuations_exact, [[1, 2], [1]], 8)
        self._assert_err("INVALID_INT", o.snf_2adic_valuations_exact, [[1.5]], 8)
        self.assertEqual(o.snf_2adic_valuations_exact([[0, 0], [0, 0]], 8), [8, 8])
        self.assertEqual(o.snf_2adic_valuations_exact([[0, 2, 0]], 8), [1, 8, 8])
        self.assertEqual(o.snf_2adic_valuations_exact([[0, 4], [2, 0]], 8), [1, 2])

    def test_02_portal_summary_validation_and_positive_pillars(self):
        fx = copy.deepcopy(a.STANDALONE_PORTAL_FIXTURE)
        self._assert_err("INVALID_PORTAL_SUMMARY", o.validate_portal_summary, [])
        for bad_mut, exp_code in (
            (lambda d: d.pop("tii_94_summary"), "INVALID_PORTAL_SUMMARY"),
            (lambda d: d.__setitem__("extra", 1), "INVALID_PORTAL_SUMMARY"),
            (lambda d: d.__setitem__("diag_source", "other"), "INVALID_PORTAL_SUMMARY"),
            (lambda d: d.__setitem__("diag_source", " standalone_pinned_fixture "), "INVALID_STR"),
            (lambda d: d.__setitem__("upstream_commit", "a" * 39), "INVALID_COMMIT"),
            (lambda d: d.__setitem__("upstream_commit", "A" * 40), "INVALID_COMMIT"),
            (lambda d: d.__setitem__("upstream_commit", "0" * 40), "INVALID_COMMIT"),
            (lambda d: d.__setitem__("upstream_commit", "a" * 40), "COMMIT_MISMATCH"),
            (lambda d: d.__setitem__("bentsum_lean", []), "INVALID_LEAN_MANIFEST"),
            (lambda d: d["bentsum_lean"].__setitem__("extra", 1), "INVALID_LEAN_MANIFEST"),
            (lambda d: d["bentsum_lean"].__setitem__("files_checked", 0), "RANGE_ERROR"),
            (lambda d: d["bentsum_lean"].__setitem__("banned_construct_findings", -1), "RANGE_ERROR"),
            (lambda d: d["bentsum_lean"].__setitem__("lean_file_sha256", [1, 2, 3, 4, 5]), "INVALID_LEAN_MANIFEST"),
            (
                lambda d: (
                    d["bentsum_lean"]["lean_file_sha256"].pop("BentSum.lean"),
                    d["bentsum_lean"]["lean_file_sha256"].__setitem__("Evil.lean", "0" * 64),
                ),
                "INVALID_LEAN_MANIFEST",
            ),
            (
                lambda d: (
                    d["bentsum_lean"]["lean_file_sha256"].__setitem__("Extra.lean", "0" * 64),
                    d["bentsum_lean"].__setitem__("files_checked", 6),
                ),
                "INVALID_LEAN_MANIFEST",
            ),
            (lambda d: d["bentsum_lean"].__setitem__("files_checked", 6), "INVALID_LEAN_MANIFEST"),
            (lambda d: d["bentsum_lean"]["lean_file_sha256"].__setitem__("BentSum.lean", "bad"), "INVALID_SHA256"),
            (lambda d: d["bentsum_lean"]["lean_file_sha256"].__setitem__("BentSum.lean", "0" * 64), "INVALID_SHA256"),
            (lambda d: d.__setitem__("blender_snf_witness", []), "INVALID_BLENDER_WITNESS"),
            (lambda d: d["blender_snf_witness"].__setitem__("extra", 1), "INVALID_BLENDER_WITNESS"),
            (lambda d: d["blender_snf_witness"].__setitem__("witness_sha256", "bad"), "INVALID_SHA256"),
            (lambda d: d["blender_snf_witness"].__setitem__("unshifted_count", 0), "RANGE_ERROR"),
            (lambda d: d["blender_snf_witness"].__setitem__("shifted_multi_count", 1), "RANGE_ERROR"),
            (lambda d: d["blender_snf_witness"].__setitem__("f2_xor_fail_count", -1), "RANGE_ERROR"),
            (lambda d: d["blender_snf_witness"].__setitem__("mod32_superposition_pass_count", -1), "RANGE_ERROR"),
            (lambda d: d["blender_snf_witness"].__setitem__("unshifted_snf_exps", "12345678"), "INVALID_BLENDER_WITNESS"),
            (lambda d: d["blender_snf_witness"].__setitem__("unshifted_snf_exps", [0] * 7), "INVALID_BLENDER_WITNESS"),
            (lambda d: d["blender_snf_witness"].__setitem__("shifted_multi_snf_exps", "12345678"), "INVALID_BLENDER_WITNESS"),
            (lambda d: d["blender_snf_witness"].__setitem__("shifted_multi_snf_exps", [0] * 7), "INVALID_BLENDER_WITNESS"),
            (lambda d: d["blender_snf_witness"]["unshifted_snf_exps"].__setitem__(0, 33), "RANGE_ERROR"),
            (lambda d: d["blender_snf_witness"]["shifted_multi_snf_exps"].__setitem__(0, -1), "RANGE_ERROR"),
            (lambda d: d.__setitem__("blender_issues_text_checks", []), "INVALID_BLENDER_ISSUES"),
            (lambda d: d["blender_issues_text_checks"].__setitem__("extra", True), "INVALID_BLENDER_ISSUES"),
            (lambda d: d["blender_issues_text_checks"].__setitem__("issue1_global_minimum_claim_present", 1), "INVALID_BOOL"),
            (lambda d: d.__setitem__("tii_94_summary", []), "INVALID_TII_SUMMARY"),
            (lambda d: d["tii_94_summary"].__setitem__("extra", 1), "INVALID_TII_SUMMARY"),
            (lambda d: d["tii_94_summary"].__setitem__("summary_sha256", "bad"), "INVALID_SHA256"),
            (lambda d: d["tii_94_summary"].__setitem__("total_solved", 0), "RANGE_ERROR"),
            (lambda d: d["tii_94_summary"].__setitem__("route_a_solved", -1), "RANGE_ERROR"),
            (lambda d: d["tii_94_summary"].__setitem__("route_b_solved", 95), "RANGE_ERROR"),
            (lambda d: d["tii_94_summary"].__setitem__("first_bloods", 95), "RANGE_ERROR"),
            (lambda d: d["tii_94_summary"].__setitem__("route_a_solved", 80), "TII_SUM_MISMATCH"),
        ):
            bad_d = copy.deepcopy(fx)
            bad_mut(bad_d)
            self._assert_err(exp_code, o.validate_portal_summary, bad_d)

        # Positive computational verification of Pillars 1, 2, 3
        p1 = o.audit_bentsum_walsh_exact()
        self.assertTrue(p1["passed"])
        self.assertEqual(p1["q3_weight"], 28)
        self.assertEqual(p1["cylq3_n8_weight"], 28)
        self.assertEqual(p1["cylq3_n8_weight_mod_8"], 4)
        self.assertFalse(p1["cylq3_n8_plus_g8_bent"])
        self.assertEqual(p1["positive_bentsum_parseval_N"], 8)
        self.assertEqual(p1["liftcylq3_n10_weight"], 512)
        self.assertEqual(p1["liftcylq3_n10_periods"], [0, 1])

        p2 = o.audit_fast_algebraic_and_blender_exact()
        self.assertTrue(p2["passed"])
        self.assertEqual(p2["aradi"]["analytical_zero_sum_eq_count"], 198)
        self.assertEqual(p2["aradi"]["latincrypt2025_blind_column_hist"], {"8": 16, "13": 16})
        self.assertEqual(p2["aradi"]["check_scopes"]["zero_empirical_violations"], "sampled")
        self.assertTrue(p2["colm"]["mod128_irreducible"])
        self.assertEqual(p2["colm"]["transplant_set"], [1, 3, 4, 5, 6, 7, 129, 130])
        self.assertEqual(p2["colm"]["definitional_controls"]["scope"], "definitional")
        self.assertEqual(p2["colm"]["literature_anchor"]["scope"], "anchor")
        self.assertTrue(p2["sbcvole"]["secret_256bit_recovered_exact"])
        self.assertEqual(p2["sbcvole"]["claim_scope"], "sampled")
        self.assertEqual(p2["blender"]["sampling_metadata"]["start_state"], "standard_blender256_iv_only")
        self.assertEqual(p2["blender"]["snf_from_iv_unshifted"], [0, 0, 1, 1, 2, 2, 3, 3])
        self.assertEqual(p2["blender"]["snf_from_iv_multi_shifted"], [0, 0, 1, 1, 1, 1, 1, 1])

        p3 = o.audit_background_goppa_and_hawk_identities_exact()
        self.assertTrue(p3["passed"])
        self.assertTrue(p3["tii_goppa_identity"]["shortened_code_equals_goppa_on_shorter_support"])
        self.assertEqual(p3["tii_goppa_identity"]["mini_goppa_shortened_n21_codeword_count"], 64)
        self.assertEqual(p3["tii_goppa_identity"]["literature_anchors"]["tii250_compression_exact"], "197803/30016")
        self.assertEqual(p3["tii_goppa_identity"]["literature_anchors"]["tii125_compression_exact"], "98347/15052")
        self.assertTrue(p3["hawk_lattice_identity"]["h_generates_parity_sublattice"])
        self.assertEqual(p3["hawk_lattice_identity"]["parity_sublattice_abs_det_H"], 128)
        self.assertEqual(p3["hawk_lattice_identity"]["lll_blind_max_gram_diag"], 41)
        self.assertEqual(p3["hawk_lattice_identity"]["lll_abs_det_U"], 1)
        self.assertEqual(p3["hawk_lattice_identity"]["gram_diag_compression_exact"], "31954/41")

        # Declared upstream inputs are recorded cleanly outside all_gates_passed
        decl = o.build_declared_upstream_inputs(o.validate_portal_summary(fx))
        self.assertTrue(decl["excluded_from_all_gates_passed"])
        self.assertEqual(decl["provenance_status"], "declared_pinned_fixture_not_remeasured_offline")
        self.assertEqual(decl["tii_94_campaign_manifest"]["total_solved"], 94)

    def test_03_negative_wrong_value_controls_for_every_computational_gate(self):
        """Targeted wrong-value must-fail tests killing replacing ANY computational check entry with True."""
        # --- Pillar 1: BentSum (19 checks) ---
        base_q3 = [
            (((z >> 0) & 1) & ((z >> 1) & 1))
            ^ (((z >> 2) & 1) & ((z >> 3) & 1))
            ^ (((z >> 4) & 1) & ((z >> 5) & 1))
            for z in range(64)
        ]
        base_cyl4 = [(((x >> 0) & 1) & ((x >> 1) & 1)) & base_q3[x >> 2] for x in range(256)]
        base_g8 = [
            (((x >> 0) & 1) & ((x >> 4) & 1))
            ^ (((x >> 1) & 1) & ((x >> 5) & 1))
            ^ (((x >> 2) & 1) & ((x >> 6) & 1))
            ^ (((x >> 3) & 1) & ((x >> 7) & 1))
            for x in range(256)
        ]
        base_pos_r8 = [((x >> 0) & 1) & ((x >> 1) & 1) & ((x >> 2) & 1) for x in range(256)]
        base_lift4 = [((x >> 1) & 1) ^ base_cyl4[x >> 2] for x in range(1024)]
        base_g10 = [
            (((x >> 0) & 1) & ((x >> 1) & 1)) ^ (((x >> 0) & 1) & base_pos_r8[x >> 2]) ^ base_g8[x >> 2]
            for x in range(1024)
        ]

        q3_flip1 = list(base_q3)
        q3_flip1[0] ^= 1
        r = o.audit_bentsum_walsh_exact(q3_tt=q3_flip1)
        self.assertFalse(r["checks"]["q3_is_bent"])
        self.assertFalse(r["passed"])

        # Invert q3: remains bent & deg 2, fails ONLY q3_weight_28 (wt=36) when cyl4_tt is held fixed
        r = o.audit_bentsum_walsh_exact(q3_tt=[1 ^ b for b in base_q3], cyl4_tt=base_cyl4)
        self.assertFalse(r["checks"]["q3_weight_28"])
        self.assertTrue(r["checks"]["q3_is_bent"])
        self.assertTrue(r["checks"]["q3_degree_2"])
        self.assertFalse(r["passed"])

        r = o.audit_bentsum_walsh_exact(q3_tt=[0] * 64, cyl4_tt=base_cyl4)
        self.assertFalse(r["checks"]["q3_degree_2"])
        self.assertFalse(r["passed"])

        # cyl4 weight 36 inside coset (still mod 8 == 4, deg 4, in coset, unique const deriv -> isolates weight_28)
        cyl4_inv_coset = [(((x >> 0) & 1) & ((x >> 1) & 1)) & (1 ^ base_q3[x >> 2]) for x in range(256)]
        r = o.audit_bentsum_walsh_exact(cyl4_tt=cyl4_inv_coset, lift4_tt=base_lift4)
        self.assertFalse(r["checks"]["cylq3_n8_weight_28"])
        self.assertFalse(r["passed"])

        # cyl4 constant zero -> fails degree_4, weight_not_div_8, only_zero_const_deriv
        r = o.audit_bentsum_walsh_exact(cyl4_tt=[0] * 256, lift4_tt=base_lift4)
        self.assertFalse(r["checks"]["cylq3_n8_degree_4"])
        self.assertFalse(r["checks"]["cylq3_n8_weight_not_div_8"])
        self.assertFalse(r["checks"]["cylq3_n8_only_zero_const_deriv"])
        self.assertFalse(r["passed"])

        # cyl4 outside coset {x0=x1=1}
        cyl4_out = list(base_cyl4)
        cyl4_out[0] = 1
        r = o.audit_bentsum_walsh_exact(cyl4_tt=cyl4_out, lift4_tt=base_lift4)
        self.assertFalse(r["checks"]["cylq3_n8_in_codim2_coset"])
        self.assertFalse(r["passed"])

        # cyl4 = pos_r8 -> g8 + cyl4 = h8 IS bent -> fails cylq3_n8_plus_g8_not_bent
        r = o.audit_bentsum_walsh_exact(cyl4_tt=base_pos_r8, lift4_tt=base_lift4)
        self.assertFalse(r["checks"]["cylq3_n8_plus_g8_not_bent"])
        self.assertFalse(r["passed"])

        # Positive controls on g8, pos_r8, h8, wphi, parseval_N, weight_32
        g8_flip1 = list(base_g8)
        g8_flip1[0] ^= 1
        r = o.audit_bentsum_walsh_exact(g8_tt=g8_flip1, g10_tt=base_g10)
        self.assertFalse(r["checks"]["pos_ctrl_g8_bent"])
        self.assertFalse(r["passed"])

        pos_r8_flip1 = list(base_pos_r8)
        pos_r8_flip1[3] ^= 1
        r = o.audit_bentsum_walsh_exact(pos_r8=pos_r8_flip1, g10_tt=base_g10)
        self.assertFalse(r["checks"]["pos_ctrl_h8_bent"])
        self.assertFalse(r["checks"]["pos_ctrl_wphi_ternary"])
        self.assertFalse(r["passed"])

        r = o.audit_bentsum_walsh_exact(pos_r8=[0] * 256, g10_tt=base_g10)
        self.assertFalse(r["checks"]["pos_ctrl_parseval_N_even_8"])
        self.assertFalse(r["checks"]["pos_ctrl_weight_32_div_8"])
        self.assertFalse(r["passed"])

        # lift4 controls: unbalanced, low degree, extra periods
        lift4_flip1 = list(base_lift4)
        lift4_flip1[0] ^= 1
        r = o.audit_bentsum_walsh_exact(lift4_tt=lift4_flip1)
        self.assertFalse(r["checks"]["liftcylq3_n10_balanced_512"])
        self.assertFalse(r["passed"])

        r = o.audit_bentsum_walsh_exact(lift4_tt=[(x >> 1) & 1 for x in range(1024)])
        self.assertFalse(r["checks"]["liftcylq3_n10_degree_4"])
        self.assertFalse(r["checks"]["liftcylq3_n10_only_period_e0"])
        self.assertFalse(r["passed"])

        # g10 controls: non-bent & shifted linear x0 (still bent, isolates dg10_matches_lift!)
        g10_flip1 = list(base_g10)
        g10_flip1[0] ^= 1
        r = o.audit_bentsum_walsh_exact(g10_tt=g10_flip1)
        self.assertFalse(r["checks"]["pos_ctrl_g10_bent"])
        self.assertFalse(r["passed"])

        g10_lin = [base_g10[x] ^ (x & 1) for x in range(1024)]
        r = o.audit_bentsum_walsh_exact(g10_tt=g10_lin)
        self.assertTrue(r["checks"]["pos_ctrl_g10_bent"])
        self.assertFalse(r["checks"]["pos_ctrl_dg10_matches_lift"])
        self.assertFalse(r["passed"])

        # --- Pillar 2A: ARADI (13 checks) ---
        r = o._audit_aradi_exact(rot_consts=((1, 2, 3), (10, 9, 11), (9, 4, 14), (8, 9, 7)))
        self.assertFalse(r["checks"]["all_L_involutive"])
        self.assertFalse(r["passed"])

        r = o._audit_aradi_exact(rot_consts=((11, 8, 14), (10, 9, 11), (9, 4, 14), (7, 3, 11)))
        for k in (
            "cancel_dims_0_0_0_8",
            "L3_only_symmetric",
            "L3_only_orthogonal",
            "L3_eight_4col_islands",
            "latincrypt_blind_hist_exact",
            "zero_sum_eq_count_198",
            "island_nullities_exact",
        ):
            self.assertFalse(r["checks"][k], f"ARADI check {k} should fail for L3=(7,3,11)")
        self.assertFalse(r["passed"])

        base_sbox = []
        for u in range(16):
            ow, ox, oy, oz = o._aradi_sbox_word(u & 1, (u >> 1) & 1, (u >> 2) & 1, (u >> 3) & 1)
            base_sbox.append(ow | (ox << 1) | (oy << 2) | (oz << 3))
        sbox_bad_x = list(base_sbox)
        sbox_bad_x[15] ^= 0b0010  # flips x bit at u=15 -> degree-4 term in super_x
        r = o._audit_aradi_exact(sbox_tbl=sbox_bad_x)
        self.assertFalse(r["checks"]["super_sbox_deg_x_3"])
        self.assertFalse(r["passed"])

        sbox_bad_z = list(base_sbox)
        sbox_bad_z[15] ^= 0b1000  # flips z bit at u=15 -> degree-4 term in super_z
        r = o._audit_aradi_exact(sbox_tbl=sbox_bad_z)
        self.assertFalse(r["checks"]["super_sbox_deg_z_3"])
        self.assertFalse(r["passed"])

        r = o._audit_aradi_exact(num_rounds=4)
        self.assertFalse(r["checks"]["zero_empirical_violations"])
        self.assertGreater(r["empirical_violations_sampled"], 0)
        self.assertFalse(r["passed"])

        r = o._audit_aradi_exact(mitigation_rc=(1, 2, 3))
        self.assertFalse(r["checks"]["mitigation_L3p_involutive"])
        self.assertFalse(r["passed"])

        r = o._audit_aradi_exact(mitigation_rc=(8, 9, 7))
        self.assertTrue(r["checks"]["mitigation_L3p_involutive"])
        self.assertFalse(r["checks"]["mitigation_L3p_zero_cancel"])
        self.assertFalse(r["passed"])

        # --- Pillar 2B: COLM (5 checks) ---
        r = o._audit_colm_exact(mod128=(1 << 128) | 1, alpha_const=3)
        self.assertFalse(r["checks"]["mod128_irreducible"])
        self.assertFalse(r["checks"]["inv3_exact"])
        self.assertFalse(r["passed"])

        r = o._audit_colm_exact(alpha_const=2)
        self.assertTrue(r["checks"]["mod128_irreducible"])
        self.assertTrue(r["checks"]["inv3_exact"])
        self.assertFalse(r["checks"]["transplant_first_m_129"])
        self.assertFalse(r["checks"]["transplant_set_exact"])
        self.assertFalse(r["checks"]["colm_tau_blocked"])
        self.assertFalse(r["passed"])

        # --- Pillar 2C: SBC-VOLE (4 checks) ---
        r = o._audit_sbcvole_exact(mod257=(1 << 257) | (1 << 1) | 1)
        self.assertFalse(r["checks"]["modulus_irreducible"])
        self.assertFalse(r["passed"])

        r = o._audit_sbcvole_exact(corrupt_v_last=1)
        self.assertFalse(r["checks"]["nsbc_planted"])
        self.assertFalse(r["passed"])

        r = o._audit_sbcvole_exact(zero_linear_cols=True)
        self.assertFalse(r["checks"]["linear_rank_ge_254"])
        self.assertFalse(r["passed"])

        r = o._audit_sbcvole_exact(corrupt_bval=1)
        self.assertFalse(r["checks"]["secret_256bit_recovered_exact"])
        self.assertFalse(r["passed"])

        # --- Pillar 2D: Blender-256 (6 checks) ---
        r = o._audit_blender_exact(iv=(0, 0, 0, 0, 0, 0, 0, 0))
        self.assertFalse(r["checks"]["thm2_period8"])
        self.assertFalse(r["checks"]["thm2_permanent_invariants"])
        self.assertFalse(r["checks"]["entry_obeys_thm2"])
        self.assertFalse(r["checks"]["entry_refutes_sec33_prose"])
        self.assertFalse(r["passed"])

        r = o._audit_blender_exact(truncate_unsh_vectors=1)
        self.assertFalse(r["checks"]["snf_from_iv_unshifted_exact"])
        self.assertFalse(r["passed"])

        r = o._audit_blender_exact(shift_list=())
        self.assertTrue(r["checks"]["snf_from_iv_unshifted_exact"])
        self.assertFalse(r["checks"]["snf_from_iv_multi_shifted_exact"])
        self.assertFalse(r["passed"])

        # --- Pillar 3A: Binary Goppa shortening identity (8 checks) ---
        r = o._audit_tii_goppa_identity_exact(g_poly=(0, 2, 1, 1))
        self.assertFalse(r["checks"]["goppa_no_roots"])
        self.assertFalse(r["passed"])

        r = o._audit_tii_goppa_identity_exact(n_len=23)
        self.assertFalse(r["checks"]["mini_dim_9"])
        self.assertFalse(r["checks"]["mini_min_weight_13"])
        self.assertFalse(r["passed"])

        r = o._audit_tii_goppa_identity_exact(short_n=20)
        self.assertFalse(r["checks"]["mini_short_n21_dim_6"])
        self.assertFalse(r["checks"]["mini_short_n21_min_weight_6"])
        self.assertFalse(r["passed"])

        r = o._audit_tii_goppa_identity_exact(short_support_override=list(range(1, 22)))
        self.assertFalse(r["checks"]["shortened_equals_goppa_on_shorter_support"])
        self.assertFalse(r["passed"])

        r = o._audit_tii_goppa_identity_exact(verify_g_poly=(1, 1, 1, 1))
        self.assertFalse(r["checks"]["thm1_locator_deriv_square"])
        self.assertFalse(r["passed"])

        r = o._audit_tii_goppa_identity_exact(verify_g_poly=(1, 2, 0, 1))
        self.assertFalse(r["checks"]["thm1_e2_equals_gt1_sq"])
        self.assertFalse(r["passed"])

        # --- Pillar 3B: HAWK parity sublattice & exact LLL (11 checks) ---
        eye8 = [[1 if i == j else 0 for j in range(8)] for i in range(8)]
        two_eye8 = [[2 if i == j else 0 for j in range(8)] for i in range(8)]
        r = o._audit_hawk_lattice_identity_exact(u_rec_override=eye8)
        self.assertFalse(r["checks"]["unimodular_planted_inverse_exact"])
        self.assertFalse(r["passed"])

        r = o._audit_hawk_lattice_identity_exact(u_rec_override=two_eye8)
        self.assertFalse(r["checks"]["abs_det_U_1"])
        self.assertFalse(r["checks"]["gram_det_equal"])
        self.assertFalse(r["passed"])

        sing_b = [[0] * 8] + [[1 if i == j else 0 for j in range(8)] for i in range(1, 8)]
        r = o._audit_hawk_lattice_identity_exact(b_good=sing_b)
        self.assertFalse(r["checks"]["gram_det_positive"])
        self.assertFalse(r["checks"]["lll_unimodular_and_exact"])
        self.assertFalse(r["passed"])

        r = o._audit_hawk_lattice_identity_exact(u_bad=eye8)
        self.assertFalse(r["checks"]["max_diag_raw_31954"])
        self.assertFalse(r["passed"])

        scaled_b = [
            [6, 0, 0, 0, 0, 0, 0, 0],
            [2, 6, 0, 0, 0, 0, 0, 0],
            [-2, 2, 8, 0, 0, 0, 0, 0],
            [0, -2, 2, 8, 0, 0, 0, 0],
            [2, 0, -2, 2, 10, 0, 0, 0],
            [-2, 2, 0, -2, 2, 10, 0, 0],
            [0, -2, 2, 0, -2, 2, 12, 0],
            [2, 0, -2, 2, 0, -2, 2, 12],
        ]
        r = o._audit_hawk_lattice_identity_exact(b_good=scaled_b)
        self.assertFalse(r["checks"]["max_diag_red_41"])
        self.assertFalse(r["checks"]["lll_blind_recovers_max_diag_41"])
        self.assertFalse(r["passed"])

        # Non-parity H with det=128 (diag(2,2,2,2,2,2,2,1)): isolates h_generates_parity_sublattice!
        non_parity_h = [[(1 if i == 7 else 2) if i == j else 0 for j in range(8)] for i in range(8)]
        r = o._audit_hawk_lattice_identity_exact(h_override=non_parity_h)
        self.assertTrue(r["checks"]["parity_sublattice_index_128"])
        self.assertTrue(r["checks"]["gram_prime_det_scaling"])
        self.assertFalse(r["checks"]["h_generates_parity_sublattice"])
        self.assertFalse(r["passed"])

        r = o._audit_hawk_lattice_identity_exact(h_override=two_eye8)
        self.assertFalse(r["checks"]["parity_sublattice_index_128"])
        self.assertFalse(r["checks"]["gram_prime_det_scaling"])
        self.assertFalse(r["passed"])

        # Wrapper checks in Pillar 2 & Pillar 3
        for fn_name, check_key in (
            ("_audit_aradi_exact", "aradi_verified"),
            ("_audit_colm_exact", "colm_verified"),
            ("_audit_sbcvole_exact", "sbcvole_verified"),
            ("_audit_blender_exact", "blender_computed_verified"),
        ):
            with mock.patch.object(o, fn_name, return_value={"passed": False}):
                p2_fail = o.audit_fast_algebraic_and_blender_exact()
                self.assertFalse(p2_fail["checks"][check_key])
                self.assertFalse(p2_fail["passed"])

        for fn_name, check_key in (
            ("_audit_tii_goppa_identity_exact", "binary_goppa_shortening_identity_verified"),
            ("_audit_hawk_lattice_identity_exact", "hawk_parity_sublattice_and_lll_verified"),
        ):
            with mock.patch.object(o, fn_name, return_value={"passed": False}):
                p3_fail = o.audit_background_goppa_and_hawk_identities_exact()
                self.assertFalse(p3_fail["checks"][check_key])
                self.assertFalse(p3_fail["passed"])

    def test_04_certification_lean4_rawstr_scanner_verify_and_live_pins(self):
        fx = copy.deepcopy(a.STANDALONE_PORTAL_FIXTURE)
        cert = a.run_audit(live=False, research_dir=None)
        self.assertTrue(cert["all_gates_passed"])
        self.assertEqual(cert["verdict"], "AUDITED_MINIMAX_CRYPTANALYSIS_PORTAL")
        self.assertEqual(cert["novelty_classification"], "N0")
        self.assertIs(cert["live_portal_inspected"], False)
        self.assertTrue(cert["declared_upstream_inputs"]["excluded_from_all_gates_passed"])

        raw_cert_bytes = o.canonical_json_bytes(cert) + b"\n"
        receipt = a.verify_certificate_bytes(raw_cert_bytes)
        self.assertTrue(receipt["verified"])
        self.assertEqual(receipt["certificate_sha256"], cert["certificate_sha256"])

        # Verify committed certificate file in this directory matches strictly
        committed_path = os.path.join(_SCRIPT_DIR, "minimax_cryptanalysis_certificate.json")
        if os.path.isfile(committed_path):
            disk_receipt = a.verify_certificate_file(committed_path)
            self.assertTrue(disk_receipt["verified"])
            self.assertEqual(disk_receipt["certificate_sha256"], cert["certificate_sha256"])

        p1 = cert["pillar1_bentsum_walsh"]
        p2 = cert["pillar2_fast_algebraic_and_blender"]
        p3 = cert["pillar3_background_goppa_and_hawk_identities"]
        axes = cert["three_axis_audit_checks"]

        self._assert_err("INVALID_MODE", o.certify_minimax_cryptanalysis_audit_exact, "bad", False, a.OPERATOR_LABELS, fx, p1, p2, p3, axes)
        self._assert_err("INVALID_STR", o.certify_minimax_cryptanalysis_audit_exact, " standalone_pinned_replay ", False, a.OPERATOR_LABELS, fx, p1, p2, p3, axes)
        self._assert_err("MODE_MISMATCH", o.certify_minimax_cryptanalysis_audit_exact, "standalone_pinned_replay", True, a.OPERATOR_LABELS, fx, p1, p2, p3, axes)
        self._assert_err("INVALID_AXES", o.certify_minimax_cryptanalysis_audit_exact, "standalone_pinned_replay", False, a.OPERATOR_LABELS, fx, p1, p2, p3, {"x": True})
        self._assert_err("INVALID_AXES", o.certify_minimax_cryptanalysis_audit_exact, "standalone_pinned_replay", False, a.OPERATOR_LABELS, fx, p1, p2, p3, [])
        for bad_pillars in (("bad", p2, p3), (p1, "bad", p3), (p1, p2, "bad")):
            self._assert_err("INVALID_PILLAR", o.certify_minimax_cryptanalysis_audit_exact, "standalone_pinned_replay", False, a.OPERATOR_LABELS, fx, *bad_pillars, axes)
        for bad_pillars in ((dict(p1, passed=1), p2, p3), (p1, dict(p2, passed=1), p3), (p1, p2, dict(p3, passed=1))):
            self._assert_err("PILLAR_CONTRADICTION", o.certify_minimax_cryptanalysis_audit_exact, "standalone_pinned_replay", False, a.OPERATOR_LABELS, fx, *bad_pillars, axes)
        self._assert_err("PROVENANCE_MISMATCH", o.certify_minimax_cryptanalysis_audit_exact, "live_portal_audit", True, a.OPERATOR_LABELS, fx, p1, p2, p3, axes)
        fx_lv = copy.deepcopy(fx)
        fx_lv["diag_source"] = "live_portal_read"
        self._assert_err("PROVENANCE_MISMATCH", o.certify_minimax_cryptanalysis_audit_exact, "standalone_pinned_replay", False, a.OPERATOR_LABELS, fx_lv, p1, p2, p3, axes)
        self._assert_err("AXIS_CONTRADICTION", o.certify_minimax_cryptanalysis_audit_exact, "standalone_pinned_replay", False, a.OPERATOR_LABELS, fx, p1, p2, p3, dict(axes, fast_algebraic_and_blender_computed=False))
        # Standalone commit drift fails closed
        fx_bad_commit = copy.deepcopy(fx)
        fx_bad_commit["upstream_commit"] = "a" * 40
        self._assert_err("COMMIT_MISMATCH", o.certify_minimax_cryptanalysis_audit_exact, "standalone_pinned_replay", False, a.OPERATOR_LABELS, fx_bad_commit, p1, p2, p3, axes)

        # Rejected gate verdict when a computational pillar fails
        p1_fail = dict(p1, passed=False)
        with mock.patch.object(o, "audit_bentsum_walsh_exact", return_value=p1_fail):
            cert_fail = o.certify_minimax_cryptanalysis_audit_exact(
                "standalone_pinned_replay",
                False,
                a.OPERATOR_LABELS,
                fx,
                p1_fail,
                p2,
                p3,
                dict(axes, bentsum_walsh_hadamard_and_anf=False),
            )
            self.assertFalse(cert_fail["all_gates_passed"])
            self.assertEqual(cert_fail["verdict"], "REJECTED_GATE_FAILED")

        # --- Forged-certificate rejection tests for --verify FILE ---
        def _rehash(d):
            c = copy.deepcopy(d)
            c.pop("certificate_sha256", None)
            c["certificate_sha256"] = o.canonical_sha256(c)
            return o.canonical_json_bytes(c) + b"\n"

        # 1. Perturbed q3_weight=29 re-hashed
        f_q3 = copy.deepcopy(cert)
        f_q3["pillar1_bentsum_walsh"]["q3_weight"] = 29
        self._assert_err("CERTIFICATE_MISMATCH", a.verify_certificate_bytes, _rehash(f_q3))

        # 2. REJECTED_GATE_FAILED next to all_gates_passed=True
        f_ver = copy.deepcopy(cert)
        f_ver["verdict"] = "REJECTED_GATE_FAILED"
        self._assert_err("INVALID_VERDICT", a.verify_certificate_bytes, _rehash(f_ver))

        # 3. all_gates_passed=False
        f_gate = copy.deepcopy(cert)
        f_gate["all_gates_passed"] = False
        self._assert_err("GATE_FAILED", a.verify_certificate_bytes, _rehash(f_gate))

        # 4. standalone with live_portal_inspected=True
        f_mode = copy.deepcopy(cert)
        f_mode["live_portal_inspected"] = True
        self._assert_err("MODE_MISMATCH", a.verify_certificate_bytes, _rehash(f_mode))

        # 5. different upstream_commit
        f_com = copy.deepcopy(cert)
        f_com["upstream_commit"] = "a" * 40
        self._assert_err("COMMIT_MISMATCH", a.verify_certificate_bytes, _rehash(f_com))

        # 6. Float 28.0 in place of 28
        raw_float = raw_cert_bytes.replace(b'"q3_weight":28', b'"q3_weight":28.0', 1)
        self._assert_err("FLOAT_FORBIDDEN", a.verify_certificate_bytes, raw_float)

        # 7. NaN constant
        raw_nan = raw_cert_bytes.replace(b'"q3_weight":28', b'"q3_weight":NaN', 1)
        self._assert_err("FLOAT_FORBIDDEN", a.verify_certificate_bytes, raw_nan)

        # 8. Hollow certificate with only flags
        hollow = {"all_gates_passed": True, "live_portal_inspected": True}
        hollow["certificate_sha256"] = o.canonical_sha256(hollow)
        self._assert_err("INVALID_STR", a.verify_certificate_bytes, o.canonical_json_bytes(hollow) + b"\n")

        # 9. Duplicate key copy
        raw_dup = raw_cert_bytes.replace(b'"q3_weight":28', b'"q3_weight":28,"q3_weight":28', 1)
        self._assert_err("DUPLICATE_KEY", a.verify_certificate_bytes, raw_dup)

        # 10. CRLF copy
        self._assert_err("CRLF_FORBIDDEN", a.verify_certificate_bytes, raw_cert_bytes[:-1] + b"\r\n")

        # 11. Pretty-printed / non-canonical JSON copy
        pretty = json.dumps(cert, indent=2).encode("utf-8") + b"\n"
        self._assert_err("NON_CANONICAL_JSON", a.verify_certificate_bytes, pretty)
        spaced = json.dumps(cert, sort_keys=True).encode("utf-8") + b"\n"
        self._assert_err("NON_CANONICAL_JSON", a.verify_certificate_bytes, spaced)

        # 12. Invalid UTF-8, bad JSON, oversized int (1000-digit boundary + 5000-digit DoS), non-dict root, bad SHA, bad mode, non-bytes
        self._assert_err("INVALID_BYTES", a.verify_certificate_bytes, "not_bytes")
        self._assert_err("INVALID_UTF8", a.verify_certificate_bytes, b"\xff\xfe")
        self._assert_err("INVALID_JSON", a.verify_certificate_bytes, b"{bad json")
        self._assert_err("INVALID_CERTIFICATE", a.verify_certificate_bytes, b"[1,2,3]\n")
        max_json_int = (1 << o.MAX_INT_BITS) - 1
        self.assertEqual(len(str(max_json_int)), o.MAX_INT_DIGITS)
        self.assertEqual(a._parse_strict_json_text('{"x":' + str(max_json_int) + "}")["x"], max_json_int)
        self._assert_err("INT_TOO_LARGE", a.verify_certificate_bytes, b'{"x":' + (b"9" * 5000) + b"}\n")
        self._assert_err("INT_TOO_LARGE", a.verify_certificate_bytes, b'{"x":' + str(1 << 3322).encode("ascii") + b"}\n")
        f_bad_sha = copy.deepcopy(cert)
        f_bad_sha["certificate_sha256"] = "f" * 64
        self._assert_err("HASH_MISMATCH", a.verify_certificate_bytes, o.canonical_json_bytes(f_bad_sha) + b"\n")
        f_bad_mode = copy.deepcopy(cert)
        f_bad_mode["mode"] = "unknown_mode"
        self._assert_err("INVALID_MODE", a.verify_certificate_bytes, _rehash(f_bad_mode))

        # 13. live_portal_audit cert refused without --research-dir; standalone cert refused with --research-dir
        f_live = copy.deepcopy(cert)
        f_live["mode"] = "live_portal_audit"
        f_live["live_portal_inspected"] = True
        self._assert_err("LIVE_DIR_REQUIRED", a.verify_certificate_bytes, _rehash(f_live))
        self._assert_err("MODE_MISMATCH", a.verify_certificate_bytes, raw_cert_bytes, research_dir=_SCRIPT_DIR)

        # --- Lean 4 lexical scanner upgrades (raw strings r"..." / r#"..."# + decide +native / ofReduceBool / extern / skipKernelTC) ---
        self.assertEqual(a._strip_lean_comments("-- sorry\ndef x := 1"), "\ndef x := 1")
        self.assertEqual(a._strip_lean_comments("def x := 1 -- sorry"), "def x := 1 ")
        self.assertEqual(a._strip_lean_comments("/- -- sorry /- axiom -/ -/def y := 2"), "def y := 2")
        self.assertEqual(a._strip_lean_comments("a -/ b"), "a -/ b")
        self.assertIn("sorry", a._strip_lean_comments("theorem t : True := by sorry"))
        str_attack = 'def msg : String := "/-"\naxiom evil : False\ntheorem bad : False := by sorry\n'
        stripped_attack = a._strip_lean_comments(str_attack)
        self.assertIn("axiom", stripped_attack)
        self.assertIn("sorry", stripped_attack)
        self.assertIn("sorry", a._strip_lean_comments('def s := "\\\\" ; sorry'))
        self.assertIn("axiom", a._strip_lean_comments('def s := "\\\"/-" ; axiom x : False'))
        self.assertIn("sorry", a._strip_lean_comments("def q' : Char := '\"' ; sorry"))
        self.assertIn("sorry", a._strip_lean_comments("def a_' : Char := '\\\"' ; sorry"))
        self.assertEqual(a._strip_lean_comments("'a' + 1"), "'' + 1")
        self.assertEqual(a._strip_lean_comments("f'a' + x_'b' + 1"), "f'a' + x_'b' + 1")
        self.assertEqual(a._strip_lean_comments("def u := 'ab'"), "def u := 'ab'")
        self.assertEqual(a._strip_lean_comments("def v := '\\ab"), "def v := '\\ab")
        self.assertEqual(a._strip_lean_comments("def w := '\\'"), "def w := '\\'")
        self.assertEqual(a._strip_lean_comments("def z := '''"), "def z := '''")
        self.assertEqual(a._strip_lean_comments("def n := '\n'"), "def n := '\n'")
        self.assertEqual(a._strip_lean_comments('def unclosed := "abc'), 'def unclosed := ""')
        self.assertEqual(a._strip_lean_comments('def unclosed_raw := r#"abc'), 'def unclosed_raw := ""')
        self.assertEqual(a._strip_lean_comments("def bar := r + 1"), "def bar := r + 1")
        self.assertTrue(a._is_lean_ident_char("a"))
        self.assertTrue(a._is_lean_ident_char("_"))
        self.assertFalse(a._is_lean_ident_char(" "))

        # Exact raw-string backslash bypass reproducer (0-hash r"\" and 1-hash r#"\"#)
        raw0_bypass = 'def a := r"\\"\ntheorem t : False := by sorry\ndef b := "x"\n'
        self.assertEqual(a.scan_lean4_lexical(raw0_bypass), ["sorry"])
        raw1_bypass = 'def a := r#"\\"#\ntheorem t : False := by sorry\ndef b := "x"\n'
        self.assertEqual(a.scan_lean4_lexical(raw1_bypass), ["sorry"])
        # Zero false positives inside raw strings and on benign decide / +kernel / +revert / native := false
        self.assertEqual(
            a.scan_lean4_lexical(
                'def s := r#"sorry "admit" decide +native Lean.ofReduceBool extern set_option debug.skipKernelTC"#\n'
                "theorem ok : True := by decide\n"
                "theorem ok2 : True := by decide +kernel\n"
                "theorem ok3 : True := by decide +revert\n"
                "theorem ok4 : True := by decide (config := { native := false })\n"
            ),
            [],
        )
        # Missing banned constructs all caught (including -revert +native and config record)
        self.assertEqual(a.scan_lean4_lexical("theorem t : True := by decide +native\n"), ["decide +native"])
        self.assertEqual(a.scan_lean4_lexical("theorem t : True := by decide +revert +native\n"), ["decide +native"])
        self.assertEqual(a.scan_lean4_lexical("theorem t : True := by decide -revert +native\n"), ["decide +native"])
        self.assertEqual(a.scan_lean4_lexical("theorem t : True := by decide\n  +native\n"), ["decide +native"])
        self.assertEqual(
            a.scan_lean4_lexical("theorem t : True := by decide (config := { native := true })\n"),
            ["decide +native"],
        )
        self.assertEqual(a.scan_lean4_lexical("def x := Lean.ofReduceBool true\n"), ["ofReduceBool"])
        self.assertEqual(a.scan_lean4_lexical("def y := Lean.ofReduceNat 0\n"), ["ofReduceNat"])
        self.assertEqual(a.scan_lean4_lexical('@[extern "c_bad"] opaque badFn : Nat\n'), ["extern"])
        self.assertEqual(a.scan_lean4_lexical("set_option debug.skipKernelTC true\n"), ["set_option debug.skipKernelTC"])

        # --- Live loader pin enforcement, no-.git refusal & CLI tests ---
        self._assert_err("PATH_REQUIRED", a.run_audit, True, None)
        with tempfile.TemporaryDirectory() as td:
            self._assert_err("DIR_MISSING", a.load_live_portal_summary, os.path.join(td, "no_such_dir"))
            syn_root = os.path.join(td, "mini_research")
            syn_digests = self._build_synthetic_research_dir(syn_root)

            # Default pinned digests MUST refuse synthetic invented files!
            self._assert_err("PIN_HASH_MISMATCH", a.run_audit, True, syn_root)

            # Isolated single-pin mismatch tests (each pin tested independently with the other two matched)
            only_lean_bad = copy.deepcopy(syn_digests)
            only_lean_bad["lean_file_sha256"]["BentSum.lean"] = "a" * 64
            with mock.patch.object(a, "PINNED_PORTAL_DIGESTS", only_lean_bad):
                self._assert_err("PIN_HASH_MISMATCH", a.load_live_portal_summary, syn_root)

            only_snf_bad = copy.deepcopy(syn_digests)
            only_snf_bad["blender_snf_witness_sha256"] = "b" * 64
            with mock.patch.object(a, "PINNED_PORTAL_DIGESTS", only_snf_bad):
                self._assert_err("PIN_HASH_MISMATCH", a.load_live_portal_summary, syn_root)

            only_tii_bad = copy.deepcopy(syn_digests)
            only_tii_bad["tii_94_summary_sha256"] = "c" * 64
            with mock.patch.object(a, "PINNED_PORTAL_DIGESTS", only_tii_bad):
                self._assert_err("PIN_HASH_MISMATCH", a.load_live_portal_summary, syn_root)

            # With all synthetic pins matched, live loader & --verify FILE on live cert succeed
            with mock.patch.object(a, "PINNED_PORTAL_DIGESTS", syn_digests):
                summary = a.load_live_portal_summary(syn_root)
                self.assertEqual(summary["diag_source"], "live_portal_read")
                self.assertEqual(summary["upstream_commit"], o.UPSTREAM_COMMIT)
                self.assertEqual(summary["bentsum_lean"]["banned_construct_findings"], 0)
                self.assertEqual(summary["blender_snf_witness"]["unshifted_snf_exps"], [0, 0, 1, 1, 2, 2, 3, 3])
                self.assertEqual(summary["blender_snf_witness"]["shifted_multi_snf_exps"], [0, 0, 1, 1, 1, 1, 1, 1])

                c_lv = a.run_audit(live=False, research_dir=syn_root)
                self.assertTrue(c_lv["all_gates_passed"])
                self.assertIs(c_lv["live_portal_inspected"], True)
                lv_receipt = a.verify_certificate_bytes(o.canonical_json_bytes(c_lv) + b"\n", research_dir=syn_root)
                self.assertTrue(lv_receipt["verified"])

                # Live .git/HEAD resolution tests (detached, mismatch, invalid ref, packed-refs, no-.git refusal)
                git_dir = os.path.join(syn_root, ".git")
                head_f = os.path.join(git_dir, "HEAD")
                ref_main = os.path.join(git_dir, "refs", "heads", "main")
                packed_f = os.path.join(git_dir, "packed-refs")
                with open(head_f, "w", encoding="utf-8") as fh:
                    fh.write(o.UPSTREAM_COMMIT + "\n")
                self.assertEqual(a._resolve_live_git_commit(syn_root), o.UPSTREAM_COMMIT)
                self.assertEqual(a._resolve_live_git_commit(syn_root, explicit_commit=o.UPSTREAM_COMMIT), o.UPSTREAM_COMMIT)
                self._assert_err("COMMIT_MISMATCH", a._resolve_live_git_commit, syn_root, explicit_commit="b" * 40)
                with open(head_f, "w", encoding="utf-8") as fh:
                    fh.write("a" * 40 + "\n")
                self._assert_err("COMMIT_MISMATCH", a._resolve_live_git_commit, syn_root)
                with open(head_f, "w", encoding="utf-8") as fh:
                    fh.write("0" * 40 + "\n")
                self._assert_err("INVALID_COMMIT", a._resolve_live_git_commit, syn_root)
                outside_abs = os.path.join(td, "outside_abs_ref")
                outside_rel = os.path.join(syn_root, "outside_rel_ref")
                for p_out in (outside_abs, outside_rel):
                    with open(p_out, "w", encoding="utf-8") as fh:
                        fh.write(o.UPSTREAM_COMMIT + "\n")
                for bad_ref in ("ref: \n", f"ref: {outside_abs}\n", "ref: ../outside_rel_ref\n"):
                    with open(head_f, "w", encoding="utf-8") as fh:
                        fh.write(bad_ref)
                    self._assert_err("UNSAFE_GIT_REF", a._resolve_live_git_commit, syn_root)
                with open(head_f, "w", encoding="utf-8") as fh:
                    fh.write("ref: refs/heads/main\n")
                os.remove(ref_main)
                self._assert_err("INVALID_COMMIT", a._resolve_live_git_commit, syn_root)
                with open(packed_f, "w", encoding="utf-8") as fh:
                    fh.write(
                        "# refs/heads/main\n\n"
                        f"{'b' * 40} refs/heads/other\n"
                        f"^{'c' * 40} refs/heads/main\n"
                        f"{o.UPSTREAM_COMMIT} refs/heads/main\n"
                    )
                self.assertEqual(a._resolve_live_git_commit(syn_root), o.UPSTREAM_COMMIT)
                with open(packed_f, "w", encoding="utf-8") as fh:
                    fh.write("# only comment\nonly_one_token\n")
                self._assert_err("INVALID_COMMIT", a._resolve_live_git_commit, syn_root)
                os.remove(packed_f)
                os.remove(head_f)
                # Tree with NO .git/HEAD MUST be refused unless explicit upstream_commit is passed!
                self._assert_err("GIT_DIR_MISSING", a._resolve_live_git_commit, syn_root)
                self._assert_err("COMMIT_MISMATCH", a._resolve_live_git_commit, syn_root, explicit_commit="a" * 40)
                self.assertEqual(a._resolve_live_git_commit(syn_root, explicit_commit=o.UPSTREAM_COMMIT), o.UPSTREAM_COMMIT)
                with open(head_f, "w", encoding="utf-8") as fh:
                    fh.write("ref: refs/heads/main\n")
                with open(ref_main, "w", encoding="utf-8") as fh:
                    fh.write(o.UPSTREAM_COMMIT + "\n")

                # Missing Lean file & symlink refusal
                lean_f = os.path.join(syn_root, "Cryptography", "BentSum", "lean", "BentSum.lean")
                with open(lean_f, "rb") as fh:
                    orig_lean = fh.read()
                os.remove(lean_f)
                self._assert_err("FILE_MISSING", a.load_live_portal_summary, syn_root)
                os.symlink(os.path.join(syn_root, ".git", "HEAD"), lean_f)
                self._assert_err("FILE_MISSING", a.load_live_portal_summary, syn_root)
                os.remove(lean_f)
                with open(lean_f, "wb") as fh:
                    fh.write(orig_lean)

                # Malformed snf_audit_vectors.json cases (with updated SHA pin so parser guards run)
                snf_f = os.path.join(syn_root, "Cryptography", "Blender", "artifacts", "snf_steering", "witnesses", "snf_audit_vectors.json")
                with open(snf_f, "rb") as fh:
                    orig_snf = fh.read()
                for payload, code in (
                    ([1, 2], "INVALID_JSON"),
                    ({"unshifted_eqlen_eqcsum": 123, "shifted_multi_eqlen_eqcsum": [[1] * 8, [2] * 8]}, "INVALID_BLENDER_WITNESS"),
                    ({"unshifted_eqlen_eqcsum": [], "shifted_multi_eqlen_eqcsum": [[1] * 8, [2] * 8]}, "INVALID_BLENDER_WITNESS"),
                    ({"unshifted_eqlen_eqcsum": [[1] * 8], "shifted_multi_eqlen_eqcsum": 123}, "INVALID_BLENDER_WITNESS"),
                    ({"unshifted_eqlen_eqcsum": [[1] * 8], "shifted_multi_eqlen_eqcsum": [[1] * 8]}, "INVALID_BLENDER_WITNESS"),
                    ({"unshifted_eqlen_eqcsum": [[1] * 4], "shifted_multi_eqlen_eqcsum": [[1] * 8, [2] * 8]}, "INVALID_BLENDER_WITNESS"),
                    ({"unshifted_eqlen_eqcsum": [[1] * 8], "shifted_multi_eqlen_eqcsum": [[1] * 4, [2] * 4]}, "INVALID_BLENDER_WITNESS"),
                ):
                    raw_p = json.dumps(payload).encode("utf-8")
                    with open(snf_f, "wb") as fh:
                        fh.write(raw_p)
                    syn_digests["blender_snf_witness_sha256"] = hashlib.sha256(raw_p).hexdigest()
                    self._assert_err(code, a.load_live_portal_summary, syn_root)
                with open(snf_f, "wb") as fh:
                    fh.write(orig_snf)
                syn_digests["blender_snf_witness_sha256"] = hashlib.sha256(orig_snf).hexdigest()

                # Blender main.tex issue1/issue2 conjunct checks
                btex_f = os.path.join(syn_root, "Cryptography", "Blender", "paper", "main.tex")
                with open(btex_f, "rb") as fh:
                    orig_btex = fh.read()
                with open(btex_f, "w", encoding="utf-8") as fh:
                    fh.write("only two-step silent-carry healing family\n")
                s_no_gm = a.load_live_portal_summary(syn_root)
                self.assertFalse(s_no_gm["blender_issues_text_checks"]["issue1_global_minimum_claim_present"])
                self.assertFalse(s_no_gm["blender_issues_text_checks"]["issue2_sec33_w0246_in_x_notx_present"])
                with open(btex_f, "w", encoding="utf-8") as fh:
                    fh.write("only global minimum without family phrase\n")
                s_no_fam = a.load_live_portal_summary(syn_root)
                self.assertFalse(s_no_fam["blender_issues_text_checks"]["issue1_global_minimum_claim_present"])
                with open(btex_f, "wb") as fh:
                    fh.write(orig_btex)

                # Malformed verified_tii_94_summary.json & per-challenge validation cases
                tii_f = os.path.join(syn_root, "Cryptography", "TII-McEliece", "artifacts", "goppa_key_recovery", "witnesses", "verified_tii_94_summary.json")
                with open(tii_f, "rb") as fh:
                    orig_tii = fh.read()
                c0 = self._make_challenge(0, route="Route-A (s)", first_blood=True)
                c1 = self._make_challenge(1, route="Route-B (s)", first_blood=False)
                for payload, code in (
                    ([1, 2], "INVALID_JSON"),
                    ({"challenges": 123, "total_solved": 1, "route_a_solved": 1, "route_b_solved": 0, "first_bloods": 0}, "INVALID_TII_SUMMARY"),
                    ({"challenges": [], "total_solved": 1, "route_a_solved": 1, "route_b_solved": 0, "first_bloods": 0}, "INVALID_TII_SUMMARY"),
                    ({"challenges": [c0], "total_solved": 2, "route_a_solved": 1, "route_b_solved": 0, "first_bloods": 1}, "TII_SUM_MISMATCH"),
                    ({"challenges": [c0, c1], "total_solved": 3, "route_a_solved": 1, "route_b_solved": 1, "first_bloods": 1}, "TII_SUM_MISMATCH"),
                    ({"challenges": [c0, c1], "total_solved": 2, "route_a_solved": 1, "route_b_solved": 0, "first_bloods": 1}, "TII_SUM_MISMATCH"),
                    ({"challenges": [None], "total_solved": 1, "route_a_solved": 1, "route_b_solved": 0, "first_bloods": 0}, "INVALID_TII_CHALLENGE"),
                    ({"challenges": [c0, dict(c1, sec=1)], "total_solved": 2, "route_a_solved": 1, "route_b_solved": 1, "first_bloods": 1}, "INVALID_TII_CHALLENGE"),
                    ({"challenges": [dict(c0, mt=47, k=207)], "total_solved": 1, "route_a_solved": 1, "route_b_solved": 0, "first_bloods": 1}, "INVALID_TII_CHALLENGE"),
                    ({"challenges": [dict(c0, k=205)], "total_solved": 1, "route_a_solved": 1, "route_b_solved": 0, "first_bloods": 1}, "INVALID_TII_CHALLENGE"),
                    ({"challenges": [dict(c0, official_checker_output=0)], "total_solved": 1, "route_a_solved": 1, "route_b_solved": 0, "first_bloods": 1}, "INVALID_TII_CHALLENGE"),
                    ({"challenges": [dict(c0, rref_bit_identical=False)], "total_solved": 1, "route_a_solved": 1, "route_b_solved": 0, "first_bloods": 1}, "INVALID_TII_CHALLENGE"),
                    ({"challenges": [dict(c0, g_is_irreducible=False)], "total_solved": 1, "route_a_solved": 1, "route_b_solved": 0, "first_bloods": 1}, "INVALID_TII_CHALLENGE"),
                    ({"challenges": [dict(c0, route="Route-C (bad)")], "total_solved": 1, "route_a_solved": 1, "route_b_solved": 0, "first_bloods": 1}, "INVALID_TII_CHALLENGE"),
                    ({"challenges": [c0, c1], "total_solved": 2, "route_a_solved": 2, "route_b_solved": 0, "first_bloods": 1}, "TII_SUM_MISMATCH"),
                    ({"challenges": [c0, c1], "total_solved": 2, "route_a_solved": 0, "route_b_solved": 2, "first_bloods": 1}, "TII_SUM_MISMATCH"),
                    ({"challenges": [c0, c1], "total_solved": 2, "route_a_solved": 1, "route_b_solved": 1, "first_bloods": 0}, "TII_SUM_MISMATCH"),
                ):
                    raw_t = json.dumps(payload).encode("utf-8")
                    with open(tii_f, "wb") as fh:
                        fh.write(raw_t)
                    syn_digests["tii_94_summary_sha256"] = hashlib.sha256(raw_t).hexdigest()
                    self._assert_err(code, a.load_live_portal_summary, syn_root)
                self._assert_err("TII_SUM_MISMATCH", a._validate_tii_challenges_live, [c0, c1], 2, 1, 1)
                self._assert_err("TII_SUM_MISMATCH", a._validate_tii_challenges_live, [c0, c1], 1, 2, 1)
                with open(tii_f, "wb") as fh:
                    fh.write(orig_tii)
                syn_digests["tii_94_summary_sha256"] = hashlib.sha256(orig_tii).hexdigest()

                # CLI tests (--standalone --output, --verify pass/fail, --live / --research-dir dispatch)
                out_p = os.path.join(td, "cert.json")
                buf = io.StringIO()
                with mock.patch.object(a, "run_audit", return_value=cert), mock.patch.object(sys, "stdout", buf):
                    rc = a.main(["--standalone", "--json", "--output", out_p])
                self.assertEqual(rc, 0)
                with open(out_p, "r", encoding="utf-8", newline="") as fh:
                    self.assertEqual(fh.read(), buf.getvalue())

                v_buf = io.StringIO()
                with mock.patch.object(sys, "stdout", v_buf):
                    self.assertEqual(a.main(["--verify", out_p]), 0)
                self.assertTrue(json.loads(v_buf.getvalue())["verified"])

                forged_p = os.path.join(td, "forged.json")
                with open(forged_p, "wb") as fh:
                    fh.write(_rehash(f_q3))
                err_buf = io.StringIO()
                with mock.patch.object(sys, "stderr", err_buf):
                    self.assertEqual(a.main(["--verify", forged_p]), 1)
                self.assertIn("CERTIFICATE_MISMATCH", err_buf.getvalue())

                with mock.patch.object(a, "run_audit", return_value={"all_gates_passed": False}), mock.patch.object(sys, "stdout", io.StringIO()):
                    self.assertEqual(a.main(["--standalone"]), 1)
                with mock.patch.object(a, "run_audit", return_value={"all_gates_passed": True}) as m_ra, mock.patch.object(sys, "stdout", io.StringIO()):
                    self.assertEqual(a.main(["--live"]), 0)
                    m_ra.assert_called_once_with(live=True, research_dir=None, upstream_commit=None)
                with mock.patch.object(a, "run_audit", return_value={"all_gates_passed": True}) as m_ra, mock.patch.object(sys, "stdout", io.StringIO()):
                    self.assertEqual(a.main(["--research-dir", syn_root, "--upstream-commit", o.UPSTREAM_COMMIT]), 0)
                    m_ra.assert_called_once_with(live=True, research_dir=syn_root, upstream_commit=o.UPSTREAM_COMMIT)


def run_all():
    suite = unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=0, failfast=True).run(suite)
    if not result.wasSuccessful():
        sys.exit(1)
    print("ALL_MINIMAX_CRYPTANALYSIS_TESTS_PASSED")


if __name__ == "__main__":
    run_all()
