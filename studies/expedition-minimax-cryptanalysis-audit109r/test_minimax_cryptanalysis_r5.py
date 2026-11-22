"""Assertion-free R5 adversarial & mutation-killing test suite for Track S14 (AUDIT-109):
MiniMax-AI/Research Cryptography Portal Clean-Room Audit.

Pure Python 3 stdlib. Zero floats in certified paths. Zero bare assert statements.
"""

import copy
from fractions import Fraction
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
        """Construct a minimal valid synthetic MiniMax-AI/Research tree for offline live-loader tests."""
        git_refs = os.path.join(root, ".git", "refs", "heads")
        os.makedirs(git_refs, exist_ok=True)
        with open(os.path.join(root, ".git", "HEAD"), "w", encoding="utf-8") as fh:
            fh.write("ref: refs/heads/main\n")
        with open(os.path.join(git_refs, "main"), "w", encoding="utf-8") as fh:
            fh.write(o.UPSTREAM_COMMIT + "\n")

        cdir = os.path.join(root, "Cryptography")
        lean_dir = os.path.join(cdir, "BentSum", "lean")
        os.makedirs(os.path.join(lean_dir, "BentSum"), exist_ok=True)
        for rel in o.REQUIRED_LEAN_FILES:
            p = os.path.join(lean_dir, rel)
            with open(p, "w", encoding="utf-8") as fh:
                fh.write("-- clean comment mentioning sorry\n/- nested /- axiom -/ -/\ndef ok := 1\n")

        snf_dir = os.path.join(cdir, "Blender", "artifacts", "snf_steering", "witnesses")
        os.makedirs(snf_dir, exist_ok=True)
        # Synthetic 8-column vectors with exact 2-adic SNF [0,0,1,1,2,2,3,3] and [0,0,1,1,1,1,1,1]
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
        sh = [
            [1, 0, 0, 0, 0, 0, 0, 0],
            [0, 1, 0, 0, 0, 0, 0, 0],
            [0, 0, 2, 0, 0, 0, 0, 0],
            [0, 0, 0, 2, 0, 0, 0, 0],
            [0, 0, 0, 0, 2, 0, 0, 0],
            [0, 0, 0, 0, 0, 2, 0, 0],
            [0, 0, 0, 0, 0, 0, 2, 0],
            [0, 0, 0, 0, 0, 0, 0, 2],
        ]
        # Add carries in every adjacent pair so 2nd-order XOR derivative != 0 while mod 2^32 == 0
        sh_carry = [[(row[j] + ((idx + 1) * 0x10101010 if j == 0 else 0)) & 0xFFFFFFFF for j in range(8)] for idx, row in enumerate(sh)]
        # Preserve exact SNF [0,0,1,1,1,1,1,1] by keeping pure unit generators at front
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
        _ = sh_carry
        with open(os.path.join(snf_dir, "snf_audit_vectors.json"), "w", encoding="utf-8") as fh:
            json.dump({"unshifted_eqlen_eqcsum": unsh, "shifted_multi_eqlen_eqcsum": sh_vecs}, fh)

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
        with open(os.path.join(tii_dir, "verified_tii_94_summary.json"), "w", encoding="utf-8") as fh:
            json.dump(
                {
                    "total_solved": 94,
                    "route_a_solved": 89,
                    "route_b_solved": 5,
                    "first_bloods": 55,
                    "challenges": challenges,
                },
                fh,
            )

    def test_01_core_primitives_hygiene_and_linear_algebra(self):
        # Float/complex, non-str key, and unsupported container rejection
        for bad in (1.5, complex(1, 2), {"a": 0.1}, {0.5: "a"}, [1, 2.0], (3.0,)):
            self._assert_err("FLOAT_FORBIDDEN", o.verify_no_floats, bad)
        for bad_k in ({8: 16}, {True: "a"}):
            self._assert_err("INVALID_KEY_TYPE", o.verify_no_floats, bad_k)
            self._assert_err("INVALID_KEY_TYPE", o.canonical_json_bytes, bad_k)
        for bad_t in ({1, 2}, b"abc", object(), {"s": {1}}, [b"x"]):
            self._assert_err("INVALID_JSON_TYPE", o.verify_no_floats, bad_t)
            self._assert_err("INVALID_JSON_TYPE", o.canonical_json_bytes, bad_t)
        self._assert_err("INVALID_JSON_TYPE", o.canonical_json_bytes, {"q": Fraction(1, 2)})
        o.verify_no_floats({"k": [1, True, None, "s", Fraction(3, 7)]})

        # require_exact_int boundaries
        self._assert_err("INVALID_INT", o.require_exact_int, True, "x")
        self._assert_err("INVALID_INT", o.require_exact_int, "1", "x")
        self._assert_err("INVALID_INT", o.require_exact_int, 1.0, "x")
        self.assertEqual(o.require_exact_int(-5, "x"), -5)
        self.assertEqual(o.require_exact_int(0, "x", min_value=0, max_value=3), 0)
        self.assertEqual(o.require_exact_int(3, "x", min_value=0, max_value=3), 3)
        self._assert_err("RANGE_ERROR", o.require_exact_int, -1, "x", min_value=0)
        self._assert_err("RANGE_ERROR", o.require_exact_int, 4, "x", max_value=3)

        # require_exact_bool & require_non_empty_str & require_hex_sha256 & require_hex_sha1
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

        # frac_str & format_exact_decimal (including half-to-even ties and -0 guard)
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

        # Law 5 label hygiene
        self._assert_err("INVALID_LABELS", o.enforce_law5_label_hygiene, "not_seq")
        self._assert_err("INVALID_LABELS", o.enforce_law5_label_hygiene, [])
        self._assert_err("LAW5_METAPHOR_REJECTED", o.enforce_law5_label_hygiene, ["valid_op", "quantum_leap_lift"])
        self.assertTrue(o.enforce_law5_label_hygiene(a.OPERATOR_LABELS)["passed"])

        # Bareiss determinant edge cases (singular, row swap, zero col)
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

    def test_02_portal_summary_validation_and_pillars_1_2_3(self):
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
            (lambda d: d.__setitem__("bentsum_lean", []), "INVALID_LEAN_MANIFEST"),
            (lambda d: d["bentsum_lean"].__setitem__("extra", 1), "INVALID_LEAN_MANIFEST"),
            (lambda d: d["bentsum_lean"].__setitem__("files_checked", 0), "RANGE_ERROR"),
            (lambda d: d["bentsum_lean"].__setitem__("banned_construct_findings", -1), "RANGE_ERROR"),
            (lambda d: d["bentsum_lean"].__setitem__("lean_file_sha256", [1, 2, 3, 4, 5]), "INVALID_LEAN_MANIFEST"),
            (lambda d: (d["bentsum_lean"]["lean_file_sha256"].pop("BentSum.lean"), d["bentsum_lean"]["lean_file_sha256"].__setitem__("Evil.lean", "0" * 64)), "INVALID_LEAN_MANIFEST"),
            (lambda d: (d["bentsum_lean"]["lean_file_sha256"].__setitem__("Extra.lean", "0" * 64), d["bentsum_lean"].__setitem__("files_checked", 6)), "INVALID_LEAN_MANIFEST"),
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

        # Positive full verification of Pillars 1, 2, 3
        p1 = o.audit_bentsum_lean_and_walsh_exact(fx)
        self.assertTrue(p1["passed"])
        self.assertEqual(p1["q3_weight"], 28)
        self.assertEqual(p1["cylq3_n8_weight"], 28)
        self.assertEqual(p1["cylq3_n8_weight_mod_8"], 4)
        self.assertEqual(p1["positive_bentsum_parseval_N"], 8)
        self.assertEqual(p1["liftcylq3_n10_weight"], 512)
        self.assertEqual(p1["liftcylq3_n10_periods"], [0, 1])

        p2 = o.audit_fast_algebraic_and_errata_exact(fx)
        self.assertTrue(p2["passed"])
        self.assertEqual(p2["aradi"]["analytical_zero_sum_eq_count"], 198)
        self.assertEqual(p2["aradi"]["latincrypt2025_blind_column_hist"], {"8": 16, "13": 16})
        self.assertEqual(p2["colm"]["transplant_set"], [1, 3, 4, 5, 6, 7, 129, 130])
        self.assertTrue(p2["sbcvole"]["secret_256bit_recovered_exact"])
        self.assertTrue(p2["blender"]["issue1_scope_overclaim_confirmed"])
        self.assertTrue(p2["blender"]["issue2_prose_conflict_confirmed"])
        self.assertEqual(p2["blender"]["snf_from_iv_unshifted"], [0, 0, 1, 1, 2, 2, 3, 3])
        self.assertEqual(p2["blender"]["snf_from_iv_multi_shifted"], [0, 0, 1, 1, 1, 1, 1, 1])

        p3 = o.audit_law5_math0_siliquant_operators_exact(fx)
        self.assertTrue(p3["passed"])
        self.assertEqual(p3["tii_mceliece_operator"]["tii250_compression_exact"], "197803/30016")
        self.assertEqual(p3["tii_mceliece_operator"]["tii125_compression_exact"], "98347/15052")
        self.assertEqual(p3["hawk_lattice_operator"]["parity_sublattice_abs_det_H"], 128)
        self.assertEqual(p3["hawk_lattice_operator"]["gram_diag_compression_exact"], "31954/41")

        # Polarity flips on caller-supplied summary fields
        bad_p1 = copy.deepcopy(fx)
        bad_p1["bentsum_lean"]["banned_construct_findings"] = 1
        self.assertFalse(o.audit_bentsum_lean_and_walsh_exact(bad_p1)["passed"])

        for bmut in (
            lambda d: d["blender_snf_witness"]["unshifted_snf_exps"].__setitem__(0, 1),
            lambda d: d["blender_snf_witness"]["shifted_multi_snf_exps"].__setitem__(0, 1),
            lambda d: d["blender_snf_witness"].__setitem__("f2_xor_fail_count", 99),
            lambda d: d["blender_snf_witness"].__setitem__("mod32_superposition_pass_count", 99),
            lambda d: d["blender_issues_text_checks"].__setitem__("issue1_global_minimum_claim_present", False),
            lambda d: d["blender_issues_text_checks"].__setitem__("issue2_sec33_w0246_in_x_notx_present", False),
        ):
            bd = copy.deepcopy(fx)
            bmut(bd)
            self.assertFalse(o._audit_blender_exact(o.validate_portal_summary(bd))["passed"])

        for tmut in (
            lambda d: (d["tii_94_summary"].__setitem__("total_solved", 93), d["tii_94_summary"].__setitem__("route_a_solved", 88)),
            lambda d: (d["tii_94_summary"].__setitem__("route_a_solved", 88), d["tii_94_summary"].__setitem__("route_b_solved", 6)),
            lambda d: d["tii_94_summary"].__setitem__("first_bloods", 54),
        ):
            td = copy.deepcopy(fx)
            tmut(td)
            self.assertFalse(o.audit_law5_math0_siliquant_operators_exact(td)["passed"])

    def test_03_pillar4_fail_closed_certification_and_live_loader(self):
        fx = copy.deepcopy(a.STANDALONE_PORTAL_FIXTURE)
        cert = a.run_audit(live=False, research_dir=None)
        self.assertTrue(cert["all_gates_passed"])
        self.assertEqual(cert["verdict"], "AUDITED_MINIMAX_CRYPTANALYSIS_PORTAL")
        self.assertIs(cert["live_portal_inspected"], False)
        # MM109-BUG-01 JSON round-trip canonical SHA-256 invariance check
        reloaded = json.loads(o.canonical_json_bytes(cert).decode("utf-8"))
        saved_sha = reloaded.pop("certificate_sha256")
        self.assertEqual(o.canonical_sha256(reloaded), saved_sha)

        p1 = cert["pillar1_bentsum_lean_and_walsh"]
        p2 = cert["pillar2_fast_algebraic_and_errata"]
        p3 = cert["pillar3_law5_tii_mceliece_and_hawk"]
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
        p1_lv = dict(p1, diag_source="live_portal_read")
        self._assert_err("PROVENANCE_MISMATCH", o.certify_minimax_cryptanalysis_audit_exact, "standalone_pinned_replay", False, a.OPERATOR_LABELS, fx_lv, p1_lv, p2, p3, axes)
        self._assert_err("AXIS_CONTRADICTION", o.certify_minimax_cryptanalysis_audit_exact, "standalone_pinned_replay", False, a.OPERATOR_LABELS, fx, p1, p2, p3, dict(axes, fast_algebraic_operators_and_peer_errata=False))

        # Rejected gate verdict when a portal check fails
        fx_fail = copy.deepcopy(fx)
        fx_fail["bentsum_lean"]["banned_construct_findings"] = 1
        p1_fail = o.audit_bentsum_lean_and_walsh_exact(fx_fail)
        cert_fail = o.certify_minimax_cryptanalysis_audit_exact(
            "standalone_pinned_replay",
            False,
            a.OPERATOR_LABELS,
            fx_fail,
            p1_fail,
            p2,
            p3,
            dict(axes, bentsum_lean_purity_and_walsh_hadamard=False),
        )
        self.assertFalse(cert_fail["all_gates_passed"])
        self.assertEqual(cert_fail["verdict"], "REJECTED_GATE_FAILED")

        # Lean comment stripper edge cases (comments, string literals with "/-", escapes, char literals, primes)
        self.assertEqual(a._strip_lean_comments("-- sorry\ndef x := 1"), "\ndef x := 1")
        self.assertEqual(a._strip_lean_comments("def x := 1 -- sorry"), "def x := 1 ")
        self.assertEqual(a._strip_lean_comments("/- -- sorry /- axiom -/ -/def y := 2"), "def y := 2")
        self.assertEqual(a._strip_lean_comments("a -/ b"), "a -/ b")
        self.assertIn("sorry", a._strip_lean_comments("theorem t : True := by sorry"))
        mm109_str_attack = 'def msg : String := "/-"\naxiom evil : False\ntheorem bad : False := by sorry\n'
        stripped_attack = a._strip_lean_comments(mm109_str_attack)
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
        self.assertTrue(a._is_lean_ident_char("a"))
        self.assertTrue(a._is_lean_ident_char("_"))
        self.assertFalse(a._is_lean_ident_char(" "))

        # Live loader & CLI tests on synthetic directory
        self._assert_err("PATH_REQUIRED", a.run_audit, True, None)
        with tempfile.TemporaryDirectory() as td:
            self._assert_err("DIR_MISSING", a.load_live_portal_summary, os.path.join(td, "no_such_dir"))
            syn_root = os.path.join(td, "mini_research")
            self._build_synthetic_research_dir(syn_root)

            summary = a.load_live_portal_summary(syn_root)
            self.assertEqual(summary["diag_source"], "live_portal_read")
            self.assertEqual(summary["upstream_commit"], o.UPSTREAM_COMMIT)
            self.assertEqual(summary["bentsum_lean"]["banned_construct_findings"], 0)
            self.assertEqual(summary["blender_snf_witness"]["unshifted_snf_exps"], [0, 0, 1, 1, 2, 2, 3, 3])
            self.assertEqual(summary["blender_snf_witness"]["shifted_multi_snf_exps"], [0, 0, 1, 1, 1, 1, 1, 1])
            self.assertTrue(summary["blender_issues_text_checks"]["issue1_global_minimum_claim_present"])
            self.assertTrue(summary["blender_issues_text_checks"]["issue2_sec33_w0246_in_x_notx_present"])

            # Live .git/HEAD resolution tests (detached, mismatch, invalid ref, packed-refs, no-.git archive)
            git_dir = os.path.join(syn_root, ".git")
            head_f = os.path.join(git_dir, "HEAD")
            ref_main = os.path.join(git_dir, "refs", "heads", "main")
            packed_f = os.path.join(git_dir, "packed-refs")
            with open(head_f, "w", encoding="utf-8") as fh:
                fh.write(o.UPSTREAM_COMMIT + "\n")
            self.assertEqual(a._resolve_live_git_commit(syn_root), o.UPSTREAM_COMMIT)
            with open(head_f, "w", encoding="utf-8") as fh:
                fh.write("a" * 40 + "\n")
            self._assert_err("COMMIT_MISMATCH", a._resolve_live_git_commit, syn_root)
            with open(head_f, "w", encoding="utf-8") as fh:
                fh.write("0" * 40 + "\n")
            self._assert_err("INVALID_COMMIT", a._resolve_live_git_commit, syn_root)
            # Create real outside commit files so unsafe ref guards are independently killed
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
            self.assertEqual(a._resolve_live_git_commit(syn_root), o.UPSTREAM_COMMIT)
            with open(head_f, "w", encoding="utf-8") as fh:
                fh.write("ref: refs/heads/main\n")
            with open(ref_main, "w", encoding="utf-8") as fh:
                fh.write(o.UPSTREAM_COMMIT + "\n")

            # Live run via research_dir with live=False still triggers live_portal_audit
            c_lv = a.run_audit(live=False, research_dir=syn_root)
            self.assertTrue(c_lv["all_gates_passed"])
            self.assertIs(c_lv["live_portal_inspected"], True)

            # Mutate synthetic tree for every refusal guard in load_live_portal_summary
            # 1. Missing Lean file
            lean_f = os.path.join(syn_root, "Cryptography", "BentSum", "lean", "BentSum.lean")
            with open(lean_f, "rb") as fh:
                orig_lean = fh.read()
            os.remove(lean_f)
            self._assert_err("FILE_MISSING", a.load_live_portal_summary, syn_root)
            # 2. Banned sorry / string-hidden axiom in Lean file
            with open(lean_f, "w", encoding="utf-8") as fh:
                fh.write(mm109_str_attack)
            self.assertEqual(a.load_live_portal_summary(syn_root)["bentsum_lean"]["banned_construct_findings"], 2)
            with open(lean_f, "wb") as fh:
                fh.write(orig_lean)

            # 3. Malformed snf_audit_vectors.json cases
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
                with open(snf_f, "w", encoding="utf-8") as fh:
                    json.dump(payload, fh)
                self._assert_err(code, a.load_live_portal_summary, syn_root)
            with open(snf_f, "wb") as fh:
                fh.write(orig_snf)

            # 4. Blender main.tex issue1/issue2 conjunct checks
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

            # 5. Malformed verified_tii_94_summary.json & per-challenge validation cases (MM109-BUG-03)
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
                with open(tii_f, "w", encoding="utf-8") as fh:
                    json.dump(payload, fh)
                self._assert_err(code, a.load_live_portal_summary, syn_root)
            # Direct helper checks for isolated ra_s and rb_s mismatches
            self._assert_err("TII_SUM_MISMATCH", a._validate_tii_challenges_live, [c0, c1], 2, 1, 1)
            self._assert_err("TII_SUM_MISMATCH", a._validate_tii_challenges_live, [c0, c1], 1, 2, 1)
            with open(tii_f, "wb") as fh:
                fh.write(orig_tii)

            # 6. CLI tests (--standalone --json --output, failure exit code 1, --live / --research-dir dispatch)
            out_p = os.path.join(td, "cert.json")
            buf = io.StringIO()
            with mock.patch.object(a, "run_audit", return_value=cert), mock.patch.object(sys, "stdout", buf):
                rc = a.main(["--standalone", "--json", "--output", out_p])
            self.assertEqual(rc, 0)
            with open(out_p, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), buf.getvalue())
            with mock.patch.object(a, "run_audit", return_value={"all_gates_passed": False}), mock.patch.object(sys, "stdout", io.StringIO()):
                self.assertEqual(a.main(["--standalone"]), 1)
            with mock.patch.object(a, "run_audit", return_value={"all_gates_passed": True}) as m_ra, mock.patch.object(sys, "stdout", io.StringIO()):
                self.assertEqual(a.main(["--live"]), 0)
                m_ra.assert_called_once_with(live=True, research_dir=None)
            with mock.patch.object(a, "run_audit", return_value={"all_gates_passed": True}) as m_ra, mock.patch.object(sys, "stdout", io.StringIO()):
                self.assertEqual(a.main(["--research-dir", syn_root]), 0)
                m_ra.assert_called_once_with(live=True, research_dir=syn_root)
            with mock.patch.object(a, "run_audit", return_value={"all_gates_passed": True}) as m_ra, mock.patch.object(sys, "stdout", io.StringIO()):
                self.assertEqual(a.main(["--live", "--research-dir", syn_root]), 0)
                m_ra.assert_called_once_with(live=True, research_dir=syn_root)


def run_all():
    suite = unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=0, failfast=True).run(suite)
    if not result.wasSuccessful():
        sys.exit(1)
    print("ALL_AUDIT109_MINIMAX_CRYPTANALYSIS_TESTS_PASSED")


if __name__ == "__main__":
    run_all()
