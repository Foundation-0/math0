#!/usr/bin/env python3
"""
Track S94 Assertion-Free R5 Hardened Unit Test Suite.

Covers:
  - All 3 Wave-6 x Expedition exact-Q mathematical pillars & Law-5 boundaries
  - Every parameterized oracle primitive & boundary guard (100% mutate & BoolOp)
  - Strict canonical rational parser, iterative JSON tree & pre-parse int caps
  - Hardened dir_fd I/O: PWD symlink, scratch os.mkfifo, hardlink R&W, atomic 0o600, TOCTOU
  - Genuine non-hollow SEC / FR0 / FR1 re-signed semantic tamper matrix
  - Read-only upstream cert & Wave-6 snapshot pin verifier (synthetic isolated roots)
  - Full R10+ static Lean 4 scanner (incl. all 6 decide native bool-expr PoCs) + live/0-skip CI
"""
from __future__ import annotations

from contextlib import redirect_stderr, redirect_stdout
import copy
from fractions import Fraction
import hashlib
import io
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

TRACK_DIR = Path(__file__).resolve().parent
if str(TRACK_DIR) not in sys.path:
    sys.path.insert(0, str(TRACK_DIR))

import s94_wave6_convergence_oracle as oracle
import verify_s94_wave6_convergence as verifier


def _resign(env: dict) -> dict:
    p_sha = hashlib.sha256(oracle.canonical_json_bytes(env["payload"])).hexdigest()
    body = {
        "schema_version": env["schema_version"],
        "track_id": env["track_id"],
        "payload_sha256": p_sha,
        "payload": env["payload"],
    }
    c_sha = hashlib.sha256(oracle.canonical_json_bytes(body)).hexdigest()
    return {
        "schema_version": env["schema_version"],
        "track_id": env["track_id"],
        "payload_sha256": p_sha,
        "certificate_sha256": c_sha,
        "payload": env["payload"],
    }


def _lean_available() -> bool:
    try:
        verifier.resolve_lean_binary()
        return True
    except ValueError:
        return False


class TestS94Wave6ConvergenceR5(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.valid_env = oracle.build_certificate_envelope()

    def test_01_oracle_primitives_and_boundaries(self) -> None:
        oracle.require_ok(True, "OK")
        for bad in (False, 1, "true", None):
            with self.assertRaisesRegex(ValueError, "BAD"):
                oracle.require_ok(bad, "BAD")

        self.assertEqual(oracle.q_str(Fraction(71, 8)), "71/8")
        self.assertEqual(oracle.q_str(Fraction(6, 2)), "3")
        with self.assertRaisesRegex(ValueError, "Q_STR_REQUIRES_FRACTION"):
            oracle.q_str(3)  # type: ignore[arg-type]

        self.assertEqual(oracle.dec_str(Fraction(71, 8), 4), "8.8750")
        self.assertEqual(oracle.dec_str(Fraction(1, 2), 1), "0.5")
        self.assertEqual(oracle.dec_str(Fraction(1, 2), 12), "0.500000000000")
        with self.assertRaisesRegex(ValueError, "DEC_STR_REQUIRES_FRACTION"):
            oracle.dec_str(1, 4)  # type: ignore[arg-type]
        for bad_pl in (0, 13, True):
            with self.assertRaisesRegex(ValueError, "DEC_STR_BAD_PLACES"):
                oracle.dec_str(Fraction(1, 2), bad_pl)  # type: ignore[arg-type]

        # Hadamard matrix & [H_k, D] != 0 smearing
        self.assertEqual(oracle.sylvester_hadamard_int(1), [[1]])
        self.assertEqual(oracle.sylvester_hadamard_int(2), [[1, 1], [1, -1]])
        for bad_ord in (0, -2, 3, True):
            with self.assertRaisesRegex(ValueError, "HADAMARD_ORDER_NOT_POW2"):
                oracle.sylvester_hadamard_int(bad_ord)  # type: ignore[arg-type]

        h8 = oracle.compute_hadamard_commutator_smearing(8, Fraction(8, 1))
        self.assertEqual(h8["commutator_nonzero_entries"], 14)
        self.assertEqual(h8["smeared_diagonal_q"], "15/8")
        self.assertEqual(h8["off_diagonal_abs_q"], "7/8")
        self.assertEqual(h8["true_importance_mse_q"], "71/8")
        self.assertEqual(h8["true_importance_mse_dec4"], "8.8750")
        with self.assertRaisesRegex(ValueError, "INVALID_SPIKE_ALPHA"):
            oracle.compute_hadamard_commutator_smearing(8, Fraction(0, 1))
        with self.assertRaisesRegex(ValueError, "INVALID_SPIKE_ALPHA"):
            oracle.compute_hadamard_commutator_smearing(8, 8)  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "HADAMARD_SMEARING_MIN_ORDER_2"):
            oracle.compute_hadamard_commutator_smearing(1, Fraction(2, 1))

        # Householder dial operator & matrix multiply
        h2 = oracle.compute_householder_dial_operator([Fraction(3, 5), Fraction(4, 5)], Fraction(2, 1))
        self.assertEqual(oracle.mat_mul_q(h2, h2), [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)]])
        for bad_d, code in (
            ("bad", "INVALID_AXIS_D"),
            ([Fraction(1)], "INVALID_AXIS_D"),
            ([1, 0], "AXIS_ENTRY_NOT_FRACTION"),
            ([Fraction(1), Fraction(1)], "AXIS_NOT_UNIT_NORM"),
        ):
            with self.assertRaisesRegex(ValueError, code):
                oracle.compute_householder_dial_operator(bad_d, Fraction(2))  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "INVALID_K_DIAL"):
            oracle.compute_householder_dial_operator([Fraction(1), Fraction(0)], 2)  # type: ignore[arg-type]

        for a, b, code in (
            ([], [[Fraction(1)]], "MAT_EMPTY"),
            ([[Fraction(1)]], [], "MAT_EMPTY"),
            ("bad", [[Fraction(1)]], "MAT_EMPTY"),
            ([[Fraction(1)]], "bad", "MAT_EMPTY"),
            ([[Fraction(1), Fraction(2)]], [[Fraction(1)]], "MAT_DIM_MISMATCH"),
            ([[Fraction(1)]], [[]], "MAT_DIM_MISMATCH"),
        ):
            with self.assertRaisesRegex(ValueError, code):
                oracle.mat_mul_q(a, b)  # type: ignore[arg-type]

        # 3-tier roofline: GPU-only, GPU+RAM, GPU+RAM+SSD, and all validation guards
        r_gpu = oracle.compute_three_tier_roofline(
            Fraction(5), Fraction(6), Fraction(30), Fraction(300), Fraction(50), Fraction(6)
        )
        self.assertTrue(r_gpu["fully_gpu_resident"])
        self.assertEqual(r_gpu["spill_slowdown_q"], "1")
        r_ram = oracle.compute_three_tier_roofline(
            Fraction(10), Fraction(6), Fraction(30), Fraction(300), Fraction(50), Fraction(6)
        )
        self.assertFalse(r_ram["fully_gpu_resident"])
        self.assertEqual(r_ram["f_ssd_q"], "0")
        r_ssd = oracle.compute_three_tier_roofline(
            Fraction(50), Fraction(6), Fraction(30), Fraction(300), Fraction(50), Fraction(6)
        )
        self.assertFalse(r_ssd["fully_gpu_resident"])
        self.assertEqual(r_ssd["m_ssd_gb_q"], "14")
        # Edge case: m_ram == 0 and m_ssd > 0 cannot happen when c_ram > 0, test boundary params
        for bad_args, code in (
            ((Fraction(0), Fraction(6), Fraction(30), Fraction(300), Fraction(50), Fraction(6)), "INVALID_MODEL_GB"),
            ((1, Fraction(6), Fraction(30), Fraction(300), Fraction(50), Fraction(6)), "INVALID_MODEL_GB"),
            ((Fraction(5), Fraction(0), Fraction(30), Fraction(300), Fraction(50), Fraction(6)), "INVALID_CGPU_GB"),
            ((Fraction(5), Fraction(6), Fraction(0), Fraction(300), Fraction(50), Fraction(6)), "INVALID_CRAM_GB"),
            ((Fraction(5), Fraction(6), Fraction(30), Fraction(0), Fraction(50), Fraction(6)), "INVALID_BGPU_GBS"),
            ((Fraction(5), Fraction(6), Fraction(30), Fraction(300), Fraction(0), Fraction(6)), "INVALID_BRAM_GBS"),
            ((Fraction(5), Fraction(6), Fraction(30), Fraction(300), Fraction(50), Fraction(0)), "INVALID_BSSD_GBS"),
            ((Fraction(5), Fraction(6), Fraction(30), Fraction(300), Fraction(6), Fraction(6)), "TIER_BW_NOT_STRICT_DESC"),
            ((Fraction(5), Fraction(6), Fraction(30), Fraction(50), Fraction(50), Fraction(6)), "TIER_BW_NOT_STRICT_DESC"),
        ):
            with self.assertRaisesRegex(ValueError, code):
                oracle.compute_three_tier_roofline(*bad_args)  # type: ignore[arg-type]

        # Brier proper scoring & reference mixture bias
        bp = oracle.evaluate_brier_proper_scoring(Fraction(3, 5), Fraction(4, 5))
        self.assertTrue(bp["overconfident_wins_on_y1"])
        self.assertTrue(bp["calibrated_strictly_better_in_expectation"])
        self.assertEqual(bp["excess_penalty_q"], "1/25")
        bp_cal = oracle.evaluate_brier_proper_scoring(Fraction(3, 5), Fraction(3, 5))
        self.assertFalse(bp_cal["calibrated_strictly_better_in_expectation"])
        bp_edge0 = oracle.evaluate_brier_proper_scoring(Fraction(1, 2), Fraction(0, 1))
        self.assertEqual(bp_edge0["excess_penalty_q"], "1/4")
        bp_edge1 = oracle.evaluate_brier_proper_scoring(Fraction(1, 2), Fraction(1, 1))
        self.assertEqual(bp_edge1["excess_penalty_q"], "1/4")
        class _FracSub(Fraction):
            pass

        for qv, pv, code in (
            (Fraction(0), Fraction(1, 2), "INVALID_TRUE_PROB"),
            (Fraction(1), Fraction(1, 2), "INVALID_TRUE_PROB"),
            (_FracSub(1, 2), Fraction(1, 2), "INVALID_TRUE_PROB"),
            (Fraction(1, 2), Fraction(-1, 10), "INVALID_FCST_PROB"),
            (Fraction(1, 2), Fraction(11, 10), "INVALID_FCST_PROB"),
            (Fraction(1, 2), 1, "INVALID_FCST_PROB"),
        ):
            with self.assertRaisesRegex(ValueError, code):
                oracle.evaluate_brier_proper_scoring(qv, pv)  # type: ignore[arg-type]

        for qv, rv, lv, code in (
            (Fraction(0), Fraction(1, 2), Fraction(1, 2), "INVALID_MIX_Q"),
            (Fraction(1), Fraction(1, 2), Fraction(1, 2), "INVALID_MIX_Q"),
            (_FracSub(1, 2), Fraction(1, 2), Fraction(1, 2), "INVALID_MIX_Q"),
            (Fraction(1, 2), Fraction(0), Fraction(1, 2), "INVALID_MIX_R"),
            (Fraction(1, 2), Fraction(1), Fraction(1, 2), "INVALID_MIX_R"),
            (Fraction(1, 2), _FracSub(1, 2), Fraction(1, 2), "INVALID_MIX_R"),
            (Fraction(1, 2), Fraction(1, 2), Fraction(-1, 2), "INVALID_MIX_LAM"),
            (Fraction(1, 2), Fraction(1, 2), Fraction(3, 2), "INVALID_MIX_LAM"),
            (Fraction(1, 2), Fraction(1, 2), 1, "INVALID_MIX_LAM"),
        ):
            with self.assertRaisesRegex(ValueError, code):
                oracle.evaluate_reference_mixture_bias(qv, rv, lv)  # type: ignore[arg-type]

        # 5-gate consolidation evaluator guards + all-false case
        all_fail = oracle.evaluate_five_gate_consolidation(
            rho=Fraction(1, 1),
            forgetting_budgeted=False,
            outcome_lambda=Fraction(0, 1),
            goodhart_drift=Fraction(1, 10),
            residency_ok=False,
            steps=1,
        )
        self.assertFalse(all_fail["all_five_gates_pass"])
        for kw, code in (
            ({"rho": Fraction(0), "forgetting_budgeted": True, "outcome_lambda": Fraction(1, 2), "goodhart_drift": Fraction(0), "residency_ok": True}, "INVALID_RHO"),
            ({"rho": 1, "forgetting_budgeted": True, "outcome_lambda": Fraction(1, 2), "goodhart_drift": Fraction(0), "residency_ok": True}, "INVALID_RHO"),
            ({"rho": Fraction(1, 2), "forgetting_budgeted": 1, "outcome_lambda": Fraction(1, 2), "goodhart_drift": Fraction(0), "residency_ok": True}, "INVALID_FORGETTING_FLAG"),
            ({"rho": Fraction(1, 2), "forgetting_budgeted": True, "outcome_lambda": Fraction(-1, 2), "goodhart_drift": Fraction(0), "residency_ok": True}, "INVALID_LAMBDA"),
            ({"rho": Fraction(1, 2), "forgetting_budgeted": True, "outcome_lambda": Fraction(3, 2), "goodhart_drift": Fraction(0), "residency_ok": True}, "INVALID_LAMBDA"),
            ({"rho": Fraction(1, 2), "forgetting_budgeted": True, "outcome_lambda": 1, "goodhart_drift": Fraction(0), "residency_ok": True}, "INVALID_LAMBDA"),
            ({"rho": Fraction(1, 2), "forgetting_budgeted": True, "outcome_lambda": Fraction(1, 2), "goodhart_drift": Fraction(-1), "residency_ok": True}, "INVALID_DRIFT"),
            ({"rho": Fraction(1, 2), "forgetting_budgeted": True, "outcome_lambda": Fraction(1, 2), "goodhart_drift": 0, "residency_ok": True}, "INVALID_DRIFT"),
            ({"rho": Fraction(1, 2), "forgetting_budgeted": True, "outcome_lambda": Fraction(1, 2), "goodhart_drift": Fraction(0), "residency_ok": 1}, "INVALID_RESIDENCY_FLAG"),
            ({"rho": Fraction(1, 2), "forgetting_budgeted": True, "outcome_lambda": Fraction(1, 2), "goodhart_drift": Fraction(0), "residency_ok": True, "steps": 0}, "INVALID_STEPS"),
            ({"rho": Fraction(1, 2), "forgetting_budgeted": True, "outcome_lambda": Fraction(1, 2), "goodhart_drift": Fraction(0), "residency_ok": True, "steps": True}, "INVALID_STEPS"),
        ):
            with self.assertRaisesRegex(ValueError, code):
                oracle.evaluate_five_gate_consolidation(**kw)  # type: ignore[arg-type]

    def test_02_certificate_pillars_and_disk_parity(self) -> None:
        disk_cert = TRACK_DIR / "s94_wave6_convergence_certificate.json"
        self.assertIn(stat.S_IMODE(os.lstat(disk_cert).st_mode), (0o600, 0o644))
        self.assertEqual(disk_cert.read_bytes(), oracle.canonical_json_bytes(self.valid_env))
        res = verifier.check_certificate_file(disk_cert, full_replay=True)
        self.assertEqual(res["status"], "PASS")
        self.assertEqual(res["certificate_sha256"], self.valid_env["certificate_sha256"])

        p = self.valid_env["payload"]
        p1 = p["pillar_1_privileged_neuron_basis"]
        self.assertEqual(p1["hadamard_h8_skewed_d8"]["true_importance_mse_q"], "71/8")
        self.assertEqual(p1["householder_reflection_dpi_witness"]["global_frob_delta_q"], "0")
        self.assertEqual(p1["householder_reflection_dpi_witness"]["qwen3_8b_100neuron_dpi_conc_q"], "110592/25")

        p2 = p["pillar_2_bonsai_magnitude_roofline"]
        self.assertEqual(p2["hardware_three_tier_specs"]["dense_27b_residency_cliff_bpw_q"], "325/171")
        self.assertTrue(p2["dense_27b_regimes"]["bonsai25_ptq10_1p76bpw"]["fully_gpu_resident"])
        self.assertFalse(p2["dense_27b_regimes"]["a16_quadsnake_3p0bpw"]["fully_gpu_resident"])
        self.assertEqual(p2["dense_27b_regimes"]["bonsai25_ptq10_1p76bpw"]["roofline_tps_dec4"], "60.1349")

        p3 = p["pillar_3_sleep_trilogy_consolidation"]
        self.assertEqual(p3["axis1_zero_dw_kv_sleep"]["sleep_n2_token_efficiency_q"], "21/10")
        self.assertEqual(p3["axis1_zero_dw_kv_sleep"]["sleep_n4_token_efficiency_q"], "239/100")
        self.assertTrue(p3["five_gate_consolidation_fixed_point"]["all_five_gates_pass"])
        self.assertTrue(p3["all_five_ablations_rejected"])

        p4 = p["pillar_4_provenance_and_lean4"]
        self.assertEqual(p4["wave6_snapshot_count"], 12)
        self.assertEqual(p4["upstream_cert_count"], 10)
        self.assertEqual(p4["lean4_companion"]["theorem_count"], 18)

    def test_03_json_parser_rational_and_exact_equal(self) -> None:
        self.assertEqual(verifier.parse_canonical_q("0", "Q"), Fraction(0))
        self.assertEqual(verifier.parse_canonical_q("-7", "Q"), Fraction(-7))
        self.assertEqual(verifier.parse_canonical_q("71/8", "Q"), Fraction(71, 8))
        for bad_q in (123, "", "-0", "01", "+1", "1/2/3", "2/4", "3/1", "1/0", "1/-2", "01/3", "1/03", " 1/2"):
            with self.assertRaisesRegex(ValueError, "BADQ"):
                verifier.parse_canonical_q(bad_q, "BADQ")

        self.assertTrue(verifier._is_sha256_hex("a" * 64))
        self.assertFalse(verifier._is_sha256_hex(123))
        self.assertFalse(verifier._is_sha256_hex("A" * 64))

        # Iterative JSON tree checks (depth exact boundary + overflow, int bits, NUL, surrogate, cycle, non-str key, subclass)
        verifier._check_json_tree({"a": [1, True, None, "ok", (1 << 2048) - 1]})
        exact_deep: Any = 1
        for _ in range(verifier.MAX_JSON_DEPTH):
            exact_deep = [exact_deep]
        verifier._check_json_tree(exact_deep)
        deep: Any = [exact_deep]
        with self.assertRaisesRegex(ValueError, "JSON_MAX_DEPTH_EXCEEDED"):
            verifier._check_json_tree(deep)
        with self.assertRaisesRegex(ValueError, "JSON_INT_TOO_LARGE"):
            verifier._check_json_tree(1 << 2048)
        self.assertEqual(verifier._parse_capped_int(str((1 << 2048) - 1)), (1 << 2048) - 1)
        self.assertEqual(verifier._parse_capped_int("1" + "0" * 616), 10**616)
        with self.assertRaisesRegex(ValueError, "JSON_INT_TOO_LARGE"):
            verifier._parse_capped_int(str(1 << 2048))
        with self.assertRaisesRegex(ValueError, "JSON_NUL_IN_STRING"):
            verifier._check_json_tree("a\x00b")
        with self.assertRaisesRegex(ValueError, "JSON_LONE_SURROGATE"):
            verifier._check_json_tree("\ud800")
        cyc_l: list[Any] = []
        cyc_l.append(cyc_l)
        with self.assertRaisesRegex(ValueError, "JSON_CYCLE"):
            verifier._check_json_tree(cyc_l)
        cyc_d: dict[str, Any] = {}
        cyc_d["self"] = cyc_d
        with self.assertRaisesRegex(ValueError, "JSON_CYCLE"):
            verifier._check_json_tree(cyc_d)
        with self.assertRaisesRegex(ValueError, "JSON_NON_STRING_KEY"):
            verifier._check_json_tree({1: "a"})

        class EvilInt(int):
            pass

        with self.assertRaisesRegex(ValueError, "JSON_DISALLOWED_TYPE"):
            verifier._check_json_tree(EvilInt(5))

        # Strict JSON bytes parser
        for raw, err in (
            (b'{"a":1}\r\n', "CRLF_FORBIDDEN"),
            (b'{"a":"x\x00y"}\n', "NUL_BYTE_IN_JSON"),
            (b"\xff\xfe", "INVALID_UTF8"),
            (b'{"a":1,"a":2}\n', "JSON_DUPLICATE_KEY"),
            (b'{"a":1.5}\n', "JSON_FLOAT_FORBIDDEN"),
            (b'{"a":NaN}\n', "JSON_CONSTANT_FORBIDDEN"),
            (b'{"a":' + (b"9" * 5000) + b"}\n", "JSON_INT_TOO_LARGE"),
            (b'{"a":-' + (b"9" * 618) + b"}\n", "JSON_INT_TOO_LARGE"),
            (b'{"a":' + str(1 << 2048).encode() + b"}\n", "JSON_INT_TOO_LARGE"),
            (b"[1,2]\n", "JSON_ROOT_NOT_OBJECT"),
            (b'{\n  "a": 1\n}\n', "NON_CANONICAL_JSON_BYTES"),
            (b"{broken\n", ""),
        ):
            with self.assertRaisesRegex(ValueError, err):
                verifier.parse_strict_json_bytes(raw)
        with mock.patch("json.loads", side_effect=RecursionError("deep")):
            with self.assertRaisesRegex(ValueError, "JSON_MAX_DEPTH_EXCEEDED"):
                verifier.parse_strict_json_bytes(b'{"a":1}\n')
        self.assertEqual(verifier.parse_strict_json_bytes(b'{"a":-1}\n'), {"a": -1})

        # exact_typed_equal
        self.assertTrue(verifier.exact_typed_equal({"a": [1, True, None]}, {"a": [1, True, None]}))
        self.assertFalse(verifier.exact_typed_equal(1, True))
        self.assertFalse(verifier.exact_typed_equal({"a": 1}, {"a": 1, "b": 2}))
        self.assertFalse(verifier.exact_typed_equal({"a": 1}, {"b": 1}))
        self.assertFalse(verifier.exact_typed_equal([1, 2], [1]))
        self.assertFalse(verifier.exact_typed_equal([1, 2], [1, 3]))
        self.assertFalse(verifier.exact_typed_equal("x", "y"))

    def test_04_hardened_io_pwd_symlink_fifo_hardlink_and_atomic_write(self) -> None:
        with tempfile.TemporaryDirectory(prefix="s94_io_") as td:
            d = Path(td).resolve()
            good = d / "cert.json"
            raw_good = oracle.canonical_json_bytes(self.valid_env)
            verifier.atomic_write_0600(good, raw_good)
            self.assertEqual(stat.S_IMODE(os.lstat(good).st_mode), 0o600)
            self.assertEqual(good.read_bytes(), raw_good)
            verifier.atomic_write_0600(good, raw_good)

            for bad_p, code in (
                ("not_a_path", "INVALID_PATH_TYPE"),
                (Path("a\x00b"), "INVALID_PATH"),
                (Path("/tmp/\ud800"), "INVALID_PATH_SURROGATE"),
                (Path("/"), "INVALID_PATH"),
                (d / "..", "INVALID_PATH"),
                (d / "no_dir" / "x.json", "INVALID_PARENT_DIR"),
                (d / "missing.json", "FILE_OPEN_ERROR"),
                (d, "NOT_REGULAR_FILE"),
            ):
                with self.assertRaisesRegex(ValueError, code):
                    verifier.read_regular_file_bytes(bad_p)  # type: ignore[arg-type]

            sym_f = d / "sym.json"
            sym_f.symlink_to(good)
            with self.assertRaisesRegex(ValueError, "SYMLINK_IN_PATH"):
                verifier.read_regular_file_bytes(sym_f)
            with self.assertRaisesRegex(ValueError, "SYMLINK_IN_PATH"):
                verifier.atomic_write_0600(sym_f, raw_good)

            sub = d / "real_sub"
            sub.mkdir()
            (sub / "g.json").write_bytes(raw_good)
            sym_d = d / "sym_sub"
            sym_d.symlink_to(sub)
            with self.assertRaisesRegex(ValueError, "SYMLINK_IN_PATH"):
                verifier.read_regular_file_bytes(sym_d / "g.json")
            with self.assertRaisesRegex(ValueError, "TARGET_NOT_REGULAR"):
                verifier.atomic_write_0600(sub, raw_good)

            # Live logical $PWD symlink check
            p_pwd = subprocess.run(
                [sys.executable, "-I", "-B", str(TRACK_DIR / "verify_s94_wave6_convergence.py"), "--check", "g.json"],
                cwd=str(sym_d),
                env={"PATH": os.environ.get("PATH", ""), "PWD": str(sym_d)},
                capture_output=True,
                text=True,
                timeout=15,
                check=False,
            )
            self.assertEqual(p_pwd.returncode, 2)
            self.assertIn("SYMLINK_IN_PATH", p_pwd.stderr)

            orig_cwd = os.getcwd()
            try:
                os.chdir(sub)
                with mock.patch.dict(os.environ, {"PWD": str(sub)}, clear=False):
                    self.assertEqual(verifier.read_regular_file_bytes(Path("g.json")), raw_good)
                with mock.patch.dict(os.environ, {"PWD": "rel/pwd"}, clear=False):
                    self.assertEqual(verifier.read_regular_file_bytes(Path("g.json")), raw_good)
                with mock.patch.object(verifier.os, "environ", {"PWD": "rel/\ud800"}):
                    self.assertEqual(verifier.read_regular_file_bytes(Path("g.json")), raw_good)
                with mock.patch.dict(os.environ, {"PWD": str(d / "no_such_pwd")}, clear=False):
                    self.assertEqual(verifier.read_regular_file_bytes(Path("g.json")), raw_good)
                with mock.patch.dict(os.environ, {}, clear=True):
                    self.assertEqual(verifier.read_regular_file_bytes(Path("g.json")), raw_good)
                with mock.patch.object(verifier.os, "environ", {"PWD": "/tmp/\ud800"}):
                    with self.assertRaisesRegex(ValueError, "INVALID_PWD_SURROGATE"):
                        verifier.read_regular_file_bytes(Path("g.json"))
            finally:
                os.chdir(orig_cwd)

            # Exact max_bytes boundary (kills M052 & M054 <= -> < mutants)
            self.assertEqual(verifier.read_regular_file_bytes(good, max_bytes=len(raw_good)), raw_good)

            # Non-blocking scratch os.mkfifo rejection (< 1s)
            fifo_p = d / "pipe.fifo"
            os.mkfifo(fifo_p)
            t0 = time.monotonic_ns()
            with self.assertRaisesRegex(ValueError, "NOT_REGULAR_FILE"):
                verifier.read_regular_file_bytes(fifo_p)
            self.assertLess(time.monotonic_ns() - t0, 1_000_000_000)

            # Live hardlink read & write rejection
            hl = d / "hl.json"
            os.link(good, hl)
            try:
                with self.assertRaisesRegex(ValueError, "HARDLINK_FORBIDDEN"):
                    verifier.read_regular_file_bytes(hl)
                with self.assertRaisesRegex(ValueError, "HARDLINK_FORBIDDEN"):
                    verifier.atomic_write_0600(hl, raw_good)
            finally:
                hl.unlink()

            # Oversized fstat & stream checks
            big_st = os.stat_result((stat.S_IFREG | 0o600, 0, 0, 1, 0, 0, verifier.MAX_JSON_BYTES + 1, 0, 0, 0))
            with mock.patch("os.fstat", return_value=big_st):
                with self.assertRaisesRegex(ValueError, "FILE_TOO_LARGE"):
                    verifier.read_regular_file_bytes(good)
            orig_read = os.read
            cnt = [0]

            def _big_read(fd: int, n: int) -> bytes:
                cnt[0] += 1
                if cnt[0] <= 2:
                    return b" " * (verifier.MAX_JSON_BYTES // 2 + 10)
                return orig_read(fd, n)

            with mock.patch("os.read", side_effect=_big_read):
                with self.assertRaisesRegex(ValueError, "FILE_TOO_LARGE"):
                    verifier.read_regular_file_bytes(good)

            # Atomic write temp hardlink, TOCTOU swap, and short write
            hl_st = os.stat_result((stat.S_IFREG | 0o600, 0, 0, 2, 0, 0, len(raw_good), 0, 0, 0))
            with mock.patch("os.fstat", return_value=hl_st):
                with self.assertRaisesRegex(ValueError, "TMP_HARDLINK_DETECTED"):
                    verifier.atomic_write_0600(d / "t_hl.json", raw_good)
            self.assertEqual([p.name for p in d.iterdir() if p.name.endswith(".tmp")], [])

            toctou = d / "toctou.json"
            real_fsync = os.fsync
            swapped = [False]

            def _swap(fd: int) -> None:
                real_fsync(fd)
                if not swapped[0]:
                    swapped[0] = True
                    toctou.symlink_to(good)

            with mock.patch("os.fsync", side_effect=_swap):
                with self.assertRaisesRegex(ValueError, "SYMLINK_IN_PATH"):
                    verifier.atomic_write_0600(toctou, raw_good)

            fired = [False]
            real_write = os.write

            def _zero_w(fd: int, data: bytes) -> int:
                if not fired[0]:
                    fired[0] = True
                    return 0
                return real_write(fd, data)

            with mock.patch("os.write", side_effect=_zero_w):
                with self.assertRaisesRegex(OSError, "SHORT_WRITE"):
                    verifier.atomic_write_0600(d / "short.json", raw_good)

    def test_05_non_hollow_sec_fr0_fr1_semantic_tamper_matrix(self) -> None:
        self.assertEqual(verifier.verify_certificate_dict(self.valid_env, full_replay=True)["status"], "PASS")
        with mock.patch.object(verifier, "build_certificate_envelope", side_effect=RuntimeError("NO_REPLAY_IN_FR0")):
            self.assertEqual(verifier.verify_certificate_dict(self.valid_env, full_replay=False)["status"], "PASS")
        self.assertIs(verifier.secondary_audit_payload(self.valid_env["payload"]), self.valid_env["payload"])

        with self.assertRaisesRegex(ValueError, "INVALID_FULL_REPLAY_FLAG"):
            verifier.verify_certificate_dict(self.valid_env, full_replay=0)  # type: ignore[arg-type]

        # Envelope rejections
        with self.assertRaisesRegex(ValueError, "CERT_NOT_DICT"):
            verifier.verify_certificate_dict([])
        e_extra = copy.deepcopy(self.valid_env)
        e_extra["extra"] = 1
        with self.assertRaisesRegex(ValueError, "CERT_KEYS_MISMATCH"):
            verifier.verify_certificate_dict(e_extra)
        for field, val, err in (
            ("schema_version", "wrong", "SCHEMA_VERSION_MISMATCH"),
            ("track_id", "wrong", "TRACK_ID_MISMATCH"),
            ("payload_sha256", "bad", "INVALID_PAYLOAD_SHA256"),
            ("certificate_sha256", "bad", "INVALID_CERT_SHA256"),
            ("payload", [], "PAYLOAD_NOT_DICT"),
            ("certificate_sha256", "0" * 64, "CERTIFICATE_SHA256_TAMPERED"),
        ):
            e = copy.deepcopy(self.valid_env)
            e[field] = val
            with self.assertRaisesRegex(ValueError, err):
                verifier.verify_certificate_dict(e)
        e_ptamp = copy.deepcopy(self.valid_env)
        e_ptamp["payload"]["novelty_tier"] = "N9"
        with self.assertRaisesRegex(ValueError, "PAYLOAD_SHA256_TAMPERED"):
            verifier.verify_certificate_dict(e_ptamp)

        # FR0-pass / FR1-reject oracle drift
        drift = copy.deepcopy(self.valid_env)
        drift["payload"]["pillar_3_sleep_trilogy_consolidation"]["axis2_weight_modifying_consolidation"]["harvey_tenet_early_stop_steps_default"] = 81
        drift_s = _resign(drift)
        self.assertEqual(verifier.verify_certificate_dict(drift_s, full_replay=False)["status"], "PASS")
        with self.assertRaisesRegex(ValueError, "ORACLE_PAYLOAD_DRIFT"):
            verifier.verify_certificate_dict(drift_s, full_replay=True)

        fake_exp = copy.deepcopy(self.valid_env)
        fake_exp["certificate_sha256"] = "f" * 64
        with mock.patch.object(verifier, "build_certificate_envelope", return_value=fake_exp):
            with self.assertRaisesRegex(ValueError, "ORACLE_CERT_DRIFT"):
                verifier.verify_certificate_dict(self.valid_env, full_replay=True)

        # Exhaustive re-signed semantic tamper matrix verified rejected on SEC, FR0, AND FR1!
        def _tamper(mut_fn, code: str) -> None:
            e = copy.deepcopy(self.valid_env)
            mut_fn(e["payload"])
            rs = _resign(e)
            with self.assertRaisesRegex(ValueError, code):
                verifier.secondary_audit_payload(rs["payload"])
            with self.assertRaisesRegex(ValueError, code):
                verifier.verify_certificate_dict(rs, full_replay=False)
            with self.assertRaisesRegex(ValueError, code):
                verifier.verify_certificate_dict(rs, full_replay=True)

        with self.assertRaisesRegex(ValueError, "PAYLOAD_NOT_DICT"):
            verifier.secondary_audit_payload([])

        _tamper(lambda p: p.pop("novelty_tier"), "PAYLOAD_KEYS_MISMATCH")
        _tamper(lambda p: p.__setitem__("track_id", "X"), "PAYLOAD_TRACK_MISMATCH")
        _tamper(lambda p: p.__setitem__("oracle_class", "X"), "ORACLE_CLASS_MISMATCH")
        _tamper(lambda p: p.__setitem__("novelty_tier", "N2"), "NOVELTY_TIER_MISMATCH")
        _tamper(lambda p: p.__setitem__("all_pillars_verified", False), "PILLARS_NOT_VERIFIED")
        # Empty pillars 1-4 must ALL fail SEC, FR0 & FR1!
        _tamper(lambda p: p.__setitem__("pillar_1_privileged_neuron_basis", {}), "P1_SCHEMA")
        _tamper(lambda p: p.__setitem__("pillar_2_bonsai_magnitude_roofline", {}), "P2_SCHEMA")
        _tamper(lambda p: p.__setitem__("pillar_3_sleep_trilogy_consolidation", {}), "P3_SCHEMA")
        _tamper(lambda p: p.__setitem__("pillar_4_provenance_and_lean4", {}), "P4_SCHEMA")

        # AUDIT-194 S94-VER-01 P01..P10 explicit regressions on SEC, FR0 & FR1!
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"].__setitem__("s86_8gib_training_anchor", "NOT_A_DICT"), "P2_S86_SCHEMA")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["s86_8gib_training_anchor"].__setitem__("qwen3b_r64_peak_alloc_bytes", 1), "P2_S86_VALS")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["magnitude_sparse_moe_contrast"].__setitem__("hit80_ram20_tps_q", "999"), "P2_MOE_H80_VAL")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["magnitude_sparse_moe_contrast"].__setitem__("hit80_ram20_tps_dec4", "999.0000"), "P2_MOE_H80_DEC4")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["magnitude_sparse_moe_contrast"].__setitem__("hit80_ram20_slowdown_q", "1"), "P2_MOE_H80S_VAL")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["magnitude_sparse_moe_contrast"].__setitem__("hit80_ram20_slowdown_dec4", "9.9999"), "P2_MOE_H80S_DEC4")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis2_weight_modifying_consolidation"].__setitem__("reference_mixture_pure_ref", None), "P3_M0_SCHEMA")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis2_weight_modifying_consolidation"].__setitem__("reference_mixture_pure_outcome", None), "P3_M1_SCHEMA")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis2_weight_modifying_consolidation"]["reference_mixture_pure_ref"].__setitem__("lambda_q", "1/2"), "P3_M0_LAM_VAL")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis2_weight_modifying_consolidation"]["reference_mixture_pure_outcome"].__setitem__("anchored_to_outcomes", False), "P3_M1_ANCHOR")
        _tamper(
            lambda p: p["pillar_4_provenance_and_lean4"].__setitem__(
                "wave6_snapshot_pins",
                [{"filename": "fake.txt", "portal": "P98", "bytes": 1, "sha256": "0" * 64} for _ in range(12)],
            ),
            "P4_W6_NAME",
        )
        _tamper(
            lambda p: p["pillar_4_provenance_and_lean4"].__setitem__(
                "upstream_cert_pins",
                [{"track_id": "FAKE", "relative_ref": "fake.json", "bytes": 1, "sha256": "0" * 64} for _ in range(10)],
            ),
            "P4_UP_FIELDS",
        )
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["hardware_three_tier_specs"].__setitem__("dense_27b_residency_cliff_bpw_dec4", "GARBAGE"), "P2_BCRIT_DEC4")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["hadamard_h8_skewed_d8"].__setitem__("true_importance_mse_dec4", "999.9999"), "P1_H8_DEC4")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].__setitem__("gemma4_12b_total_neurons", -1), "P1_GEMMA_COUNTS")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].__setitem__("qwen3_8b_100neuron_dpi_conc_dec2", "0.00"), "P1_QWEN_CONC_DEC2")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].__setitem__("s31_two_row_dpi_anchor_q", "1"), "P1_S31_DPI_VAL")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].__setitem__("refusal_unedited_q", "1/2"), "P1_REFUSAL_VALS")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["borromean_five_gate_ablations"]["ablate_g1_divergent_sleep_loop"].__setitem__("error_after_steps_q", "0"), "P3_ABL_ERR_VAL")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["five_gate_consolidation_fixed_point"].__setitem__("error_after_steps_q", "1"), "P3_FP_ERR_VAL")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["hadamard_h8_skewed_d8"].__setitem__("rogue_key", "123"), "P1_H8_SCHEMA")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["bonsai25_primary_anchors"].__setitem__("rogue_key", "123"), "P2_BA_SCHEMA")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis1_zero_dw_kv_sleep"].__setitem__("rogue_key", "123"), "P3_A1_SCHEMA")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["lean4_companion"].__setitem__("rogue_key", "123"), "P4_LEAN_SCHEMA")

        # Pillar 1 exhaustive guards & BoolOp subconditions
        _tamper(lambda p: p.__setitem__("pillar_1_privileged_neuron_basis", []), "P1_NOT_DICT")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"].__setitem__("all_verified", False), "P1_NOT_VERIFIED")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"].__setitem__("hadamard_h8_skewed_d8", []), "P1_H8_SCHEMA")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["hadamard_h8_skewed_d8"].__setitem__("order", 4), "P1_H8_ORDER")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["hadamard_h8_skewed_d8"].__setitem__("spike_alpha_q", "7"), "P1_H8_ALPHA_VAL")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["hadamard_h8_skewed_d8"].__setitem__("commutator_nonzero_entries", 12), "P1_H8_COMM")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["hadamard_h8_skewed_d8"].__setitem__("commutator_total_entries", 16), "P1_H8_COMM")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["hadamard_h8_skewed_d8"].__setitem__("all_diagonals_flattened", False), "P1_H8_FLAT")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["hadamard_h8_skewed_d8"].__setitem__("all_off_diagonals_uniform_abs", False), "P1_H8_FLAT")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["hadamard_h8_skewed_d8"].__setitem__("smeared_diagonal_q", "2"), "P1_H8_DIAG_VAL")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["hadamard_h8_skewed_d8"].__setitem__("off_diagonal_abs_q", "1"), "P1_H8_OFF_VAL")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["hadamard_h8_skewed_d8"].__setitem__("unweighted_mse_q", "2"), "P1_H8_UNW_VAL")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["hadamard_h8_skewed_d8"].__setitem__("true_importance_mse_q", "9"), "P1_H8_IMP_VAL")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["hadamard_h8_isotropic_control"].__setitem__("commutator_nonzero_entries", 1), "P1_ISO_COMM")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["hadamard_h8_isotropic_control"].__setitem__("true_importance_mse_q", "2"), "P1_ISO_IMP_VAL")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"].__setitem__("hadamard_o_k_smearing_ladder", "bad"), "P1_LADDER_NOT_LIST")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"].__setitem__("hadamard_o_k_smearing_ladder", []), "P1_LADDER_LEN")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["hadamard_o_k_smearing_ladder"][0].__setitem__("order", 99), "P1_LADDER_ORDER")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["hadamard_o_k_smearing_ladder"][0].__setitem__("commutator_nonzero_entries", 99), "P1_LADDER_COMM")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["hadamard_o_k_smearing_ladder"][0].__setitem__("true_importance_mse_q", "1"), "P1_LADDER_IMP_VAL")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["axis_aligned_perm_control"].__setitem__("off_diagonal_leakage", 1), "P1_PERM_LEAK")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["axis_aligned_perm_control"].__setitem__("s70_swiglu_perm_max_abs_diff", 1), "P1_PERM_LEAK")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["axis_aligned_perm_control"].__setitem__("s59_a16_rho_axis", 2), "P1_S59_RHO")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["axis_aligned_perm_control"].__setitem__("s59_a16_rho_h16", 2), "P1_S59_RHO")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["axis_aligned_perm_control"].__setitem__("importance_mse_ratio_q", "2"), "P1_PERM_MSE_VAL")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].__setitem__("axis_d_q", ["1"]), "P1_HH_AXIS_LEN")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].__setitem__("axis_d_q", ["1", "1", "0", "0"]), "P1_HH_UNIT")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].__setitem__("k2_is_involution", False), "P1_HH_K2")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].__setitem__("k2_is_isometry", False), "P1_HH_K2")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].__setitem__("k1_is_idempotent", False), "P1_HH_K1")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].update({"frob_norm_sq_before_q": "0", "frob_norm_sq_after_q": "0"}), "P1_HH_ZERO_FROB_DELTA")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].__setitem__("frob_norm_sq_after_q", "99"), "P1_HH_ZERO_FROB_DELTA")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].__setitem__("global_frob_delta_q", "1"), "P1_HH_ZERO_FROB_DELTA")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].__setitem__("diff_matrix_frob_sq_q", "0"), "P1_HH_DIFF_NONZERO")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].__setitem__("diff_matrix_exact_rank", 2), "P1_HH_RANK1")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].__setitem__("dpi_spectral_concentration_q", "2"), "P1_HH_DPI_VAL")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].__setitem__("qwen3_8b_total_neurons", "442368"), "P1_QWEN_N")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].update({"qwen3_8b_total_neurons": 100, "qwen3_8b_poles": 200}), "P1_QWEN_COUNTS")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].__setitem__("qwen3_8b_poles", 100), "P1_QWEN_COUNTS")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].__setitem__("qwen3_8b_100neuron_dpi_conc_q", "1"), "P1_QWEN_CONC_VAL")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].__setitem__("relp_rs_adjoint_exact", False), "P1_RELP_ADJOINT")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"].__setitem__("relp_rs_adjoint_lhs_q", "0"), "P1_RELP_EQ")

        # Pillar 2 exhaustive guards & BoolOp subconditions
        _tamper(lambda p: p.__setitem__("pillar_2_bonsai_magnitude_roofline", []), "P2_NOT_DICT")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"].__setitem__("all_verified", False), "P2_NOT_VERIFIED")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["bonsai25_primary_anchors"].__setitem__("compression_ratio_q", "1"), "P2_COMP_VAL")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["bonsai25_primary_anchors"].__setitem__("compression_ratio_dec4", "0.0000"), "P2_COMP_DEC4")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["bonsai25_primary_anchors"].__setitem__("tool_calling_retention_q", "1"), "P2_TOOL_VAL")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["bonsai25_primary_anchors"].__setitem__("agentic_coding_retention_q", "1"), "P2_CODE_VAL")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["hardware_three_tier_specs"].__setitem__("b_ssd_gbs_q", "60"), "P2_BW_ORDER")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["hardware_three_tier_specs"].__setitem__("b_ram_gbs_q", "500"), "P2_BW_ORDER")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["hardware_three_tier_specs"].__setitem__("dense_27b_residency_cliff_bpw_q", "2"), "P2_BCRIT_VAL")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["hardware_three_tier_specs"].__setitem__("bonsai_below_residency_cliff", False), "P2_BELOW_CLIFF")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["bonsai25_primary_anchors"].__setitem__("ptq10_bpw_q", "2"), "P2_BELOW_CLIFF")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["dense_27b_regimes"].pop("fp16_16p0bpw"), "P2_REGS_KEYS")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["dense_27b_regimes"]["fp16_16p0bpw"].__setitem__("model_gb_q", "1"), "P2_REG_M_VAL")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["dense_27b_regimes"]["fp16_16p0bpw"].__setitem__("f_gpu_q", "1"), "P2_FG_VAL")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["dense_27b_regimes"]["fp16_16p0bpw"].__setitem__("f_ram_q", "0"), "P2_FR_VAL")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["dense_27b_regimes"]["fp16_16p0bpw"].__setitem__("f_ssd_q", "0"), "P2_FS_VAL")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["dense_27b_regimes"]["fp16_16p0bpw"].__setitem__("spill_slowdown_q", "1"), "P2_SLOW_VAL")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["dense_27b_regimes"]["fp16_16p0bpw"].__setitem__("spill_slowdown_dec4", "0.0000"), "P2_SLOW_DEC4")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["dense_27b_regimes"]["fp16_16p0bpw"].__setitem__("roofline_tps_q", "1"), "P2_TPS_VAL")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["dense_27b_regimes"]["fp16_16p0bpw"].__setitem__("roofline_tps_dec4", "0.0000"), "P2_TPS_DEC4")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["dense_27b_regimes"]["bonsai25_ptq10_1p76bpw"].__setitem__("fully_gpu_resident", False), "P2_RESIDENT_FLAG")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["dense_27b_regimes"]["a16_quadsnake_3p0bpw"].__setitem__("fully_gpu_resident", True), "P2_RESIDENT_FLAG")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["magnitude_sparse_moe_contrast"].update({"active_expert_fraction_q": "1/10", "active_bytes_per_token_gb_q": "269/50"}), "P2_MOE_GB_VAL")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["magnitude_sparse_moe_contrast"].__setitem__("active_bytes_per_token_gb_q", "1"), "P2_MOE_GB_VAL")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["magnitude_sparse_moe_contrast"].__setitem__("fits_in_gpu_hot_cache", False), "P2_MOE_FITS")
        _tamper(lambda p: p["pillar_2_bonsai_magnitude_roofline"]["magnitude_sparse_moe_contrast"].__setitem__("hit100_tps_q", "1"), "P2_MOE_H100_VAL")

        def _mut_moe_overflow(p: dict) -> None:
            hw = p["pillar_2_bonsai_magnitude_roofline"]["hardware_three_tier_specs"]
            hw["c_gpu_weight_budget_gb_q"] = "1"
            hw["dense_27b_residency_cliff_bpw_q"] = "50/171"
            hw["dense_27b_residency_cliff_bpw_dec4"] = oracle.dec_str(Fraction(50, 171), 4)
            p["pillar_2_bonsai_magnitude_roofline"]["bonsai25_primary_anchors"]["ptq10_bpw_q"] = "1/10"
            for name, m_val in (
                ("bonsai25_ptq10_1p76bpw", Fraction(593, 100)),
                ("a16_quadsnake_3p0bpw", Fraction(513, 50)),
                ("quant_4p5bpw", Fraction(1539, 100)),
                ("fp16_16p0bpw", Fraction(269, 5)),
            ):
                p["pillar_2_bonsai_magnitude_roofline"]["dense_27b_regimes"][name] = oracle.compute_three_tier_roofline(
                    m_val, Fraction(1), Fraction(31), Fraction(1783, 5), Fraction(50), Fraction(6)
                )

        _tamper(_mut_moe_overflow, "P2_MOE_FITS")

        # Pillar 3 exhaustive guards & BoolOp subconditions
        _tamper(lambda p: p.__setitem__("pillar_3_sleep_trilogy_consolidation", []), "P3_NOT_DICT")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"].__setitem__("all_verified", False), "P3_NOT_VERIFIED")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis1_zero_dw_kv_sleep"].__setitem__("sleep_n2_token_efficiency_q", "2"), "P3_N2_VAL")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis1_zero_dw_kv_sleep"].__setitem__("sleep_n4_token_efficiency_q", "2"), "P3_N4_VAL")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis1_zero_dw_kv_sleep"].__setitem__("wake_latency_overhead", 1), "P3_ZERO_OVERHEAD")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis1_zero_dw_kv_sleep"].__setitem__("kv_cache_size_growth", 1), "P3_ZERO_OVERHEAD")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis1_zero_dw_kv_sleep"].__setitem__("weight_forgetting_ratio_q", "1"), "P3_ZERO_F_VAL")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis1_zero_dw_kv_sleep"].__setitem__("cross_session_persistence", True), "P3_A1_PERSIST")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis1_zero_dw_kv_sleep"].__setitem__("s76_loop4_err_q", "1/2"), "P3_RHO_E4")

        def _mut_rho_ge1(p: dict) -> None:
            a1 = p["pillar_3_sleep_trilogy_consolidation"]["axis1_zero_dw_kv_sleep"]
            a1["s76_contractive_rho_q"] = "1"
            a1["s76_loop2_err_q"] = "1"
            a1["s76_loop4_err_q"] = "1"

        _tamper(_mut_rho_ge1, "P3_RHO_E4")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis1_zero_dw_kv_sleep"]["s79_last_loop_kv_ratios"].__setitem__("r4_w64_l2048_q", "1"), "P3_KVR_VAL")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis2_weight_modifying_consolidation"].__setitem__("cross_session_persistence", False), "P3_A2_PERSIST")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis2_weight_modifying_consolidation"].__setitem__("s78_forgetting_over_learning_q", "0"), "P3_S78_F_VAL")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis2_weight_modifying_consolidation"].__setitem__("s80_songe_1night_fwer_q", "1/10"), "P3_S80_1N_VAL")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis2_weight_modifying_consolidation"].__setitem__("s80_songe_20night_fwer_dec4", "0.0000"), "P3_S80_20N_DEC")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis2_weight_modifying_consolidation"].__setitem__("s80_ratchet_goodhart_accepts", 1), "P3_S80_RATCHET")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis2_weight_modifying_consolidation"]["brier_overconfidence_paradox"].update({"expected_bs_true_q": "1/5", "expected_bs_fcst_q": "6/25"}), "P3_BP_DECOMP")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis2_weight_modifying_consolidation"]["brier_overconfidence_paradox"].__setitem__("expected_bs_fcst_q", "6/25"), "P3_BP_DECOMP")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis2_weight_modifying_consolidation"]["brier_overconfidence_paradox"].__setitem__("overconfident_wins_on_y1", False), "P3_BP_FLAGS")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis2_weight_modifying_consolidation"]["brier_overconfidence_paradox"].__setitem__("calibrated_strictly_better_in_expectation", False), "P3_BP_FLAGS")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis2_weight_modifying_consolidation"]["reference_mixture_half"].__setitem__("p_star_q", "1/2"), "P3_MH_PSTAR")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["axis2_weight_modifying_consolidation"]["reference_mixture_half"].__setitem__("excess_true_brier_q", "0"), "P3_MH_EX_VAL")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["five_gate_consolidation_fixed_point"].__setitem__("all_five_gates_pass", False), "P3_FP_PASS")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"].__setitem__("all_five_ablations_rejected", False), "P3_ABLS_FLAG")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["borromean_five_gate_ablations"].pop("ablate_g5_vram_spill_violation"), "P3_ABLS_KEYS")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["borromean_five_gate_ablations"]["ablate_g1_divergent_sleep_loop"].__setitem__("all_five_gates_pass", True), "P3_ABL_NOT_REJECTED")
        _tamper(lambda p: p["pillar_3_sleep_trilogy_consolidation"]["borromean_five_gate_ablations"]["ablate_g1_divergent_sleep_loop"].__setitem__("gate2_forgetting_budgeted", False), "P3_ABL_GATE_PATTERN")

        # Pillar 4 exhaustive guards & BoolOp subconditions
        _tamper(lambda p: p.__setitem__("pillar_4_provenance_and_lean4", []), "P4_NOT_DICT")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"].__setitem__("zero_dataset_copies_in_expedition", False), "P4_NO_COPIES")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"].__setitem__("wave6_snapshot_count", 11), "P4_W6_LEN")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["wave6_snapshot_pins"].pop(), "P4_W6_LEN")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["wave6_snapshot_pins"][0].__setitem__("filename", ""), "P4_W6_NAME")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["wave6_snapshot_pins"][0].__setitem__("filename", 123), "P4_W6_NAME")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["wave6_snapshot_pins"][0].__setitem__("bytes", 0), "P4_W6_BYTES_POS")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["wave6_snapshot_pins"][0].__setitem__("sha256", "Z" * 64), "P4_W6_SHA")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["wave6_snapshot_pins"][0].__setitem__("sha256", 123), "P4_W6_SHA")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"].__setitem__("upstream_cert_count", 9), "P4_UP_LEN")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["upstream_cert_pins"].pop(), "P4_UP_LEN")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["upstream_cert_pins"][0].__setitem__("track_id", 123), "P4_UP_FIELDS")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["upstream_cert_pins"][0].__setitem__("relative_ref", 123), "P4_UP_FIELDS")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["upstream_cert_pins"][0].__setitem__("bytes", 0), "P4_UP_BYTES_POS")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["upstream_cert_pins"][0].__setitem__("sha256", "0"), "P4_UP_SHA")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["upstream_cert_pins"][0].__setitem__("sha256", 123), "P4_UP_SHA")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["lean4_companion"].__setitem__("file", "X"), "P4_LEAN_META")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["lean4_companion"].__setitem__("toolchain", "X"), "P4_LEAN_META")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["lean4_companion"].__setitem__("sha256", "0" * 64), "P4_LEAN_SHA")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["lean4_companion"].__setitem__("sha256", "Z" * 64), "P4_LEAN_SHA")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["lean4_companion"].__setitem__("sha256", 123), "P4_LEAN_SHA")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["lean4_companion"].__setitem__("theorem_count", 17), "P4_LEAN_COUNT")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["lean4_companion"].__setitem__("all_theorems_universally_quantified", False), "P4_LEAN_UNIV")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["lean4_companion"].__setitem__("theorems", []), "P4_LEAN_THMS")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["lean4_companion"].__setitem__("allowed_axioms", ["sorryAx"]), "P4_LEAN_AXIOMS")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["novelty_honesty_law4"].__setitem__("novelty_tier", "N2"), "P4_NOV_TIER")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["novelty_honesty_law4"].__setitem__("n0_prior_art_anchored", False), "P4_NOV_FLAGS")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["novelty_honesty_law4"].__setitem__("n1_exact_synthesis_verified", False), "P4_NOV_FLAGS")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["novelty_honesty_law4"].__setitem__("n2_claims", 1), "P4_NOV_N2")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["novelty_honesty_law4"].__setitem__("n2_claims", "0"), "P4_NOV_N2")
        _tamper(lambda p: p["pillar_4_provenance_and_lean4"]["novelty_honesty_law4"].__setitem__("n2_claims", False), "UNEXPECTED_BOOL_FIELD")
        _tamper(lambda p: p["pillar_1_privileged_neuron_basis"]["householder_reflection_dpi_witness"]["axis_d_q"].__setitem__(0, True), "UNEXPECTED_BOOL_ITEM")

    def test_06_lean_r10_static_live_and_zero_skip_ci(self) -> None:
        clean_src = (
            "-- sorry in line comment\n"
            "/- /- admit \"quoted\" 'x' \u00abbad\u00bb nested -/ -/\n"
            "theorem ok : 1 = 1 := by decide\n"
            "theorem ok_f : 1 = 1 := by decide (native := false)\n"
            "theorem ok_bf : 1 = 1 := by decide (native := Bool.false)\n"
            "theorem ok_cfg : 1 = 1 := by decide (config := { native := false })\n"
            "#print axioms ok\n"
        )
        self.assertTrue(verifier.audit_lean_source_static(clean_src)["clean"])
        self.assertTrue(verifier.audit_lean_source_static("-- eof no newline")["clean"])
        self.assertTrue(verifier.audit_lean_source_static("def x := 1 / 2 - 1\n")["clean"])

        with self.assertRaisesRegex(ValueError, "LEAN_SOURCE_NOT_STR"):
            verifier.audit_lean_source_static(123)  # type: ignore[arg-type]

        for snippet, code in (
            ('def _a : String := s!"x"\n#eval 1\ndef _b : Char := \'"\'\n', "LEAN_QUOTE_OR_GUILLEMET_FORBIDDEN"),
            ('def _a : String := s!"x"\naxiom fake : False\ndef _b : Char := \'"\'\n', "LEAN_FORBIDDEN_KEYWORD"),
            ('def _r := r#"""#\n', "LEAN_QUOTE_OR_GUILLEMET_FORBIDDEN"),
            ("set_option \u00abdebug\u00bb.\u00abskipKernelTC\u00bb true\n", "LEAN_SKIP_KERNEL_TC"),
            ("-- harmless comment\ntheorem t : False := by sorry\n", "LEAN_FORBIDDEN_KEYWORD"),
            ("theorem t : False := by sorry", "LEAN_FORBIDDEN_KEYWORD"),
            ("theorem t : False := by admit", "LEAN_FORBIDDEN_KEYWORD"),
            ("axiom bogus : False", "LEAN_FORBIDDEN_KEYWORD"),
            ("unsafe def u := 1", "LEAN_FORBIDDEN_KEYWORD"),
            ("def x := Lean.ofReduceNat", "LEAN_FORBIDDEN_KEYWORD"),
            ("def x := Lean.Meta.mkSorry", "LEAN_FORBIDDEN_KEYWORD"),
            ("declare_syntax_cat mycat", "LEAN_FORBIDDEN_KEYWORD"),
            ("notation myop => 0", "LEAN_FORBIDDEN_KEYWORD"),
            ("def f : Nat := dbg_trace 1; 0", "LEAN_FORBIDDEN_KEYWORD"),
            ("def f : Nat := throwError 0", "LEAN_FORBIDDEN_KEYWORD"),
            ("initialize pure ()", "LEAN_FORBIDDEN_KEYWORD"),
            ("builtin_initialize pure ()", "LEAN_FORBIDDEN_KEYWORD"),
            ("opaque f : Nat", "LEAN_FORBIDDEN_KEYWORD"),
            ("run_cmd pure ()", "LEAN_FORBIDDEN_KEYWORD"),
            ("run_meta pure ()", "LEAN_FORBIDDEN_KEYWORD"),
            ("partial def p (n : Nat) : Nat := p n", "LEAN_PARTIAL_DECL"),
            ("theorem t : True := by decide +native", "LEAN_DECIDE_NATIVE"),
            ("theorem t : True := by decide -revert +native", "LEAN_DECIDE_NATIVE"),
            ("theorem t : True := by decide +revert +native", "LEAN_DECIDE_NATIVE"),
            ("theorem t : True := by decide -kernel +native", "LEAN_DECIDE_NATIVE"),
            ("theorem t : True := by decide (revert := true) +native", "LEAN_DECIDE_NATIVE"),
            ("theorem t : True := by decide +revert (config := { native })", "LEAN_DECIDE_NATIVE"),
            ("theorem t : True := by decide (revert := false) (config := { native })", "LEAN_DECIDE_NATIVE"),
            ("theorem t : True := by decide +revert (config := { ({} : _) with native })", "LEAN_DECIDE_NATIVE"),
            ("theorem t : True := by decide (config := myCfg)", "LEAN_DECIDE_NATIVE"),
            ("theorem t : True := by decide (config := { native := !false })", "LEAN_DECIDE_NATIVE"),
            ("theorem t : 1 + 1 = 2 := by decide (native := false || true)", "LEAN_DECIDE_NATIVE"),
            ("theorem t : 1 + 1 = 2 := by decide (native := false == false)", "LEAN_DECIDE_NATIVE"),
            ("theorem t : 1 + 1 = 2 := by decide (native := false != true)", "LEAN_DECIDE_NATIVE"),
            ("theorem t : 1 + 1 = 2 := by decide (native := false.not)", "LEAN_DECIDE_NATIVE"),
            ("theorem t : 1 + 1 = 2 := by decide (native := false\n  || true)", "LEAN_DECIDE_NATIVE"),
            ("theorem t : 1 + 1 = 2 := by decide (native := Bool.false || true)", "LEAN_DECIDE_NATIVE"),
            ("def cfg : DecideConfig := {}", "LEAN_DECIDE_NATIVE"),
            ("set_option debug.skipKernelTC true", "LEAN_SKIP_KERNEL_TC"),
            ("set_option debug.terminalTacticsAsSorry true", "LEAN_SKIP_KERNEL_TC"),
            ("#eval 1 + 1", "LEAN_EVAL_OR_PRINT_SPOOF"),
            ("#guard_msgs in #eval 1", "LEAN_EVAL_OR_PRINT_SPOOF"),
            ("#print Nat.add", "LEAN_EVAL_OR_PRINT_SPOOF"),
            ("#print axioms example", "LEAN_EVAL_OR_PRINT_SPOOF"),
            ("#exit", "LEAN_EVAL_OR_PRINT_SPOOF"),
            ("@[csimp] theorem bad : 1 = 1 := rfl", "LEAN_ATTR_TRUST_ESCAPE"),
            ("attribute [implemented_by g] f", "LEAN_ATTR_TRUST_ESCAPE"),
            ("import Lean", "LEAN_NON_ZERO_IMPORTS"),
            ("/- unterminated comment", "LEAN_UNTERMINATED_BLOCK_COMMENT"),
        ):
            r = verifier.audit_lean_source_static(snippet)
            self.assertFalse(r["clean"], msg=f"Expected failure on {snippet!r}")
            self.assertTrue(any(f.startswith(code) for f in r["findings"]), msg=f"{snippet!r} -> {r}")

        lean_file = TRACK_DIR / oracle.LEAN_FILE_NAME
        if _lean_available():
            live = verifier.verify_lean_proof(lean_file, enforce_sha256=True)
            self.assertTrue(live["static_clean"])
            self.assertEqual(live["theorems_verified"], 18)
            self.assertEqual(live["zero_axiom_theorems"], 4)
            self.assertEqual(live["axioms_used"], ["propext"])
        else:
            with self.assertRaisesRegex(ValueError, "LEAN_BINARY_UNAVAILABLE"):
                verifier.verify_lean_proof(lean_file, enforce_sha256=True)

        with tempfile.TemporaryDirectory(prefix="s94_lean_") as td:
            d = Path(td).resolve()
            fake_bin = d / "lean"
            fake_bin.write_text("#!/bin/sh\n", encoding="utf-8")
            os.chmod(fake_bin, 0o700)
            noexec = d / "lean_nx"
            noexec.write_text("#!/bin/sh\n", encoding="utf-8")
            os.chmod(noexec, 0o600)

            with mock.patch.dict(os.environ, {"ALETHEIA_LEAN_BIN": str(fake_bin)}, clear=True):
                self.assertEqual(verifier.resolve_lean_binary(), str(fake_bin))
            with mock.patch.dict(os.environ, {"ALETHEIA_LEAN_BIN": str(noexec)}, clear=True):
                with self.assertRaisesRegex(ValueError, "LEAN_BINARY_UNAVAILABLE"):
                    verifier.resolve_lean_binary()
            with mock.patch.dict(os.environ, {"ALETHEIA_LEAN_BIN": str(d)}, clear=True):
                with self.assertRaisesRegex(ValueError, "LEAN_BINARY_UNAVAILABLE"):
                    verifier.resolve_lean_binary()
            with mock.patch.dict(os.environ, {"HOME": str(d)}, clear=True):
                with mock.patch("shutil.which", return_value=None):
                    with self.assertRaisesRegex(ValueError, "LEAN_BINARY_UNAVAILABLE"):
                        verifier.resolve_lean_binary()
                    local_bin = d / ".local" / "bin"
                    local_bin.mkdir(parents=True)
                    hl_lean = local_bin / "lean"
                    hl_lean.mkdir()
                    with self.assertRaisesRegex(ValueError, "LEAN_BINARY_UNAVAILABLE"):
                        verifier.resolve_lean_binary()
                    hl_lean.rmdir()
                    hl_lean.write_text("#!/bin/sh\n", encoding="utf-8")
                    os.chmod(hl_lean, 0o600)
                    with self.assertRaisesRegex(ValueError, "LEAN_BINARY_UNAVAILABLE"):
                        verifier.resolve_lean_binary()
                    os.chmod(hl_lean, 0o700)
                    self.assertEqual(verifier.resolve_lean_binary(), str(hl_lean))
            with mock.patch.dict(os.environ, {}, clear=True):
                with mock.patch("shutil.which", return_value=None):
                    with self.assertRaisesRegex(ValueError, "LEAN_BINARY_UNAVAILABLE"):
                        verifier.resolve_lean_binary()

            # verify_lean_proof error guards
            with self.assertRaisesRegex(ValueError, "INVALID_ENFORCE_SHA256_FLAG"):
                verifier.verify_lean_proof(lean_file, enforce_sha256=0)  # type: ignore[arg-type]
            crlf_l = d / "c.lean"
            crlf_l.write_bytes(b"theorem t : True := trivial\r\n")
            with self.assertRaisesRegex(ValueError, "CRLF_FORBIDDEN"):
                verifier.verify_lean_proof(crlf_l, enforce_sha256=False)
            badu_l = d / "u.lean"
            badu_l.write_bytes(b"\xff\xfe")
            with self.assertRaisesRegex(ValueError, "LEAN_INVALID_UTF8"):
                verifier.verify_lean_proof(badu_l, enforce_sha256=False)
            triv_l = d / "t.lean"
            triv_l.write_text("theorem t : True := trivial\n#print axioms t\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "LEAN_SHA256_MISMATCH"):
                verifier.verify_lean_proof(triv_l, enforce_sha256=True)
            bad_st = d / "bad.lean"
            bad_st.write_text("#eval 1\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "LEAN_STATIC_AUDIT_FAILED"):
                verifier.verify_lean_proof(bad_st, enforce_sha256=False)

            # Mocked lean subprocess edge cases (work with OR without live lean)
            with mock.patch.object(verifier, "resolve_lean_binary", return_value="lean"):
                for cp, code in (
                    (subprocess.CompletedProcess(["lean"], 1, stdout="", stderr="err"), "LEAN_COMPILE_FAILED"),
                    (subprocess.CompletedProcess(["lean"], 0, stdout="", stderr="warn"), "LEAN_NONEMPTY_STDERR"),
                    (subprocess.CompletedProcess(["lean"], 0, stdout="", stderr=""), "LEAN_NO_THEOREMS_VERIFIED"),
                    (subprocess.CompletedProcess(["lean"], 0, stdout="weird\n", stderr=""), "LEAN_UNEXPECTED_STDOUT_LINE"),
                    (subprocess.CompletedProcess(["lean"], 0, stdout="  indented\n", stderr=""), "LEAN_UNEXPECTED_STDOUT_LINE"),
                    (subprocess.CompletedProcess(["lean"], 0, stdout="'t' does not depend on any axioms\n't' does not depend on any axioms\n", stderr=""), "LEAN_DUPLICATE_THEOREM"),
                    (subprocess.CompletedProcess(["lean"], 0, stdout="'t' depends on axioms: [propext]\n't' depends on axioms: [propext]\n", stderr=""), "LEAN_DUPLICATE_THEOREM"),
                    (subprocess.CompletedProcess(["lean"], 0, stdout="'t' depends on axioms: [Classical.choice]\n", stderr=""), "LEAN_FORBIDDEN_AXIOM"),
                ):
                    with mock.patch("subprocess.run", return_value=cp):
                        with self.assertRaisesRegex(ValueError, code):
                            verifier.verify_lean_proof(triv_l, enforce_sha256=False)

                short_cp = subprocess.CompletedProcess(["lean"], 0, stdout="'Wrong.thm' does not depend on any axioms\n", stderr="")
                with mock.patch("subprocess.run", return_value=short_cp):
                    with self.assertRaisesRegex(ValueError, "LEAN_THEOREM_LIST_MISMATCH"):
                        verifier.verify_lean_proof(lean_file, enforce_sha256=True)

                wrapped_lines = []
                for idx, thm in enumerate(oracle.EXPECTED_LEAN_THEOREMS):
                    if idx == 0:
                        wrapped_lines.append(f"'{thm}' depends on axioms:\n  [propext]")
                    else:
                        wrapped_lines.append(f"'{thm}' does not depend on any axioms")
                wrap_cp = subprocess.CompletedProcess(["lean"], 0, stdout="\n".join(wrapped_lines) + "\n", stderr="")
                with mock.patch("subprocess.run", return_value=wrap_cp):
                    res_w = verifier.verify_lean_proof(lean_file, enforce_sha256=True)
                    self.assertEqual(res_w["theorems_verified"], 18)

    def test_07_verify_pins_and_cli_modes(self) -> None:
        with tempfile.TemporaryDirectory(prefix="s94_cli_") as td:
            d = Path(td).resolve()
            exp_r = d / "exp"
            w6_r = d / "w6"
            (exp_r / "t1").mkdir(parents=True)
            w6_r.mkdir()
            b1 = b'{"ok":true}\n'
            b2 = b"wave6 snapshot\n"
            (exp_r / "t1" / "c.json").write_bytes(b1)
            (w6_r / "s.txt").write_bytes(b2)
            fake_up = ({"track_id": "S1", "relative_ref": "t1/c.json", "bytes": len(b1), "sha256": hashlib.sha256(b1).hexdigest()},)
            fake_w6 = ({"portal": "P98", "filename": "s.txt", "bytes": len(b2), "sha256": hashlib.sha256(b2).hexdigest()},)

            with self.assertRaisesRegex(ValueError, "NO_PIN_ROOT_SPECIFIED"):
                verifier.verify_pins_on_disk()
            with self.assertRaisesRegex(ValueError, "EXPEDITION_ROOT_INVALID"):
                verifier.verify_pins_on_disk(expedition_root=d / "no_exp")
            with self.assertRaisesRegex(ValueError, "WAVE6_ROOT_INVALID"):
                verifier.verify_pins_on_disk(wave6_root=d / "no_w6")

            with mock.patch.object(verifier, "UPSTREAM_CERT_PINS", fake_up), mock.patch.object(verifier, "WAVE6_SNAPSHOT_PINS", fake_w6):
                r_both = verifier.verify_pins_on_disk(expedition_root=exp_r, wave6_root=w6_r)
                self.assertEqual(r_both["upstream_certs_verified"], 1)
                self.assertEqual(r_both["wave6_snapshots_verified"], 1)

                out_b = io.BytesIO()
                with mock.patch.object(sys, "stdout", type("FO", (), {"buffer": out_b})()):
                    self.assertEqual(verifier.main(["--verify-pins", "--expedition-root", str(exp_r), "--wave6-root", str(w6_r), "--json"]), 0)
                self.assertEqual(json.loads(out_b.getvalue().decode())["status"], "PINS_VERIFIED")
                self.assertEqual(verifier.main(["--verify-pins", "--expedition-root", str(exp_r)]), 0)

                (exp_r / "t1" / "c.json").write_bytes(b'{"ok":false}\n')
                with self.assertRaisesRegex(ValueError, "UPSTREAM_BYTES_MISMATCH"):
                    verifier.verify_pins_on_disk(expedition_root=exp_r)
                (exp_r / "t1" / "c.json").write_bytes(b'{"no":true}\n')
                with self.assertRaisesRegex(ValueError, "UPSTREAM_SHA_MISMATCH"):
                    verifier.verify_pins_on_disk(expedition_root=exp_r)

                (w6_r / "s.txt").write_bytes(b"short\n")
                with self.assertRaisesRegex(ValueError, "WAVE6_BYTES_MISMATCH"):
                    verifier.verify_pins_on_disk(wave6_root=w6_r)
                (w6_r / "s.txt").write_bytes(b"wave6 snapsh0t\n")
                with self.assertRaisesRegex(ValueError, "WAVE6_SHA_MISMATCH"):
                    verifier.verify_pins_on_disk(wave6_root=w6_r)

            # CLI --write, --check, --standalone, --verify-lean, and error path
            out_p = d / "out.json"
            wb = io.BytesIO()
            with mock.patch.object(sys, "stdout", type("FO", (), {"buffer": wb})()):
                self.assertEqual(verifier.main(["--write", str(out_p), "--json"]), 0)
            self.assertEqual(json.loads(wb.getvalue().decode())["status"], "WRITTEN")
            self.assertEqual(verifier.main(["--write", str(out_p)]), 0)

            cb = io.BytesIO()
            with mock.patch.object(sys, "stdout", type("FO", (), {"buffer": cb})()):
                self.assertEqual(verifier.main(["--check", str(out_p), "--json"]), 0)
            self.assertEqual(json.loads(cb.getvalue().decode())["status"], "PASS")
            self.assertEqual(verifier.main(["--check", str(out_p)]), 0)

            sb = io.BytesIO()
            with mock.patch.object(sys, "stdout", type("FO", (), {"buffer": sb})()):
                self.assertEqual(verifier.main(["--standalone", "--json"]), 0)
            self.assertEqual(sb.getvalue(), out_p.read_bytes())

            lean_stub = {"lean_file": oracle.LEAN_FILE_NAME, "theorems_verified": 18, "static_clean": True}
            with mock.patch.object(verifier, "verify_lean_proof", return_value=lean_stub):
                lb = io.BytesIO()
                with mock.patch.object(sys, "stdout", type("FO", (), {"buffer": lb})()):
                    self.assertEqual(verifier.main(["--verify-lean", str(TRACK_DIR / oracle.LEAN_FILE_NAME), "--json"]), 0)
                self.assertEqual(json.loads(lb.getvalue().decode())["theorems_verified"], 18)
                self.assertEqual(verifier.main(["--verify-lean", str(TRACK_DIR / oracle.LEAN_FILE_NAME)]), 0)

            eb = io.StringIO()
            with redirect_stderr(eb):
                self.assertEqual(verifier.main(["--check", str(d / "missing.json")]), 2)
            self.assertIn("ERROR:", eb.getvalue())


if __name__ == "__main__":
    unittest.main()
