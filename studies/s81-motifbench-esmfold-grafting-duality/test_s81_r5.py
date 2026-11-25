"""Adversarial R1-R5 + R10+ verification suite for Track S81 R2 (MotifBench <-> Grafting Duality).

Fast unit, oracle, Table-4 case-list pinning, mutation-kill, Zone-B security,
$PWD-symlink, and R10+ Lean static bypass tests run first (test_01..test_11);
live Lean 4.36.0 kernel + live red-team bypass regressions run last (test_90).
"""

from __future__ import annotations

from decimal import Decimal
from fractions import Fraction
import io
import json
import os
import stat
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import s81_motifbench_grafting_oracle as oracle
import verify_s81_motifbench as verifier

DISK_CERT = os.path.join(HERE, "s81_motifbench_certificate.json")
DISK_LEAN = os.path.join(HERE, "MotifScaffoldingDuality.lean")


class TestS81MotifBenchR5(unittest.TestCase):
    # ------------------------------------------------------------------
    # Fast Oracle & Helper Invariant Tests (01..02)
    # ------------------------------------------------------------------

    def test_01_all_five_oracles_exact_values(self) -> None:
        res = oracle.run_all_s81_oracles()
        self.assertEqual(len(res), 5)

        o1 = res["oracle_1_motifbench_table3"]
        self.assertEqual(o1["n_cases"], 30)
        self.assertEqual(o1["esm_sum_unique"], 267)
        self.assertEqual(o1["esm_mean_unique_q"], "89/10")
        self.assertEqual(o1["af2_sum_unique"], 228)
        self.assertEqual(o1["af2_mean_unique_q"], "38/5")
        self.assertEqual(o1["esm_solved_total"], 16)
        self.assertEqual(o1["af2_solved_total"], 12)
        self.assertEqual(o1["esm_score_table3_q"], "337100261/11785536")
        self.assertEqual(o1["af2_score_table3_q"], "160304/7137")
        self.assertEqual(o1["table3_gap_q"], "19133925919/3115310016")
        self.assertEqual(o1["orphan_esm_solved"], 6)
        self.assertEqual(o1["orphan_af2_solved"], 4)
        self.assertEqual(
            o1["table5_contingency"],
            {"both_pass": 14, "ref_only": 6, "rfdiff_only": 2, "neither_pass": 8},
        )
        self.assertEqual(
            o1["ref_only_cases"],
            ["10:7WRK", "23:1MPY", "25:2RKX", "26:3B5V", "27:4XOJ", "29:6CPA"],
        )
        self.assertEqual(o1["rfdiff_only_cases"], ["18:7MQQ", "19:7MQQ"])
        self.assertEqual(
            o1["neither_pass_cases"],
            ["3:2CGA", "8:7AD5", "12:4JHW", "13:4JHW", "20:7UWL", "21:1B73", "24:1QY3", "30:7UWL"],
        )

        o2 = res["oracle_2_se3_chirality_gram"]
        self.assertEqual(o2["pairwise_sq_distance_checks"], 16)
        self.assertEqual(o2["mirror_pairwise_distance_error"], 0)
        self.assertEqual(o2["signed_volume_orig"], -16)
        self.assertEqual(o2["signed_volume_so3_rot"], -16)
        self.assertEqual(o2["signed_volume_mirror"], 16)
        self.assertEqual(o2["kabsch_det_H"], -64)
        self.assertEqual(o2["kabsch_r_opt_det"], 1)
        self.assertEqual(o2["se3_min_msd_unit_radius"], "4/3")

        o3 = res["oracle_3_multisegment_dof"]
        self.assertEqual(o3["group1_to_group3_collapse_factor_q"], "7/2")
        self.assertEqual(o3["high_dof_k_ge_5_cases"], ["1MPY", "2RKX", "3B5V", "6CPA"])
        self.assertEqual(o3["high_dof_k_ge_5_min_dof"], 24)
        self.assertEqual(o3["high_dof_k_ge_5_max_dof"], 42)
        self.assertEqual(o3["high_dof_k_ge_5_solved"], 0)

        o4 = res["oracle_4_proxy_and_gpt6_stats"]
        self.assertEqual([c["pdb"] for c in o4["esm_positive_af2_zero_cases"]], ["1LDB", "5ZE9", "7A8S", "7DGW"])
        self.assertEqual(o4["gpt6_hit_rate_q"], "5/46")
        self.assertEqual(o4["gpt6_score_z2_vs_5pct_q"], "10206/437")
        self.assertEqual(o4["bayes_single_oracle_ppv_q"], "4/23")
        self.assertEqual(o4["bayes_dual_oracle_ppv_q"], "32/51")
        self.assertEqual(o4["bayes_dual_ppv_gain_q"], "184/51")

        o5 = res["oracle_5_portal77_duality_s31"]
        self.assertEqual(o5["granite_d_ext"], 3700)
        self.assertEqual(o5["granite_gamma_nl_sq_q"], "128/185")
        self.assertTrue(o5["rmsnorm_gauge_exact_cancel"])
        self.assertEqual(o5["orthogonal_cross_ip"], 0)
        self.assertEqual(o5["ky_fan_test_err_q"], "10/3")
        self.assertEqual(o5["r3_4vec_gram_det"], "0")
        self.assertEqual(o5["r4_extended_4vec_gram_det"], "1")

    def test_02_oracle_helper_edge_cases(self) -> None:
        with self.assertRaises(oracle.OracleError):
            oracle._require(False, "fail")
        self.assertEqual(oracle.motifbench_score_exact([1], 5), Fraction(35, 2))
        self.assertEqual(oracle.motifbench_score_exact([5], 5), Fraction(105, 2))
        self.assertEqual(oracle.motifbench_score_exact([50], 5), Fraction(1050, 11))
        self.assertEqual(oracle.motifbench_score_exact([0], 1), Fraction(0))
        with self.assertRaisesRegex(oracle.OracleError, "non-empty"):
            oracle.motifbench_score_exact([], 5)
        with self.assertRaisesRegex(oracle.OracleError, "alpha must be positive"):
            oracle.motifbench_score_exact([1], 0)
        with self.assertRaisesRegex(oracle.OracleError, "nonnegative"):
            oracle.motifbench_score_exact([-1], 5)

        lo0, hi0 = oracle._wilson_ci_exact_bracket(0, 10, Fraction(196, 100), 1000)
        self.assertLessEqual(lo0, Fraction(0))
        self.assertGreater(hi0, Fraction(0))
        lo10, hi10 = oracle._wilson_ci_exact_bracket(10, 10, Fraction(196, 100), 1000)
        self.assertGreater(lo10, Fraction(0))
        self.assertGreaterEqual(hi10, Fraction(1))
        lo_z0, hi_z0 = oracle._wilson_ci_exact_bracket(5, 10, Fraction(0, 1), 100)
        self.assertEqual(lo_z0, Fraction(1, 2))
        self.assertEqual(hi_z0, Fraction(1, 2))
        with self.assertRaisesRegex(oracle.OracleError, "0 <= k <= n"):
            oracle._wilson_ci_exact_bracket(-1, 10, Fraction(1, 1))
        with self.assertRaisesRegex(oracle.OracleError, "0 <= k <= n"):
            oracle._wilson_ci_exact_bracket(11, 10, Fraction(1, 1))
        with self.assertRaisesRegex(oracle.OracleError, "Sample size n must be positive"):
            oracle._wilson_ci_exact_bracket(0, 0, Fraction(1, 1))

        self.assertEqual(oracle._det_q([[Fraction(0), Fraction(1)], [Fraction(1), Fraction(0)]]), Fraction(-1))
        self.assertEqual(oracle._det_q([[Fraction(1), Fraction(2)], [Fraction(3), Fraction(4)]]), Fraction(-2))
        self.assertEqual(oracle._det_q([[Fraction(0), Fraction(0)], [Fraction(0), Fraction(1)]]), Fraction(0))

    # ------------------------------------------------------------------
    # Canonical Rational & Decimal Parser Tests (03)
    # ------------------------------------------------------------------

    def test_03_parse_q_and_dec_canonical_dos_safe(self) -> None:
        self.assertEqual(verifier.parse_q("0"), Fraction(0))
        self.assertEqual(verifier.parse_q("9"), Fraction(9))
        self.assertEqual(verifier.parse_q("-5/46"), Fraction(-5, 46))
        self.assertEqual(verifier.parse_q("9" * 1000), Fraction(int("9" * 1000), 1))
        self.assertEqual(verifier.parse_q("1/" + "9" * 1000), Fraction(1, int("9" * 1000)))

        for bad in (
            123,
            None,
            "",
            " 1",
            "1 ",
            "+1",
            "-0",
            "00",
            "01",
            "-01",
            "1/02",
            "3/1",
            "2/4",
            "0/2",
            "-2/4",
            "1/2/3",
            "1/0",
            "1/-2",
            "1/",
            "/2",
            "1.5",
            "\u0661",
            "1/\u0662",
            "/",
            ":",
            "9" * 1001,
            "1/" + "9" * 1001,
            "9" * 5001,
        ):
            with self.assertRaises(verifier.VerifyError, msg=f"Should reject {bad!r}"):
                verifier.parse_q(bad)

        self.assertEqual(verifier._parse_dec_str("0.1234"), Decimal("0.1234"))
        self.assertEqual(verifier._parse_dec_str("9" * 1000), Decimal("9" * 1000))
        for bad_d in (123, "FORGED", "NaN", "01.2", "1.", "9" * 1001):
            with self.assertRaises(verifier.VerifyError, msg=f"Should reject dec {bad_d!r}"):
                verifier._parse_dec_str(bad_d)

    # ------------------------------------------------------------------
    # Certificate Generation, 4 Surfaces (CLI/FR1/FR0/SEC), & Zone-B I/O (04..07)
    # ------------------------------------------------------------------

    def test_04_certificate_write_check_surfaces_and_tamper_rejection(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            cpath = os.path.join(td, "cert.json")
            wres = verifier.write_certificate_file(cpath)
            self.assertTrue(wres["ok"])
            self.assertEqual(stat.S_IMODE(os.lstat(cpath).st_mode), 0o600)
            wres2 = verifier.write_certificate_file(cpath)
            self.assertEqual(wres2["payload_sha256"], wres["payload_sha256"])

            cres_fr1 = verifier.verify_certificate_file(cpath, full_replay=True)
            cres_fr0 = verifier.verify_certificate_file(cpath, full_replay=False)
            self.assertEqual(cres_fr1["payload_sha256"], cres_fr0["payload_sha256"])

            with self.assertRaisesRegex(verifier.VerifyError, "full_replay must be a bool"):
                verifier.verify_certificate_file(os.path.join(td, "missing.json"), full_replay=0)  # type: ignore[arg-type]

            cert = verifier.build_certificate()
            self.assertTrue(verifier.audit_certificate_semantics(cert)["semantic_ok"])

            with self.assertRaisesRegex(verifier.VerifyError, "full_replay must be a bool"):
                verifier.verify_certificate_dict(cert, full_replay=0)  # type: ignore[arg-type]
            with self.assertRaisesRegex(verifier.VerifyError, "schema keys or type mismatch"):
                verifier.verify_certificate_dict([])
            bad_keys = dict(cert)
            bad_keys["extra"] = 1
            with self.assertRaisesRegex(verifier.VerifyError, "schema keys or type mismatch"):
                verifier.verify_certificate_dict(bad_keys)
            with self.assertRaisesRegex(verifier.VerifyError, "schema_version mismatch"):
                verifier.verify_certificate_dict(dict(cert, schema_version="wrong"))
            with self.assertRaisesRegex(verifier.VerifyError, "leaf field type mismatch"):
                verifier.verify_certificate_dict(dict(cert, payload_sha256=123))
            with self.assertRaisesRegex(verifier.VerifyError, "lowercase 64-char hex"):
                verifier.verify_certificate_dict(dict(cert, payload_sha256="A" * 64))
            with self.assertRaisesRegex(verifier.VerifyError, "schema keys or type mismatch"):
                verifier.verify_certificate_dict(dict(cert, payload="bad"))
            with self.assertRaisesRegex(verifier.VerifyError, "digest mismatch"):
                verifier.verify_certificate_dict(dict(cert, payload_sha256="0" * 64))

            # Tampered re-signed payload caught by FR1 recomputation (passes FR0 when invariants hold)
            tampered_payload = json.loads(json.dumps(cert["payload"]))
            tampered_payload["oracles"]["oracle_1_motifbench_table3"]["esm_sum_unique"] = 266
            resigned = {
                "schema_version": verifier.SCHEMA_VERSION,
                "payload_sha256": verifier._compute_payload_sha256(tampered_payload),
                "payload": tampered_payload,
            }
            self.assertTrue(verifier.verify_certificate_dict(resigned, full_replay=False)["ok"])
            with self.assertRaisesRegex(verifier.VerifyError, "clean-room recomputation"):
                verifier.verify_certificate_dict(resigned, full_replay=True)

            bad_utf8 = os.path.join(td, "bad_utf8.json")
            with open(bad_utf8, "wb") as f:
                f.write(b"\xff\xfe")
            with self.assertRaises(verifier.VerifyError):
                verifier.verify_certificate_file(bad_utf8)
            bad_json = os.path.join(td, "bad.json")
            with open(bad_json, "w", encoding="utf-8") as f:
                f.write("{broken")
            with self.assertRaises(verifier.VerifyError):
                verifier.verify_certificate_file(bad_json)

    def test_05_disk_cert_matches_recomputation_and_ci_mode(self) -> None:
        self.assertTrue(os.path.isfile(DISK_CERT), "Disk certificate must exist")
        mode = stat.S_IMODE(os.lstat(DISK_CERT).st_mode)
        self.assertIn(mode, (0o600, 0o644))
        res = verifier.verify_certificate_file(DISK_CERT)
        self.assertTrue(res["ok"])
        self.assertEqual(res["oracles_passed"], 5)

    def test_06_zone_b_path_and_io_adversarial(self) -> None:
        with self.assertRaisesRegex(verifier.VerifyError, "non-empty string"):
            verifier._validate_path("")
        with self.assertRaisesRegex(verifier.VerifyError, "non-empty string"):
            verifier._validate_path(42)
        with self.assertRaisesRegex(verifier.VerifyError, "Path must name a file"):
            verifier._open_parent_dir_fd("/")
        for bad_p in ("", 42, "bad\x00path", "bad\ud800surr"):
            with self.assertRaises(verifier.VerifyError):
                verifier.verify_certificate_file(bad_p)  # type: ignore[arg-type]
            with self.assertRaises(verifier.VerifyError):
                verifier.write_certificate_file(bad_p)  # type: ignore[arg-type]
            with self.assertRaises(verifier.VerifyError):
                verifier.verify_lean_file(bad_p)  # type: ignore[arg-type]

        with tempfile.TemporaryDirectory() as td:
            real_f = os.path.join(td, "real.json")
            verifier.write_certificate_file(real_f)
            real_bytes = verifier._read_bytes_safe(real_f)
            self.assertEqual(verifier._read_bytes_safe(real_f, max_bytes=len(real_bytes)), real_bytes)

            sym = os.path.join(td, "sym.json")
            os.symlink(real_f, sym)
            with self.assertRaises(verifier.VerifyError):
                verifier._read_bytes_safe(sym)
            with self.assertRaisesRegex(verifier.VerifyError, "non-regular or hard-linked"):
                verifier._write_bytes_atomic_safe(sym, b"x")

            with self.assertRaises(verifier.VerifyError):
                verifier._read_bytes_safe(td)

            fifo = os.path.join(td, "pipe.fifo")
            os.mkfifo(fifo)
            with self.assertRaises(verifier.VerifyError):
                verifier._read_bytes_safe(fifo)
            with self.assertRaisesRegex(verifier.VerifyError, "non-regular or hard-linked"):
                verifier._write_bytes_atomic_safe(fifo, b"x")

            hard = os.path.join(td, "hard.json")
            os.link(real_f, hard)
            with self.assertRaises(verifier.VerifyError):
                verifier._read_bytes_safe(hard)
            with self.assertRaisesRegex(verifier.VerifyError, "non-regular or hard-linked"):
                verifier._write_bytes_atomic_safe(hard, b"x")
            os.unlink(hard)

            with mock.patch("os.lstat", side_effect=PermissionError("EACCES")):
                with self.assertRaisesRegex(verifier.VerifyError, "Cannot inspect existing target file"):
                    verifier._write_bytes_atomic_safe(os.path.join(td, "perm.json"), b"x")

            with self.assertRaisesRegex(verifier.VerifyError, "exceeds maximum permitted size"):
                verifier._read_bytes_safe(real_f, max_bytes=len(real_bytes) - 1)
            fake_st = os.lstat(real_f)
            small_st = mock.MagicMock(st_mode=fake_st.st_mode, st_nlink=1, st_size=4)
            with mock.patch("os.fstat", return_value=small_st):
                with self.assertRaisesRegex(verifier.VerifyError, "grew beyond maximum permitted size"):
                    verifier._read_bytes_safe(real_f, max_bytes=len(real_bytes) - 1)

            with self.assertRaises(verifier.VerifyError):
                verifier._read_bytes_safe(os.path.join(td, "missing.json"))

            for bad_out in (td + "/", os.path.join(td, "."), os.path.join(td, "..")):
                with self.assertRaisesRegex(verifier.VerifyError, "must name a regular file"):
                    verifier._write_bytes_atomic_safe(bad_out, b"x")
            with self.assertRaisesRegex(verifier.VerifyError, "Parent directory step-down rejected"):
                verifier._write_bytes_atomic_safe(os.path.join(td, "no_such_dir", "a.json"), b"x")
            with self.assertRaisesRegex(verifier.VerifyError, "Parent directory step-down rejected"):
                verifier._write_bytes_atomic_safe(os.path.join(real_f, "child.json"), b"x")

            with mock.patch("os.getcwd", side_effect=OSError("deleted cwd")):
                with self.assertRaisesRegex(verifier.VerifyError, "Cannot resolve working directory"):
                    verifier._write_bytes_atomic_safe("relative.json", b"x")

            before_files = set(os.listdir(td))
            with mock.patch("os.write", return_value=0):
                with self.assertRaisesRegex(verifier.VerifyError, "Short write"):
                    verifier._write_bytes_atomic_safe(os.path.join(td, "short.json"), b"abc")
            self.assertEqual(set(os.listdir(td)), before_files)

            real_open = os.open
            def fail_creat(p, fl, *a, **kw):
                if fl & os.O_CREAT:
                    raise OSError("EACCES")
                return real_open(p, fl, *a, **kw)
            with mock.patch("os.open", side_effect=fail_creat):
                with self.assertRaisesRegex(verifier.VerifyError, "Cannot create atomic temp file"):
                    verifier._write_bytes_atomic_safe(os.path.join(td, "noopen.json"), b"abc")

            with mock.patch("os.replace", side_effect=OSError("EXDEV")):
                with self.assertRaisesRegex(verifier.VerifyError, "Atomic write failed"):
                    verifier._write_bytes_atomic_safe(os.path.join(td, "noreplace.json"), b"abc")
            self.assertEqual(set(os.listdir(td)), before_files)

            bad_link_st = mock.MagicMock(st_mode=stat.S_IFREG | 0o600, st_nlink=2)
            with mock.patch("os.fstat", return_value=bad_link_st):
                with self.assertRaises(verifier.VerifyError):
                    verifier._write_bytes_atomic_safe(os.path.join(td, "badlink.json"), b"abc")
            self.assertEqual(set(os.listdir(td)), before_files)

            bad_mode_st = mock.MagicMock(st_mode=stat.S_IFIFO | 0o600, st_nlink=1)
            with mock.patch("os.fstat", return_value=bad_mode_st):
                with self.assertRaises(verifier.VerifyError):
                    verifier._write_bytes_atomic_safe(os.path.join(td, "badmode.json"), b"abc")
            self.assertEqual(set(os.listdir(td)), before_files)

            with mock.patch("os.fsync", side_effect=KeyboardInterrupt()):
                with self.assertRaises(KeyboardInterrupt):
                    verifier._write_bytes_atomic_safe(os.path.join(td, "kb.json"), b"abc")
            self.assertEqual(set(os.listdir(td)), before_files)

            old_cwd = os.getcwd()
            try:
                os.chdir(td)
                with mock.patch.dict("os.environ", {"PWD": "/nonexistent_pwd_path"}, clear=False):
                    verifier._write_bytes_atomic_safe("rel_ok.json", b"ok\n")
                    self.assertEqual(verifier._read_bytes_safe(os.path.join(td, "rel_ok.json")), b"ok\n")
            finally:
                os.chdir(old_cwd)

    def test_07_semantic_audit_malformed_and_invariant_guards(self) -> None:
        good_cert = verifier.build_certificate()

        with self.assertRaises(verifier.VerifyError):
            verifier.audit_certificate_semantics([])
        with self.assertRaises(verifier.VerifyError):
            verifier.audit_certificate_semantics({"payload": "bad"})
        with self.assertRaises(verifier.VerifyError):
            verifier.audit_certificate_semantics({"payload": {"oracles": "bad"}})

        bad_sv = json.loads(json.dumps(good_cert))
        bad_sv["payload"]["schema_version"] = "wrong"
        with self.assertRaisesRegex(verifier.VerifyError, "schema_version mismatch"):
            verifier.audit_certificate_semantics(bad_sv)

        bad_op = json.loads(json.dumps(good_cert))
        bad_op["payload"]["oracles_passed"] = 4
        with self.assertRaisesRegex(verifier.VerifyError, "Semantic invariant check failed"):
            verifier.audit_certificate_semantics(bad_op)

        bad_rf = json.loads(json.dumps(good_cert))
        bad_rf["payload"]["oracles"]["oracle_1_motifbench_table3"]["rfdiff_only_cases"] = ["17:7DGW", "28:5YUI"]
        with self.assertRaisesRegex(verifier.VerifyError, "Semantic invariant check failed"):
            verifier.audit_certificate_semantics(bad_rf)

        bad_dec = json.loads(json.dumps(good_cert))
        bad_dec["payload"]["oracles"]["oracle_1_motifbench_table3"]["esm_score_table3_dec"] = "FORGED"
        with self.assertRaisesRegex(verifier.VerifyError, "Invalid canonical decimal"):
            verifier.audit_certificate_semantics(bad_dec)

        bad_bool_int = json.loads(json.dumps(good_cert))
        bad_bool_int["payload"]["oracles"]["oracle_2_se3_chirality_gram"]["mirror_pairwise_distance_error"] = False
        with self.assertRaisesRegex(verifier.VerifyError, "leaf field type mismatch"):
            verifier.audit_certificate_semantics(bad_bool_int)

        bad_list = json.loads(json.dumps(good_cert))
        bad_list["payload"]["oracles"]["oracle_1_motifbench_table3"]["rfdiff_only_cases"] = "not-a-list"
        with self.assertRaisesRegex(verifier.VerifyError, "list schema type mismatch"):
            verifier.audit_certificate_semantics(bad_list)

        bad_list_elem = json.loads(json.dumps(good_cert))
        bad_list_elem["payload"]["oracles"]["oracle_5_portal77_duality_s31"]["s31_iso_proxy_blindness_witness"]["empirical_5ze9_esm_vs_af2"] = [27, False]
        with self.assertRaisesRegex(verifier.VerifyError, "leaf field type mismatch"):
            verifier.audit_certificate_semantics(bad_list_elem)

    # ------------------------------------------------------------------
    # Lean 4 R10+ Static Anti-Bypass & Mocked Subprocess Tests (08..09)
    # ------------------------------------------------------------------

    def test_08_lean_lexer_and_r10_plus_static_bypasses(self) -> None:
        base_prints = "\n".join(f"#print axioms {t}" for t in verifier.EXPECTED_LEAN_THEOREMS) + "\n"
        res = verifier.audit_lean_source("theorem ok : True := trivial\n" + base_prints)
        self.assertTrue(res["static_clean"])
        self.assertEqual(res["expected_theorems_declared"], 15)

        tricky_clean = (
            "/- outer /- nested sorry import Lean -/ still comment axiom -/\n"
            "-- line comment sorry #eval native_decide debug.skipKernelTC\n"
            "def s1 := \"sorry \\\" #eval\"\n"
            "def bar := \"ok\"\n"
            "def c1 := 'a'\n"
            "def c2 := '\\''\n"
            "def c3 := '\\x22'\n"
            "def c4 := '\\u0022'\n"
            "def \u00absorry_ident\u00bb := 1\n"
            "def x' := 2\n"
            "theorem clean_nf : 1 = 1 := by decide (config := { native := false })\n"
        ) + base_prints
        self.assertTrue(verifier.audit_lean_source(tricky_clean)["static_clean"])

        self.assertEqual(verifier.strip_lean_comments_and_literals("a / b"), "a / b")
        self.assertEqual(verifier.strip_lean_comments_and_literals("/- a-b / c -/ ok"), "              ok")
        self.assertEqual(verifier.strip_lean_comments_and_literals("a - b -- tail"), "a - b        ")
        self.assertEqual(verifier.strip_lean_comments_and_literals("a - b -- tail\nz"), "a - b        \nz")
        self.assertEqual(verifier.strip_lean_comments_and_literals('"a\\"" ok'), "      ok")
        self.assertEqual(verifier.strip_lean_comments_and_literals('\u00aba\u00bb "hi"'), " a      ")
        self.assertEqual(verifier.strip_lean_comments_and_literals(" 'a' '\\n' '\\x41' '\\u0041'"), "                         ")
        self.assertEqual(verifier.strip_lean_comments_and_literals(" '"), " '")
        self.assertEqual(verifier.strip_lean_comments_and_literals(" '\\"), " '\\")
        self.assertEqual(verifier.strip_lean_comments_and_literals(" '\\x"), " '\\x")
        self.assertEqual(verifier.strip_lean_comments_and_literals(" '\\u"), " '\\u")
        self.assertEqual(verifier.strip_lean_comments_and_literals(" 'ab"), " 'ab")
        self.assertEqual(verifier.strip_lean_comments_and_literals("f!'x'"), "f!'x'")
        self.assertEqual(verifier.strip_lean_comments_and_literals("a'x'"), "a'x'")
        self.assertEqual(verifier.strip_lean_comments_and_literals("bar#1"), "bar#1")
        self.assertEqual(verifier.strip_lean_comments_and_literals('_r"x"'), "_r   ")
        self.assertEqual(verifier.strip_lean_comments_and_literals("def r := 1"), "def r := 1")
        self.assertEqual(verifier.strip_lean_comments_and_literals("a != b !"), "a != b !")
        self.assertEqual(verifier.strip_lean_comments_and_literals("a ! -- c"), "a !     ")
        self.assertEqual(verifier.strip_lean_comments_and_literals("a ! -- c\nx"), "a !     \nx")
        self.assertEqual(verifier.strip_lean_comments_and_literals("a ! /- /- n -/ -/ x"), "a !               x")

        with self.assertRaisesRegex(verifier.VerifyError, "Unterminated Lean string literal"):
            verifier.strip_lean_comments_and_literals('"\\')
        with self.assertRaisesRegex(verifier.VerifyError, "Unterminated Lean guillemet"):
            verifier.strip_lean_comments_and_literals("\u00abunterminated")
        with self.assertRaisesRegex(verifier.VerifyError, "Unterminated Lean block comment"):
            verifier._skip_ws_and_comments(" /- unclosed", 0)
        with self.assertRaisesRegex(verifier.VerifyError, "Unterminated Lean block comment"):
            verifier.strip_lean_comments_and_literals("a ! /- unclosed")

        for lit_exploit in (
            'def a := s!"hi"',
            'def a := s! "hi"',
            'def a := s! /- c -/ "hi"',
            'def a := s! -- c\n"hi"',
            'def a := f! /- /- n -/ -/ "hi"',
            'def a := foo!"hi"',
        ):
            with self.assertRaisesRegex(verifier.VerifyError, "bang-string", msg=f"Failed to block {lit_exploit!r}"):
                verifier.audit_lean_source(lit_exploit + "\n" + base_prints)
        for raw_exploit in ('def a := r"ok"', 'def a := r"\\"', 'def a := r#"x"#'):
            with self.assertRaisesRegex(verifier.VerifyError, "Raw string", msg=f"Failed to block {raw_exploit!r}"):
                verifier.audit_lean_source(raw_exploit + "\n" + base_prints)

        with self.assertRaises(verifier.VerifyError):
            verifier.audit_lean_source("def x' := '\"'\ntheorem bad : False := sorry\n" + base_prints)
        with self.assertRaises(verifier.VerifyError):
            verifier.audit_lean_source("def \u00aba\"b\u00bb := 1\ntheorem bad : False := sorry\n" + base_prints)
        with self.assertRaises(verifier.VerifyError):
            verifier.strip_lean_comments_and_literals("/- unterminated")

        for empty_src in ("", "   \n ", 123):
            with self.assertRaisesRegex(verifier.VerifyError, "Lean source must be non-empty"):
                verifier.audit_lean_source(empty_src)  # type: ignore[arg-type]

        for snip in (
            "import Std",
            "import Lean",
            "theorem t : False := sorry",
            "theorem t : False := sorryAx _ false",
            "def x := Lean.Meta.mkSorry",
            "theorem t : False := by admit",
            "axiom bad : False",
            "opaque f : Nat",
            "theorem t : True := by native_decide",
            "theorem t : True := by decide +native",
            "theorem t : True := by decide (config := { native := !false })",
            "theorem t : True := by decide (config := { \u00abnative\u00bb := true })",
            "def cfg : DecideConfig := default",
            "def x := Lean.ofReduceBool",
            "def x := Lean.trustCompiler",
            "@[implemented_by foo] def bar := 1",
            "@[csimp] theorem x : 1 = 1 := rfl",
            "@[extern \"c_fn\"] def bar := 1",
            "unsafe def u := 1",
            "partial def p : Nat := p",
            "set_option debug.skipKernelTC true",
            "set_option \u00abdebug\u00bb.\u00abskipKernelTC\u00bb true",
            "set_option debug.byAsSorry true",
            "elab \"boom\" : tactic => pure ()",
            "macro_rules | `(tactic| boom) => `(tactic| trivial)",
            "syntax \"boom\" : tactic",
            "declare_syntax_cat boom",
            "notation \"openq\\\"\" => 0",
            "infixl:65 \" +++ \" => Nat.add",
            "initialize pure ()",
            "builtin_initialize pure ()",
            "#eval IO.println \"spoof\"",
            "#reduce 1 + 1",
            "#exit",
            "run_cmd pure ()",
            "run_meta pure ()",
            "dbg_trace \"ok\"",
            "throwError \"ok\"",
            "#print Nat",
            "#print axioms example",
        ):
            with self.assertRaises(verifier.VerifyError, msg=f"Failed to block {snip!r}"):
                verifier.audit_lean_source(snip + "\n" + base_prints)

        missing_print = "\n".join(f"#print axioms {t}" for t in verifier.EXPECTED_LEAN_THEOREMS[:-1])
        with self.assertRaises(verifier.VerifyError):
            verifier.audit_lean_source(missing_print)
        dup_print = base_prints + f"#print axioms {verifier.EXPECTED_LEAN_THEOREMS[0]}\n"
        with self.assertRaises(verifier.VerifyError):
            verifier.audit_lean_source(dup_print)
        swapped_print = base_prints.replace(verifier.EXPECTED_LEAN_THEOREMS[0], "Fake.Thm")
        with self.assertRaises(verifier.VerifyError):
            verifier.audit_lean_source(swapped_print)

    def test_09_verify_lean_file_and_exact_set_axioms_mocked(self) -> None:
        lines_out = []
        for idx, t in enumerate(verifier.EXPECTED_LEAN_THEOREMS):
            if idx == 0:
                lines_out.append(f"'{t}' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]")
            elif idx % 2 == 0:
                lines_out.append(f"'{t}' depends on axioms: [propext, Quot.sound]")
            else:
                lines_out.append(f"'{t}' does not depend on any axioms")
        good_stdout = "\n".join(lines_out) + "\n"

        self.assertEqual(
            verifier._coalesce_axiom_lines("'T' depends on axioms: [propext,\n"),
            ["'T' depends on axioms: [propext,"],
        )

        with self.assertRaisesRegex(verifier.VerifyError, "require_pinned_sha must be a bool"):
            verifier.verify_lean_file(DISK_LEAN, require_pinned_sha=0)  # type: ignore[arg-type]

        with tempfile.TemporaryDirectory() as td:
            bad_utf8 = os.path.join(td, "bad.lean")
            with open(bad_utf8, "wb") as f:
                f.write(b"\xff\xfe")
            with self.assertRaises(verifier.VerifyError):
                verifier.verify_lean_file(bad_utf8)

            # Trivial statement substitution rejected by default SHA-256 pin!
            triv_lean = os.path.join(td, "triv.lean")
            triv_src = (
                "namespace S81MotifScaffoldingDuality\n"
                + "\n".join(f"theorem {t.split('.')[1]} : True := trivial" for t in verifier.EXPECTED_LEAN_THEOREMS)
                + "\nend S81MotifScaffoldingDuality\n"
                + "\n".join(f"#print axioms {t}" for t in verifier.EXPECTED_LEAN_THEOREMS)
                + "\n"
            )
            with open(triv_lean, "w", encoding="utf-8") as f:
                f.write(triv_src)
            with self.assertRaisesRegex(verifier.VerifyError, "SHA-256 does not match pinned"):
                verifier.verify_lean_file(triv_lean)

        with mock.patch("shutil.which", return_value=None):
            with mock.patch.dict("os.environ", {"HOME": ""}, clear=False):
                with self.assertRaises(verifier.VerifyError):
                    verifier._find_lean_binary()
            with tempfile.TemporaryDirectory() as td:
                with mock.patch.dict("os.environ", {"HOME": td}, clear=False):
                    with self.assertRaises(verifier.VerifyError):
                        verifier._find_lean_binary()
                fake_bin = os.path.join(td, ".local", "bin", "lean")
                os.makedirs(fake_bin)
                with mock.patch.dict("os.environ", {"HOME": td}, clear=False):
                    with self.assertRaises(verifier.VerifyError):
                        verifier._find_lean_binary()
                os.rmdir(fake_bin)
                with open(fake_bin, "w", encoding="utf-8") as f:
                    f.write("#!/bin/sh\n")
                os.chmod(fake_bin, 0o600)
                with mock.patch.dict("os.environ", {"HOME": td}, clear=False):
                    with self.assertRaises(verifier.VerifyError):
                        verifier._find_lean_binary()
                os.chmod(fake_bin, 0o700)
                with mock.patch.dict("os.environ", {"HOME": td}, clear=False):
                    self.assertEqual(verifier._find_lean_binary(), fake_bin)
                os.unlink(fake_bin)
                elan_bin = os.path.join(td, ".elan", "bin", "lean")
                os.makedirs(os.path.dirname(elan_bin), exist_ok=True)
                with open(elan_bin, "w", encoding="utf-8") as f:
                    f.write("#!/bin/sh\n")
                os.chmod(elan_bin, 0o700)
                with mock.patch.dict("os.environ", {"HOME": td}, clear=False):
                    self.assertEqual(verifier._find_lean_binary(), elan_bin)

        with mock.patch.object(verifier, "_find_lean_binary", return_value="/usr/bin/lean"):
            with mock.patch("subprocess.run", side_effect=OSError("ENOENT")):
                with self.assertRaises(verifier.VerifyError):
                    verifier.verify_lean_file(DISK_LEAN)

            with mock.patch("subprocess.run", return_value=subprocess.CompletedProcess([], 1, good_stdout, "")):
                with self.assertRaisesRegex(verifier.VerifyError, "exited with status 1"):
                    verifier.verify_lean_file(DISK_LEAN)

            with mock.patch("subprocess.run", return_value=subprocess.CompletedProcess([], 0, good_stdout, "err")):
                with self.assertRaisesRegex(verifier.VerifyError, "Unexpected Lean stderr"):
                    verifier.verify_lean_file(DISK_LEAN)

            with mock.patch("subprocess.run", return_value=subprocess.CompletedProcess([], 0, "warning: w\n" + good_stdout, "")):
                with self.assertRaisesRegex(verifier.VerifyError, "compiler warning"):
                    verifier.verify_lean_file(DISK_LEAN)

            with mock.patch("subprocess.run", return_value=subprocess.CompletedProcess([], 0, "junk\n" + good_stdout, "")):
                with self.assertRaisesRegex(verifier.VerifyError, "Unexpected Lean stdout"):
                    verifier.verify_lean_file(DISK_LEAN)

            with mock.patch("subprocess.run", return_value=subprocess.CompletedProcess([], 0, good_stdout.replace("propext", "sorryAx", 1), "")):
                with self.assertRaisesRegex(verifier.VerifyError, "Disallowed axiom"):
                    verifier.verify_lean_file(DISK_LEAN)

            dup_none = good_stdout + f"'{verifier.EXPECTED_LEAN_THEOREMS[1]}' does not depend on any axioms\n"
            with mock.patch("subprocess.run", return_value=subprocess.CompletedProcess([], 0, dup_none, "")):
                with self.assertRaisesRegex(verifier.VerifyError, "Duplicate axiom report"):
                    verifier.verify_lean_file(DISK_LEAN)

            dup_list = good_stdout + f"'{verifier.EXPECTED_LEAN_THEOREMS[2]}' depends on axioms: [propext]\n"
            with mock.patch("subprocess.run", return_value=subprocess.CompletedProcess([], 0, dup_list, "")):
                with self.assertRaisesRegex(verifier.VerifyError, "Duplicate axiom report"):
                    verifier.verify_lean_file(DISK_LEAN)

            extra_out = good_stdout + "'Extra.Thm' does not depend on any axioms\n"
            with mock.patch("subprocess.run", return_value=subprocess.CompletedProcess([], 0, extra_out, "")):
                with self.assertRaisesRegex(verifier.VerifyError, "does not exactly match"):
                    verifier.verify_lean_file(DISK_LEAN)

            miss_out = "\n".join(good_stdout.splitlines()[:-1]) + "\n"
            with mock.patch("subprocess.run", return_value=subprocess.CompletedProcess([], 0, miss_out, "")):
                with self.assertRaisesRegex(verifier.VerifyError, "does not exactly match"):
                    verifier.verify_lean_file(DISK_LEAN)

            with mock.patch("subprocess.run", return_value=subprocess.CompletedProcess([], 0, "\n" + good_stdout, "")):
                ok_res = verifier.verify_lean_file(DISK_LEAN)
                self.assertEqual(ok_res["theorems_verified"], 15)
                with tempfile.TemporaryDirectory() as td_u:
                    alt_lean = os.path.join(td_u, "alt.lean")
                    with open(DISK_LEAN, "r", encoding="utf-8") as src_fh:
                        orig_txt = src_fh.read()
                    with open(alt_lean, "w", encoding="utf-8") as fh:
                        fh.write("-- unpinned clean comment\n" + orig_txt)
                    ok_unpinned = verifier.verify_lean_file(alt_lean, require_pinned_sha=False)
                    self.assertEqual(ok_unpinned["theorems_verified"], 15)

    # ------------------------------------------------------------------
    # CLI & Zone-B JSON / $PWD-Symlink Ancestor Hardening Tests (10..11)
    # ------------------------------------------------------------------

    def test_10_cli_modes_and_fail_closed_flags(self) -> None:
        buf_out = io.StringIO()
        with mock.patch("sys.stdout", buf_out):
            self.assertEqual(verifier.main(["--standalone", "--json"]), 0)
        self.assertEqual(json.loads(buf_out.getvalue())["oracles_passed"], 5)

        buf_out = io.StringIO()
        with mock.patch("sys.stdout", buf_out):
            self.assertEqual(verifier.main([]), 0)
        self.assertIn("PASS mode=standalone", buf_out.getvalue())

        with tempfile.TemporaryDirectory() as td:
            cpath = os.path.join(td, "cli_cert.json")
            buf_out = io.StringIO()
            with mock.patch("sys.stdout", buf_out):
                self.assertEqual(verifier.main(["--write", "--cert", cpath, "--json"]), 0)
            self.assertEqual(stat.S_IMODE(os.lstat(cpath).st_mode), 0o600)
            buf_out = io.StringIO()
            with mock.patch("sys.stdout", buf_out):
                self.assertEqual(verifier.main(["--check", "--cert", cpath, "--json"]), 0)
            self.assertTrue(json.loads(buf_out.getvalue())["ok"])

            cpath2 = os.path.join(td, "cli_cert_pos.json")
            buf_out = io.StringIO()
            with mock.patch("sys.stdout", buf_out):
                self.assertEqual(verifier.main(["--write", cpath2, "--json"]), 0)
            buf_out = io.StringIO()
            with mock.patch("sys.stdout", buf_out):
                self.assertEqual(verifier.main(["--check", cpath2, "--json"]), 0)
            self.assertTrue(json.loads(buf_out.getvalue())["ok"])

            buf_err = io.StringIO()
            with mock.patch("sys.stderr", buf_err):
                self.assertEqual(verifier.main(["--check", os.path.join(td, "nope.json")]), 1)

        with mock.patch.object(
            verifier,
            "verify_lean_file",
            return_value={"static_clean": True, "theorems_verified": 15, "axioms_by_theorem": {}},
        ) as m_lean:
            for argv in (["--verify-lean", DISK_LEAN, "--json"], ["--verify-lean", "--json"], ["--verify-lean"]):
                buf_out = io.StringIO()
                with mock.patch("sys.stdout", buf_out):
                    self.assertEqual(verifier.main(argv), 0)
                self.assertEqual(m_lean.call_args[0][0], DISK_LEAN)

        buf_out = io.StringIO()
        with mock.patch("sys.stdout", buf_out):
            self.assertEqual(verifier.main(["--check", "--json"]), 0)
        self.assertTrue(json.loads(buf_out.getvalue())["ok"])
        buf_out = io.StringIO()
        with mock.patch("sys.stdout", buf_out):
            self.assertEqual(verifier.main(["--check"]), 0)
        self.assertIn("PASS mode=check", buf_out.getvalue())

        with self.assertRaisesRegex(verifier.VerifyError, "Duplicate JSON object key"):
            verifier._strict_json_object_pairs([("k", 1), ("k", 2)])

        for bad_argv in (
            ["--unknown"],
            ["--unknown", "extra"],
            ["--standalone", "unexpected_arg"],
            ["--cert"],
            ["--lean"],
            ["--standalone", "--check"],
        ):
            buf_err = io.StringIO()
            with mock.patch("sys.stderr", buf_err):
                self.assertEqual(verifier.main(bad_argv), 2)

    def test_11_zone_b_json_and_ancestor_hardening(self) -> None:
        class EvilDict(dict):
            pass

        class EvilList(list):
            pass

        verifier._validate_plain_json_tree({"ok": [1, True, None, "s", (1 << 3300) - 1]})
        with self.assertRaises(verifier.VerifyError):
            verifier._validate_plain_json_tree(EvilDict(verifier.build_certificate()))
        with self.assertRaises(verifier.VerifyError):
            verifier._validate_plain_json_tree({"a": EvilList([1])})
        with self.assertRaises(verifier.VerifyError):
            verifier._validate_plain_json_tree({1: "non-str-key"})
        with self.assertRaisesRegex(verifier.VerifyError, "key contains lone surrogate"):
            verifier._validate_plain_json_tree({"\ud800": 1})
        with self.assertRaisesRegex(verifier.VerifyError, "string value contains lone surrogate"):
            verifier._validate_plain_json_tree({"s": "\ud800"})
        with self.assertRaises(verifier.VerifyError):
            verifier._validate_plain_json_tree({"big": 1 << 3300})
        with self.assertRaises(verifier.VerifyError):
            verifier._validate_plain_json_tree({"flt": 1.5})

        ok_deep: object = 0
        for _ in range(32):
            ok_deep = [ok_deep]
        verifier._validate_plain_json_tree(ok_deep)
        with self.assertRaises(verifier.VerifyError):
            verifier._validate_plain_json_tree([ok_deep])

        self.assertEqual(verifier._strict_parse_json_int("-" + "9" * 1000), -int("9" * 1000))
        with self.assertRaises(verifier.VerifyError):
            verifier._strict_parse_json_int("9" * 1001)
        with self.assertRaises(verifier.VerifyError):
            verifier._strict_parse_json_int("-" + "9" * 1001)

        with tempfile.TemporaryDirectory() as td:
            real_sub = os.path.join(td, "real_sub")
            os.mkdir(real_sub)
            sym_sub = os.path.join(td, "sym_sub")
            os.symlink(real_sub, sym_sub)
            real_c = os.path.join(real_sub, "c.json")
            verifier.write_certificate_file(real_c)
            with self.assertRaises(verifier.VerifyError):
                verifier.verify_certificate_file(os.path.join(sym_sub, "c.json"))
            with self.assertRaises(verifier.VerifyError):
                verifier.write_certificate_file(os.path.join(sym_sub, "out.json"))

            with self.assertRaisesRegex(verifier.VerifyError, "Path traversal"):
                verifier._open_parent_dir_fd(os.path.join(td, "real_sub", "..", "x.json"))

            old_cwd = os.getcwd()
            try:
                os.chdir(td)
                with self.assertRaisesRegex(verifier.VerifyError, "Parent directory step-down rejected"):
                    verifier.verify_certificate_file("sym_sub/c.json")
                os.chdir(real_sub)
                # Logical $PWD pointing through symlink ancestor MUST fail closed!
                with mock.patch.dict("os.environ", {"PWD": sym_sub}, clear=False):
                    with self.assertRaisesRegex(verifier.VerifyError, "Parent directory step-down rejected"):
                        verifier.verify_certificate_file("c.json")
                with mock.patch.dict("os.environ", {"PWD": real_sub}, clear=False):
                    fd_ok, lf = verifier._open_parent_dir_fd("./c.json")
                    os.close(fd_ok)
                    self.assertEqual(lf, "c.json")
            finally:
                os.chdir(old_cwd)

            for idx, txt in enumerate((
                '{"a": ' + "9" * 5000 + '}\n',
                '{"a": 1.5}\n',
                '{"a": NaN}\n',
                '{"a": 1, "a": 2}\n',
            )):
                hp = os.path.join(td, f"h{idx}.json")
                with open(hp, "w", encoding="utf-8") as fh:
                    fh.write(txt)
                with self.assertRaises(verifier.VerifyError):
                    verifier.verify_certificate_file(hp)

            raw_canon = verifier._read_bytes_safe(real_c)
            crlf_p = os.path.join(td, "crlf.json")
            with open(crlf_p, "wb") as fh:
                fh.write(raw_canon.replace(b"\n", b"\r\n"))
            with self.assertRaises(verifier.VerifyError):
                verifier.verify_certificate_file(crlf_p)

            pretty_p = os.path.join(td, "pretty.json")
            with open(pretty_p, "w", encoding="utf-8") as fh:
                fh.write(json.dumps(verifier.build_certificate(), indent=2) + "\n")
            with self.assertRaises(verifier.VerifyError):
                verifier.verify_certificate_file(pretty_p)

    # ------------------------------------------------------------------
    # Live Lean 4.36.0 Kernel Verification & Red-Team Regressions (90, last!)
    # ------------------------------------------------------------------

    def test_90_live_lean436_kernel_axioms_and_bypass_regressions(self) -> None:
        buf_out = io.StringIO()
        buf_err = io.StringIO()
        with mock.patch("sys.stdout", buf_out), mock.patch("sys.stderr", buf_err):
            rc = verifier.main(["--verify-lean", "--lean", DISK_LEAN, "--json"])
        self.assertEqual(rc, 0, msg=buf_err.getvalue())
        res = json.loads(buf_out.getvalue())
        self.assertTrue(res["ok"])
        self.assertEqual(res["mode"], "verify-lean")
        self.assertTrue(res["static_clean"])
        self.assertEqual(res["theorems_verified"], 15)
        ax_map = res["axioms_by_theorem"]
        self.assertIsInstance(ax_map, dict)
        for thm in verifier.EXPECTED_LEAN_THEOREMS:
            self.assertIn(thm, ax_map)
            for ax in ax_map[thm]:
                self.assertIn(ax, verifier.ALLOWED_AXIOMS)
        self.assertEqual(ax_map["S81MotifScaffoldingDuality.motifbench_score_example_values"], [])
        self.assertEqual(ax_map["S81MotifScaffoldingDuality.esmfold_vs_af2_gap_exceeds_sd_multiples"], [])
        self.assertEqual(ax_map["S81MotifScaffoldingDuality.gpt6_wetlab_hitrate_and_wilson_95ci"], [])

        # Live R10+ E2E red-team probes against verify_lean_file (even with require_pinned_sha=False!)
        with open(DISK_LEAN, "r", encoding="utf-8") as fh:
            orig_lean = fh.read()
        with tempfile.TemporaryDirectory() as td:
            for name, prefix in (
                ("skip_kernel.lean", "set_option debug.skipKernelTC true\n"),
                ("guil_debug.lean", "set_option \u00abdebug\u00bb.\u00abskipKernelTC\u00bb true\n"),
                ("raw_smuggle.lean", 'def _a := r#"""#\naxiom evil_smuggled : False\ndef _b := r#"""#\n'),
                ("comment_bang.lean", 'def _s : String := s! /- c -/ "{(fun (_ : 1 = 1) => "") (by decide +native)}"\n'),
                ("notation_quote.lean", 'notation "openq\\"" => 0\ndef _o : Nat := openq"\naxiom bad : False\ndef _c : Nat := openq"\n'),
                ("import_std.lean", "import Std\n"),
            ):
                bad_p = os.path.join(td, name)
                with open(bad_p, "w", encoding="utf-8") as fh:
                    fh.write(prefix + orig_lean)
                with self.assertRaises(verifier.VerifyError, msg=f"Live bypass not blocked: {name}"):
                    verifier.verify_lean_file(bad_p, require_pinned_sha=False)


if __name__ == "__main__":
    unittest.main()
