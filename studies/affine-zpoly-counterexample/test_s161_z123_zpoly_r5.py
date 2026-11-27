#!/usr/bin/env python3
"""R5 refusal, boundary, Zone-B strict I/O, Lean R12/R13b, and exact witness
verification suite for Z-polynomial log-concavity counterexamples.
"""
from __future__ import annotations

import ast
from fractions import Fraction
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest import mock

_HERE = Path(__file__).parent
BASE = _HERE if _HERE.is_absolute() else (Path(os.getcwd()) / _HERE)
sys.path.insert(0, str(BASE))

import s161_z123_zpoly_oracle as oracle  # noqa: E402
from s161_z123_zpoly_oracle import ZPolyError  # noqa: E402
import verify_s161_z123_zpoly as vmod  # noqa: E402


def _capture_fds(fn, *args, **kwargs) -> tuple[int, str, str]:
    with tempfile.TemporaryFile() as out_f, tempfile.TemporaryFile() as err_f:
        saved_out = os.dup(1)
        saved_err = os.dup(2)
        try:
            os.dup2(out_f.fileno(), 1)
            os.dup2(err_f.fileno(), 2)
            rc = fn(*args, **kwargs)
        finally:
            os.dup2(saved_out, 1)
            os.dup2(saved_err, 2)
            os.close(saved_out)
            os.close(saved_err)
        out_f.seek(0)
        err_f.seek(0)
        return rc, out_f.read().decode("utf-8"), err_f.read().decode("utf-8")


def _copy_lean_pkg(dst: Path) -> None:
    for name in (oracle.LEAN_FILE_NAME, "lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        shutil.copyfile(BASE / name, dst / name)


def _valid_live_result() -> dict[str, object]:
    lean_text = (BASE / oracle.LEAN_FILE_NAME).read_text(encoding="utf-8")
    cleaned = vmod.strip_lean_comments(lean_text)
    thms = vmod._PRINT_RE.findall(cleaned)
    ax_lines = [f"'ZPolyCounterexample.{t}' depends on axioms: [propext, Quot.sound]" for t in thms]
    ax_lines[0] = f"'ZPolyCounterexample.{thms[0]}' does not depend on any axioms"
    return {
        "version_rc": 0,
        "version_output": "Lean (version 4.36.0, linux, release)\n",
        "build_rc": 0,
        "build_output": "Build completed successfully (4 jobs).\n",
        "axiom_rc": 0,
        "axiom_stderr": "",
        "axiom_stdout": "\n".join(ax_lines) + "\n",
    }


class TestZPolyCounterexampleR5(unittest.TestCase):
    payload: dict[str, object] = {}
    oracle_json: dict[str, object] = {}

    @classmethod
    def setUpClass(cls) -> None:
        rc_v, out_v, err_v = _capture_fds(vmod.main, ["--check", "--json"])
        if rc_v != 0 or err_v != "":
            raise RuntimeError(f"verifier baseline failed rc={rc_v} err={err_v}")
        cls.payload = json.loads(out_v)

        with mock.patch.object(oracle, "compute_oracle_sections", return_value=cls.payload["oracle"]):
            rc_o, out_o, err_o = _capture_fds(oracle.main, ["--json"])
        if rc_o != 0 or err_o != "":
            raise RuntimeError(f"oracle baseline failed rc={rc_o} err={err_o}")
        cls.oracle_json = json.loads(out_o)

    def _expect_code(self, code: str, fn, *args, **kwargs) -> None:
        with self.assertRaises(ZPolyError) as ctx:
            fn(*args, **kwargs)
        self.assertEqual(ctx.exception.code, code)

    def test_exact_witnesses_and_prior_art(self) -> None:
        self.assertEqual(self.payload["schema"], "s161.q44a.z123_affine_zpoly.v1")
        self.assertEqual(self.payload["novelty_classification"], "N1")
        self.assertEqual(self.payload["lean"]["public_theorems"], 62)

        orc = self.payload["oracle"]
        self.assertEqual(orc["pillar4_prior_art_law4"]["n2_claims"], 0)
        self.assertEqual(orc["pillar4_prior_art_law4"]["bcel_arxiv_2610_17135_zpoly_mentions"], 0)

        p3 = orc["pillar3_explicit_pg3_25_spread_packing"]
        self.assertEqual(p3["spreads_verified"], 651)
        self.assertEqual(p3["point_partitions_verified"], 651)
        self.assertEqual(p3["total_distinct_lines"], 407526)
        self.assertEqual(p3["distinct_lines_at_m537"], 336162)
        self.assertEqual(p3["pairwise_overlaps"], 0)
        self.assertEqual(orc["pillar2_finite_gabidulin_ground_truth"]["a43"]["Z"], [1, 5142, 21222, 5142, 1])

        p5 = orc["pillar5_shifts_and_witnesses"]
        self.assertEqual(p5["pg5_defect1296_degree"], 46)
        self.assertEqual(p5["pg5_neg_shift27_coeffs_count"], 47)
        self.assertEqual(p5["pg5_neg_shift27_min_coeff"], 324)
        self.assertEqual(p5["ag4_elem_defect1296_degree"], 34)
        self.assertEqual(p5["ag4_elem_neg_shift27_coeffs_count"], 35)
        self.assertEqual(p5["ag4_elem_neg_shift27_min_coeff"], 324)

        pc_v = p5["pconn_q2_verification"]
        self.assertEqual(pc_v["m_values"], [1, 2, 3, 4])
        self.assertEqual(pc_v["rank_tuples_per_m"], 41)
        self.assertEqual(pc_v["max_active_orbits"], 17)
        self.assertEqual(pc_v["mismatches"], 0)
        self.assertEqual(pc_v["rank7_explicit_pairs"], [[1, 1], [1, 2]])
        self.assertEqual(pc_v["rank7_explicit_ground_sets"], [33, 34])
        self.assertEqual(pc_v["rank7_explicit_hyperplanes"], [14440, 14456])
        self.assertEqual(
            pc_v["rank7_explicit_flat_counts"],
            [
                [1, 33, 528, 4376, 18882, 29232, 14440, 1],
                [1, 34, 561, 4784, 21198, 31473, 14456, 1],
            ],
        )
        self.assertEqual(pc_v["rank7_explicit_mismatches"], 0)

        sweeps = p5["range_sweeps"]
        self.assertEqual(sweeps["ag4_elem_q27_s729"]["fail_min_m"], 461)
        self.assertEqual(sweeps["ag4_elem_q27_s729"]["fail_max_m"], 729)
        self.assertEqual(sweeps["ag4_elem_q27_s729"]["fail_count"], 269)
        self.assertEqual(sweeps["ag4_elem_q27_s729"]["min_ratio_m"], 618)
        self.assertEqual(sweeps["ag4_spread_q25_s626"]["fail_min_m"], 510)
        self.assertEqual(sweeps["ag4_spread_q25_s626"]["fail_max_m"], 565)
        self.assertEqual(sweeps["ag4_spread_q25_s626"]["fail_count"], 56)
        self.assertEqual(sweeps["ag4_spread_q25_s626"]["min_ratio_m"], 537)

        ctrls = p5["negative_controls"]
        self.assertEqual(ctrls["ag4_partial_q25_s625_sweep"]["fail_count"], 0)
        self.assertEqual(ctrls["ag4_partial_q25_s625_sweep"]["min_ratio_m"], 537)
        m625_r = Fraction(ctrls["ag4_partial_q25_s625_sweep"]["m625_ratio"])
        self.assertTrue(Fraction(1057818, 1000000) < m625_r < Fraction(1057819, 1000000))
        self.assertEqual(ctrls["ag4_spread_q23_T_sweep"]["fail_count"], 0)
        self.assertEqual(ctrls["ag4_spread_q23_T_sweep"]["min_ratio_m"], 461)
        self.assertEqual(ctrls["ag4_spread_q23_P_sweep"]["fail_count"], 0)
        self.assertEqual(ctrls["ag4_spread_q23_P_sweep"]["min_ratio_m"], 462)
        self.assertEqual(ctrls["ag4_3conn_q25_m537"]["ground_set"], 782325)
        self.assertEqual(ctrls["ag4_rk6_q25_sweep"]["fail_count"], 0)
        self.assertEqual(ctrls["ag4_rk6_q25_sweep"]["min_z2_ratio_m"], 651)

        wits = p5["witnesses"]
        self.assertEqual(wits["pg5_q27_m19683_guoriyue"]["ground_set"], 29840942)
        self.assertEqual(
            wits["pg5_q27_m19683_guoriyue"]["z2_sq_minus_z1_z3"],
            -30629060076556831072416516750219744007195842510749495518880944028,
        )
        self.assertFalse(wits["pg5_q25_m15625_full_control"]["fails_log_concavity"])
        self.assertTrue(wits["pg5_q25_m13000_subset"]["fails_log_concavity"])
        self.assertEqual(wits["ag4_elem_q27_m618"]["ground_set"], 1064118)
        self.assertEqual(wits["ag4_elem_asym_q27m510_q25m456"]["ground_set"], 923032)
        self.assertEqual(wits["ag4_spread_q25_m537_submillion"]["ground_set"], 782324)
        self.assertEqual(
            wits["ag4_spread_q25_m537_submillion"]["z2_sq_minus_z1_z3"],
            -212974814633787833903301832658405502046453382,
        )
        self.assertEqual(wits["ag4_spread_q25_m510_threshold"]["ground_set"], 782270)
        self.assertEqual(wits["ag4_pconn_asym_q25_m496_m497"]["ground_set"], 782242)
        self.assertFalse(wits["ag4_spread_q23_m461_control"]["fails_log_concavity"])
        self.assertEqual(p5["shrinkage_ratios_vs_z123"]["ag4_spread_q25_m537"], "14920471/391162")
        self.assertIn("oracle_sha256", self.oracle_json)

    def test_qbin_and_alpha_bounds(self) -> None:
        self.assertEqual(oracle.qbin(3, 0, 2), 1)
        self.assertEqual(oracle.qbin(3, 1, 2), 7)
        self.assertEqual(oracle.qbin(3, 3, 2), 1)
        self._expect_code("QBIN_Q_MIN", oracle.qbin, 3, 1, 1)
        self._expect_code("QBIN_BOUNDS", oracle.qbin, 3, -1, 2)
        self._expect_code("QBIN_BOUNDS", oracle.qbin, 3, 4, 2)

        self.assertEqual(oracle.proj_gabidulin_alpha(2)[(1,)], 71)
        self.assertEqual(oracle.proj_gabidulin_alpha(2, 0)[(1,)], 63)
        self.assertEqual(oracle.proj_gabidulin_alpha(2, 8)[(1,)], 71)
        self._expect_code("ALPHA_Q_MIN", oracle.proj_gabidulin_alpha, 1, 0)
        self._expect_code("FAMILY_M_BOUNDS", oracle.proj_gabidulin_alpha, 2, -1)
        self._expect_code("FAMILY_M_BOUNDS", oracle.proj_gabidulin_alpha, 2, 9)

        self.assertEqual(oracle.affine_coalesced_alpha(2, 0, 4)[(1,)], 16)
        self.assertEqual(oracle.affine_coalesced_alpha(2, 4, 4)[(1,)], 20)
        self.assertEqual(oracle.affine_coalesced_alpha(2, 7, 5)[(1,)], 23)
        self._expect_code("ALPHA_Q_MIN", oracle.affine_coalesced_alpha, 1, 0, 1)
        self._expect_code("FAMILY_M_BOUNDS", oracle.affine_coalesced_alpha, 2, -1, 4)
        self._expect_code("FAMILY_M_BOUNDS", oracle.affine_coalesced_alpha, 2, 5, 4)
        self._expect_code("FAMILY_M_BOUNDS", oracle.affine_coalesced_alpha, 2, 8, 5)

    def test_poset_epw_and_finite_matroid_refusals(self) -> None:
        self._expect_code(
            "MATROID_LOOPLESS",
            oracle.build_lattice_from_hyperplanes,
            3,
            2,
            {frozenset([0, 1]), frozenset([0, 2])},
        )
        self._expect_code(
            "MATROID_COVER_COUNT",
            oracle.build_lattice_from_hyperplanes,
            3,
            2,
            {frozenset([0]), frozenset([1])},
        )
        self._expect_code(
            "MATROID_COVER_UNION",
            oracle.build_lattice_from_hyperplanes,
            3,
            2,
            {frozenset([0]), frozenset([1]), frozenset([99])},
        )

        for tm, code in [
            ("antisym", "EPW_ANTISYMMETRY"),
            ("palindrome", "ZPOLY_PALINDROME"),
            ("rk3", "KL_RK3_FORMULA"),
            ("rk4", "KL_RK4_FORMULA"),
            ("rk5", "KL_RK5_FORMULA"),
            ("rk7", "ZPOLY_RK7_FORMULA"),
        ]:
            self._expect_code(code, oracle.verify_epw_kl_and_zpoly_audit, tamper=tm)

        for tm, code in [
            ("a42_missing", "A42_TRIPLE_COUNT"),
            ("a42_dup", "A42_TRIPLE_UNIQUE"),
            ("a42_flag", "A42_FLAG_MATCH"),
            ("a43_pair", "A43_PAIR_PARTITION"),
            ("a43_pair_dup", "A43_PAIR_UNIQUE"),
            ("a43_rk2", "A43_RK2_PARTITION"),
            ("a43_flag", "A43_FLAG_MATCH"),
        ]:
            self._expect_code(code, oracle.verify_finite_a42_and_a43, tamper=tm)

    def test_pg3_q25_parallelism_and_shift_refusals(self) -> None:
        self._expect_code("SPREAD_MIN_537", oracle.verify_pg3_q25_parallelism, check_spreads=536)
        self._expect_code("SPREAD_MAX_651", oracle.verify_pg3_q25_parallelism, check_spreads=652)
        self._expect_code("GOOD_SET_INVALID", oracle.verify_pg3_q25_parallelism, check_spreads=537, tamper="good_set")
        self._expect_code("ALLOWED_NORMS_INVALID", oracle.verify_pg3_q25_parallelism, check_spreads=537, tamper="allowed_norms")

        res_537 = oracle.verify_pg3_q25_parallelism(check_spreads=537)
        self.assertEqual(res_537["spreads_verified"], 537)
        self.assertEqual(res_537["point_partitions_verified"], 537)
        self.assertEqual(res_537["total_distinct_lines"], 336162)

        self._expect_code("SPREAD_SIZE_MISMATCH", oracle.verify_pg3_q25_parallelism, check_spreads=537, tamper="size")
        self._expect_code("SPREAD_OVERLAP", oracle.verify_pg3_q25_parallelism, check_spreads=537, tamper="overlap")
        self._expect_code("SPREAD_POINT_PARTITION", oracle.verify_pg3_q25_parallelism, check_spreads=537, tamper="pt_partition")
        self._expect_code("NON_INTEGRAL_DEFECT", oracle._scale_neg1296_exact, [Fraction(1, 2592)])

        self._expect_code(
            "PCONN_RK7_OXLEY_FAIL",
            oracle._verify_bitmask_lattice_and_41_tuples,
            3,
            2,
            {0b011, 0b101},
            [],
            [],
            [],
            [],
            [],
        )

        for tm, code in [
            ("pg_zero", "PG_SHIFT_NONPOS"),
            ("el_zero", "EL_SHIFT_NONPOS"),
            ("pconn", "PCONN_DAG_MISMATCH"),
            ("sweep", "SWEEP_CONTROL_FAIL"),
            ("witness", "WITNESS_CHECK_FAIL"),
            ("pconn_rk7", "PCONN_RK7_MISMATCH"),
        ]:
            self._expect_code(code, oracle.verify_universal_shifts_and_witnesses, tamper=tm)

    def test_strict_zone_b_io_and_json_scanner(self) -> None:
        self._expect_code("BAD_PATH_TYPE", vmod.read_strict_bytes, 123)
        self._expect_code("BAD_PATH_STR", vmod.read_strict_bytes, "")
        self._expect_code("BAD_PATH_STR", vmod.read_strict_bytes, "bad\x00path")
        self._expect_code("READ_OPEN", vmod._open_parent_nofollow, "/")

        dfd_tmp, leaf_tmp = vmod._open_parent_nofollow("/tmp")
        os.close(dfd_tmp)
        self.assertEqual(leaf_tmp, "tmp")

        with tempfile.TemporaryDirectory() as td:
            tp = Path(td)
            self._expect_code("PARENT_OPEN", vmod.read_strict_bytes, tp / "missing_dir" / "f.txt")
            self._expect_code("READ_OPEN", vmod.read_strict_bytes, tp / "missing.txt")

            sub = tp / "sub"
            sub.mkdir()
            self._expect_code("NOT_REGULAR", vmod.read_strict_bytes, sub)

            fifo = tp / "pipe"
            os.mkfifo(fifo)
            self._expect_code("NOT_REGULAR", vmod.read_strict_bytes, fifo)

            real_f = sub / "ok.txt"
            real_f.write_bytes(b"ok\n")
            self.assertEqual(vmod.read_strict_text(real_f), "ok\n")

            hl_f = tp / "hardlink.txt"
            os.link(real_f, hl_f)
            self._expect_code("HARDLINK_FILE", vmod.read_strict_bytes, hl_f)
            hl_f.unlink()

            link_f = tp / "sym.txt"
            link_f.symlink_to(real_f)
            self._expect_code("SYMLINK_ANCESTOR", vmod.read_strict_bytes, link_f)

            link_dir = tp / "symdir"
            link_dir.symlink_to(sub)
            self._expect_code("SYMLINK_ANCESTOR", vmod.read_strict_bytes, str(tp) + "/symdir/../sub/ok.txt")

            exact_f = tp / "exact.bin"
            exact_f.write_bytes(b"a" * vmod.MAX_BYTES)
            self.assertEqual(len(vmod.read_strict_bytes(exact_f)), vmod.MAX_BYTES)

            big_f = tp / "big.bin"
            big_f.write_bytes(b"a" * (vmod.MAX_BYTES + 1))
            self._expect_code("TOO_LARGE", vmod.read_strict_bytes, big_f)

        self._expect_code("BAD_UTF8", vmod.decode_strict_text, b"\xff\n")
        self._expect_code("BAD_BOM", vmod.decode_strict_text, "\ufeffok\n".encode("utf-8"))
        self._expect_code("BAD_LF", vmod.decode_strict_text, b"ok\r\n")
        self._expect_code("BAD_FINAL_LF", vmod.decode_strict_text, b"ok")

        vmod.scan_json_text("[" * vmod.MAX_DEPTH + "]" * vmod.MAX_DEPTH + "\n")
        self._expect_code("JSON_DEPTH_BOUNDS", vmod.scan_json_text, "}\n")
        self._expect_code("JSON_DEPTH_BOUNDS", vmod.scan_json_text, "[" * (vmod.MAX_DEPTH + 1) + "]" * (vmod.MAX_DEPTH + 1) + "\n")

        ok_256 = '{"n": ' + ("9" * vmod.MAX_INT_DIGITS) + "}\n"
        self.assertEqual(vmod.parse_strict_json(ok_256)["n"], int("9" * vmod.MAX_INT_DIGITS))
        bad_257 = '{"n": ' + ("9" * (vmod.MAX_INT_DIGITS + 1)) + "}\n"
        self._expect_code("INT_DIGITS", vmod.parse_strict_json, bad_257)

        self._expect_code("UNBALANCED_FINAL", vmod.scan_json_text, "{\n")
        self._expect_code("FLOAT_TOKEN", vmod.parse_strict_json, '{"x": 1.5}\n')
        self._expect_code("FLOAT_TOKEN", vmod.parse_strict_json, '{"x": 1e5}\n')
        self._expect_code("FLOAT_TOKEN", vmod.parse_strict_json, '{"x": 1E5}\n')
        self._expect_code("UNTERMINATED_JSON_STRING", vmod.scan_json_text, '"abc\n')
        self.assertEqual(vmod.parse_strict_json('{"x": "a\\"b\\\\c1.5"}\n')["x"], 'a"b\\c1.5')

        self._expect_code("DUP_KEY", vmod.parse_strict_json, '{"a": 1, "a": 2}\n')
        self._expect_code("BAD_CONSTANT", vmod.parse_strict_json, '{"a": NaN}\n')
        self._expect_code("BAD_JSON", vmod.parse_strict_json, "{bad}\n")
        self._expect_code("NOT_OBJECT", vmod.parse_strict_json, "[1, 2]\n")

        self.assertTrue(vmod.strict_json_equal({"a": [1, True, "x"]}, {"a": [1, True, "x"]}))
        self.assertFalse(vmod.strict_json_equal(1, True))
        self.assertFalse(vmod.strict_json_equal(0, False))
        self.assertFalse(vmod.strict_json_equal({"a": 1}, {"a": 1, "b": 2}))
        self.assertFalse(vmod.strict_json_equal({"a": 1}, {"a": 2}))
        self.assertFalse(vmod.strict_json_equal([1, 2], [1, 2, 3]))
        self.assertFalse(vmod.strict_json_equal([1, 2], [1, 3]))
        self.assertFalse(vmod.strict_json_equal([1, True], [1, 1]))

    def test_lean_package_and_axiom_auditor(self) -> None:
        cleaned_sample = vmod.strip_lean_comments("a -- x\n/- b /- c -/ d -/\ne\n")
        self.assertEqual([ln.strip() for ln in cleaned_sample.splitlines()], ["a", "", "e"])
        self._expect_code("UNTERMINATED_BLOCK_COMMENT", vmod.strip_lean_comments, "/- a /- b -/\n")

        self._expect_code("AXIOM_LINE_COUNT", vmod.validate_axiom_lines, [], 1)
        self._expect_code("AXIOM_THM_PREFIX", vmod.validate_axiom_lines, ["xx' does not depend on any axioms"], 1)
        self._expect_code("AXIOM_THM_PREFIX", vmod.validate_axiom_lines, ["'' does not depend on any axioms"], 1)
        self._expect_code("AXIOM_LINE_FORMAT", vmod.validate_axiom_lines, ["'x' weird"], 1)
        self._expect_code("AXIOM_LBRACKET", vmod.validate_axiom_lines, ["'x' depends on axioms: propext]"], 1)
        self._expect_code("AXIOM_RBRACKET", vmod.validate_axiom_lines, ["'x' depends on axioms: [propext"], 1)
        self._expect_code("FORBIDDEN_AXIOM", vmod.validate_axiom_lines, ["'x' depends on axioms: [propext, Classical.choice]"], 1)
        self._expect_code("AXIOM_THM_MISMATCH", vmod.validate_axiom_lines, ["'a' does not depend on any axioms"], 1, ["b"])
        ok_ax = vmod.validate_axiom_lines(
            ["'a' does not depend on any axioms", "'b' depends on axioms: [propext, Quot.sound]"],
            2,
            ["a", "b"],
        )
        self.assertEqual(ok_ax, {"zero_axiom": 1, "listed": 1})

        with tempfile.TemporaryDirectory() as td:
            tp = Path(td)
            _copy_lean_pkg(tp)
            info = vmod.verify_lean_package(tp, lean_runner=lambda _b: _valid_live_result())
            self.assertEqual(info["public_theorems"], 62)

            # LOW-2: default_live_lean_runner stages exact in-memory bytes without re-reading disk
            staged = {
                oracle.LEAN_FILE_NAME: (BASE / oracle.LEAN_FILE_NAME).read_bytes(),
                "lean-toolchain": (BASE / "lean-toolchain").read_bytes(),
                "lakefile.toml": (BASE / "lakefile.toml").read_bytes(),
                "lake-manifest.json": (BASE / "lake-manifest.json").read_bytes(),
            }
            staged_seen: dict[str, bytes] = {}

            def _fake_subproc_run(cmd, cwd=None, **_kwargs):
                for fname in staged:
                    staged_seen[fname] = (Path(cwd) / fname).read_bytes()
                res_d = _valid_live_result()
                if cmd == ["lean", "--version"]:
                    return mock.Mock(returncode=res_d["version_rc"], stdout=res_d["version_output"], stderr="")
                if cmd == ["lake", "build"]:
                    return mock.Mock(returncode=res_d["build_rc"], stdout=res_d["build_output"], stderr="")
                return mock.Mock(returncode=res_d["axiom_rc"], stdout=res_d["axiom_stdout"], stderr=res_d["axiom_stderr"])

            with (
                mock.patch.object(vmod, "read_strict_bytes", side_effect=RuntimeError("unexpected_reread")),
                mock.patch.object(vmod.subprocess, "run", side_effect=_fake_subproc_run),
            ):
                live_res = vmod.default_live_lean_runner(staged)
            self.assertEqual(live_res["version_rc"], 0)
            self.assertEqual(staged_seen, staged)

            def _wrong_thm_runner(_b):
                d = _valid_live_result()
                d["axiom_stdout"] = d["axiom_stdout"].replace("ZPolyCounterexample.evalP_addP", "ZPolyCounterexample.bogus", 1)
                return d

            self._expect_code("AXIOM_THM_MISMATCH", vmod.verify_lean_package, tp, lean_runner=_wrong_thm_runner)

            for field, bad_val, code in [
                ("version_rc", 1, "LEAN_VERSION_RC"),
                ("version_output", "Lean 4.15.0\n", "BAD_LEAN_VERSION"),
                ("build_rc", 1, "LAKE_BUILD_FAIL"),
                ("build_output", "warning: unused variable\n", "LAKE_BUILD_WARNING"),
                ("axiom_rc", 1, "AXIOM_RC"),
                ("axiom_stderr", "err\n", "AXIOM_STDERR"),
            ]:
                def _bad_runner(_b, f=field, v=bad_val):
                    d = _valid_live_result()
                    d[f] = v
                    return d
                self._expect_code(code, vmod.verify_lean_package, tp, lean_runner=_bad_runner)

            # SHA pin checks
            (tp / "lean-toolchain").write_text("leanprover/lean4:v4.36.0\n\n", encoding="utf-8")
            self._expect_code("PIN_TOOLCHAIN_SHA", vmod.verify_lean_package, tp, enforce_sha_pins=True)
            _copy_lean_pkg(tp)

            (tp / "lakefile.toml").write_text((tp / "lakefile.toml").read_text(encoding="utf-8") + "\n", encoding="utf-8")
            self._expect_code("PIN_LAKEFILE_SHA", vmod.verify_lean_package, tp, enforce_sha_pins=True)
            _copy_lean_pkg(tp)

            mf_obj = json.loads((tp / "lake-manifest.json").read_text(encoding="utf-8"))
            (tp / "lake-manifest.json").write_text(json.dumps(mf_obj) + "\n", encoding="utf-8")
            self._expect_code("PIN_MANIFEST_SHA", vmod.verify_lean_package, tp, enforce_sha_pins=True)
            _copy_lean_pkg(tp)

            (tp / oracle.LEAN_FILE_NAME).write_text((tp / oracle.LEAN_FILE_NAME).read_text(encoding="utf-8") + "\n", encoding="utf-8")
            self._expect_code("PIN_LEAN_SHA", vmod.verify_lean_package, tp, enforce_sha_pins=True)
            _copy_lean_pkg(tp)

            # Structural checks (enforce_sha_pins=False)
            (tp / "lean-toolchain").write_text("leanprover/lean4:v4.14.0\n", encoding="utf-8")
            self._expect_code("BAD_TOOLCHAIN", vmod.verify_lean_package, tp, enforce_sha_pins=False)
            _copy_lean_pkg(tp)

            for lf_bad in [
                'name = "x"\n[[require]]\nname = "mathlib"\n',
                'name = "x"\nprecompileModules = true\n',
                'name = "x"\n[[extern_lib]]\nname = "c_hook"\n',
            ]:
                (tp / "lakefile.toml").write_text(lf_bad, encoding="utf-8")
                self._expect_code("LAKEFILE_REQUIRE", vmod.verify_lean_package, tp, enforce_sha_pins=False)
            _copy_lean_pkg(tp)

            (tp / "lake-manifest.json").write_text('{"version": "1.1.0", "packages": [{"name": "x"}]}\n', encoding="utf-8")
            self._expect_code("NONEMPTY_PACKAGES", vmod.verify_lean_package, tp, enforce_sha_pins=False)
            _copy_lean_pkg(tp)

            (tp / "Extra.lean").write_text("theorem t : True := trivial\n", encoding="utf-8")
            self._expect_code("LEAN_FILE_COUNT", vmod.verify_lean_package, tp, enforce_sha_pins=False)
            (tp / "Extra.lean").unlink()

            (tp / oracle.LEAN_FILE_NAME).rename(tp / "Wrong.lean")
            self._expect_code("LEAN_FILE_NAME", vmod.verify_lean_package, tp, enforce_sha_pins=False)
            (tp / "Wrong.lean").rename(tp / oracle.LEAN_FILE_NAME)

            orig_lean = (tp / oracle.LEAN_FILE_NAME).read_text(encoding="utf-8")
            for snippet in [
                'def s := "str"\n',
                "import Init\n",
                "axiom ax : False\n",
                "#eval 1\n",
                "#check_failure 1\n",
                "run_cmd pure ()\n",
                "run_meta pure ()\n",
                "run_elab pure ()\n",
                "run_tac pure ()\n",
                "set_option\ndebug.skipKernelTC true\n",
            ]:
                (tp / oracle.LEAN_FILE_NAME).write_text(snippet + orig_lean, encoding="utf-8")
                self._expect_code("LEAN_ESCAPE", vmod.verify_lean_package, tp, enforce_sha_pins=False)

            (tp / oracle.LEAN_FILE_NAME).write_text(orig_lean + "\n#print Nat\n", encoding="utf-8")
            self._expect_code("UNEXPECTED_PRINT_CMD", vmod.verify_lean_package, tp, enforce_sha_pins=False)

            extra_both = (
                orig_lean.replace("end ZPolyCounterexample", "@[simp] theorem extra_t : True := trivial\n\nend ZPolyCounterexample")
                + "#print axioms ZPolyCounterexample.extra_t\n"
            )
            (tp / oracle.LEAN_FILE_NAME).write_text(extra_both, encoding="utf-8")
            self._expect_code("THM_COUNT", vmod.verify_lean_package, tp, enforce_sha_pins=False)

            thm_names = vmod._PUB_THM_RE.findall(vmod.strip_lean_comments(orig_lean))
            dup_print = orig_lean + f"#print axioms ZPolyCounterexample.{thm_names[0]}\n"
            (tp / oracle.LEAN_FILE_NAME).write_text(dup_print, encoding="utf-8")
            self._expect_code("AUDIT_COUNT", vmod.verify_lean_package, tp, enforce_sha_pins=False)

            swapped_set = orig_lean.replace(
                f"#print axioms ZPolyCounterexample.{thm_names[0]}",
                f"#print axioms ZPolyCounterexample.{thm_names[1]}",
                1,
            )
            (tp / oracle.LEAN_FILE_NAME).write_text(swapped_set, encoding="utf-8")
            self._expect_code("AUDIT_SET", vmod.verify_lean_package, tp, enforce_sha_pins=False)

    def test_cli_modes_and_error_handlers(self) -> None:
        rc_bad_o, _, err_bad_o = _capture_fds(oracle.main, ["--bogus"])
        self.assertEqual(rc_bad_o, 2)
        self.assertEqual(json.loads(err_bad_o)["code"], "BAD_ORACLE_ARGS")

        rc_bad_o2, out_bad_o2, err_bad_o2 = _capture_fds(oracle.main, ["--json=1"])
        self.assertEqual(rc_bad_o2, 2)
        self.assertEqual(out_bad_o2, "")
        self.assertEqual(json.loads(err_bad_o2)["code"], "BAD_ORACLE_ARGS")

        rc_abbr_o, _, err_abbr_o = _capture_fds(oracle.main, ["--jso"])
        self.assertEqual(rc_abbr_o, 2)
        self.assertEqual(json.loads(err_abbr_o)["code"], "BAD_ORACLE_ARGS")

        rc_bad_v, _, err_bad_v = _capture_fds(vmod.main, ["--bogus"])
        self.assertEqual(rc_bad_v, 2)
        self.assertEqual(json.loads(err_bad_v)["code"], "BAD_CLI_ARGS")

        rc_bad_v2, out_bad_v2, err_bad_v2 = _capture_fds(vmod.main, ["--json=1"])
        self.assertEqual(rc_bad_v2, 2)
        self.assertEqual(out_bad_v2, "")
        self.assertEqual(json.loads(err_bad_v2)["code"], "BAD_CLI_ARGS")

        rc_abbr_v, _, err_abbr_v = _capture_fds(vmod.main, ["--chec"])
        self.assertEqual(rc_abbr_v, 2)
        self.assertEqual(json.loads(err_abbr_v)["code"], "BAD_CLI_ARGS")

        rc_m2, _, err_m2 = _capture_fds(vmod.main, ["--standalone", "--check"])
        self.assertEqual(rc_m2, 2)
        self.assertEqual(json.loads(err_m2)["code"], "MODE_COUNT")

        with mock.patch.object(vmod, "build_payload", return_value=self.payload):
            rc_def, out_def, _ = _capture_fds(vmod.main, [])
            self.assertEqual(rc_def, 0)
            self.assertIn("PASS s161.q44a.z123_affine_zpoly.v1", out_def)

            rc_st, out_st, _ = _capture_fds(vmod.main, ["--standalone"])
            self.assertEqual(rc_st, 0)
            self.assertIn("PASS s161.q44a.z123_affine_zpoly.v1", out_st)

            with tempfile.TemporaryDirectory() as td:
                tp = Path(td)
                out_cert = tp / "written_cert.json"
                rc_w, _, _ = _capture_fds(vmod.main, ["--write", str(out_cert)])
                self.assertEqual(rc_w, 0)
                self.assertTrue(vmod.strict_json_equal(vmod.read_strict_json(out_cert), self.payload))
                # Atomic overwrite of existing regular file leaves zero temp files
                rc_w2, _, _ = _capture_fds(vmod.main, ["--write", str(out_cert)])
                self.assertEqual(rc_w2, 0)
                self.assertEqual([p.name for p in tp.iterdir() if p.name.startswith(".s161_cert_tmp_")], [])

                tampered = dict(self.payload)
                tampered["novelty_classification"] = "N2"
                bad_cert = tp / "bad_cert.json"
                vmod.write_cert(bad_cert, tampered)
                rc_mis, _, err_mis = _capture_fds(vmod.main, ["--check", str(bad_cert)])
                self.assertEqual(rc_mis, 2)
                self.assertEqual(json.loads(err_mis)["code"], "CERT_MISMATCH")

                # MED-1 regression: bool/int spoof (lean_files: 1 -> true) MUST fail closed
                bool_spoof = json.loads(json.dumps(self.payload))
                bool_spoof["lean"]["lean_files"] = True
                bool_cert = tp / "bool_spoof.json"
                vmod.write_cert(bool_cert, bool_spoof)
                rc_bs, _, err_bs = _capture_fds(vmod.main, ["--check", str(bool_cert)])
                self.assertEqual(rc_bs, 2)
                self.assertEqual(json.loads(err_bs)["code"], "CERT_MISMATCH")

                # HIGH-2 regression: --write <symlink>/../victim.json MUST fail closed and leave victim untouched
                sub_dir = tp / "sub"
                sub_dir.mkdir()
                sym_dir = tp / "symdir"
                sym_dir.symlink_to(sub_dir)
                victim = tp / "victim.json"
                victim.write_bytes(b"victim\n")
                rc_esc, _, err_esc = _capture_fds(vmod.main, ["--write", str(tp) + "/symdir/../victim.json"])
                self.assertEqual(rc_esc, 2)
                self.assertEqual(json.loads(err_esc)["code"], "SYMLINK_ANCESTOR")
                self.assertEqual(victim.read_bytes(), b"victim\n")

                # Symlink leaf refusal
                sym_cert = tp / "sym_cert.json"
                sym_cert.symlink_to(victim)
                rc_sl, _, err_sl = _capture_fds(vmod.main, ["--write", str(sym_cert)])
                self.assertEqual(rc_sl, 2)
                self.assertEqual(json.loads(err_sl)["code"], "SYMLINK_ANCESTOR")
                self.assertEqual(victim.read_bytes(), b"victim\n")

                # Hardlink target refusal
                hl_cert = tp / "hl_cert.json"
                os.link(victim, hl_cert)
                rc_hl, _, err_hl = _capture_fds(vmod.main, ["--write", str(hl_cert)])
                self.assertEqual(rc_hl, 2)
                self.assertEqual(json.loads(err_hl)["code"], "HARDLINK_TARGET")
                self.assertEqual(victim.read_bytes(), b"victim\n")
                hl_cert.unlink()

                # Directory target and dotdot leaf refusals
                rc_dir, _, err_dir = _capture_fds(vmod.main, ["--write", str(sub_dir)])
                self.assertEqual(rc_dir, 2)
                self.assertEqual(json.loads(err_dir)["code"], "NOT_REGULAR")

                rc_dd, _, err_dd = _capture_fds(vmod.main, ["--write", str(sub_dir) + "/.."])
                self.assertEqual(rc_dd, 2)
                self.assertEqual(json.loads(err_dd)["code"], "BAD_PATH_LEAF")

                # LOW-4: O_EXCL collision leaves pre-existing temp file intact
                collide_name = ".s161_cert_tmp_" + str(os.getpid()) + "_deadbeef00000001"
                collide_path = tp / collide_name
                collide_path.write_bytes(b"KEEP\n")
                with mock.patch.object(vmod.secrets, "token_hex", return_value="deadbeef00000001"):
                    with self.assertRaises(OSError):
                        vmod.write_cert(tp / "collided_cert.json", self.payload)
                self.assertEqual(collide_path.read_bytes(), b"KEEP\n")

        with mock.patch.object(oracle, "run_oracle_cli", side_effect=OSError("io_err")):
            rc_o_os, _, err_o_os = _capture_fds(oracle.main, [])
            self.assertEqual(rc_o_os, 2)
            self.assertEqual(json.loads(err_o_os)["code"], "OS_ERROR")

        with mock.patch.object(oracle, "run_oracle_cli", side_effect=RecursionError("deep")):
            rc_o_rec, _, err_o_rec = _capture_fds(oracle.main, [])
            self.assertEqual(rc_o_rec, 2)
            self.assertEqual(json.loads(err_o_rec)["code"], "RECURSION")

        with mock.patch.object(vmod, "run_cli", side_effect=OSError("io_err")):
            rc_os, _, err_os = _capture_fds(vmod.main, [])
            self.assertEqual(rc_os, 2)
            self.assertEqual(json.loads(err_os)["code"], "OS_ERROR")

        with mock.patch.object(vmod, "run_cli", side_effect=RecursionError("deep")):
            rc_rec, _, err_rec = _capture_fds(vmod.main, [])
            self.assertEqual(rc_rec, 2)
            self.assertEqual(json.loads(err_rec)["code"], "RECURSION")

        import subprocess
        with mock.patch.object(vmod, "run_cli", side_effect=subprocess.TimeoutExpired(cmd="lean", timeout=1)):
            rc_sub, _, err_sub = _capture_fds(vmod.main, [])
            self.assertEqual(rc_sub, 2)
            self.assertEqual(json.loads(err_sub)["code"], "SUBPROCESS_ERROR")

        # Read-only package directory check (leaves zero .lake artifacts)
        with tempfile.TemporaryDirectory() as ro_td:
            ro_tp = Path(ro_td)
            _copy_lean_pkg(ro_tp)
            for p_item in ro_tp.iterdir():
                p_item.chmod(0o444)
            ro_tp.chmod(0o555)
            try:
                ro_info = vmod.verify_lean_package(ro_tp, lean_runner=lambda _b: _valid_live_result())
                self.assertEqual(ro_info["public_theorems"], 62)
                self.assertFalse((ro_tp / ".lake").exists())
            finally:
                ro_tp.chmod(0o755)
                for p_item in ro_tp.iterdir():
                    p_item.chmod(0o644)

        with mock.patch.object(oracle, "compute_oracle_sections", return_value=self.payload["oracle"]):
            rc_op, out_op, _ = _capture_fds(oracle.main, [])
            self.assertEqual(rc_op, 0)
            self.assertIn("PASS s161.q44a.z123_affine_zpoly.oracle.v1", out_op)

    def test_ast_zero_floats_asserts_and_local_paths(self) -> None:
        for fn in ("s161_z123_zpoly_oracle.py", "verify_s161_z123_zpoly.py"):
            src = (BASE / fn).read_text(encoding="utf-8")
            self.assertNotIn("/" + "home/", src)
            tree = ast.parse(src)
            for node in ast.walk(tree):
                self.assertNotIsInstance(node, ast.Assert)
                if isinstance(node, ast.Constant):
                    self.assertNotEqual(type(node.value).__name__, "float")
                if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                    self.assertNotEqual(node.func.id, "float")
                if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
                    self.assertNotEqual(node.func.attr, "__float__")

        test_src = (BASE / "test_s161_z123_zpoly_r5.py").read_text(encoding="utf-8")
        self.assertNotIn("/" + "home/", test_src)
        for node in ast.walk(ast.parse(test_src)):
            self.assertNotIsInstance(node, ast.Assert)
            if isinstance(node, ast.Constant):
                self.assertNotEqual(type(node.value).__name__, "float")
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                self.assertNotEqual(node.func.id, "float")
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
                self.assertNotEqual(node.func.attr, "__float__")


if __name__ == "__main__":
    unittest.main()
