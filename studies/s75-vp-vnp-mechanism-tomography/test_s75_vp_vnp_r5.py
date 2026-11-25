"""Adversarial R1-R5 verification suite for the VP != VNP Mechanism Audit.

Fast unit, oracle, mutation-kill, filesystem/JSON hardening, FR0/SEC tamper sweep,
and R9+ Lean static + live exploit regression tests.
"""

from __future__ import annotations

import copy
import errno
from fractions import Fraction
import io
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import s75_vp_vnp_mechanism_probe as probe
import verify_s75_vp_vnp as verifier

DISK_CERT = os.path.join(HERE, "s75_vp_vnp_certificate.json")
DISK_LEAN = os.path.join(HERE, "VpVnpMechanismCerts.lean")


class _FloatSubclass(float):
    pass


def _resign(payload: dict) -> dict:
    return {
        "schema_version": verifier.SCHEMA_VERSION,
        "payload_sha256": verifier._compute_payload_sha256(payload),
        "payload": payload,
    }


class TestS75VpVnpR5(unittest.TestCase):
    # ------------------------------------------------------------------
    # Fast Oracle & Helper Invariant Tests (01..02)
    # ------------------------------------------------------------------

    def test_01_all_seven_oracles_exact_values(self) -> None:
        res = probe.run_all_mechanism_probes()
        self.assertEqual(len(res), 7)

        o1 = res["oracle_1_meixner_crossing"]
        self.assertEqual(o1["recip_checks"], 36)
        self.assertEqual(o1["orth_checks"], 216)
        self.assertEqual(o1["theta"], 16)
        self.assertEqual(o1["max_deg_psi"], 16)
        self.assertEqual(o1["x1_sign"], 1)
        self.assertEqual(o1["x1_matched_count"], 4)
        self.assertEqual(o1["reflection_checks"], 16)
        self.assertEqual(o1["max_ad_bc_rank"], 4)
        self.assertEqual(o1["p_energy_0_to_6"], [1, 1, 2, 2, 4, 4, 7])
        self.assertEqual(o1["ad_bc_rank_profile"][0], 1)
        self.assertEqual(o1["ad_bc_rank_profile"][2], 3)
        self.assertEqual(o1["ad_bc_rank_profile"][16], 4)

        o2 = res["oracle_2_cat0_mat_f2_dichotomy"]
        self.assertEqual(o2["mat2_rank_hist"], [1, 9, 6])
        self.assertEqual(o2["mat3_rank_hist"], [1, 49, 294, 168])
        self.assertEqual(o2["cube_pairs_verified"], 64)
        self.assertEqual(o2["tree_cn_gap"], "2")
        self.assertEqual(o2["non_euclidean_gram_det"], "-1/4")
        self.assertEqual(o2["non_euclidean_quad_form"], "-1")

        o3 = res["oracle_3_flat_perm_and_hubs"]
        self.assertEqual(o3["prop_e1_matrix_dim"], 9)
        self.assertEqual(o3["direct_grid_sum"], 31075)
        self.assertEqual(o3["perm_q_exact"], "31075")
        self.assertEqual(o3["fp_matches"], {"F_3": 1, "F_5": 0})
        self.assertEqual(o3["char2_cleared_perm_mod2"], 0)
        self.assertEqual(o3["char2_true_sum_mod2"], 1)
        self.assertEqual(o3["f31_monomial_count"], 8)
        self.assertEqual(o3["balanced_cuts_checked"], 334)
        self.assertEqual(o3["min_81_normsq_over_k3"], "21/4")
        self.assertEqual(o3["exponent_scaling_checks"], 5)

        o4 = res["oracle_4_char2_perm_vs_hc_and_s41"]
        self.assertEqual(o4["char2_3x3_det_perm_hc"], [0, 0, 1])
        self.assertEqual(o4["char2_4x4_det_perm_hc"], [0, 0, 1])
        self.assertEqual(o4["s41_polya_3x3_valid_sign_maps"], 0)
        self.assertEqual(o4["prop_m2_vertices"], 39)
        self.assertEqual(o4["prop_m2_hc_exact_z"], 27)
        self.assertEqual(o4["prop_m2_direct_sum"], 27)
        self.assertEqual(o4["prop_m2_mod_checks"], {"F_2": 1, "F_3": 0, "F_5": 2})

        o5 = res["oracle_5_contracting_unitriangular"]
        self.assertEqual(o5["u4_u5_general_rank1_checked"], 95)
        self.assertEqual(o5["u4_u5_endpoint1_checked"], 44)
        self.assertEqual(o5["max_endpoint1_gen_mult"], 4)
        self.assertEqual(o5["max_general_gen_mult"], 16)
        self.assertEqual(o5["sl3_tower_commutator_checks"], 54)

        o6 = res["oracle_6_lowdeg_parse_tree_and_diag"]
        self.assertEqual(o6["rings_verified"], ["Z", "F_2", "F_3", "F_5"])
        self.assertEqual(o6["output_degree"], 5)
        self.assertEqual(o6["boolean_points_identical"], 8)
        self.assertEqual(o6["boolean_f_deg3_terms"], 1)
        self.assertEqual(o6["boolean_g_deg3_terms"], 0)
        self.assertEqual(o6["finite_field_squaring_periods"], {"F_3": 1, "F_5": 1, "F_7": 2})

        o7 = res["oracle_7_border_laurent_closure"]
        self.assertEqual(o7["lem_n2_cutoff_n"], 16)
        self.assertEqual(o7["lem_n2_rings_verified"], ["Z", "F_2"])
        self.assertEqual(o7["lem_n3_cover_n32_lhs"], 276922881)
        self.assertEqual(o7["lem_n3_cover_n32_rhs"], 4294967296)
        self.assertEqual(o7["prop_n4_sigma_r"], 3)
        self.assertEqual(o7["prop_n4_min_exp_after_sigma_r"], 0)
        self.assertEqual(o7["prop_n4_eps0_after_sigma_r"], 7)
        self.assertEqual(o7["prop_n4_mod_2w_extracted_eps0"], 17)

    def test_02_probe_helper_edge_cases(self) -> None:
        with self.assertRaises(probe.ProbeError):
            probe._require(False, "boom")
        self.assertEqual(probe._poly_trim(()), ())
        self.assertEqual(probe._poly_trim((0, 0)), ())
        self.assertEqual(probe._poly_trim((1, 0)), (1,))
        self.assertEqual(probe._poly_mul((), (1, 2)), ())
        self.assertEqual(probe._poly_mul((1, 2), ()), ())
        self.assertEqual(probe._poly_mul((2, 0, 3), (0, 5)), (0, 10, 0, 15))
        self.assertEqual(probe._poly_shift((), 3), ())
        self.assertEqual(probe._poly_sub_x2(()), ())
        self.assertEqual(probe._poly_sub_x2((3, 5)), (3, 0, 5))

        self.assertEqual(probe._rank_q([]), 0)
        self.assertEqual(probe._rank_q([[]]), 0)
        self.assertEqual(probe._rank_q([[0, 0], [0, 0]]), 0)
        self.assertEqual(probe._rank_q([[1, 2], [2, 4]]), 1)
        self.assertEqual(probe._rank_q([[0, 1], [1, 0]]), 2)

        self.assertEqual(probe._det_q([[Fraction(0), Fraction(0)], [Fraction(0), Fraction(1)]]), Fraction(0))
        self.assertEqual(probe._det_q([[Fraction(0), Fraction(1)], [Fraction(1), Fraction(0)]]), Fraction(-1))
        self.assertEqual(probe._det_q([[Fraction(1), Fraction(2)], [Fraction(0), Fraction(3)]]), Fraction(3))
        self.assertEqual(probe._det_mod([[0, 1], [1, 0]], 3), 2)
        self.assertEqual(probe._det_mod([[1, 2], [2, 4]], 5), 0)
        self.assertEqual(probe._det_mod([[1, 0], [0, 2]], 5), 2)

        b_tbl, c_tbl = probe._meixner_tables(2, 2)
        s0 = ((0,), (0,))
        mat0 = probe._build_crossing_matrix(s0, s0, s0, s0, b_tbl, c_tbl)
        self.assertEqual(mat0[0][0], ())
        self.assertEqual(mat0[1][1], ())
        self.assertEqual(mat0[3][3], ())
        self.assertEqual(mat0[1][3], (0, -1))
        self.assertEqual(mat0[3][1], (0, 1))

        self.assertEqual(probe._hc_sum_sparse({0: {1: 0, 2: 3}, 1: {0: 5}, 2: {1: 7}}, 3), 105)
        self.assertEqual(probe._hc_sum_sparse({0: {1: 1}, 1: {2: 1}, 2: {0: 0}}, 3), 0)

        self.assertEqual(probe._mvpoly_add({(1,): 2}, {(1,): -2}, 0), {})
        self.assertEqual(probe._mvpoly_mul({(1,): 2}, {(1,): 3}, 6), {})
        self.assertEqual(probe._mvpoly_scale({(1,): 3}, 0, 0), {})
        self.assertEqual(probe._mvpoly_scale({(1,): 2}, 4, 2), {})
        self.assertEqual(probe._mvpoly_scale({(1,): 3}, 2, 6), {})
        self.assertEqual(probe._laurent_add({0: 2}, {0: -2}, 0), {})
        self.assertEqual(probe._laurent_add({0: 1}, {0: 1}, 2), {})
        self.assertEqual(probe._laurent_mul({0: 2}, {0: 3}, 6), {})

    # ------------------------------------------------------------------
    # Canonical Exact Rational Parser Tests (03 — closes S75-DEF-03)
    # ------------------------------------------------------------------

    def test_03_parse_q_canonical_strict_and_dos_safe(self) -> None:
        self.assertEqual(verifier.parse_q("0"), Fraction(0))
        self.assertEqual(verifier.parse_q("9"), Fraction(9))
        self.assertEqual(verifier.parse_q("-1/4"), Fraction(-1, 4))
        self.assertEqual(verifier.parse_q("21/4"), Fraction(21, 4))
        max_ok = (1 << verifier._MAX_INT_BITS) - 1
        self.assertEqual(verifier.parse_q(str(max_ok)), Fraction(max_ok, 1))
        self.assertEqual(verifier.parse_q("1/" + str(max_ok)), Fraction(1, max_ok))

        bad_inputs = [
            123,
            None,
            "",
            "-",
            "-0",
            "01",
            "-01",
            "1/02",
            "2/4",
            "3/1",
            "0/2",
            " 1",
            "1 ",
            "+1",
            "1/2/3",
            "1/0",
            "1/-2",
            "1/",
            "/2",
            "1.5",
            "1e3",
            "\u0661",
            "1/\u0662",
            "/",
            ":",
            str(1 << verifier._MAX_INT_BITS),
            "9" * 1001,
            "1/" + "9" * 1001,
            "9" * 5001,
            "1/" + "9" * 5001,
        ]
        for bad in bad_inputs:
            with self.assertRaises(verifier.VerifyError, msg=f"Should reject {bad!r}"):
                verifier.parse_q(bad)
        with self.assertRaisesRegex(verifier.VerifyError, "Negative sign disallowed"):
            verifier.parse_q("1/-2")
        with self.assertRaisesRegex(verifier.VerifyError, "oversized"):
            verifier.parse_q("9" * 1001)

    # ------------------------------------------------------------------
    # Certificate Generation, FR0/SEC Exhaustive Tamper & Replay (04..05)
    # ------------------------------------------------------------------

    def _mutate_leaf(self, val: object) -> object:
        if type(val) is int:
            return val + 1
        if type(val) is str:
            if "/" in val:
                try:
                    q = verifier.parse_q(val)
                    return f"{q.numerator + 1}/{q.denominator}" if (q.numerator + 1) % q.denominator else f"{q.numerator + 2}/{q.denominator}"
                except verifier.VerifyError:
                    return val + "_tampered"
            if val.lstrip("-").isascii() and val.lstrip("-").isnumeric():
                return str(int(val) + 1)
            return val + "_tampered"
        return val

    def _walk_and_tamper(self, base_payload: dict, path: tuple, node: object, count: list) -> None:
        if type(node) is dict:
            for k in list(node.keys()):
                p_miss = copy.deepcopy(base_payload)
                cur = p_miss
                for step in path:
                    cur = cur[step]
                del cur[k]
                with self.assertRaises(verifier.VerifyError, msg=f"missing key {path + (k,)}"):
                    verifier.secondary_audit_payload(p_miss)
                count[0] += 1
            p_extra = copy.deepcopy(base_payload)
            cur = p_extra
            for step in path:
                cur = cur[step]
            cur["__unexpected_key__"] = 1
            with self.assertRaises(verifier.VerifyError, msg=f"extra key at {path}"):
                verifier.secondary_audit_payload(p_extra)
            count[0] += 1
            for k, v in node.items():
                self._walk_and_tamper(base_payload, path + (k,), v, count)
        elif type(node) is list:
            p_len = copy.deepcopy(base_payload)
            cur = p_len
            for step in path[:-1]:
                cur = cur[step]
            cur[path[-1]] = cur[path[-1]][:-1]
            with self.assertRaises(verifier.VerifyError, msg=f"bad list len at {path}"):
                verifier.secondary_audit_payload(p_len)
            count[0] += 1
            for idx, item in enumerate(node):
                self._walk_and_tamper(base_payload, path + (idx,), item, count)
        else:
            p_mut = copy.deepcopy(base_payload)
            cur = p_mut
            for step in path[:-1]:
                cur = cur[step]
            cur[path[-1]] = self._mutate_leaf(node)
            resigned = _resign(p_mut)
            with self.assertRaises(verifier.VerifyError, msg=f"FR0 bypass at {path}"):
                verifier.verify_certificate_dict(resigned, full_replay=False)
            with self.assertRaises(verifier.VerifyError, msg=f"SEC bypass at {path}"):
                verifier.secondary_audit(resigned)
            count[0] += 1

    def test_04_certificate_fr1_fr0_sec_and_exhaustive_tamper(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            cpath = os.path.join(td, "cert.json")
            wres = verifier.write_certificate_file(cpath)
            self.assertTrue(wres["ok"])
            self.assertEqual(stat.S_IMODE(os.lstat(cpath).st_mode), 0o600)
            cres = verifier.verify_certificate_file(cpath)
            self.assertEqual(cres["payload_sha256"], wres["payload_sha256"])

            cert = verifier.build_certificate()
            res_fr0 = verifier.verify_certificate_dict(cert, full_replay=False)
            self.assertTrue(res_fr0["ok"])
            self.assertFalse(res_fr0["full_replay"])
            self.assertTrue(res_fr0["secondary_audit_passed"])
            self.assertTrue(verifier.secondary_audit(cert)["secondary_audit_passed"])
            with self.assertRaisesRegex(verifier.VerifyError, "schema_version mismatch"):
                verifier.secondary_audit(dict(cert, schema_version="wrong"))
            with self.assertRaisesRegex(verifier.VerifyError, "64-char lowercase hex"):
                verifier.secondary_audit(dict(cert, payload_sha256="\u00e9" * 64))

            for bad_fr in (1, 0, "true", None):
                with self.assertRaises(verifier.VerifyError):
                    verifier.verify_certificate_dict(cert, full_replay=bad_fr)  # type: ignore[arg-type]

            with self.assertRaisesRegex(verifier.VerifyError, "root must be a plain dict"):
                verifier.verify_certificate_dict([])
            bad_keys = dict(cert, extra=1)
            with self.assertRaisesRegex(verifier.VerifyError, "root keys mismatch"):
                verifier.verify_certificate_dict(bad_keys)
            bad_ver = dict(cert, schema_version="wrong")
            with self.assertRaisesRegex(verifier.VerifyError, "schema_version mismatch"):
                verifier.verify_certificate_dict(bad_ver)
            for bad_sha in (123, "abc", "A" * 64, "g" * 64):
                with self.assertRaisesRegex(verifier.VerifyError, "64-char lowercase hex"):
                    verifier.verify_certificate_dict(dict(cert, payload_sha256=bad_sha))
            with self.assertRaisesRegex(verifier.VerifyError, "payload must be a plain dict"):
                verifier.verify_certificate_dict(dict(cert, payload="not-a-dict"))
            with self.assertRaisesRegex(verifier.VerifyError, "digest mismatch"):
                verifier.verify_certificate_dict(dict(cert, payload_sha256="0" * 64))

            # Full replay mismatch when build_certificate diverges
            fake_fresh = copy.deepcopy(cert)
            fake_fresh["payload_sha256"] = "f" * 64
            with mock.patch.object(verifier, "build_certificate", return_value=fake_fresh):
                with self.assertRaisesRegex(verifier.VerifyError, "clean-room recomputation"):
                    verifier.verify_certificate_dict(cert, full_replay=True)

            # Bool-as-int and non-str/non-list type checks in secondary audit helpers
            with self.assertRaises(verifier.VerifyError):
                verifier._require_exact_int(True, 1, "b")
            with self.assertRaises(verifier.VerifyError):
                verifier._require_exact_int_list([True], [1], "bl")
            with self.assertRaises(verifier.VerifyError):
                verifier._require_exact_int_list((1,), [1], "tl")
            with self.assertRaises(verifier.VerifyError):
                verifier._require_exact_str_list([1], ["1"], "sl")

            class _StrSub(str):
                pass

            with self.assertRaises(verifier.VerifyError):
                verifier._require_exact_str_list([_StrSub("Z")], ["Z"], "ss")
            with self.assertRaises(verifier.VerifyError):
                verifier._require_exact_str_list(("a",), ["a"], "ts")
            with self.assertRaises(verifier.VerifyError):
                verifier._require_exact_dict([], frozenset(), "nd")

            # Exhaustive re-signed leaf & schema tamper sweep over ALL 7 oracles
            count = [0]
            self._walk_and_tamper(cert["payload"], (), cert["payload"], count)
            self.assertGreater(count[0], 120)

            # Malformed UTF-8 and JSON files
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
        self.assertEqual(res["oracles_passed"], 7)

    # ------------------------------------------------------------------
    # Hardened dir_fd I/O, Hardlink/FIFO Write Rejection & Darwin (06..07)
    # ------------------------------------------------------------------

    def test_06_hardened_dirfd_path_and_io_adversarial(self) -> None:
        with self.assertRaisesRegex(verifier.VerifyError, "non-empty string"):
            verifier._validate_path("")
        with self.assertRaisesRegex(verifier.VerifyError, "non-empty string"):
            verifier._validate_path(42)
        for bad_p in ("", 42, "bad\x00path", "bad\ud800surr"):
            with self.assertRaises(verifier.VerifyError):
                verifier.verify_certificate_file(bad_p)  # type: ignore[arg-type]
            with self.assertRaises(verifier.VerifyError):
                verifier.write_certificate_file(bad_p)  # type: ignore[arg-type]
            with self.assertRaises(verifier.VerifyError):
                verifier.verify_lean_file(bad_p)  # type: ignore[arg-type]

        # Darwin root-alias normalization mocked
        p_var = Path("/var/tmp/x")
        st_root_lnk = os.stat_result((stat.S_IFLNK | 0o777, 0, 0, 1, 0, 0, 0, 0, 0, 0))
        st_user_lnk = os.stat_result((stat.S_IFLNK | 0o777, 0, 0, 1, 1000, 0, 0, 0, 0, 0))
        st_root_dir = os.stat_result((stat.S_IFDIR | 0o755, 0, 0, 2, 0, 0, 0, 0, 0, 0))
        with mock.patch.object(sys, "platform", "linux"), mock.patch.object(
            os, "lstat", return_value=st_root_lnk
        ), mock.patch.object(os, "readlink", return_value="/private/var"):
            self.assertEqual(verifier._normalize_darwin_system_prefix(p_var), p_var)
        with mock.patch.object(sys, "platform", "darwin"):
            with mock.patch.object(os, "lstat", return_value=st_root_lnk), mock.patch.object(
                os, "readlink", return_value="private/var"
            ):
                self.assertEqual(verifier._normalize_darwin_system_prefix(Path("x/var/y")), Path("x/var/y"))
                self.assertEqual(verifier._normalize_darwin_system_prefix(Path("/var"), allow_exact=False), Path("/var"))
                self.assertEqual(verifier._normalize_darwin_system_prefix(Path("/var/../etc/x")), Path("/var/../etc/x"))
                self.assertEqual(verifier._normalize_darwin_system_prefix(Path("/usr/local/x")), Path("/usr/local/x"))
                self.assertEqual(verifier._normalize_darwin_system_prefix(Path("/var/tmp/x")), Path("/private/var/tmp/x"))
                self.assertEqual(verifier._normalize_darwin_system_prefix(Path("/var"), allow_exact=True), Path("/private/var"))
            with mock.patch.object(os, "lstat", return_value=st_root_lnk), mock.patch.object(
                os, "readlink", return_value="/private/tmp"
            ):
                self.assertEqual(verifier._normalize_darwin_system_prefix(Path("/tmp/a/b")), Path("/private/tmp/a/b"))
            with mock.patch.object(os, "lstat", return_value=st_user_lnk), mock.patch.object(
                os, "readlink", return_value="/private/var"
            ):
                self.assertEqual(verifier._normalize_darwin_system_prefix(p_var), p_var)
            with mock.patch.object(os, "lstat", return_value=st_root_dir), mock.patch.object(
                os, "readlink", return_value="/private/var"
            ):
                self.assertEqual(verifier._normalize_darwin_system_prefix(p_var), p_var)
            with mock.patch.object(os, "lstat", return_value=st_root_lnk), mock.patch.object(
                os, "readlink", return_value="/evil/var"
            ):
                self.assertEqual(verifier._normalize_darwin_system_prefix(p_var), p_var)
            with mock.patch.object(os, "lstat", side_effect=OSError("no")):
                self.assertEqual(verifier._normalize_darwin_system_prefix(p_var), p_var)

        with tempfile.TemporaryDirectory() as td:
            real_f = os.path.join(td, "real.json")
            verifier.write_certificate_file(real_f)
            real_bytes = verifier._read_bytes_safe(real_f)
            verifier._write_bytes_atomic_safe(real_f, real_bytes)
            self.assertEqual(verifier._read_bytes_safe(real_f, max_bytes=len(real_bytes)), real_bytes)
            with self.assertRaisesRegex(verifier.VerifyError, "exceeds maximum permitted size"):
                verifier._read_bytes_safe(real_f, max_bytes=len(real_bytes) - 1)

            # Symlink rejected on BOTH read and write
            sym = os.path.join(td, "sym.json")
            os.symlink(real_f, sym)
            with self.assertRaisesRegex(verifier.VerifyError, "Symlink"):
                verifier._read_bytes_safe(sym)
            with self.assertRaisesRegex(verifier.VerifyError, "symlink write target"):
                verifier._write_bytes_atomic_safe(sym, b"x")

            # Directory rejected on BOTH read and write
            sub_d = os.path.join(td, "sub")
            os.mkdir(sub_d)
            with self.assertRaises(verifier.VerifyError):
                verifier._read_bytes_safe(sub_d)
            with self.assertRaisesRegex(verifier.VerifyError, "non-regular write target"):
                verifier._write_bytes_atomic_safe(sub_d, b"x")

            # FIFO rejected on BOTH read and write (closes S75-DEF-03!)
            fifo = os.path.join(td, "pipe.fifo")
            os.mkfifo(fifo, 0o600)
            with self.assertRaisesRegex(verifier.VerifyError, "regular file"):
                verifier._read_bytes_safe(fifo)
            with self.assertRaisesRegex(verifier.VerifyError, "non-regular write target"):
                verifier._write_bytes_atomic_safe(fifo, b"x")

            # Hardlink rejected on BOTH read and write (closes S75-DEF-03!)
            hard = os.path.join(td, "hard.json")
            os.link(real_f, hard)
            with self.assertRaisesRegex(verifier.VerifyError, "hard-linked"):
                verifier._read_bytes_safe(hard)
            with self.assertRaisesRegex(verifier.VerifyError, "hard-linked write target"):
                verifier._write_bytes_atomic_safe(hard, b"x")
            os.unlink(hard)

            # Missing file -> typed VerifyError
            with self.assertRaises(verifier.VerifyError):
                verifier._read_bytes_safe(os.path.join(td, "missing.json"))

            # Bad target names & parent errors
            for bad_out in (td + "/", os.path.join(td, "."), os.path.join(td, ".."), "/"):
                with self.assertRaisesRegex(verifier.VerifyError, "must name a regular file"):
                    verifier._write_bytes_atomic_safe(bad_out, b"x")
            with self.assertRaisesRegex(verifier.VerifyError, "Directory unavailable"):
                verifier._write_bytes_atomic_safe(os.path.join(td, "no_such_dir", "a.json"), b"x")
            with self.assertRaisesRegex(verifier.VerifyError, "real directory"):
                verifier._write_bytes_atomic_safe(os.path.join(real_f, "child.json"), b"x")
            with self.assertRaisesRegex(verifier.VerifyError, "traversal"):
                verifier._read_bytes_safe(os.path.join(td, "sub", "..", "real.json"))

            # Symlink ancestor rejected on BOTH read and write
            sym_sub = os.path.join(td, "sym_sub")
            os.symlink(sub_d, sym_sub)
            with self.assertRaisesRegex(verifier.VerifyError, "Symlink"):
                verifier._read_bytes_safe(os.path.join(sym_sub, "x.json"))
            with self.assertRaisesRegex(verifier.VerifyError, "Symlink"):
                verifier._write_bytes_atomic_safe(os.path.join(sym_sub, "x.json"), b"x")

            # $PWD symlink & relative path checks
            old_cwd = os.getcwd()
            try:
                os.chdir(sub_d)
                with open(os.path.join(sub_d, "rel.bin"), "wb") as fh:
                    fh.write(b"rel")
                with mock.patch.dict(os.environ, {"PWD": sub_d}, clear=False):
                    self.assertEqual(verifier._read_bytes_safe("./rel.bin"), b"rel")
                with mock.patch.object(os, "environ", {}):
                    self.assertEqual(verifier._read_bytes_safe("rel.bin"), b"rel")
                with mock.patch.object(os, "environ", {"PWD": "rel/pwd"}):
                    self.assertEqual(verifier._read_bytes_safe("rel.bin"), b"rel")
                with mock.patch.object(os, "environ", {"PWD": "."}):
                    self.assertEqual(verifier._read_bytes_safe("rel.bin"), b"rel")
                with mock.patch.dict(os.environ, {"PWD": os.path.join(td, "missing_pwd")}, clear=False):
                    self.assertEqual(verifier._read_bytes_safe("rel.bin"), b"rel")
                with mock.patch.dict(os.environ, {"PWD": td}, clear=False):
                    self.assertEqual(verifier._read_bytes_safe("rel.bin"), b"rel")
                with mock.patch.dict(os.environ, {"PWD": sym_sub}, clear=False):
                    with self.assertRaisesRegex(verifier.VerifyError, "Symlink"):
                        verifier._read_bytes_safe("rel.bin")
                with mock.patch.dict(os.environ, {"PWD": ""}, clear=False):
                    with mock.patch("os.getcwd", side_effect=OSError("deleted cwd")):
                        with self.assertRaisesRegex(verifier.VerifyError, "Cannot resolve working directory"):
                            verifier._write_bytes_atomic_safe("relative.json", b"x")
                with mock.patch.dict(os.environ, {"PWD": sub_d}, clear=False):
                    verifier._write_bytes_atomic_safe("rel_ok.json", b"ok\n")
                    self.assertEqual(verifier._read_bytes_safe("rel_ok.json"), b"ok\n")
            finally:
                os.chdir(old_cwd)

            # Mocked TOCTOU & I/O fault branches (zero temp-file leaks!)
            before_files = set(os.listdir(td))
            with mock.patch("os.open", side_effect=OSError(errno.EACCES, "denied")):
                with self.assertRaises(verifier.VerifyError):
                    verifier._open_dir_chain_nofollow(("a",))

            real_open = os.open

            def open_enotdir(path, flags, *args, **kwargs):
                if path == "symcomp":
                    raise OSError(errno.ENOTDIR, "not dir")
                return real_open(path, flags, *args, **kwargs)

            st_sym = os.stat_result((stat.S_IFLNK | 0o777, 1, 1, 1, 0, 0, 0, 0, 0, 0))
            with mock.patch("os.open", side_effect=open_enotdir):
                with mock.patch("os.lstat", return_value=st_sym):
                    with self.assertRaisesRegex(verifier.VerifyError, "Symlink"):
                        verifier._open_dir_chain_nofollow(("symcomp",))
                with mock.patch("os.lstat", side_effect=OSError("no")):
                    with self.assertRaisesRegex(verifier.VerifyError, "real directory"):
                        verifier._open_dir_chain_nofollow(("symcomp",))

            with mock.patch.dict(os.environ, {"PWD": td}, clear=False):
                with mock.patch("os.stat", side_effect=OSError("no dot")):
                    with self.assertRaises(verifier.VerifyError):
                        verifier._verify_pwd_not_symlink()
                st_same = os.stat(td)
                st_diff = os.stat_result((stat.S_IFDIR | 0o755, st_same.st_ino + 99, st_same.st_dev, 2, 0, 0, 0, 0, 0, 0))
                with mock.patch("os.stat", return_value=st_same), mock.patch("os.fstat", return_value=st_diff):
                    with self.assertRaisesRegex(verifier.VerifyError, "changed"):
                        verifier._verify_pwd_not_symlink()

            with mock.patch("os.fstat", side_effect=OSError("fstat fail")):
                with self.assertRaises(verifier.VerifyError):
                    verifier._read_bytes_safe(real_f)
            with mock.patch("os.read", side_effect=OSError("read fail")):
                with self.assertRaises(verifier.VerifyError):
                    verifier._read_bytes_safe(real_f)
            with mock.patch("os.lstat", side_effect=OSError(errno.EIO, "io")):
                with self.assertRaises(verifier.VerifyError):
                    verifier._write_bytes_atomic_safe(os.path.join(td, "w.bin"), b"x")

            calls = [0]

            def open_eexist_once(path, flags, *args, **kwargs):
                if isinstance(path, str) and path.startswith(".w1.bin.tmp."):
                    calls[0] += 1
                    if calls[0] == 1:
                        raise FileExistsError("exists")
                return real_open(path, flags, *args, **kwargs)

            with mock.patch("os.open", side_effect=open_eexist_once):
                verifier._write_bytes_atomic_safe(os.path.join(td, "w1.bin"), b"ok")
            self.assertEqual(calls[0], 2)
            os.unlink(os.path.join(td, "w1.bin"))

            def open_eexist_always(path, flags, *args, **kwargs):
                if isinstance(path, str) and path.startswith(".w2.bin.tmp."):
                    raise FileExistsError("exists")
                return real_open(path, flags, *args, **kwargs)

            with mock.patch("os.open", side_effect=open_eexist_always):
                with self.assertRaisesRegex(verifier.VerifyError, "Exhausted"):
                    verifier._write_bytes_atomic_safe(os.path.join(td, "w2.bin"), b"ok")

            def open_eacces_tmp(path, flags, *args, **kwargs):
                if isinstance(path, str) and path.startswith(".w3.bin.tmp."):
                    raise OSError(errno.EACCES, "denied")
                return real_open(path, flags, *args, **kwargs)

            with mock.patch("os.open", side_effect=open_eacces_tmp):
                with self.assertRaisesRegex(verifier.VerifyError, "Cannot create atomic temp file"):
                    verifier._write_bytes_atomic_safe(os.path.join(td, "w3.bin"), b"ok")

            with mock.patch("os.write", return_value=0):
                with self.assertRaisesRegex(verifier.VerifyError, "Short write"):
                    verifier._write_bytes_atomic_safe(os.path.join(td, "short.json"), b"abc")
            self.assertEqual(set(os.listdir(td)), before_files)

            st_real = os.lstat(real_f)
            st_fifo = os.stat_result((stat.S_IFIFO | 0o600, st_real.st_ino, st_real.st_dev, 1, 0, 0, 0, 0, 0, 0))
            st_hl = os.stat_result((stat.S_IFREG | 0o600, st_real.st_ino, st_real.st_dev, 2, 0, 0, 5, 0, 0, 0))
            for bad_tmp in (st_fifo, st_hl):
                with mock.patch("os.fstat", return_value=bad_tmp):
                    with self.assertRaisesRegex(verifier.VerifyError, "regular/single-link"):
                        verifier._write_bytes_atomic_safe(os.path.join(td, "badtmp.json"), b"abc")
            self.assertEqual(set(os.listdir(td)), before_files)

            for race_st, pat in (
                (st_sym, "Symlink appeared"),
                (st_fifo, "Non-regular file appeared"),
                (st_hl, "Hard-link appeared"),
            ):
                seq = [FileNotFoundError(), race_st]

                def lstat_race(*args, **kwargs):
                    nxt = seq.pop(0)
                    if isinstance(nxt, BaseException):
                        raise nxt
                    return nxt

                with mock.patch("os.lstat", side_effect=lstat_race):
                    with self.assertRaisesRegex(verifier.VerifyError, pat):
                        verifier._write_bytes_atomic_safe(os.path.join(td, "race.json"), b"abc")
            self.assertEqual(set(os.listdir(td)), before_files)

            with mock.patch("os.replace", side_effect=OSError("EXDEV")), mock.patch(
                "os.unlink", side_effect=OSError("unlink fail")
            ):
                with self.assertRaisesRegex(verifier.VerifyError, "Atomic write failed"):
                    verifier._write_bytes_atomic_safe(os.path.join(td, "norep.json"), b"abc")
            for f in os.listdir(td):
                if f.startswith(".norep.json.tmp."):
                    os.unlink(os.path.join(td, f))
            self.assertEqual(set(os.listdir(td)), before_files)

            with mock.patch("os.fsync", side_effect=KeyboardInterrupt()):
                with self.assertRaises(KeyboardInterrupt):
                    verifier._write_bytes_atomic_safe(os.path.join(td, "kb.json"), b"abc")
            self.assertEqual(set(os.listdir(td)), before_files)

    def test_07_build_certificate_malformed_and_invariant_guards(self) -> None:
        good = probe.run_all_mechanism_probes()

        bad_type1 = dict(good, oracle_2_cat0_mat_f2_dichotomy="oops")
        with mock.patch.object(probe, "run_all_mechanism_probes", return_value=bad_type1):
            with self.assertRaises(verifier.VerifyError):
                verifier.build_certificate()

        bad_type2 = dict(good, oracle_3_flat_perm_and_hubs="oops")
        with mock.patch.object(probe, "run_all_mechanism_probes", return_value=bad_type2):
            with self.assertRaises(verifier.VerifyError):
                verifier.build_certificate()

        bad_det = copy.deepcopy(good)
        bad_det["oracle_2_cat0_mat_f2_dichotomy"]["non_euclidean_gram_det"] = "0"
        with mock.patch.object(probe, "run_all_mechanism_probes", return_value=bad_det):
            with self.assertRaises(verifier.VerifyError):
                verifier.build_certificate()

        bad_quad = copy.deepcopy(good)
        bad_quad["oracle_2_cat0_mat_f2_dichotomy"]["non_euclidean_quad_form"] = "0"
        with mock.patch.object(probe, "run_all_mechanism_probes", return_value=bad_quad):
            with self.assertRaises(verifier.VerifyError):
                verifier.build_certificate()

        bad_ratio = copy.deepcopy(good)
        bad_ratio["oracle_3_flat_perm_and_hubs"]["min_81_normsq_over_k3"] = "3"
        with mock.patch.object(probe, "run_all_mechanism_probes", return_value=bad_ratio):
            with self.assertRaises(verifier.VerifyError):
                verifier.build_certificate()

    # ------------------------------------------------------------------
    # Full R9+ Lean 4 Static Scanner & Mocked Subprocess Tests (08..09)
    # ------------------------------------------------------------------

    def test_08_lean_lexer_and_r9_plus_static_bypasses(self) -> None:
        base_prints = "\n".join(f"#print axioms {t}" for t in verifier.EXPECTED_LEAN_THEOREMS) + "\n"
        res = verifier.audit_lean_source("theorem ok : 1 = 1 := by rfl\n" + base_prints)
        self.assertTrue(res["static_clean"])
        self.assertEqual(res["expected_theorems_declared"], 15)

        clean_samples = [
            "-- sorry axiom native_decide #eval initialize\ntheorem t : 1 = 1 := by rfl\n",
            "/- outer /- nested / - sorry -/ still / - comment -/\ntheorem t : 1 = 1 := by decide\n",
            'def s1 := "sorry \\" \\n axiom"\ndef s2 := r"sorry"\ndef s3 := r#"sorry"#\ndef s3b := r##"hello "# sorry"##\n',
            'def s4 (x : Nat) := s!"prefix \\n { { a := x } } sorry"\ndef s5 := m!"axiom"\ndef s6 := f!"unsafe"\n',
            'def s7 := s! "hello \\{sorry}"\ndef s8 := s!a "{sorry}"\ndef s9 := s! r"ok" "{sorry}"\n',
            'def s10 := s! «tok» "{sorry}"\ndef s11 := s! \'a\' "{sorry}"\n',
            'def s12 := s! "{ let _ := s! { a := 1 }; def b := "{sorry}" }"\ndef s13 := s! "{ s! }" ++ "{sorry}"\n',
            'def sp := panic!"sorry inside panic"\n',
            "def c1 : Char := '\"'\ndef c2 : Char := '\\''\ndef c3 : Char := '\\x27'\ndef c4 : Char := '\\u0027'\n",
            "def f (r : Nat) (x' : Nat) := r + x' + (1 / 2)\ntheorem t1 : 1 = 1 := by decide -native\n",
            "theorem t2 : 1 = 1 := by decide (native := false)\n",
            "theorem t3 : 1 = 1 := by decide (native := (Bool.false))\n",
            "theorem t4 : 1 = 1 := by decide (config := { native := false })\n",
            "theorem t5 : 1 = 1 := by decide (config := ({ }))\n",
            "theorem t6 : 1 = 1 := by decide (config := { native := false, zeta := true })\n",
            "def cfg : DecideConfig := { native := false }\n",
            "def dotOk := Foo.partial + Foo.axiom + Foo.opaque + Foo.unsafe + Foo.run_cmd + Foo.initialize + Foo.builtin_initialize + Foo.macro\n",
            "def «cleanName» := 1\ndef «clean + op» := 2\n",
            'def a := bar"{sorry}"\ndef b := x.r"{sorry}"\ndef c := !"{sorry}"\n',
            "def u := ) + ] + (1 / 2)\ntheorem t8 : 1 = 1 := by decide (config := ({ }))\n",
            "theorem a : 1 = 1 := by decide + 1\ntheorem c : 1 = 1 := by decide (1\ntheorem d : 1 = 1 := by decide (1)\n",
            "def x := 'a\ndef y := '\\xZZ'\ndef z := '\\uZZZZ'\nattribute [unclosed\ndef r_id := r#1\n",
        ]
        for idx, snip in enumerate(clean_samples):
            self.assertTrue(verifier.audit_lean_source(snip + base_prints)["static_clean"], f"FP on {idx}")

        # Direct helper boundary checks (kills all lexer BoolOps!)
        self.assertFalse(verifier._is_lean4_ident_prev("x", -1))
        self.assertTrue(verifier._is_lean4_ident_prev("x", 0))
        self.assertTrue(verifier._is_lean4_ident_prev("_", 0))
        self.assertTrue(verifier._is_lean4_ident_prev(".", 0))
        self.assertTrue(verifier._is_lean4_ident_prev("'", 0))
        self.assertFalse(verifier._is_lean4_ident_prev("!", 0))
        self.assertFalse(verifier._is_lean4_ident_prev("!!", 1))
        self.assertFalse(verifier._is_lean4_ident_prev(" !", 1))
        self.assertTrue(verifier._is_lean4_ident_prev("a!", 1))
        self.assertTrue(verifier._is_lean4_ident_prev("a!!", 2))
        self.assertTrue(verifier._is_lean4_ident_prev("_!", 1))
        self.assertTrue(verifier._is_lean4_ident_prev("'?", 1))
        self.assertEqual(verifier.strip_lean_comments_and_literals("'a'"), "   ")
        self.assertEqual(verifier.strip_lean_comments_and_literals("'\\''"), "    ")
        self.assertEqual(verifier.strip_lean_comments_and_literals("'\\x27'"), "      ")
        self.assertEqual(verifier.strip_lean_comments_and_literals("'\\u0027'"), "        ")
        self.assertEqual(verifier.strip_lean_comments_and_literals("def «a b» := 1"), "def       := 1")
        self.assertEqual(verifier.strip_lean_comments_and_literals("def a := '"), "def a := '")
        self.assertEqual(verifier.strip_lean_comments_and_literals("def a := '\\"), "def a := '\\")
        self.assertEqual(verifier.strip_lean_comments_and_literals("def a := '\\'"), "def a := '\\'")
        self.assertEqual(verifier.strip_lean_comments_and_literals("def a := '\n'"), "def a := '\n'")
        self.assertEqual(verifier.strip_lean_comments_and_literals("def a := 'ab'"), "def a := 'ab'")
        self.assertEqual(verifier.strip_lean_comments_and_literals("def a := '\\\n'"), "def a := '\\\n'")
        self.assertEqual(verifier.strip_lean_comments_and_literals("def a := '\\ab'"), "def a := '\\ab'")
        self.assertEqual(verifier.strip_lean_comments_and_literals("def a := '\\x2"), "def a := '\\x2")
        self.assertEqual(verifier.strip_lean_comments_and_literals("def a := '\\x27a"), "def a := '\\x27a")
        self.assertEqual(verifier.strip_lean_comments_and_literals("def a := '\\xZZ'"), "def a := '\\xZZ'")
        self.assertEqual(verifier.strip_lean_comments_and_literals("def a := '\\y27'"), "def a := '\\y27'")
        self.assertEqual(verifier.strip_lean_comments_and_literals("def a := '\\u002"), "def a := '\\u002")
        self.assertEqual(verifier.strip_lean_comments_and_literals("def a := '\\u0027a"), "def a := '\\u0027a")
        self.assertEqual(verifier.strip_lean_comments_and_literals("def a := '\\uZZZZ'"), "def a := '\\uZZZZ'")
        self.assertEqual(verifier.strip_lean_comments_and_literals("def a := '\\v0027'"), "def a := '\\v0027'")
        self.assertEqual(verifier.strip_lean_comments_and_literals("def a := r#"), "def a := r#")
        self.assertEqual(verifier.strip_lean_comments_and_literals('def a := x.r"\\""'), "def a := x.r    ")
        self.assertEqual(verifier.strip_lean_comments_and_literals('def a := s!x'), "def a := s!x")
        self.assertEqual(verifier.strip_lean_comments_and_literals('def a := s"x"'), "def a := s   ")
        self.assertEqual(verifier.strip_lean_comments_and_literals('def a := as! "{1}"'), "def a := as!      ")
        self.assertEqual(verifier.strip_lean_comments_and_literals('r"\\" -- x'), "         ")
        self.assertEqual(verifier.strip_lean_comments_and_literals('def s := r"\\" -- x'), "def s :=          ")
        self.assertEqual(verifier.strip_lean_comments_and_literals('!"x"'), "!   ")
        self.assertEqual(verifier.strip_lean_comments_and_literals('!"{1}" -- s'), "!          ")
        self.assertEqual(verifier.strip_lean_comments_and_literals("aa'"), "aa'")
        self.assertEqual(verifier.strip_lean_comments_and_literals("x'a'"), "x'a'")
        self.assertEqual(verifier.strip_lean_comments_and_literals("x!'a'"), "x!'a'")
        self.assertEqual(verifier.strip_lean_comments_and_literals('panic!"x"'), "panic!   ")
        self.assertFalse(verifier._is_lean4_native_rhs_false_span("(false", 0, 6))
        self.assertFalse(verifier._is_lean4_native_rhs_false_span("false)", 0, 6))
        self.assertFalse(verifier._is_lean4_native_rhs_false_span("(falsex", 0, 7))
        self.assertFalse(verifier._is_lean4_native_rhs_false_span("xfalse)", 0, 7))
        self.assertTrue(verifier._is_lean4_native_rhs_false_span("(false)", 0, 7))
        self.assertEqual(verifier.strip_lean_comments_and_literals("def c := /- a / b -/ 1"), "def c :=             1")
        self.assertEqual(verifier.strip_lean_comments_and_literals("def c := /- / -/ 1"), "def c :=         1")
        self.assertEqual(verifier.strip_lean_comments_and_literals("def c := /- a / b - x -/ 1"), "def c :=                 1")
        self.assertEqual(verifier.strip_lean_comments_and_literals('def a := r#"a " b"#'), "def a :=           ")
        self.assertEqual(verifier.strip_lean_comments_and_literals('def a := s!"a \\n {1}"'), "def a := s!       1} ")
        with self.assertRaisesRegex(verifier.VerifyError, "Unterminated Lean block comment"):
            verifier.strip_lean_comments_and_literals("/- unclosed")
        for unclosed_s in ('"unclosed', 's!"unclosed', 'r#"unclosed', 's!"{ 1 + 2'):
            with self.assertRaisesRegex(verifier.VerifyError, "Unterminated Lean string literal"):
                verifier.strip_lean_comments_and_literals(unclosed_s)

        with self.assertRaisesRegex(verifier.VerifyError, "Lean source must be non-empty"):
            verifier.audit_lean_source("")
        with self.assertRaisesRegex(verifier.VerifyError, "Lean source must be non-empty"):
            verifier.audit_lean_source("   \n\t ")
        with self.assertRaisesRegex(verifier.VerifyError, "Lean source must be non-empty"):
            verifier.audit_lean_source(123)  # type: ignore[arg-type]

        # ALL 15 AUDIT-175 bypasses + full R9+ adversarial battery
        banned_snippets = [
            "theorem t : False := sorry",
            "theorem t : False := by admit",
            "axiom bad : False",
            "opaque f : Nat",
            "unsafe def u := 1",
            "theorem t : 1 = 1 := by native_decide",
            "def x := sorryAx False false",
            "def x := Lean.Meta.mkSorry",
            "def x := Lean.ofReduceBool",
            "def x := Lean.ofReduceNat",
            "def x := Lean.trustCompiler",
            "import Lean",
            "public\n import Init",
            'macro "foo" : term => `(1)',
            'macro_rules | `(1) => `(1)',
            'elab "spoof" : command => pure ()',
            'syntax "baz" : term',
            "def x := interpolatedStr",
            'def a := x!"{sorry}"',
            'def a := xpanic!"{sorry}"',
            'def a := .s!"{sorry}"',
            "partial\n def p : Nat := p",
            "set_option debug.skipKernelTC true",
            "set_option debug.byAsSorry true",
            "set_option debug.proofAsSorry true",
            "set_option debug.terminalTacticsAsSorry true",
            "set_option «debug».«byAsSorry» true",
            '@[extern "c_fn"] def bar := 1',
            "@[implemented_by foo] def bar := 1",
            'attribute [extern "c_fn"] bar',
            "attribute [implemented_by foo] bar",
            "@[csimp] theorem c : 1 = 1 := rfl",
            "theorem v : False → True := fun h => False.elim h",
            "theorem e : ∃ x : Nat, x = 1 → True := ⟨0, fun _ => trivial⟩",
            '#eval IO.println "spoof"',
            "#eval! 1",
            "#reduce 1 + 1",
            "#exit",
            "#print Nat",
            "#print axioms example : True := trivial",
            "#print «axioms» Nat",
            "run_cmd pure ()",
            "run_meta pure ()",
            "initialize pure ()",
            "builtin_initialize pure ()",
            "«initialize» pure ()",
            'def a : Bool := !r"\\".isEmpty\ntheorem fake : False := by sorry\n-- "',
            'def a : Bool := !r#"\\"#.isEmpty\ntheorem fake : False := by sorry\n-- "',
            'def a : Bool := !s!"{let _ := "x"; (by sorry : String)}".isEmpty',
            'def a : Bool := !f!"{let _ := "x"; (by sorry : String)}".pretty.isEmpty',
            'def a : String := s! "{(by sorry : String)}"',
            'def a : String := s!\n"{(by sorry : String)}"',
            'def a : String := s! /- c -/ "{(by sorry : String)}"',
            'def a : String := s! -- c\n"{(by sorry : String)}"',
            'def a := m! "{sorry}"',
            'def a := bar"\\""\nsorry',
            'def a := x.r"\\""\nsorry',
            'def a := foo!r"\\""\nsorry',
            'def a := foo?r"\\""\nsorry',
            'def a := r"\\" sorry',
            "def a := '\\'\"'\ntheorem t : False := by sorry",
            "def a := 'x\"'\ntheorem t : False := by sorry",
            "def x' := '\"'\ntheorem bad : False := sorry",
            "def «a\"b» := 1\ntheorem bad : False := sorry",
            "def «unterminated",
            "/- unterminated",
            'def s := "unclosed',
            'def s := r#"unclosed',
            'def s := s!"unclosed',
            'def s := s!"{ 1 + 2',
            "theorem t : 1 = 1 := by decide +native",
            "theorem t : 1 = 1 := by decide -revert +native",
            "theorem t : 1 = 1 := by decide (revert := false) +native",
            "theorem t : 1 = 1 := by decide (native := !false)",
            "theorem t : 1 = 1 := by decide (native := (true))",
            "theorem t : 1 = 1 := by decide («native» := true)",
            "theorem t : 1 = 1 := by decide (config := cfg)",
            "theorem t : 1 = 1 := by decide (config := { native := true })",
            "theorem t : 1 = 1 := by decide (config := { native := false, native := true })",
            "theorem t : 1 = 1 := by decide (config := { cfg with native := false })",
            "theorem t : 1 = 1 := by decide (config := { a := { } })",
            "theorem t : 1 = 1 := by decide (config := { a := { })",
            "theorem t : 1 = 1 := by decide (config := { a := } })",
            "theorem t : 1 = 1 := by decide (config := { native := false, 123 })",
            "theorem t : 1 = 1 := by decide (config := { native := false junk })",
            "theorem t : 1 = 1 := by decide (config := { native := false)",
            "theorem t : 1 = 1 := by decide (config := { a )",
            "theorem t : 1 = 1 := by decide (config := native := false })",
            "theorem t : 1 = 1 := by decide (config := { native := false } })",
            "def c : DecideConfig := { native := true }",
            "def c := { native := true } : DecideConfig",
            "def c := { native := true : DecideConfig }",
            "def u := ]\n@[extern \"c\"] def f := 0",
        ]
        for snip in banned_snippets:
            with self.assertRaises(verifier.VerifyError, msg=f"Failed to block {snip!r}"):
                verifier.audit_lean_source(snip + "\n" + base_prints)

        missing_print = "\n".join(f"#print axioms {t}" for t in verifier.EXPECTED_LEAN_THEOREMS[:-1])
        with self.assertRaises(verifier.VerifyError):
            verifier.audit_lean_source(missing_print)

    def test_09_verify_lean_file_multiline_axioms_and_error_branches(self) -> None:
        # Multi-line wrapped Lean 4.36.0 #print axioms output MUST PASS (closes S75-DEF-02!)
        wrapped_lines = []
        for idx, t in enumerate(verifier.EXPECTED_LEAN_THEOREMS):
            if idx == 0:
                wrapped_lines.append(f"'{t}' depends on axioms: [Classical.choice,\n Quot.sound]")
            elif idx % 2 == 0:
                wrapped_lines.append(f"'{t}' depends on axioms: [propext, Quot.sound]")
            else:
                wrapped_lines.append(f"'{t}' does not depend on any axioms")
        good_stdout = "\n".join(wrapped_lines) + "\n"

        parsed_ok = verifier._parse_lean_axioms_stdout(good_stdout)
        self.assertEqual(parsed_ok[verifier.EXPECTED_LEAN_THEOREMS[0]], ["Classical.choice", "Quot.sound"])

        # Duplicate theorem line rejected (closes S75-DEF-02!)
        dup_out = good_stdout + f"'{verifier.EXPECTED_LEAN_THEOREMS[0]}' does not depend on any axioms\n"
        with self.assertRaisesRegex(verifier.VerifyError, "Duplicate axiom report"):
            verifier._parse_lean_axioms_stdout(dup_out)

        # Extra untracked #print axioms line rejected (closes S75-DEF-01!)
        extra_out = good_stdout + "'Untracked.extra_thm' does not depend on any axioms\n"
        with self.assertRaisesRegex(verifier.VerifyError, "does not match expected manifest"):
            verifier._parse_lean_axioms_stdout(extra_out)

        with tempfile.TemporaryDirectory() as td:
            bad_utf8 = os.path.join(td, "bad.lean")
            with open(bad_utf8, "wb") as f:
                f.write(b"\xff\xfe")
            with self.assertRaises(verifier.VerifyError):
                verifier.verify_lean_file(bad_utf8)

        # Lean binary discovery fallback (LEAN_BIN, PATH, HOME/.local/bin/lean)
        with mock.patch("shutil.which", return_value=None):
            with mock.patch.dict("os.environ", {"HOME": "", "LEAN_BIN": ""}, clear=False):
                with self.assertRaises(verifier.VerifyError):
                    verifier._find_lean_binary()
            with tempfile.TemporaryDirectory() as td:
                with mock.patch.dict("os.environ", {"HOME": td, "LEAN_BIN": ""}, clear=False):
                    with self.assertRaises(verifier.VerifyError):
                        verifier._find_lean_binary()
                fake_bin = os.path.join(td, ".local", "bin", "lean")
                os.makedirs(fake_bin)
                with mock.patch.dict("os.environ", {"HOME": td, "LEAN_BIN": ""}, clear=False):
                    with self.assertRaises(verifier.VerifyError):
                        verifier._find_lean_binary()
                with mock.patch.dict("os.environ", {"HOME": "", "LEAN_BIN": fake_bin}, clear=False):
                    with self.assertRaises(verifier.VerifyError):
                        verifier._find_lean_binary()
                os.rmdir(fake_bin)
                with open(fake_bin, "w", encoding="utf-8") as f:
                    f.write("#!/bin/sh\n")
                os.chmod(fake_bin, 0o600)
                with mock.patch.dict("os.environ", {"HOME": td, "LEAN_BIN": ""}, clear=False):
                    with self.assertRaises(verifier.VerifyError):
                        verifier._find_lean_binary()
                with mock.patch.dict("os.environ", {"HOME": "", "LEAN_BIN": fake_bin}, clear=False):
                    with self.assertRaises(verifier.VerifyError):
                        verifier._find_lean_binary()
                os.chmod(fake_bin, 0o700)
                with mock.patch.dict("os.environ", {"HOME": td, "LEAN_BIN": ""}, clear=False):
                    self.assertEqual(verifier._find_lean_binary(), fake_bin)
                with mock.patch.dict("os.environ", {"HOME": "", "LEAN_BIN": fake_bin}, clear=False):
                    self.assertEqual(verifier._find_lean_binary(), fake_bin)

        with mock.patch.object(verifier, "_find_lean_binary", return_value="/usr/bin/lean"):
            with mock.patch("subprocess.run", side_effect=OSError("ENOENT")):
                with self.assertRaises(verifier.VerifyError):
                    verifier.verify_lean_file(DISK_LEAN)
            cp_rc1 = subprocess.CompletedProcess([], 1, good_stdout, "")
            with mock.patch("subprocess.run", return_value=cp_rc1):
                with self.assertRaisesRegex(verifier.VerifyError, "exited with status 1"):
                    verifier.verify_lean_file(DISK_LEAN)
            cp_stderr = subprocess.CompletedProcess([], 0, good_stdout, "some stderr")
            with mock.patch("subprocess.run", return_value=cp_stderr):
                with self.assertRaisesRegex(verifier.VerifyError, "Unexpected Lean stderr"):
                    verifier.verify_lean_file(DISK_LEAN)
            cp_warn = subprocess.CompletedProcess([], 0, "warning: unused\n" + good_stdout, "")
            with mock.patch("subprocess.run", return_value=cp_warn):
                with self.assertRaisesRegex(verifier.VerifyError, "Unexpected Lean stdout"):
                    verifier.verify_lean_file(DISK_LEAN)
            bad_ax = good_stdout.replace("propext", "sorryAx", 1)
            cp_badax = subprocess.CompletedProcess([], 0, bad_ax, "")
            with mock.patch("subprocess.run", return_value=cp_badax):
                with self.assertRaisesRegex(verifier.VerifyError, "Disallowed axiom"):
                    verifier.verify_lean_file(DISK_LEAN)
            missing_out = "\n".join(good_stdout.splitlines()[:-1]) + "\n"
            cp_miss = subprocess.CompletedProcess([], 0, missing_out, "")
            with mock.patch("subprocess.run", return_value=cp_miss):
                with self.assertRaises(verifier.VerifyError):
                    verifier.verify_lean_file(DISK_LEAN)
            cp_ok = subprocess.CompletedProcess([], 0, "\n" + good_stdout, "")
            with mock.patch("subprocess.run", return_value=cp_ok):
                ok_res = verifier.verify_lean_file(DISK_LEAN)
                self.assertEqual(ok_res["theorems_verified"], 15)

    def test_10_cli_modes_and_fail_closed_flags(self) -> None:
        buf_out = io.StringIO()
        buf_err = io.StringIO()
        with mock.patch("sys.stdout", buf_out), mock.patch("sys.stderr", buf_err):
            rc = verifier.main(["--standalone", "--json"])
        self.assertEqual(rc, 0)
        parsed = json.loads(buf_out.getvalue())
        self.assertEqual(parsed["mode"], "standalone")
        self.assertEqual(parsed["oracles_passed"], 7)

        buf_out = io.StringIO()
        with mock.patch("sys.stdout", buf_out):
            rc = verifier.main([])
        self.assertEqual(rc, 0)
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
            for argv in (
                ["--verify-lean", DISK_LEAN, "--json"],
                ["--verify-lean", "--json"],
                ["--verify-lean"],
            ):
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

    def test_11_json_tree_depth_surrogate_and_file_hardening(self) -> None:
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
        with self.assertRaises(verifier.VerifyError):
            verifier._validate_plain_json_tree({"\ud800": "bad-key-surr"})
        with self.assertRaises(verifier.VerifyError):
            verifier._validate_plain_json_tree({"s": "\ud800"})
        with self.assertRaises(verifier.VerifyError):
            verifier._validate_plain_json_tree({"big": 1 << 3300})
        for fl in (Fraction(3, 2).__float__(), _FloatSubclass("1.5")):
            with self.assertRaisesRegex(verifier.VerifyError, "floating-point"):
                verifier._validate_plain_json_tree({"flt": fl})

        verifier._check_json_nesting_depth("[" * 32 + "]" * 32)
        with self.assertRaisesRegex(verifier.VerifyError, "nesting depth"):
            verifier._check_json_nesting_depth("[" * 33 + "]" * 33)

        ok_deep: object = 0
        for _ in range(32):
            ok_deep = [ok_deep]
        verifier._validate_plain_json_tree(ok_deep)
        with self.assertRaises(verifier.VerifyError):
            verifier._validate_plain_json_tree([ok_deep])

        max_ok = (1 << 3300) - 1
        self.assertEqual(verifier._strict_parse_json_int("-" + str(max_ok)), -max_ok)
        with self.assertRaises(verifier.VerifyError):
            verifier._strict_parse_json_int("9" * 1001)
        with self.assertRaises(verifier.VerifyError):
            verifier._strict_parse_json_int("-" + "9" * 1001)

        with tempfile.TemporaryDirectory() as td:
            real_c = os.path.join(td, "c.json")
            verifier.write_certificate_file(real_c)
            raw_canon = verifier._read_bytes_safe(real_c)

            for idx, txt in enumerate((
                '{"a": ' + "9" * 5000 + '}\n',
                '{"a": 1.5}\n',
                '{"a": NaN}\n',
                '{"a": 1, "a": 2}\n',
                '[' * 33 + ']' * 33 + '\n',
                '{"s":"' + ('{[\\"' * 20) + '"}',
            )):
                hp = os.path.join(td, f"h{idx}.json")
                with open(hp, "w", encoding="utf-8") as fh:
                    fh.write(txt)
                with self.assertRaises(verifier.VerifyError):
                    verifier.verify_certificate_file(hp)

            crlf_p = os.path.join(td, "crlf.json")
            with open(crlf_p, "wb") as fh:
                fh.write(raw_canon.replace(b"\n", b"\r\n"))
            with self.assertRaisesRegex(verifier.VerifyError, "CRLF"):
                verifier.verify_certificate_file(crlf_p)

            pretty_p = os.path.join(td, "pretty.json")
            with open(pretty_p, "w", encoding="utf-8") as fh:
                fh.write(json.dumps(verifier.build_certificate(), indent=2) + "\n")
            with self.assertRaises(verifier.VerifyError):
                verifier.verify_certificate_file(pretty_p)

    # ------------------------------------------------------------------
    # Live Lean 4.36.0 Kernel & Live E2E Exploit Regression (90..91)
    # ------------------------------------------------------------------

    def test_90_live_lean436_kernel_and_axioms(self) -> None:
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
        self.assertEqual(set(ax_map.keys()), set(verifier.EXPECTED_LEAN_THEOREMS))
        for thm in verifier.EXPECTED_LEAN_THEOREMS:
            for ax in ax_map[thm]:
                self.assertIn(ax, verifier.ALLOWED_AXIOMS)
        self.assertEqual(ax_map["S75VpVnpMechanismCerts.prop_E1_char2_collapse"], [])
        self.assertEqual(ax_map["S75VpVnpMechanismCerts.sec25_boolean_garbage_vanishes_on_bits"], [])

    def test_91_live_e2e_lean_exploit_regressions_all_rejected(self) -> None:
        disk_src = Path(DISK_LEAN).read_text(encoding="utf-8")
        spoof_lines = "\n".join(
            f'  IO.println "\'{t}\' does not depend on any axioms"' for t in verifier.EXPECTED_LEAN_THEOREMS
        )
        e2e_exploits = {
            "import_lean_elab_forge": (
                "import Lean\nopen Lean Elab Command in\n"
                f'elab "spoof_all" : command => do\n{spoof_lines}\n'
                "spoof_all\n"
                + "\n".join(f"-- #print axioms {t}" for t in verifier.EXPECTED_LEAN_THEOREMS)
                + "\n"
            ),
            "debug_skipKernelTC": "set_option debug.skipKernelTC true\n" + disk_src,
            "decide_bang_false": disk_src + "\ntheorem aux_nf : 1 = 1 := by decide (native := !false)\n",
            "decide_paren_true": disk_src + "\ntheorem aux_pt : 1 = 1 := by decide (native := (true))\n",
            "initialize_hook": "initialize pure ()\n" + disk_src,
            "dbg_trace_native_splice": disk_src + '\ndef _dbg := dbg_trace "{(fun (_ : 1 = 1) => 0) (by native_decide)}" 0\n',
            "char_quote_eval_spoof": 'def q1 : Char := \'"\'\n#eval IO.println "spoof"\ndef q2 : Char := \'"\'\n' + disk_src,
            "raw_string_axiom_smuggle": 'def _a := r#"""#\naxiom evil_smuggled : False\ndef _b := r#"""#\n' + disk_src,
            "extra_print_axioms": disk_src + "\ntheorem aux_extra : 1 = 1 := rfl\n#print axioms aux_extra\n",
        }
        with tempfile.TemporaryDirectory(prefix="s75_e2e_lean_") as td:
            for name, src in e2e_exploits.items():
                fp = os.path.join(td, f"{name}.lean")
                Path(fp).write_text(src, encoding="utf-8")
                with self.assertRaises(verifier.VerifyError, msg=f"Live E2E exploit passed: {name}"):
                    verifier.verify_lean_file(fp)


if __name__ == "__main__":
    failfast = "-f" in sys.argv or "--failfast" in sys.argv
    suite = unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=2, failfast=failfast).run(suite)
    if not result.wasSuccessful():
        raise SystemExit(1)
    raise SystemExit(0)
