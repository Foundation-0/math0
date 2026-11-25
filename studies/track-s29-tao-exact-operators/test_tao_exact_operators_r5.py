#!/usr/bin/env python3
"""Track S29 Exact-Operator Verification & Zone-B Test Suite.

Pure Python 3 stdlib, zero bare asserts, zero floats on oracle/audit assertions.
Covers:
  - Test 1: Full 5-pillar exact Z/Q mathematical verification & certificate match
  - Test 2: Exported helper soundness, domain/type/primality/ring-closure/negative controls
  - Test 3: Uniform Zone-B Gold Standard (atomic dir_fd, /proc/kallsyms, /dev/null,
            FIFO, chmod 000, hardlink, deep/dotdot/PWD symlinks, deleted-CWD,
            lone UTF-16 surrogates, CRLF/BOM/pretty/dup-key/float/depth/bits,
            flag-like & equals-syntax CLI paths, subprocess parity)
  - Test 4: Live >= 500-iter concurrent renameat2(RENAME_EXCHANGE) + >= 400-iter
            concurrent os.link() hardlink race stress (0 leaks, 0 clobbers, 0 temps)
"""
from __future__ import annotations

from contextlib import redirect_stderr, redirect_stdout
import copy
import ctypes
from fractions import Fraction
import io
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import threading
import unittest
from typing import Any

ROOT = Path(__file__).resolve().parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import tao_exact_operators_audit as audit  # noqa: E402
import tao_exact_operators_oracle as oracle  # noqa: E402

CERT_PATH = ROOT / audit.DEFAULT_CERT_NAME
_AT_FDCWD = -100
_RENAME_EXCHANGE = 2


class _EvilPath(type(Path())):
    """Path subclass rejected by strict concrete pathlib.Path check."""


class _StrSub(str):
    """str subclass rejected by strict type(x) is str check."""


class _IntSub(int):
    """int subclass rejected by strict type(x) is int check."""


class _BoolLike:
    def __bool__(self) -> bool:
        return True


def _check(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


def _expect_err(fn: Any, expected_code: str, label: str) -> None:
    try:
        fn()
    except oracle.TaoOperatorsError as exc:
        if exc.code != expected_code:
            raise AssertionError(f"{label}: expected {expected_code}, got {exc.code} ({exc})") from exc
        return
    raise AssertionError(f"{label}: expected TaoOperatorsError({expected_code}), but succeeded")


class TrackS29Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.live_cert = audit.build_certificate()

    def test_01_five_pillars_exact_math_and_certificate(self) -> None:
        cert = self.live_cert
        disk_bytes = CERT_PATH.read_bytes()
        _check(audit.canonical_json_bytes(cert) == disk_bytes, "on-disk certificate drift")
        res = audit.verify_certificate_dict(cert, expected=cert)
        _check(res["valid"] is True, "verify_certificate_dict failed")
        _check(audit.verify_certificate_file(CERT_PATH, full_replay=False) == res, "verify_certificate_file mismatch")

        pl = cert["payload"]
        _check(pl["track_id"] == "TRACK-S29-AUDIT-129" and pl["novelty_class"] == "N1", "metadata mismatch")

        # Pillar 1
        p1 = pl["pillar1_katz_tao_entropy"]
        _check(p1["all_verified"] is True, "P1 all_verified")
        _check(p1["katz_tao_11_6_certificate"]["exponent"] == "11/6" and p1["katz_tao_11_6_certificate"]["ring"] == "Z", "P1 11/6")
        _check(p1["katz_tao_7_4_certificate"]["exponent"] == "7/4" and p1["katz_tao_7_4_certificate"]["ring"] == "Z[1/2]", "P1 7/4")
        _check(p1["trivial_2_mono_certificate"]["exponent"] == "2", "P1 trivial 2")
        sep = p1["ring_closure_separation"]
        _check(sep["y_in_Z_span_x_xplus2y"] is False and sep["y_in_Zhalf_span_x_xplus2y"] is True, "P1 Z vs Z[1/2]")
        _check(sep["y_in_Zhalf_span_x_xplus3y"] is False and sep["y_in_Q_span_x_xplus3y"] is True, "P1 Z[1/2] vs Q")
        _check(p1["cross_ratio_invariance"]["cr_0_1_inf_m1"] == "2" and p1["cross_ratio_invariance"]["cr_0_inf_1_m1"] == "-1", "P1 CR")
        _check([r["D_rational_complexity"] for r in p1["tao_rational_complexity"]] == [0, 1, 2, 1, 2, 3, 3, 4], "P1 D(R;s)")
        probe = p1["open_seam_probe_honest_status"]
        _check(probe["p0_primal_closed_sets_verified"] == 100 and probe["p0_primal_lower_bound"] == "7/4", "P1 P0 primal")
        _check(probe["four_slope_2page_rank3_glues_probed"] == 8 and probe["all_glues_tight_at_7_4"] is True, "P1 8 glues")
        _check(probe["four_slope_2page_best_achieved"] == "7/4" and probe["beats_7_4_in_2page_rank3_cone"] is False, "P1 probe")
        _check(len(probe["per_glue_receipts"]) == 8 and all(r["tight_at_7_4"] is True for r in probe["per_glue_receipts"]), "P1 receipts")

        # Pillar 2
        p2 = pl["pillar2_von_mangoldt_chains"]
        _check(p2["all_verified"] is True and p2["smooth_2_to_120_count"] == 49, "P2 smooth")
        _check(p2["hit_210_omega2_uniform"] == "1" and p2["hit_210_omega2_log_approx"] == "1", "P2 210 sat")
        _check(p2["hit_180_omega2_uniform"] == "23/30", "P2 180 unif")
        _check(p2["hit_180_omega2_log_approx"] == "7925799930620659238/9872377837458467625", "P2 180 log")
        _check(p2["perfect_antichain_hit_from_10416"] == "83/420" and p2["primitive_abundant_antichain_hit_from_3780"] == "229/420", "P2 antichains")
        _check(p2["odd_banks_martin_Q357"]["subinvariance_eq62_max_upper_bound_le_1"] is True, "P2 eq62")
        _check(p2["two_in_Q_obstruction"]["beta_2_denominator_p_minus_2"] == 0, "P2 beta2 pole")

        # Pillar 3
        p3 = pl["pillar3_syracuse_and_gilbreath"]
        _check(p3["all_verified"] is True and p3["two_adic_parity_bijection_k1_to_8"] is True, "P3 2-adic")
        _check(p3["positive_short_cycles"] == [[1, 1]] and p3["negative_short_cycles"] == [[-5, 2], [-1, 1]], "P3 short cycles")
        _check(p3["negative_17_cycle"]["rational_formula_exact"] is True, "P3 -17 cycle")
        _check(p3["syracuse_3adic_mod9"]["stationary_pi_mod9"]["8"] == "22/63", "P3 mod9")
        _check(p3["syracuse_3adic_mod9"]["max_to_min_ratio"] == "11", "P3 11x ratio")
        _check(p3["syracuse_3adic_mod27"]["state_count"] == 18, "P3 mod27")
        haar = p3["syracuse_2adic_haar_drift"]
        _check(haar["precision_bits_m"] == 8 and haar["odd_residues_checked"] == 128, "P3 Haar m=8")
        _check(haar["truncated_ev2_mod256"] == "255/128" and haar["truncated_formula_matches"] is True, "P3 Haar trunc")
        _check(haar["telescoping_identity_exact"] is True and haar["asymptotic_haar_ev2"] == "2", "P3 Haar tel")
        _check(haar["asymptotic_haar_geometric_drift"] == "3/4" and haar["strictly_contractive"] is True, "P3 Haar drift")
        _check(p3["gilbreath_first_500_primes"]["p_500"] == 3571 and p3["gilbreath_first_500_primes"]["left_diagonal_all_ones"] is True, "P3 Gilbreath")
        _check(p3["chase_hunter_tao_witnesses"]["long_zero_block_left_diag"][-1] == 7, "P3 CHT zero block")

        # Pillar 4
        p4 = pl["pillar4_sidon_gowers_ruzsa"]
        _check(p4["all_verified"] is True and len(p4["singer_sidon_sets"]) == 5, "P4 Singers")
        _check([s["q"] for s in p4["singer_sidon_sets"]] == [2, 3, 4, 5, 7], "P4 orders")
        _check(p4["two_golomb_ruler_witness"]["max_difference_multiplicity"] == 2, "P4 2-Golomb")
        g4 = p4["gowers_f2_4"]
        _check(g4["bent_x0x1_plus_x2x3"]["U2_4"] == "1/16" and g4["bent_x0x1_plus_x2x3"]["U3_8"] == "1", "P4 bent")
        _check(g4["cubic_x0x1x2"]["U3_8"] == "11/32" and g4["cubic_x0x1x2"]["U4_16"] == "1", "P4 cubic")

        # Pillar 5
        p5 = pl["pillar5_dyadic_ns_dptz_etp"]
        _check(p5["all_verified"] is True, "P5 all_verified")
        _check(p5["dyadic_ns_barrier"]["energy_conservation_exact"] is True, "P5 energy")
        _check(p5["dptz_eigenvector_eigenvalue"]["matrix_3x3"]["eigenpair_minor_pairs_checked"] == 9, "P5 DPTZ 3x3")
        _check(p5["dptz_eigenvector_eigenvalue"]["matrix_4x4"]["eigenpair_minor_pairs_checked"] == 16, "P5 DPTZ 4x4")
        etp = p5["etp_magma_countermodels"]
        _check(etp["central_groupoid_order4"]["law1689_central_groupoid"] is True and etp["central_groupoid_order4"]["associative"] is False, "P5 ETP CG")
        _check(etp["left_projection_order3"]["associative"] is True and etp["left_projection_order3"]["commutative"] is False, "P5 ETP LP")
        _check(etp["affine_medial_order3"]["medial"] is True and etp["affine_medial_order3"]["associative"] is False, "P5 ETP AM")

    def test_02_exported_helpers_soundness_and_negative_controls(self) -> None:
        # Strict primitive guards
        _expect_err(lambda: oracle.require_ok(1, "X", "m"), "INVALID_CONDITION_TYPE", "int cond")
        _expect_err(lambda: oracle.require_ok(_BoolLike(), "X", "m"), "INVALID_CONDITION_TYPE", "boollike")
        _expect_err(lambda: oracle.require_ok(False, "MY_CODE", "boom"), "MY_CODE", "false cond")
        oracle.require_ok(True, "OK", "ok")

        _expect_err(lambda: oracle.require_exact_int(True, "n"), "INVALID_INT_TYPE", "bool as int")
        _expect_err(lambda: oracle.require_exact_int(_IntSub(3), "n"), "INVALID_INT_TYPE", "int sub")
        _expect_err(lambda: oracle.require_exact_int(1 << oracle.MAX_RATIONAL_BITS, "n"), "INT_BIT_LIMIT", "bit cap")
        _check(oracle.require_exact_int((1 << oracle.MAX_RATIONAL_BITS) - 1, "n") > 0, "exact max bits")
        _expect_err(lambda: oracle.require_exact_int(0, "n", lo=1), "INT_OUT_OF_RANGE", "below lo")
        _expect_err(lambda: oracle.require_exact_int(6, "n", lo=1, hi=5), "INT_OUT_OF_RANGE", "above hi")
        _check(oracle.require_exact_int(5, "n", lo=1, hi=5) == 5, "exact hi")
        _expect_err(lambda: oracle.require_exact_bool(1, "b"), "INVALID_BOOL_TYPE", "int bool")
        _check(oracle.require_exact_bool(False, "b") is False, "false bool")
        _expect_err(lambda: oracle.require_exact_fraction(1, "q"), "INVALID_FRACTION_TYPE", "int frac")
        _expect_err(lambda: oracle.require_exact_fraction(Fraction(1 << oracle.MAX_RATIONAL_BITS, 1), "q"), "RATIONAL_BIT_LIMIT", "num cap")
        _expect_err(lambda: oracle.require_exact_fraction(Fraction(1, 1 << oracle.MAX_RATIONAL_BITS), "q"), "RATIONAL_BIT_LIMIT", "den cap")
        _expect_err(lambda: oracle.format_fraction(Fraction(10**4300, 1)), "RATIONAL_BIT_LIMIT", "10**4300 format_fraction")
        _check(oracle.format_fraction(Fraction(4, 2)) == "2" and oracle.format_fraction(Fraction(5, 2)) == "5/2", "format frac")

        # Primality & factoring edge cases
        _check(oracle.is_prime_small(0) is False and oracle.is_prime_small(1) is False, "0/1 not prime")
        _check(oracle.is_prime_small(2) is True and oracle.is_prime_small(3) is True, "2/3 prime")
        _check(oracle.is_prime_small(4) is False and oracle.is_prime_small(9) is False, "4/9 composite")
        _check(oracle.is_prime_small(25) is False and oracle.is_prime_small(49) is False and oracle.is_prime_small(29) is True, "25/49/29")
        _check(oracle.factorize_small(1) == {} and oracle.factorize_small(360) == {2: 3, 3: 2, 5: 1}, "factorize")

        # Linear solver & determinant guards
        _check(
            oracle.solve_linear_fraction([[Fraction(0, 1), Fraction(2, 1)], [Fraction(3, 1), Fraction(1, 1)]], [Fraction(4, 1), Fraction(5, 1)])
            == [Fraction(1, 1), Fraction(2, 1)],
            "pivot solve",
        )
        _expect_err(lambda: oracle.solve_linear_fraction("x", []), "INVALID_MATRIX_TYPE", "bad mat")
        _expect_err(lambda: oracle.solve_linear_fraction([[Fraction(1, 1)]], "x"), "INVALID_MATRIX_TYPE", "bad rhs")
        _expect_err(lambda: oracle.solve_linear_fraction([], []), "INVALID_MATRIX_DIM", "empty mat")
        _expect_err(lambda: oracle.solve_linear_fraction([[Fraction(1, 1)]], [Fraction(1, 1), Fraction(2, 1)]), "INVALID_MATRIX_DIM", "dim mismatch")
        _expect_err(lambda: oracle.solve_linear_fraction([[Fraction(1, 1), Fraction(2, 1)]], [Fraction(1, 1)]), "INVALID_MATRIX_ROW", "non-square")
        _expect_err(lambda: oracle.solve_linear_fraction([(Fraction(1, 1),)], [Fraction(1, 1)]), "INVALID_MATRIX_ROW", "tuple row")
        _expect_err(
            lambda: oracle.solve_linear_fraction([[Fraction(1, 1), Fraction(2, 1)], [Fraction(2, 1), Fraction(4, 1)]], [Fraction(1, 1), Fraction(2, 1)]),
            "SINGULAR_MATRIX",
            "singular",
        )
        _check(oracle.det_fraction([[Fraction(0, 1), Fraction(1, 1)], [Fraction(1, 1), Fraction(0, 1)]]) == Fraction(-1, 1), "det swap")
        _check(oracle.det_fraction([[Fraction(1, 1), Fraction(2, 1)], [Fraction(2, 1), Fraction(4, 1)]]) == Fraction(0, 1), "det singular")
        _expect_err(lambda: oracle.det_fraction("x"), "INVALID_MATRIX_TYPE", "det bad type")
        _expect_err(lambda: oracle.det_fraction([]), "INVALID_MATRIX_DIM", "det empty")
        _expect_err(lambda: oracle.det_fraction([(Fraction(1, 1),)]), "INVALID_MATRIX_ROW", "det tuple row")
        _expect_err(lambda: oracle.det_fraction([[Fraction(1, 1), Fraction(2, 1)]]), "INVALID_MATRIX_ROW", "det rect")

        # Pillar 1 guards: HNF, ring span, corrupted Shannon cert, broken CI, ring mismatch, Mobius/CR
        _check(oracle.row_hnf_exact([[-6, -2], [4, 2], [1, 3]], 2) == [[1, 1], [0, 2]], "HNF exact")
        _expect_err(lambda: oracle.row_hnf_exact("bad", 2), "INVALID_ROWS_TYPE", "hnf rows type")
        _expect_err(lambda: oracle.row_hnf_exact([(1, 2)], 2), "INVALID_ROW_LEN", "hnf tuple row")
        _expect_err(lambda: oracle.row_hnf_exact([[1]], 2), "INVALID_ROW_LEN", "hnf wrong len")
        _expect_err(lambda: oracle.in_ring_span([[1, 0]], [1, 0], 2, "R"), "INVALID_RING", "bad ring")
        _expect_err(lambda: oracle.in_ring_span([[1, 0]], [1, 0], 2, 123), "INVALID_RING", "int ring")
        _expect_err(lambda: oracle.in_ring_span([[1, 0]], [1, 0], 2, _StrSub("Z")), "INVALID_RING", "strsub ring")
        _expect_err(lambda: oracle.in_ring_span([[1, 0]], (1, 0), 2, "Z"), "INVALID_TARGET_VEC", "tuple target")
        _expect_err(lambda: oracle.in_ring_span([[1, 0]], [1], 2, "Z"), "INVALID_TARGET_VEC", "short target")

        atoms_74, diff_74, copies_74, eq_74, z0_74, rhs_74, duals_74 = oracle._build_katz_tao_7_4_spec()
        _expect_err(
            lambda: oracle.verify_shannon_certificate([], [], [], [], 1, [], [], "R"),
            "INVALID_RING",
            "verify_shannon bad ring before atoms",
        )
        _expect_err(
            lambda: oracle.verify_shannon_certificate([], [], [], [], 1, [], [], _StrSub("Z")),
            "INVALID_RING",
            "verify_shannon strsub ring before atoms",
        )
        zero_mult_cert = oracle.verify_shannon_certificate(
            [("X", (1, 0)), ("Y", (0, 1)), ("D", (1, -1))],
            [],
            [],
            [],
            1 << 2,
            [(1 << 0, Fraction(1, 1)), (1 << 1, Fraction(1, 1)), (1 << 2, Fraction(0, 1))],
            [
                ("submod", Fraction(1, 1), (0, 0, 1)),
                ("submod", Fraction(0, 1), (0, 0, 1)),
                ("mono", Fraction(1, 1), (1 << 2, 0)),
                ("mono", Fraction(0, 1), (0, 0)),
            ],
            ring="Z",
        )
        _check(zero_mult_cert["exponent"] == "2" and zero_mult_cert["residual_count"] == 0, "zero-mult boundary cert")
        _expect_err(
            lambda: oracle.verify_shannon_certificate(atoms_74, diff_74, copies_74, eq_74, z0_74, rhs_74, duals_74, "Z"),
            "RING_CLOSURE_MISMATCH",
            "7/4 over Z must fail",
        )
        _expect_err(
            lambda: oracle.verify_shannon_certificate([], [], [], [], 1, [], [], "Z"),
            "INVALID_ATOMS",
            "empty atoms",
        )
        _expect_err(
            lambda: oracle.verify_shannon_certificate("x", [], [], [], 1, [], [], "Z"),
            "INVALID_ATOMS",
            "non-list atoms",
        )
        bad_rhs = [(1 << 0, Fraction(-1, 2))] + rhs_74[1:]
        _expect_err(
            lambda: oracle.verify_shannon_certificate(atoms_74, diff_74, copies_74, eq_74, z0_74, bad_rhs, duals_74, "Z[1/2]"),
            "NEGATIVE_RHS_COEFF",
            "negative rhs",
        )
        bad_sub = list(duals_74)
        bad_sub[2] = ("submod", Fraction(-1, 4), bad_sub[2][2])
        _expect_err(
            lambda: oracle.verify_shannon_certificate(atoms_74, diff_74, copies_74, eq_74, z0_74, rhs_74, bad_sub, "Z[1/2]"),
            "NEGATIVE_SHANNON_MULTIPLIER",
            "negative submod",
        )
        bad_mono = [("mono", Fraction(-1, 1), (0, 0))]
        _expect_err(
            lambda: oracle.verify_shannon_certificate(atoms_74, diff_74, copies_74, eq_74, z0_74, rhs_74, bad_mono, "Z[1/2]"),
            "NEGATIVE_SHANNON_MULTIPLIER",
            "negative mono",
        )
        bad_kind = [("bogus", Fraction(1, 1), 0)]
        _expect_err(
            lambda: oracle.verify_shannon_certificate(atoms_74, diff_74, copies_74, eq_74, z0_74, rhs_74, bad_kind, "Z[1/2]"),
            "INVALID_DUAL_KIND",
            "invalid dual kind",
        )
        bad_mult = list(duals_74)
        bad_mult[2] = ("submod", Fraction(1, 2), bad_mult[2][2])
        _expect_err(
            lambda: oracle.verify_shannon_certificate(atoms_74, diff_74, copies_74, eq_74, z0_74, rhs_74, bad_mult, "Z[1/2]"),
            "NONZERO_CERT_RESIDUAL",
            "corrupted multiplier",
        )
        bad_ci_o = [(z0_74, z0_74, 1 << 4, oracle._bmask([0, 4]))]
        _expect_err(
            lambda: oracle.verify_shannon_certificate(atoms_74, diff_74, bad_ci_o, [], z0_74, rhs_74, [], "Z[1/2]"),
            "COPY_GLUE_NOT_IN_SOURCE",
            "G not in cl(O)",
        )
        bad_ci_up = [(z0_74, z0_74, 1 << 1, oracle._bmask([0, 4]))]
        _expect_err(
            lambda: oracle.verify_shannon_certificate(atoms_74, diff_74, bad_ci_up, [], z0_74, rhs_74, [], "Z[1/2]"),
            "BROKEN_COPY_IDENTITY",
            "G not in cl(U')",
        )

        # False-theorem exploits, modularity, unique iso, eq_groups, & bounds
        xy_atoms = [("X", (1, 0)), ("Y", (0, 1))]
        _expect_err(
            lambda: oracle.verify_shannon_certificate(xy_atoms, [], [(3, 3, 0, 3)], [], 3, [], [("copy", Fraction(1, 1), 0)], "Z"),
            "BROKEN_COPY_IDENTITY",
            "false theorem H(X,Y) <= 0 must fail",
        )
        _expect_err(
            lambda: oracle.verify_shannon_certificate(xy_atoms, [], [(3, 3, 1, 3)], [], 3, [(1, Fraction(1, 1))], [("copy", Fraction(1, 1), 0)], "Z"),
            "BROKEN_COPY_IDENTITY",
            "false theorem H(X,Y) <= H(X) must fail",
        )
        # Isolating witnesses for each independent copy-step invariant (M060, M064, M066):
        # 1. M060: U not in cl(O) (unique iso b->c, disjoint cl(O)&cl(U')=={}, modular 2+0==1+1)
        m60_atoms = [("a", (1, 0, 0)), ("b", (0, 1, 0)), ("c", (0, 0, 1))]
        _expect_err(
            lambda: oracle.verify_shannon_certificate(m60_atoms, [], [(1, 2, 0, 4)], [], 1, [(1, Fraction(1, 1))], [], "Z"),
            "BROKEN_COPY_IDENTITY",
            "U not in cl(O) isolating witness",
        )
        # 2. M064: cl(O)&cl(U')={b}!=G={} while valid diff_pair (vecs[3]-vecs[4]==(1,0,1,0)) keeps rk 4+0==2+2 & unique iso
        m64_atoms = [
            ("a", (1, 0, 0, 0)),
            ("b", (0, 1, 0, 0)),
            ("c", (0, 0, 1, 0)),
            ("p", (0, 0, 0, 1)),
            ("q", (-1, 0, -1, 1)),
            ("t", (1, 2, 0, 0)),
            ("tp", (0, 2, 1, 0)),
        ]
        _expect_err(
            lambda: oracle.verify_shannon_certificate(m64_atoms, [((1, 0, 1, 0), 3, 4)], [(3, 3, 0, 6)], [], 1, [(1, Fraction(1, 1))], [], "Z"),
            "BROKEN_COPY_IDENTITY",
            "cl(O) intersect cl(U') != cl(G) isolating witness",
        )
        # 3. M066: cl(O)&cl(U')=={} & unique iso (a->c, b->d, t->tp), ONLY Q-rank modularity 3+0!=2+2 fails
        m66_atoms = [
            ("a", (1, 0, 0)),
            ("b", (0, 1, 0)),
            ("c", (0, 0, 1)),
            ("d", (1, 1, 1)),
            ("t", (1, 2, 0)),
            ("tp", (2, 2, 3)),
        ]
        _expect_err(
            lambda: oracle.verify_shannon_certificate(m66_atoms, [], [(3, 3, 0, 12)], [], 1, [(1, Fraction(1, 1))], [], "Z"),
            "BROKEN_COPY_IDENTITY",
            "Q-rank non-modular isolating witness",
        )
        # G not in cl(U) rejected directly by COPY_GLUE_NOT_IN_SOURCE
        _expect_err(
            lambda: oracle.verify_shannon_certificate(xy_atoms, [], [(3, 1, 2, 2)], [], 1, [], [], "Z"),
            "COPY_GLUE_NOT_IN_SOURCE",
            "G not in cl(U)",
        )
        # Sequential copy-chain freshness exploits + isolated step_idx>=1 witness
        xyz_atoms = [("X", (1, 0, 0)), ("Y", (0, 1, 0)), ("Z", (0, 0, 1))]
        _expect_err(
            lambda: oracle.verify_shannon_certificate(
                xyz_atoms, [], [(1, 1, 0, 4), (2, 2, 0, 4)], [[1, 4, 2]], 2, [(1, Fraction(1, 1))], [], "Z"
            ),
            "BROKEN_COPY_IDENTITY",
            "copy-chain exploit 1: false H(Y) <= H(X) via reused Z",
        )
        _expect_err(
            lambda: oracle.verify_shannon_certificate(
                xy_atoms, [], [(1, 1, 0, 2)], [[1, 2]], 3, [(1, Fraction(2, 1))], [("copy", Fraction(-1, 1), 0)], "Z"
            ),
            "BROKEN_COPY_IDENTITY",
            "copy-chain exploit 2: false H(X,Y) <= 2 H(X) via input aliasing",
        )
        _expect_err(
            lambda: oracle.verify_shannon_certificate(
                xy_atoms, [], [(1, 1, 0, 2)], [[1, 2]], 1, [(3, Fraction(1, 2))], [("copy", Fraction(1, 2), 0)], "Z"
            ),
            "BROKEN_COPY_IDENTITY",
            "copy-chain exploit 3: false H(X) <= (1/2) H(X,Y) via reverse submodularity",
        )
        xyzw_atoms = [("X", (1, 0, 0, 0)), ("Y", (0, 1, 0, 0)), ("Z", (0, 0, 1, 0)), ("W", (0, 0, 0, 1))]
        _expect_err(
            lambda: oracle.verify_shannon_certificate(
                xyzw_atoms, [], [(3, 1, 0, 4), (3, 1, 0, 8)], [], 3, [(3, Fraction(1, 1))], [], "Z"
            ),
            "BROKEN_COPY_IDENTITY",
            "isolated step_idx>=1 non-nested copy space cl_o != cum_cl",
        )
        # Forged diff_pairs vector & zero atom/diff vector guards
        _expect_err(
            lambda: oracle.verify_shannon_certificate(
                xy_atoms, [((1, 0), 0, 1)], [], [], 3, [(1, Fraction(1, 1))], [], "Z"
            ),
            "INVALID_DIFF_PAIR_VECTOR",
            "forged diff_pairs ((1,0), 0, 1) for false H(X,Y)<=H(X)",
        )
        _expect_err(
            lambda: oracle.verify_shannon_certificate([("Z0", (0, 0)), ("X", (1, 0))], [], [], [], 2, [(2, Fraction(1, 1))], [], "Z"),
            "ZERO_VECTOR_FORBIDDEN",
            "zero atom vector",
        )
        _expect_err(
            lambda: oracle.verify_shannon_certificate(xy_atoms, [((0, 0), 0, 0)], [], [], 1, [(1, Fraction(1, 1))], [], "Z"),
            "ZERO_VECTOR_FORBIDDEN",
            "zero diff_pair vector",
        )
        # Zero copy isos (cardinality mismatch & diff_pair mismatch) and ambiguous (2) copy isos
        card_atoms = [("a", (1, 0, 0)), ("b", (0, 1, 0)), ("s", (1, 1, 0)), ("c", (0, 0, 1))]
        _expect_err(
            lambda: oracle.verify_shannon_certificate(card_atoms, [], [(3, 3, 1, 9)], [], 1, [], [], "Z"),
            "BROKEN_COPY_IDENTITY",
            "zero copy isos card mismatch",
        )
        dp_mis_atoms = [("a", (1, 0, 0)), ("b", (0, 1, 0)), ("c", (0, 0, 1))]
        _expect_err(
            lambda: oracle.verify_shannon_certificate(dp_mis_atoms, [((1, -1, 0), 0, 1)], [(3, 3, 1, 5)], [], 1, [], [], "Z"),
            "BROKEN_COPY_IDENTITY",
            "zero copy isos diff_pair mismatch",
        )
        ambig_atoms = [("x", (1, 0, 0, 0)), ("y", (0, 1, 0, 0)), ("xp", (0, 0, 1, 0)), ("yp", (0, 0, 0, 1))]
        _expect_err(
            lambda: oracle.verify_shannon_certificate(ambig_atoms, [], [(3, 3, 0, 12)], [], 1, [], [], "Z"),
            "BROKEN_COPY_IDENTITY",
            "ambiguous 2 copy isos",
        )
        # Empty copy step r==0 is valid & harmless when O_0 contains base atoms
        r0_cert = oracle.verify_shannon_certificate(
            [("X", (1, 0)), ("Y", (0, 1)), ("D", (1, -1))],
            [],
            [(7, 0, 0, 0)],
            [],
            1 << 2,
            [(1 << 0, Fraction(1, 1)), (1 << 1, Fraction(1, 1))],
            [("submod", Fraction(1, 1), (0, 0, 1)), ("mono", Fraction(1, 1), (1 << 2, 0)), ("copy", Fraction(1, 1), 0)],
            "Z",
        )
        _check(r0_cert["exponent"] == "2", "r==0 trivial copy")

        # Forged & malformed eq_groups + exact-list/tuple container tests (killing M038/41/43/45/46 & DEL_0 on L385/409/430)
        one_atom = [("X", (1, 0))]
        one_rhs = [(1, Fraction(1, 1))]
        _expect_err(lambda: oracle.verify_shannon_certificate((("X", (1, 0)),), [], [], [], 1, one_rhs, [], "Z"), "INVALID_ATOMS", "tuple atoms")
        _expect_err(lambda: oracle.verify_shannon_certificate(one_atom, (), [], [], 1, one_rhs, [], "Z"), "INVALID_DIFF_PAIRS", "tuple diff_pairs")
        _expect_err(lambda: oracle.verify_shannon_certificate(one_atom, None, [], [], 1, one_rhs, [], "Z"), "INVALID_DIFF_PAIRS", "None diff_pairs")
        _expect_err(lambda: oracle.verify_shannon_certificate(one_atom, [], (), [], 1, one_rhs, [], "Z"), "INVALID_COPY_STEPS", "tuple copy_steps")
        _expect_err(lambda: oracle.verify_shannon_certificate(one_atom, [], None, [], 1, one_rhs, [], "Z"), "INVALID_COPY_STEPS", "None copy_steps")
        _expect_err(lambda: oracle.verify_shannon_certificate(one_atom, [], [], (), 1, one_rhs, [], "Z"), "INVALID_EQ_GROUP", "tuple eq_groups")
        _expect_err(lambda: oracle.verify_shannon_certificate(one_atom, [], [], None, 1, one_rhs, [], "Z"), "INVALID_EQ_GROUP", "None eq_groups")
        _expect_err(lambda: oracle.verify_shannon_certificate(one_atom, [], [], [(1,)], 1, one_rhs, [], "Z"), "INVALID_EQ_GROUP", "tuple single eq_group")
        _expect_err(lambda: oracle.verify_shannon_certificate(one_atom, [], [], [], 1, ((1, Fraction(1, 1)),), [], "Z"), "INVALID_RHS_TERMS", "tuple rhs_terms")
        _expect_err(lambda: oracle.verify_shannon_certificate(one_atom, [], [], [], 1, None, [], "Z"), "INVALID_RHS_TERMS", "None rhs_terms")
        _expect_err(lambda: oracle.verify_shannon_certificate(one_atom, [], [], [], 1, one_rhs, (), "Z"), "INVALID_DUAL_ROWS", "tuple dual_rows")
        _expect_err(lambda: oracle.verify_shannon_certificate(one_atom, [], [], [], 1, one_rhs, None, "Z"), "INVALID_DUAL_ROWS", "None dual_rows")
        _expect_err(lambda: oracle.verify_shannon_certificate(xy_atoms, [[(1, -1), 0, 1]], [], [], 1, one_rhs, [], "Z"), "INVALID_DIFF_PAIRS", "list dp_entry")
        _expect_err(lambda: oracle.verify_shannon_certificate(xy_atoms, [], [], "bad", 1, [], [], "Z"), "INVALID_EQ_GROUP", "str eq_groups")
        _expect_err(lambda: oracle.verify_shannon_certificate(xy_atoms, [], [], [[]], 1, [], [], "Z"), "INVALID_EQ_GROUP", "empty eq_group")
        _expect_err(lambda: oracle.verify_shannon_certificate(xy_atoms, [], [], [(1, 2)], 1, [], [], "Z"), "INVALID_EQ_GROUP", "tuple eq_group")
        _expect_err(lambda: oracle.verify_shannon_certificate(xy_atoms, [], [], [[1, 2]], 1, [], [], "Z"), "INVALID_EQ_GROUP", "forged X~Y no copies")
        atoms_116, diff_116, copies_116, eq_116, z0_116, rhs_116, duals_116 = oracle._build_katz_tao_11_6_spec()
        _expect_err(
            lambda: oracle.verify_shannon_certificate(atoms_116, diff_116, copies_116, eq_116 + [[1 << 0, 1 << 1]], z0_116, rhs_116, duals_116, "Z"),
            "INVALID_EQ_GROUP",
            "forged a~b in 11/6",
        )
        _expect_err(
            lambda: oracle.verify_shannon_certificate(atoms_116, diff_116, copies_116, eq_116 + [[3, 4]], z0_116, rhs_116, duals_116, "Z"),
            "INVALID_EQ_GROUP",
            "forged {a,b}~{c} rank mismatch",
        )

        # Out-of-range masks (including mult==0!) & malformed containers
        _expect_err(lambda: oracle.verify_shannon_certificate([("X", (1,))], [], [], [], 1 << 5, [], [], "Z"), "INT_OUT_OF_RANGE", "oob target_mask")
        _expect_err(
            lambda: oracle.verify_shannon_certificate(xy_atoms, [], [], [], 1, [], [("submod", Fraction(0, 1), (1 << 5, 0, 1))], "Z"),
            "INT_OUT_OF_RANGE",
            "oob submod mask at mult=0",
        )
        _expect_err(
            lambda: oracle.verify_shannon_certificate(xy_atoms, [], [], [], 1, [], [("mono", Fraction(0, 1), (1 << 5, 0))], "Z"),
            "INT_OUT_OF_RANGE",
            "oob mono mask at mult=0",
        )
        for bad_atoms in (
            [("a",)],
            [["a", (1, 0)]],
            [(123, (1, 0))],
            [("a", [1, 0])],
            [("a", ())],
            [("a", (1, 0)), ("b", (1, 0, 0))],
            [("a", (1, 0)), ("b", (1, 0))],
        ):
            _expect_err(lambda ba=bad_atoms: oracle.verify_shannon_certificate(ba, [], [], [], 1, [], [], "Z"), "INVALID_ATOMS", f"bad atoms {bad_atoms!r}")
        for bad_dp in ("bad", [((1, 0), 0)], [[[1, 0], 0, 1]], [([1, 0], 0, 1)], [((1,), 0, 1)]):
            _expect_err(lambda bd=bad_dp: oracle.verify_shannon_certificate(xy_atoms, bd, [], [], 1, [], [], "Z"), "INVALID_DIFF_PAIRS", f"bad dp {bad_dp!r}")
        for bad_cp in ("bad", [(1, 1, 0)], [[1, 1, 0, 1]]):
            _expect_err(lambda bc=bad_cp: oracle.verify_shannon_certificate(xy_atoms, [], bc, [], 1, [], [], "Z"), "INVALID_COPY_STEPS", f"bad cp {bad_cp!r}")
        for bad_rt in ("bad", [(1,)], [[1, Fraction(1, 1)]]):
            _expect_err(lambda br=bad_rt: oracle.verify_shannon_certificate(xy_atoms, [], [], [], 1, br, [], "Z"), "INVALID_RHS_TERMS", f"bad rhs {bad_rt!r}")
        for bad_dr in (
            "bad",
            [("mono", Fraction(1, 1))],
            [["mono", Fraction(1, 1), (0, 0)]],
            [("submod", Fraction(1, 1), (0, 0))],
            [("submod", Fraction(1, 1), [0, 0, 1])],
            [("mono", Fraction(1, 1), (0,))],
            [("mono", Fraction(1, 1), [0, 0])],
        ):
            _expect_err(lambda bdr=bad_dr: oracle.verify_shannon_certificate(xy_atoms, [], [], [], 1, [], bdr, "Z"), "INVALID_DUAL_ROWS", f"bad duals {bad_dr!r}")

        # Negative control on verify_primal_7_4_polymatroid (submod violation when diff_pair jumps rank by +1)
        bad_poly = oracle.verify_primal_7_4_polymatroid(
            [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 0]],
            [([0, 0, 1], 0, 1), ([1, 0, 0], 1, 2)],
            3,
            12,
            [(3, 1, 5)],
        )
        _check(bad_poly["valid_7_4_polymatroid"] is False, "invalid polymatroid rejected")
        # Negative control triggering mono violation (rk=1 h=4 > rk=2 4*2-5=3)
        bad_mono_poly = oracle.verify_primal_7_4_polymatroid(
            [[1, 0], [0, 1], [1, 1], [1, 2]],
            [([1, -1], 0, 1), ([1, 2], 0, 2), ([2, 1], 0, 3), ([1, 3], 1, 2), ([3, 1], 1, 3)],
            2,
            12,
            [],
        )
        _check(bad_mono_poly["mono_violations"] > 0 and bad_mono_poly["valid_7_4_polymatroid"] is False, "mono violation caught")
        # Negative control triggering submod violation (jump on union of independent singletons)
        bad_sub_poly = oracle.verify_primal_7_4_polymatroid(
            [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 0]],
            [([1, 1, 0], 0, 2)],
            3,
            12,
            [],
        )
        _check(bad_sub_poly["submod_violations"] > 0 and bad_sub_poly["valid_7_4_polymatroid"] is False, "submod violation caught")
        # verify_primal_7_4_polymatroid cap<=0, zero vector, type & degenerate guards
        p4_vecs = [[1, 0], [0, 1], [1, 1], [1, 2]]
        _expect_err(lambda: oracle.verify_primal_7_4_polymatroid(p4_vecs, [], 2, 0, []), "INT_OUT_OF_RANGE", "poly cap=0")
        _expect_err(lambda: oracle.verify_primal_7_4_polymatroid("bad", [], 2, 12, []), "INVALID_POLYMATROID_INPUT", "poly non-list vecs")
        _expect_err(lambda: oracle.verify_primal_7_4_polymatroid(tuple(p4_vecs), [], 2, 12, []), "INVALID_POLYMATROID_INPUT", "poly tuple len4 vecs")
        _expect_err(lambda: oracle.verify_primal_7_4_polymatroid(p4_vecs[:3], [], 2, 12, []), "INVALID_POLYMATROID_INPUT", "poly <4 vecs")
        _expect_err(lambda: oracle.verify_primal_7_4_polymatroid([(1, 0), [0, 1], [1, 1], [1, 2]], [], 2, 12, []), "INVALID_POLYMATROID_INPUT", "poly tuple row")
        _expect_err(lambda: oracle.verify_primal_7_4_polymatroid([[1], [0, 1], [1, 1], [1, 2]], [], 2, 12, []), "INVALID_POLYMATROID_INPUT", "poly wrong dim row")
        _expect_err(lambda: oracle.verify_primal_7_4_polymatroid([[0, 0], [0, 1], [1, 1], [1, 2]], [], 2, 12, []), "ZERO_VECTOR_FORBIDDEN", "poly zero atom")
        _expect_err(lambda: oracle.verify_primal_7_4_polymatroid(p4_vecs, "bad", 2, 12, []), "INVALID_POLYMATROID_INPUT", "poly bad dvecs")
        _expect_err(lambda: oracle.verify_primal_7_4_polymatroid(p4_vecs, (), 2, 12, []), "INVALID_POLYMATROID_INPUT", "poly empty tuple dvecs")
        _expect_err(lambda: oracle.verify_primal_7_4_polymatroid(p4_vecs, [([1, 0], 0)], 2, 12, []), "INVALID_POLYMATROID_INPUT", "poly short dvec tuple")
        _expect_err(lambda: oracle.verify_primal_7_4_polymatroid(p4_vecs, [[[1, 0], 0, 1]], 2, 12, []), "INVALID_POLYMATROID_INPUT", "poly list dvec entry")
        _expect_err(lambda: oracle.verify_primal_7_4_polymatroid(p4_vecs, [((1, 0), 0, 1)], 2, 12, []), "INVALID_POLYMATROID_INPUT", "poly tuple dv")
        _expect_err(lambda: oracle.verify_primal_7_4_polymatroid(p4_vecs, [([1], 0, 1)], 2, 12, []), "INVALID_POLYMATROID_INPUT", "poly short dv")
        _expect_err(lambda: oracle.verify_primal_7_4_polymatroid(p4_vecs, [([0, 0], 0, 1)], 2, 12, []), "ZERO_VECTOR_FORBIDDEN", "poly zero dv")
        _expect_err(lambda: oracle.verify_primal_7_4_polymatroid(p4_vecs, [], 2, 12, "bad"), "INVALID_POLYMATROID_INPUT", "poly bad copy_triples")
        _expect_err(lambda: oracle.verify_primal_7_4_polymatroid(p4_vecs, [], 2, 12, ()), "INVALID_POLYMATROID_INPUT", "poly empty tuple copy_triples")
        _expect_err(lambda: oracle.verify_primal_7_4_polymatroid(p4_vecs, [], 2, 12, [(1, 0)]), "INVALID_POLYMATROID_INPUT", "poly short triple")
        _expect_err(lambda: oracle.verify_primal_7_4_polymatroid(p4_vecs, [], 2, 12, [[1, 0, 2]]), "INVALID_POLYMATROID_INPUT", "poly list triple")
        col_vecs = [[1, 0], [2, 0], [3, 0], [0, 1]]
        dps_zero = [([1, 0], 0, 1), ([1, 0], 0, 2), ([1, 0], 1, 2), ([2, 0], 0, 1)]
        _expect_err(lambda: oracle.verify_primal_7_4_polymatroid(col_vecs, dps_zero, 2, 12, []), "DEGENERATE_POLYMATROID", "poly h(X)==0")
        _expect_err(lambda: oracle.verify_primal_7_4_polymatroid(col_vecs, dps_zero + [([3, 0], 0, 2)], 2, 12, []), "DEGENERATE_POLYMATROID", "poly h(X)<0")

        # projective_cross_ratio & _proj_apply_mobius strict guards
        _expect_err(lambda: oracle._proj_apply_mobius((1, 2, 2, 4), (0, 1)), "SINGULAR_MOBIUS", "singular Mobius")
        _expect_err(lambda: oracle._proj_apply_mobius([1, 0, 0, 1], (0, 1)), "INVALID_MOBIUS_MAT", "list Mobius")
        _expect_err(lambda: oracle._proj_apply_mobius((1, 0, 0), (0, 1)), "INVALID_MOBIUS_MAT", "short Mobius")
        _expect_err(lambda: oracle._proj_apply_mobius((True, 0, 0, 1), (0, 1)), "INVALID_INT_TYPE", "bool Mobius")
        _expect_err(lambda: oracle._proj_apply_mobius((1, 0, 0, 1), (0, 0)), "ZERO_PROJ_POINT", "zero pt Mobius")
        _expect_err(lambda: oracle.projective_cross_ratio((0, 1), (1, 1), (1, 0), (0, 1)), "DEGENERATE_CROSS_RATIO", "degenerate CR")
        _expect_err(lambda: oracle.projective_cross_ratio((False, True), (1, 1), (1, 0), (-1, 1)), "INVALID_INT_TYPE", "bool CR")
        _expect_err(lambda: oracle.projective_cross_ratio((1, 0), (1, 1), (0, 1), (0, 0)), "ZERO_PROJ_POINT", "zero pt CR")
        _expect_err(lambda: oracle.projective_cross_ratio([0, 1], (1, 1), (1, 0), (-1, 1)), "INVALID_PROJ_POINT", "list pt CR")
        _expect_err(lambda: oracle.projective_cross_ratio((0,), (1, 1), (1, 0), (-1, 1)), "INVALID_PROJ_POINT", "len1 pt CR")

        # Pillar 2, 3, 4, 5 helper guards
        _expect_err(lambda: oracle.von_mangoldt_hit_prob(6, [2, 3], {2: Fraction(1, 1), 3: Fraction(1, 1)}), "INVALID_TARGET_SET", "list target_set")
        _expect_err(lambda: oracle.von_mangoldt_hit_prob(6, {2}, {}), "INVALID_L_WEIGHTS", "empty weights")
        _expect_err(lambda: oracle.von_mangoldt_hit_prob(6, {2}, "bad"), "INVALID_L_WEIGHTS", "str weights")
        _expect_err(lambda: oracle.von_mangoldt_hit_prob(6, {2}, {4: Fraction(1, 1)}), "NON_PRIME_WEIGHT_KEY", "composite key 4")
        _expect_err(lambda: oracle.von_mangoldt_hit_prob(6, {2}, {2: Fraction(0, 1)}), "NONPOSITIVE_WEIGHT", "zero weight")
        _expect_err(lambda: oracle.von_mangoldt_hit_prob(6, {2}, {2: Fraction(1, 1)}), "MISSING_PRIME_WEIGHT", "missing prime 3")
        _expect_err(lambda: oracle.is_primitive_antichain([]), "INVALID_ANTICHAIN", "empty antichain")
        _expect_err(lambda: oracle.is_primitive_antichain((6, 10)), "INVALID_ANTICHAIN", "tuple antichain")
        _check(oracle.is_primitive_antichain([6, 6]) is False and oracle.is_primitive_antichain([6, 12]) is False, "non-primitive")
        _check(oracle.is_primitive_antichain([6, 10, 15]) is True, "primitive")

        _expect_err(lambda: oracle.gilbreath_left_diagonal([2]), "INVALID_SEQ", "len 1 seq")
        _expect_err(lambda: oracle.gilbreath_left_diagonal((2, 3)), "INVALID_SEQ", "tuple seq")
        _expect_err(lambda: oracle.construct_singer_sidon(6), "INVALID_SINGER_ORDER", "composite non-prime-power 6")
        _check(oracle.satisfies_cot_diameter_bound(3, 20) is True and oracle.satisfies_cot_diameter_bound(3, 9) is True, "gap <= 0 large/exact diam")
        _check(oracle.satisfies_cot_diameter_bound(3, 5) is True and oracle.satisfies_cot_diameter_bound(10, 40) is False and oracle.satisfies_cot_diameter_bound(10, 41) is True, "COT sharp boundary")
        _expect_err(lambda: oracle.wht_f2_4([1] * 8), "INVALID_WHT_LEN", "short wht")
        _expect_err(lambda: oracle.wht_f2_4(tuple([1] * 16)), "INVALID_WHT_LEN", "tuple wht")
        for gfn in (oracle.gowers_u3_pow8_f2_4, oracle.gowers_u4_pow16_f2_4):
            _expect_err(lambda f=gfn: f([True] * 16), "INVALID_INT_TYPE", "bool gowers")
            _expect_err(lambda f=gfn: f([1] * 8), "INVALID_WHT_LEN", "short gowers")
            _expect_err(lambda f=gfn: f("1" * 16), "INVALID_WHT_LEN", "str gowers")

        _expect_err(lambda: oracle.dyadic_ns_bilinear([Fraction(1, 1)], Fraction(2, 1)), "INVALID_SHELLS", "len 1 shells")
        _expect_err(lambda: oracle.dyadic_ns_bilinear((Fraction(1, 1), Fraction(1, 1)), Fraction(2, 1)), "INVALID_SHELLS", "tuple shells")
        _expect_err(lambda: oracle.dyadic_ns_bilinear([Fraction(1, 1), Fraction(1, 1)], Fraction(1, 1)), "INVALID_LAMBDA", "lam == 1")
        _expect_err(lambda: oracle.verify_dptz_rational_matrix((1,), (1,)), "INVALID_DPTZ_INPUT", "n=1 dptz")
        _expect_err(lambda: oracle.verify_dptz_rational_matrix((1, 2), (1, 2, 3)), "INVALID_DPTZ_INPUT", "len mismatch dptz")
        _expect_err(lambda: oracle.verify_dptz_rational_matrix((1, 2), (3, 3)), "REPEATED_EIGENVALUES", "repeated eigs")
        _expect_err(lambda: oracle.verify_dptz_rational_matrix((True, 2), (1, 2)), "INVALID_INT_TYPE", "bool u_vec")
        _expect_err(lambda: oracle.verify_dptz_rational_matrix((1, 2), (1, False)), "INVALID_INT_TYPE", "bool eig")
        _expect_err(lambda: oracle.verify_dptz_rational_matrix((0, 0), (1, 2)), "ZERO_HOUSEHOLDER_VEC", "zero u")
        _expect_err(lambda: oracle.verify_magma_laws([]), "INVALID_CAYLEY", "empty cayley")
        _expect_err(lambda: oracle.verify_magma_laws("x"), "INVALID_CAYLEY", "str cayley")
        _expect_err(lambda: oracle.verify_magma_laws([[0, 1]]), "INVALID_CAYLEY_ROW", "rect cayley")
        _expect_err(lambda: oracle.verify_magma_laws([(0,)]), "INVALID_CAYLEY_ROW", "tuple cayley row")

    def test_03_zone_b_hardening_symlinks_pwd_cwd_surrogates_and_cli(self) -> None:
        cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
        cert_bytes = CERT_PATH.read_bytes()

        # Hex64 + verify_certificate_dict + secondary algebraic crosscheck guards
        _expect_err(lambda: audit.require_hex64_lower_ascii("a" * 63, "h"), "INVALID_HEX64", "len 63")
        _expect_err(lambda: audit.require_hex64_lower_ascii("A" * 64, "h"), "INVALID_HEX64", "uppercase hex")
        _expect_err(lambda: audit.require_hex64_lower_ascii(123, "h"), "INVALID_HEX64", "int hex")
        _expect_err(lambda: audit.verify_certificate_dict([]), "INVALID_CERT_TYPE", "list cert")
        bad_k = copy.deepcopy(cert)
        bad_k["extra"] = 1
        _expect_err(lambda: audit.verify_certificate_dict(bad_k, expected=cert), "INVALID_CERT_KEYS", "extra key")
        bad_schema = copy.deepcopy(cert)
        bad_schema["schema_version"] = "9.9.9"
        _expect_err(lambda: audit.verify_certificate_dict(bad_schema, expected=cert), "INVALID_SCHEMA", "bad schema")
        bad_tid = copy.deepcopy(cert)
        bad_tid["track_id"] = "WRONG"
        _expect_err(lambda: audit.verify_certificate_dict(bad_tid, expected=cert), "INVALID_TRACK_ID", "bad track_id")
        bad_psha = copy.deepcopy(cert)
        bad_psha["payload_sha256"] = "0" * 64
        _expect_err(lambda: audit.verify_certificate_dict(bad_psha, expected=cert), "PAYLOAD_SHA_MISMATCH", "bad psha")
        bad_csha = copy.deepcopy(cert)
        bad_csha["certificate_sha256"] = "0" * 64
        _expect_err(lambda: audit.verify_certificate_dict(bad_csha, expected=cert), "CERTIFICATE_SHA_MISMATCH", "bad csha")
        # Re-signed tampered payload fails closed under BOTH full_replay=False AND full_replay=True!
        import hashlib as _hl

        def _resign(pl_dict: dict[str, Any]) -> dict[str, Any]:
            psha = _hl.sha256(audit.canonical_json_bytes(pl_dict)).hexdigest()
            env_r = {
                "schema_version": cert["schema_version"],
                "track_id": cert["track_id"],
                "payload_sha256": psha,
                "payload": pl_dict,
            }
            csha = _hl.sha256(audit.canonical_json_bytes(env_r)).hexdigest()
            return {
                "schema_version": cert["schema_version"],
                "track_id": cert["track_id"],
                "payload_sha256": psha,
                "certificate_sha256": csha,
                "payload": pl_dict,
            }

        bad_pl_d = copy.deepcopy(cert["payload"])
        bad_pl_d["pillar2_von_mangoldt_chains"]["hit_210_omega2_uniform"] = "2"
        bad_pl = _resign(bad_pl_d)
        _expect_err(lambda: audit.verify_certificate_dict(bad_pl, full_replay=False), "ALGEBRAIC_CROSSCHECK_FAILED", "non-replay leaf tamper")
        _expect_err(lambda: audit.verify_certificate_dict(bad_pl, expected=cert, full_replay=True), "ALGEBRAIC_CROSSCHECK_FAILED", "replay leaf tamper")
        # Direct full_replay=True expected-cert divergence checks (kills CERTIFICATE_MISMATCH guard)
        for drift_exp in (
            {**cert, "payload_sha256": "0" * 64},
            {**cert, "certificate_sha256": "0" * 64},
            {**cert, "payload": {}},
        ):
            _expect_err(lambda e=drift_exp: audit.verify_certificate_dict(cert, expected=e, full_replay=True), "CERTIFICATE_MISMATCH", "replay expected mismatch")
        _expect_err(lambda: audit.verify_certificate_dict(cert, full_replay=1), "INVALID_BOOL_TYPE", "non-bool full_replay")  # type: ignore[arg-type]

        # Division-free algebraic identity violations -> ALGEBRAIC_IDENTITY_FAILED (one targeted kill per branch)
        def _pl_copy() -> dict[str, Any]:
            return copy.deepcopy(cert["payload"])

        id_cases: list[tuple[str, Any]] = []
        for tag_i, mut_fn in (
            ("exp_non_str", lambda d: d["pillar1_katz_tao_entropy"]["katz_tao_11_6_certificate"].__setitem__("exponent", 0)),
            ("exp_three_parts", lambda d: d["pillar1_katz_tao_entropy"]["katz_tao_11_6_certificate"].__setitem__("exponent", "11/6/99")),
            ("exp_zero_denom", lambda d: d["pillar1_katz_tao_entropy"]["katz_tao_11_6_certificate"].__setitem__("exponent", "1/0")),
            ("exp_neg_denom", lambda d: d["pillar1_katz_tao_entropy"]["katz_tao_11_6_certificate"].__setitem__("exponent", "1/-2")),
            ("exp_bad_sum", lambda d: d["pillar1_katz_tao_entropy"]["katz_tao_11_6_certificate"].__setitem__("exponent", "2")),
            ("rhs_weight_zero_denom", lambda d: d["pillar1_katz_tao_entropy"]["katz_tao_11_6_certificate"].__setitem__("rhs_weights", ["1/0", "2/3", "1/2"])),
            ("null_leaf_section", lambda d: d["pillar1_katz_tao_entropy"].__setitem__("katz_tao_11_6_certificate", None)),
            ("empty_receipts", lambda d: d["pillar1_katz_tao_entropy"]["open_seam_probe_honest_status"].__setitem__("per_glue_receipts", [])),
            ("str_receipts", lambda d: d["pillar1_katz_tao_entropy"]["open_seam_probe_honest_status"].__setitem__("per_glue_receipts", "12345678")),
            ("garbage_receipts", lambda d: d["pillar1_katz_tao_entropy"]["open_seam_probe_honest_status"].__setitem__("per_glue_receipts", [0] * 8)),
            ("p2_beta_zero_denom", lambda d: d["pillar2_von_mangoldt_chains"]["odd_banks_martin_Q357"]["beta_weights"].__setitem__("3", "1/0")),
            ("p2_kernel_false", lambda d: d["pillar2_von_mangoldt_chains"].__setitem__("von_mangoldt_kernel_identity_ok", False)),
            ("p3_pi9_zero_denom", lambda d: d["pillar3_syracuse_and_gilbreath"]["syracuse_3adic_mod9"]["stationary_pi_mod9"].__setitem__("1", "1/0")),
            ("p3_pi9_bad_sum", lambda d: d["pillar3_syracuse_and_gilbreath"]["syracuse_3adic_mod9"]["stationary_pi_mod9"].__setitem__("1", "0")),
            ("p3_m9_min_zero", lambda d: d["pillar3_syracuse_and_gilbreath"]["syracuse_3adic_mod9"].__setitem__("stationary_min", "0")),
            ("p3_haar_zero", lambda d: d["pillar3_syracuse_and_gilbreath"]["syracuse_2adic_haar_drift"].__setitem__("asymptotic_haar_geometric_drift", "0")),
            ("p4_empty_singers", lambda d: d["pillar4_sidon_gowers_ruzsa"].__setitem__("singer_sidon_sets", [])),
            ("p4_str_singers", lambda d: d["pillar4_sidon_gowers_ruzsa"].__setitem__("singer_sidon_sets", "12345")),
            ("p4_null_singer_rows", lambda d: d["pillar4_sidon_gowers_ruzsa"].__setitem__("singer_sidon_sets", [None] * 5)),
            ("p4_empty_sidon_set", lambda d: (d["pillar4_sidon_gowers_ruzsa"]["singer_sidon_sets"][0].__setitem__("k", 0), d["pillar4_sidon_gowers_ruzsa"]["singer_sidon_sets"][0].__setitem__("sidon_set", []))),
            ("p4_singer_mod_zero", lambda d: d["pillar4_sidon_gowers_ruzsa"]["singer_sidon_sets"][0].__setitem__("modulus", 0)),
            ("p4_ruzsa_bad", lambda d: d["pillar4_sidon_gowers_ruzsa"]["ruzsa_and_plunnecke"].__setitem__("ruzsa_triangle_lhs", 999999)),
            ("p5_dns_lam_zero", lambda d: d["pillar5_dyadic_ns_dptz_etp"]["dyadic_ns_barrier"].__setitem__("lambda", "0")),
            ("p5_dns_rate_zero", lambda d: d["pillar5_dyadic_ns_dptz_etp"]["dyadic_ns_barrier"].__setitem__("lyapunov_growth_rates", ["0", "10379/200"])),
            ("p5_dptz_pairs_zero", lambda d: d["pillar5_dyadic_ns_dptz_etp"]["dptz_eigenvector_eigenvalue"]["matrix_3x3"].__setitem__("eigenpair_minor_pairs_checked", 0)),
        ):
            d_i = _pl_copy()
            mut_fn(d_i)
            id_cases.append((tag_i, d_i))
        for tag_i, bad_i_pl in id_cases:
            _expect_err(lambda p=bad_i_pl: audit._secondary_algebraic_crosscheck(p), "ALGEBRAIC_IDENTITY_FAILED", tag_i)

        # Direct _strict_typed_equal & _validate_json_tree kills (distinct from algebraic-law checks)
        bad_xchk_bool = _pl_copy()
        bad_xchk_bool["pillar1_katz_tao_entropy"]["open_seam_probe_honest_status"]["p0_primal_closed_sets_verified"] = _IntSub(100)
        _expect_err(lambda: audit._secondary_algebraic_crosscheck(bad_xchk_bool), "INVALID_JSON_VALUE", "intsub crosscheck")
        bad_xchk_float = _pl_copy()
        bad_xchk_float["pillar1_katz_tao_entropy"]["open_seam_probe_honest_status"]["p0_primal_closed_sets_verified"] = 3 / 2
        _expect_err(lambda: audit._secondary_algebraic_crosscheck(bad_xchk_float), "INVALID_JSON_VALUE", "float crosscheck")
        bad_xchk_type = _pl_copy()
        bad_xchk_type["pillar1_katz_tao_entropy"]["all_verified"] = 1
        _expect_err(lambda: audit._secondary_algebraic_crosscheck(bad_xchk_type), "ALGEBRAIC_CROSSCHECK_FAILED", "int-for-bool type swap")
        bad_xchk_val = _pl_copy()
        bad_xchk_val["pillar1_katz_tao_entropy"]["open_seam_probe_honest_status"]["p0_primal_closed_sets_verified"] = 99
        _expect_err(lambda: audit._secondary_algebraic_crosscheck(bad_xchk_val), "ALGEBRAIC_CROSSCHECK_FAILED", "wrong-int crosscheck")
        bad_xchk_extra_nested = _pl_copy()
        bad_xchk_extra_nested["pillar1_katz_tao_entropy"]["injected"] = 1
        _expect_err(lambda: audit._secondary_algebraic_crosscheck(bad_xchk_extra_nested), "ALGEBRAIC_CROSSCHECK_FAILED", "extra nested key")
        bad_xchk_swap_key = _pl_copy()
        del bad_xchk_swap_key["pillar2_von_mangoldt_chains"]["hit_210_omega2_uniform"]
        bad_xchk_swap_key["pillar2_von_mangoldt_chains"]["bogus_key"] = "1"
        _expect_err(lambda: audit._secondary_algebraic_crosscheck(bad_xchk_swap_key), "ALGEBRAIC_CROSSCHECK_FAILED", "swapped nested key")
        bad_xchk_extra_list = _pl_copy()
        bad_xchk_extra_list["pillar3_syracuse_and_gilbreath"]["chase_hunter_tao_witnesses"]["long_zero_block_left_diag"].append(9)
        _expect_err(lambda: audit._secondary_algebraic_crosscheck(bad_xchk_extra_list), "ALGEBRAIC_CROSSCHECK_FAILED", "extra list item")
        _check(audit.verify_certificate_file(CERT_PATH, full_replay=False)["valid"] is True, "file non-replay valid")
        _expect_err(lambda: audit.verify_certificate_file(CERT_PATH, full_replay=1), "INVALID_BOOL_TYPE", "file non-bool full_replay")  # type: ignore[arg-type]
        _expect_err(lambda: audit._secondary_algebraic_crosscheck("not_dict"), "ALGEBRAIC_CROSSCHECK_FAILED", "str crosscheck")
        _expect_err(lambda: audit._secondary_algebraic_crosscheck({}), "ALGEBRAIC_CROSSCHECK_FAILED", "empty crosscheck")
        _expect_err(lambda: audit._secondary_algebraic_crosscheck({"pillar1_katz_tao_entropy": None}), "ALGEBRAIC_CROSSCHECK_FAILED", "null section crosscheck")

        # Targeted self-contradiction, extra-key & zero-denom re-signed tampers (full_replay=False & standalone secondary)
        contradictions: list[tuple[str, Any]] = []
        c_inj = _pl_copy()
        c_inj["injected"] = "evil"
        contradictions.append(("extra_top_key", c_inj))
        contradictions.append(("extra_nested_key", bad_xchk_extra_nested))
        c_beats = _pl_copy()
        c_beats["pillar1_katz_tao_entropy"]["open_seam_probe_honest_status"]["beats_7_4_in_2page_rank3_cone"] = True
        contradictions.append(("beats_7_4_contradiction", c_beats))
        c_rec0 = _pl_copy()
        c_rec0["pillar1_katz_tao_entropy"]["open_seam_probe_honest_status"]["per_glue_receipts"] = [0] * 8
        contradictions.append(("garbage_receipts", c_rec0))
        c_res = _pl_copy()
        c_res["pillar1_katz_tao_entropy"]["katz_tao_11_6_certificate"]["residual_count"] = 999
        c_res["pillar1_katz_tao_entropy"]["katz_tao_11_6_certificate"]["cl_ring_equals_cl_Q"] = False
        contradictions.append(("p1_residual_false", c_res))
        c_p2 = _pl_copy()
        c_p2["pillar2_von_mangoldt_chains"]["von_mangoldt_kernel_identity_ok"] = False
        c_p2["pillar2_von_mangoldt_chains"]["odd_banks_martin_Q357"]["subinvariance_eq62_max_upper_bound_le_1"] = False
        contradictions.append(("p2_kernel_false", c_p2))
        c_p3 = _pl_copy()
        c_p3["pillar3_syracuse_and_gilbreath"]["two_adic_parity_bijection_k1_to_8"] = False
        c_p3["pillar3_syracuse_and_gilbreath"]["syracuse_3adic_mod27"]["stationary_residual_zero"] = False
        contradictions.append(("p3_bijection_false", c_p3))
        c_p4 = _pl_copy()
        c_p4["pillar4_sidon_gowers_ruzsa"]["singer_sidon_sets"] = [None] * 5
        c_p4["pillar4_sidon_gowers_ruzsa"]["ruzsa_and_plunnecke"]["ruzsa_triangle_lhs"] = 999999
        contradictions.append(("p4_singers_none", c_p4))
        c_p5 = _pl_copy()
        c_p5["pillar5_dyadic_ns_dptz_etp"]["dyadic_ns_barrier"]["energy_conservation_exact"] = False
        c_p5["pillar5_dyadic_ns_dptz_etp"]["dptz_eigenvector_eigenvalue"]["matrix_3x3"]["dptz_all_exact"] = False
        contradictions.append(("p5_energy_false", c_p5))
        c_zden = _pl_copy()
        c_zden["pillar3_syracuse_and_gilbreath"]["syracuse_3adic_mod9"]["stationary_min"] = "1/0"
        contradictions.append(("zero_denom_resigned", c_zden))
        for tag_c, bad_c_pl in contradictions:
            rs_c = _resign(bad_c_pl)
            for fn_c in (
                lambda d=rs_c: audit.verify_certificate_dict(d, full_replay=False),
                lambda p=bad_c_pl: audit._secondary_algebraic_crosscheck(p),
            ):
                raised_typed = False
                try:
                    fn_c()
                except oracle.TaoOperatorsError:
                    raised_typed = True
                _check(raised_typed, f"contradiction {tag_c} escaped or crashed")

        # Fast exhaustive in-place walk across ALL 402 leaves (zero-denom + value + type mutations, 0 raw crashes, 0 escapes)
        leaf_paths: list[list[Any]] = []

        def _collect_leaves(node: Any, path: list[Any]) -> None:
            if type(node) is dict:
                for k, v in node.items():
                    _collect_leaves(v, path + [k])
            elif type(node) is list:
                for idx, item in enumerate(node):
                    _collect_leaves(item, path + [idx])
            else:
                leaf_paths.append(path)

        pl_walk = _pl_copy()
        _collect_leaves(pl_walk, [])
        _check(len(leaf_paths) == 402, f"expected 402 leaves, got {len(leaf_paths)}")
        for lpath in leaf_paths:
            parent_w: Any = pl_walk
            for step in lpath[:-1]:
                parent_w = parent_w[step]
            old_v = parent_w[lpath[-1]]
            if type(old_v) is bool:
                muts: list[Any] = [not old_v, int(old_v)]
            elif type(old_v) is int:
                muts = [old_v + 1, 0 if old_v != 0 else 1, bool(old_v)]
            elif type(old_v) is str:
                muts = ["0" if old_v != "0" else "1", "1/0", 0]
            else:
                muts = ["tamper", 0]
            for mv in muts:
                parent_w[lpath[-1]] = mv
                law_ok = audit._check_division_free_algebraic_laws(pl_walk)
                eq_ok = audit._strict_typed_equal(pl_walk, audit._PINNED_PAYLOAD)
                _check(not (law_ok and eq_ok), f"leaf tamper {lpath}={mv!r} escaped")
            parent_w[lpath[-1]] = old_v

        # Strict JSON tree & parser guards
        _check(audit.parse_strict_json_text("[1,true,null]", "arr", require_object=False) == [1, True, None], "arr parse")
        _check(
            audit.parse_strict_json_text('{"n":' + str((1 << oracle.MAX_JSON_INT_BITS) - 1) + "}", "maxb")["n"] > 0,
            "exact 4000-bit int",
        )
        _check(
            audit.parse_strict_json_text('{"n":-' + str((1 << oracle.MAX_JSON_INT_BITS) - 1) + "}", "negd")["n"] < 0,
            "exact negative max-digit/max-bit int",
        )
        _expect_err(lambda: audit.parse_strict_json_text(123, "x"), "INVALID_JSON_TEXT", "non-str")
        _expect_err(lambda: audit.parse_strict_json_text("{}", "x", require_object=1), "INVALID_BOOL_TYPE", "non-bool")
        _expect_err(lambda: audit.parse_strict_json_text("\ufeff{}", "x"), "BOM_FORBIDDEN", "BOM text")
        _expect_err(lambda: audit.parse_strict_json_text("{\x00}", "x"), "NUL_BYTE_FORBIDDEN", "NUL text")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":"\ud800"}', "x"), "INVALID_UTF8_SURROGATE", "raw surrogate")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":"\\ud800"}', "x"), "INVALID_UTF8_SURROGATE", "escaped surrogate")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":"x\\u0000y"}', "x"), "NUL_BYTE_FORBIDDEN", "escaped NUL")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":1,"a":2}', "x"), "DUPLICATE_JSON_KEY", "dup key")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":NaN}', "x"), "NONFINITE_JSON", "NaN")
        _expect_err(lambda: audit.parse_strict_json_text('{"a":1.5}', "x"), "FLOAT_FORBIDDEN", "float")
        _expect_err(lambda: audit.parse_strict_json_text('{"n":' + "9" * (audit.MAX_JSON_INT_DIGITS + 1) + "}", "x"), "INT_DIGIT_LIMIT", "digit cap")
        _expect_err(lambda: audit.parse_strict_json_text('{"n":' + "9" * audit.MAX_JSON_INT_DIGITS + "}", "x"), "INT_BIT_LIMIT", "1205-digit > 4000-bit")
        _check(audit._parse_bounded_int("0") == 0 and audit._parse_bounded_int("-5") == -5 and audit._parse_bounded_int("10") == 10, "valid ASCII ints")
        for bad_tok in (12, _StrSub("5"), "", "-", "١٢", "-١٢", "²", "+12", "1_2", "-0", "00", "007", "-01"):
            _expect_err(lambda t=bad_tok: audit._parse_bounded_int(t), "INVALID_JSON_INT", f"bad int token {bad_tok!r}")
        _expect_err(lambda: audit.parse_strict_json_text("[1]", "x", require_object=True), "JSON_ROOT_NOT_OBJECT", "list root")
        _expect_err(lambda: audit.parse_strict_json_text("{bad", "x"), "INVALID_JSON", "syntax error")
        _expect_err(lambda: audit._validate_json_tree({1: "x"}, "k"), "INVALID_JSON_KEY", "int key")
        _expect_err(lambda: audit._validate_json_tree({"n": 1 << oracle.MAX_JSON_INT_BITS}, "b"), "INT_BIT_LIMIT", "4001-bit int")
        _expect_err(lambda: audit._validate_json_tree({"f": 3 / 2}, "f"), "INVALID_JSON_VALUE", "float in tree")
        _expect_err(lambda: audit.canonical_json_bytes({"f": 3 / 2}), "INVALID_JSON_VALUE", "float in canonical_json_bytes")
        _expect_err(lambda: audit.canonical_json_bytes({"n": 1 << oracle.MAX_JSON_INT_BITS}), "INT_BIT_LIMIT", "big int in canonical_json_bytes")
        cyc: dict[str, Any] = {}
        cyc["self"] = cyc
        _expect_err(lambda: audit.canonical_json_bytes(cyc), "MAX_DEPTH_EXCEEDED", "cyclic dict in canonical_json_bytes")

        ok_d: Any = 1
        for _ in range(audit.MAX_JSON_DEPTH - 1):
            ok_d = [ok_d]
        _check(type(audit.parse_strict_json_text(json.dumps({"x": ok_d}), "d64")) is dict, "depth 64 failed")
        _expect_err(lambda: audit.parse_strict_json_text(json.dumps({"x": [ok_d]}), "d65"), "MAX_DEPTH_EXCEEDED", "depth 65")

        # /proc/kallsyms st_size==0 capped read + read-only /dev/null guard (write refusal uses scratch FIFO below)
        proc_kallsyms = Path("/proc/kallsyms")
        if proc_kallsyms.exists():
            _expect_err(lambda: audit.read_regular_bytes_capped(proc_kallsyms, "kallsyms", max_bytes=16), "FILE_TOO_LARGE", "kallsyms cap")
        dev_null = Path("/dev/null")
        if dev_null.exists():
            _expect_err(lambda: audit.read_regular_bytes_capped(dev_null, "devnull"), "NOT_A_REGULAR_FILE", "devnull read")

        with tempfile.TemporaryDirectory(prefix="s29_zb_") as td:
            root = Path(td)
            cfile = root / "c.json"
            audit.write_regular_bytes_safe(cfile, cert_bytes, "c")
            _check(stat.S_IMODE(os.lstat(cfile).st_mode) == 0o600, "written file mode must be 0o600")
            audit.write_regular_bytes_safe(cfile, b"{}\n", "c_short")
            _check(cfile.read_bytes() == b"{}\n", "atomic replace shorter failed")
            audit.write_regular_bytes_safe(cfile, cert_bytes, "c_restore")

            # Live pre-replace fstat(fd).st_nlink == 1 probe via os.fsync hook + EEXIST retry/exhaustion
            probe_dir = root / "tmp_probe"
            probe_dir.mkdir()
            probe_tgt = probe_dir / "t.json"
            probe_hl = probe_dir / "evil_link"
            orig_fsync = os.fsync
            linked_tmp = False

            def _hijack_fsync(fd_arg: int) -> None:
                nonlocal linked_tmp
                if not linked_tmp:
                    for name in os.listdir(probe_dir):
                        if ".s29_tmp_" in name:
                            os.link(probe_dir / name, probe_hl)
                            linked_tmp = True
                            break
                orig_fsync(fd_arg)

            os.fsync = _hijack_fsync  # type: ignore[assignment]
            try:
                _expect_err(lambda: audit.write_regular_bytes_safe(probe_tgt, b"{}\n", "hl_tmp"), "HARDLINK_FORBIDDEN", "pre-replace tmp hardlink")
            finally:
                os.fsync = orig_fsync  # type: ignore[assignment]
            _check(linked_tmp and not probe_tgt.exists(), "tmp hardlink probe did not fire cleanly")
            _check([n for n in os.listdir(probe_dir) if ".s29_tmp_" in n] == [], "tmp hardlink leaked temp")

            eexist_dir = root / "eexist"
            eexist_dir.mkdir()
            orig_open = os.open
            ee_state = {"left": 1}

            def _flaky_open(path_arg, flags, mode=0o777, *, dir_fd=None):
                if isinstance(path_arg, str) and ".s29_tmp_" in path_arg and ee_state["left"] > 0:
                    ee_state["left"] -= 1
                    raise FileExistsError("simulated temp collision")
                return orig_open(path_arg, flags, mode, dir_fd=dir_fd)

            os.open = _flaky_open  # type: ignore[assignment]
            try:
                audit.write_regular_bytes_safe(eexist_dir / "ok.json", b"ok\n", "ee_ok")
                ee_state["left"] = 40
                _expect_err(lambda: audit.write_regular_bytes_safe(eexist_dir / "fail.json", b"x\n", "ee_fail"), "TEMP_EXHAUSTED", "32-retry EEXIST exhausted")
            finally:
                os.open = orig_open  # type: ignore[assignment]
            _check((eexist_dir / "ok.json").read_bytes() == b"ok\n", "EEXIST retry failed")
            nested = root / "nested_a" / "sub_b" / "w.json"
            audit.write_regular_bytes_safe(nested, cert_bytes, "nested")
            _check(nested.read_bytes() == cert_bytes, "nested dir_fd create failed")
            _check(audit.read_regular_bytes_capped(cfile, "c", max_bytes=len(cert_bytes)) == cert_bytes, "exact max_bytes")
            _check(audit.read_regular_bytes_capped(cfile, "c_cap", max_bytes=audit.MAX_READ_CAP_BYTES) == cert_bytes, "max cap read")
            _expect_err(lambda: audit.read_regular_bytes_capped(cfile, "c", max_bytes=len(cert_bytes) - 1), "FILE_TOO_LARGE", "max_bytes-1")
            _expect_err(lambda: audit.read_regular_bytes_capped(cfile, "huge1", max_bytes=1 << 100), "INT_OUT_OF_RANGE", "max_bytes 1<<100")
            _expect_err(lambda: audit.read_regular_bytes_capped(cfile, "huge2", max_bytes=10**18), "INT_OUT_OF_RANGE", "max_bytes 10^18")
            _expect_err(lambda: audit.read_regular_bytes_capped(cfile, "over", max_bytes=audit.MAX_READ_CAP_BYTES + 1), "INT_OUT_OF_RANGE", "max_bytes over cap")
            _expect_err(lambda: audit.write_regular_bytes_safe(cfile, "not_bytes", "nb"), "INVALID_PAYLOAD_TYPE", "str write payload")
            _expect_err(lambda: audit.write_regular_bytes_safe(cfile, bytearray(b"{}"), "ba"), "INVALID_PAYLOAD_TYPE", "bytearray write payload")
            _check(cfile.read_bytes() == cert_bytes, "bad payload write altered target")
            hollow_f = root / "hollow.json"
            hollow_f.write_bytes(
                audit.canonical_json_bytes(
                    {
                        "schema_version": "1.0.0",
                        "track_id": "TRACK-S29-AUDIT-129",
                        "payload_sha256": "0" * 64,
                        "certificate_sha256": "0" * 64,
                        "payload": {},
                    }
                )
            )
            hbuf = io.StringIO()
            with redirect_stderr(hbuf):
                rc_h = audit.main(["--check", str(hollow_f)])
            _check(rc_h == 2 and "PAYLOAD_SHA_MISMATCH" in hbuf.getvalue(), f"hollow CLI check: rc={rc_h} err={hbuf.getvalue()!r}")
            zden_f = root / "zden_resigned.json"
            zden_f.write_bytes(audit.canonical_json_bytes(_resign(c_zden)))
            zbuf = io.StringIO()
            with redirect_stderr(zbuf):
                rc_z = audit.main(["--check", str(zden_f)])
            _check(rc_z == 2 and "ALGEBRAIC_IDENTITY_FAILED" in zbuf.getvalue(), f"zero-denom CLI check: rc={rc_z} err={zbuf.getvalue()!r}")

            hlink = root / "hlink.json"
            os.link(cfile, hlink)
            try:
                _expect_err(lambda: audit.write_regular_bytes_safe(hlink, b"tamper", "hlink"), "HARDLINK_FORBIDDEN", "hardlink write")
                _check(cfile.read_bytes() == cert_bytes, "hardlink refusal altered target")
            finally:
                hlink.unlink()

            _expect_err(lambda: audit.read_regular_bytes_capped(_EvilPath(cfile), "evil"), "INVALID_PATH_TYPE", "EvilPath")
            _expect_err(lambda: audit.read_regular_bytes_capped(str(cfile), "str"), "INVALID_PATH_TYPE", "str path")
            _expect_err(lambda: audit.read_regular_bytes_capped(Path("a\x00b.json"), "nul"), "NUL_BYTE_FORBIDDEN", "NUL path")
            _expect_err(lambda: audit.read_regular_bytes_capped(Path("bad_\ud800.json"), "surr"), "INVALID_UTF8_SURROGATE", "surrogate read")
            _expect_err(lambda: audit.write_regular_bytes_safe(Path("bad_\ud800.json"), cert_bytes, "surr"), "INVALID_UTF8_SURROGATE", "surrogate write")
            _expect_err(lambda: audit.read_regular_bytes_capped(Path("/"), "root"), "NOT_A_REGULAR_FILE", "root path")
            _expect_err(lambda: audit.read_regular_bytes_capped(root / "sub" / "..", "dotdot"), "NOT_A_REGULAR_FILE", "dotdot leaf")
            _expect_err(lambda: audit.read_regular_bytes_capped(root / "no_dir" / "x.json", "nodir"), "FILE_READ_ERROR", "missing dir")
            _check(not (root / "no_dir").exists(), "read must not create dir")
            _expect_err(lambda: audit.read_regular_bytes_capped(cfile / "child.json", "nondir"), "FILE_READ_ERROR", "non-dir ancestor")
            _expect_err(lambda: audit.read_regular_bytes_capped(root / "missing.json", "missing"), "FILE_READ_ERROR", "missing file")

            adir = root / "adir"
            adir.mkdir()
            _expect_err(lambda: audit.read_regular_bytes_capped(adir, "adir"), "NOT_A_REGULAR_FILE", "dir read")
            _expect_err(lambda: audit.write_regular_bytes_safe(adir, cert_bytes, "adir"), "NOT_A_REGULAR_FILE", "dir write")
            if hasattr(os, "mkfifo"):
                fifo = root / "pipe.json"
                os.mkfifo(fifo)
                _expect_err(lambda: audit.read_regular_bytes_capped(fifo, "fifo"), "NOT_A_REGULAR_FILE", "FIFO read")
                _expect_err(lambda: audit.write_regular_bytes_safe(fifo, cert_bytes, "fifo"), "NOT_A_REGULAR_FILE", "FIFO write")

            no_perm = root / "noperm.json"
            no_perm.write_bytes(cert_bytes)
            os.chmod(no_perm, 0o000)
            try:
                if os.geteuid() != 0:
                    _expect_err(lambda: audit.read_regular_bytes_capped(no_perm, "noperm"), "FILE_READ_ERROR", "chmod 000")
            finally:
                os.chmod(no_perm, 0o600)

            ro_dir = root / "ro_dir"
            ro_dir.mkdir()
            os.chmod(ro_dir, 0o500)
            try:
                if os.geteuid() != 0:
                    _expect_err(lambda: audit.write_regular_bytes_safe(ro_dir / "x.json", cert_bytes, "ro"), "FILE_WRITE_ERROR", "ro write")
                    _expect_err(lambda: audit.write_regular_bytes_safe(ro_dir / "nd" / "x.json", cert_bytes, "ro_mk"), "FILE_WRITE_ERROR", "ro mkdir")
            finally:
                os.chmod(ro_dir, 0o700)

            sym = root / "sym.json"
            os.symlink(cfile, sym)
            _expect_err(lambda: audit.verify_certificate_file(sym), "SYMLINK_FORBIDDEN", "symlink read")
            _expect_err(lambda: audit.write_regular_bytes_safe(sym, cert_bytes, "sym_w"), "SYMLINK_FORBIDDEN", "symlink write")
            real_sub = root / "real_sub" / "nested"
            real_sub.mkdir(parents=True)
            (real_sub / "c.json").write_bytes(cert_bytes)
            sym_dir = root / "sym_dir"
            os.symlink(root / "real_sub", sym_dir)
            _expect_err(lambda: audit.verify_certificate_file(sym_dir / "nested" / "c.json"), "SYMLINK_FORBIDDEN", "deep symlink")
            _expect_err(lambda: audit.write_regular_bytes_safe(sym_dir / "nested" / "w.json", cert_bytes, "sym_dir_w"), "SYMLINK_FORBIDDEN", "write under symlink dir")
            _expect_err(lambda: audit.verify_certificate_file(sym_dir / ".." / "real_sub" / "nested" / "c.json"), "SYMLINK_FORBIDDEN", "dotdot symlink")

            bom_f = root / "bom.json"
            bom_f.write_bytes(b"\xef\xbb\xbf" + cert_bytes)
            _expect_err(lambda: audit.verify_certificate_file(bom_f), "BOM_FORBIDDEN", "BOM file")
            bad_u8 = root / "bad_u8.json"
            bad_u8.write_bytes(b"\xff\xfe")
            _expect_err(lambda: audit.verify_certificate_file(bad_u8), "INVALID_UTF8", "bad utf8")
            crlf_f = root / "crlf.json"
            crlf_f.write_bytes(cert_bytes.replace(b"\n", b"\r\n"))
            _expect_err(lambda: audit.verify_certificate_file(crlf_f), "CRLF_FORBIDDEN", "CRLF")
            pretty_f = root / "pretty.json"
            pretty_f.write_text(json.dumps(cert, indent=2, sort_keys=True) + "\n", encoding="utf-8")
            _expect_err(lambda: audit.verify_certificate_file(pretty_f), "CERTIFICATE_BYTE_MISMATCH", "pretty JSON")

            orig_cwd = os.getcwd()
            orig_pwd = os.environ.get("PWD")
            try:
                os.chdir(real_sub)
                os.symlink(real_sub, real_sub / "local_sym")
                os.environ["PWD"] = str(sym_dir / "nested")
                _expect_err(lambda: audit.verify_certificate_file(Path("c.json")), "SYMLINK_ANCESTOR_FORBIDDEN", "symlink PWD")
                os.environ["PWD"] = "/tmp/bad_\udcff_pwd"
                _expect_err(lambda: audit.read_regular_bytes_capped(Path("c.json"), "spwd"), "INVALID_UTF8_SURROGATE", "surrogate PWD")
                os.environ["PWD"] = "rel/" + str(sym_dir).lstrip("/")
                _check(audit.read_regular_bytes_capped(Path(".") / "c.json", "relpwd") == cert_bytes, "relative PWD")
                os.environ["PWD"] = str(real_sub)
                _check(audit.read_regular_bytes_capped(Path("c.json"), "realpwd") == cert_bytes, "real PWD")
                os.environ.pop("PWD", None)
                _check(audit.read_regular_bytes_capped(Path("c.json"), "nopwd") == cert_bytes, "unset PWD")

                out_path = root / "written.json"
                orig_build = audit.build_certificate
                audit.build_certificate = lambda: self.live_cert  # type: ignore[assignment]
                try:
                    _check(audit.main(["--write", str(out_path)]) == 0 and out_path.read_bytes() == cert_bytes, "CLI --write")
                    buf = io.StringIO()
                    with redirect_stdout(buf):
                        rc_c = audit.main(["--check", str(out_path)])
                    _check(rc_c == 0 and json.loads(buf.getvalue())["valid"] is True, "CLI --check")
                    orig_stdout = sys.stdout
                    for cli_argv in ([], ["--standalone", "--json"]):
                        b_raw = io.BytesIO()
                        b_wrap = io.TextIOWrapper(b_raw, encoding="utf-8")
                        sys.stdout = b_wrap
                        try:
                            rc_s = audit.main(cli_argv)
                            b_wrap.flush()
                        finally:
                            sys.stdout = orig_stdout
                        _check(rc_s == 0 and b_raw.getvalue() == cert_bytes, f"CLI {cli_argv!r} mismatch")
                finally:
                    audit.build_certificate = orig_build  # type: ignore[assignment]

                for bad_argv, exp_code in (
                    (("--standalone", "--json"), "INVALID_ARGV"),
                    ("--check", "INVALID_ARGV"),
                    ([123], "INVALID_ARGV"),
                    ([_StrSub("--check"), str(out_path)], "INVALID_ARGV"),
                    (["--standalone\x00", "--json"], "NUL_BYTE_FORBIDDEN"),
                    (["--check", "\ud800"], "INVALID_UTF8_SURROGATE"),
                    (["--write", ""], "INVALID_PATH_ARG"),
                    (["--check", ""], "INVALID_PATH_ARG"),
                    (["--write", "--json"], "INVALID_PATH_ARG"),
                    (["--check", "--json"], "INVALID_PATH_ARG"),
                    (["--check", "--help"], "INVALID_PATH_ARG"),
                    (["--write", "-"], "INVALID_PATH_ARG"),
                    (["--write=--json"], "INVALID_CLI_ARGS"),
                    (["--check=--json"], "INVALID_CLI_ARGS"),
                    (["--write"], "INVALID_CLI_ARGS"),
                    (["--check"], "INVALID_CLI_ARGS"),
                    (["--unknown", "x"], "INVALID_CLI_ARGS"),
                ):
                    ebuf = io.StringIO()
                    with redirect_stderr(ebuf):
                        rc_b = audit.main(bad_argv)
                    _check(rc_b == 2 and exp_code in ebuf.getvalue(), f"bad argv {bad_argv!r}: rc={rc_b} err={ebuf.getvalue()!r}")
                _check(not (real_sub / "--json").exists(), "--write --json created ./--json")

                gone = root / "gone_cwd"
                gone.mkdir()
                os.chdir(gone)
                os.rmdir(gone)
                _expect_err(lambda: audit.read_regular_bytes_capped(Path("r.json"), "r"), "CWD_UNAVAILABLE", "deleted CWD read")
                _expect_err(lambda: audit.write_regular_bytes_safe(Path("w.json"), cert_bytes, "w"), "CWD_UNAVAILABLE", "deleted CWD write")
                for g_argv in (["--check", "r.json"], ["--write", "w.json"]):
                    gbuf = io.StringIO()
                    with redirect_stderr(gbuf):
                        rc_g = audit.main(g_argv)
                    _check(rc_g == 2 and "CWD_UNAVAILABLE" in gbuf.getvalue(), f"deleted CWD CLI {g_argv}")
            finally:
                os.chdir(orig_cwd)
                if orig_pwd is None:
                    os.environ.pop("PWD", None)
                else:
                    os.environ["PWD"] = orig_pwd

            p_pwd = subprocess.run(
                [sys.executable, "-I", "-O", "-B", str(ROOT / "tao_exact_operators_audit.py"), "--check", "c.json"],
                cwd=str(real_sub),
                env={**os.environ, "PWD": str(sym_dir / "nested")},
                capture_output=True,
                text=True,
                timeout=60,
            )
            _check(p_pwd.returncode == 2 and "SYMLINK_ANCESTOR_FORBIDDEN" in p_pwd.stderr, f"subprocess symlink PWD: {p_pwd.stderr!r}")

    def test_04_live_renameat2_and_hardlink_race_stress(self) -> None:
        libc = ctypes.CDLL(None, use_errno=True)
        renameat2 = libc.renameat2
        renameat2.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
        renameat2.restype = ctypes.c_int

        with tempfile.TemporaryDirectory(prefix="s29_race_") as td:
            root = Path(td)
            canary = root / "canary.txt"
            canary_bytes = b"DO_NOT_LEAK_OR_CLOBBER\n"
            canary.write_bytes(canary_bytes)

            real_dir = root / "real_dir"
            real_dir.mkdir()
            target_a = real_dir / "target.json"
            target_a.write_bytes(b'{"ok":1}\n')
            sym_leaf = root / "sym_leaf.json"
            os.symlink(canary, sym_leaf)
            swap_dir = root / "swap_dir"
            os.symlink(root, swap_dir)

            stop_ev = threading.Event()
            p1_b = os.fsencode(target_a)
            p2_b = os.fsencode(sym_leaf)
            d1_b = os.fsencode(real_dir)
            d2_b = os.fsencode(swap_dir)

            def _flipper() -> None:
                while not stop_ev.is_set():
                    renameat2(_AT_FDCWD, p1_b, _AT_FDCWD, p2_b, _RENAME_EXCHANGE)
                    renameat2(_AT_FDCWD, d1_b, _AT_FDCWD, d2_b, _RENAME_EXCHANGE)

            t = threading.Thread(target=_flipper, daemon=True)
            t.start()
            leaks = 0
            clobbers = 0
            try:
                for _ in range(520):
                    try:
                        got = audit.read_regular_bytes_capped(real_dir / "target.json", "race_r")
                        if b"DO_NOT_LEAK" in got:
                            leaks += 1
                    except oracle.TaoOperatorsError:
                        pass
                    try:
                        audit.write_regular_bytes_safe(real_dir / "target.json", b'{"ok":2}\n', "race_w")
                    except oracle.TaoOperatorsError:
                        pass
                    if canary.read_bytes() != canary_bytes:
                        clobbers += 1
            finally:
                stop_ev.set()
                t.join(timeout=5)
            _check(leaks == 0 and clobbers == 0, f"renameat2 race failed: leaks={leaks}, clobbers={clobbers}")

            hl_dir = root / "hl_dir"
            hl_dir.mkdir()
            hl_target = hl_dir / "cert.json"
            hl_alias = hl_dir / "alias.json"
            hl_target.write_bytes(b'{"orig":true}\n')

            stop_hl = threading.Event()

            def _linker() -> None:
                while not stop_hl.is_set():
                    try:
                        os.link(hl_target, hl_alias)
                    except OSError:
                        pass
                    try:
                        os.unlink(hl_alias)
                    except OSError:
                        pass

            t_hl = threading.Thread(target=_linker, daemon=True)
            t_hl.start()
            hl_clobbers = 0
            try:
                for i in range(420):
                    try:
                        audit.write_regular_bytes_safe(hl_target, f'{{"iter":{i}}}\n'.encode("ascii"), "hl_w")
                    except oracle.TaoOperatorsError:
                        pass
                    try:
                        if not hl_alias.read_bytes().endswith(b"}\n"):
                            hl_clobbers += 1
                    except OSError:
                        pass
            finally:
                stop_hl.set()
                t_hl.join(timeout=5)
            _check(hl_clobbers == 0, f"hardlink clobbers={hl_clobbers}")
            leftovers = [p.name for p in hl_dir.iterdir() if ".s29_tmp_" in p.name]
            _check(len(leftovers) == 0, f"leftover temps: {leftovers}")

            # 16T distinct, 16T same-target, and 80T barrier burst concurrent atomic writes (0o600, 0 errs, 0 temps)
            conc_dir = root / "conc"
            conc_dir.mkdir()
            conc_errs: list[BaseException] = []

            def _w_dist(idx: int) -> None:
                try:
                    for j in range(4):
                        audit.write_regular_bytes_safe(conc_dir / f"d_{idx}.json", f"{idx}:{j}\n".encode("ascii"), "c_d")
                except BaseException as exc:
                    conc_errs.append(exc)

            ts = [threading.Thread(target=_w_dist, args=(i,)) for i in range(16)]
            for th in ts:
                th.start()
            for th in ts:
                th.join()
            _check(conc_errs == [], f"16T distinct errs: {conc_errs}")
            for i in range(16):
                _check(stat.S_IMODE(os.lstat(conc_dir / f"d_{i}.json").st_mode) == 0o600, "16T distinct mode != 0o600")

            same_f = conc_dir / "same.json"
            def _w_same(idx: int) -> None:
                try:
                    for j in range(4):
                        audit.write_regular_bytes_safe(same_f, f"s:{idx}:{j}\n".encode("ascii"), "c_s")
                except BaseException as exc:
                    conc_errs.append(exc)

            ts = [threading.Thread(target=_w_same, args=(i,)) for i in range(16)]
            for th in ts:
                th.start()
            for th in ts:
                th.join()
            _check(conc_errs == [], f"16T same errs: {conc_errs}")
            _check(stat.S_IMODE(os.lstat(same_f).st_mode) == 0o600, "16T same mode != 0o600")

            bar = threading.Barrier(80)
            burst_f = conc_dir / "burst.json"
            def _w_burst(idx: int) -> None:
                try:
                    bar.wait()
                    audit.write_regular_bytes_safe(burst_f, f"b:{idx}\n".encode("ascii"), "c_b")
                except BaseException as exc:
                    conc_errs.append(exc)

            ts = [threading.Thread(target=_w_burst, args=(i,)) for i in range(80)]
            for th in ts:
                th.start()
            for th in ts:
                th.join()
            _check(conc_errs == [], f"80T burst errs: {conc_errs}")
            _check([p.name for p in conc_dir.iterdir() if ".s29_tmp_" in p.name] == [], "conc leftover temps")


if __name__ == "__main__":
    unittest.main()
