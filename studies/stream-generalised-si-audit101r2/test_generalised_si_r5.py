#!/usr/bin/env python3
"""R5 mutation-killing & sub-condition test suite for generalised_si_certifier.py (AUDIT-101).

Zero bare asserts. Covers every fail-closed guard, boundary, and individual boolean
sub-condition across all pure-Z/Q verifiers plus offline standalone execution.
"""
from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import generalised_si_certifier as gsi


def _assert_no_floats(tc: unittest.TestCase, obj: object) -> None:
    if isinstance(obj, float):
        tc.fail(f"Forbidden float: {obj!r}")
    if isinstance(obj, dict):
        for k, v in obj.items():
            _assert_no_floats(tc, k)
            _assert_no_floats(tc, v)
    elif isinstance(obj, (list, tuple)):
        for item in obj:
            _assert_no_floats(tc, item)


class TestGeneralisedSiCertifierR5(unittest.TestCase):
    def test_01_helpers_and_cw_verifiers(self) -> None:
        self.assertEqual(gsi._fmt_q(Fraction(4, 1)), "4")
        self.assertEqual(gsi._fmt_q(Fraction(3, 7)), "3/7")
        with self.assertRaisesRegex(ValueError, "FLOAT_FORBIDDEN"):
            gsi._verify_no_floats({"a": [1, (0.25,)]})

        # Valid proper CW(7, 4) and improper CW(14, 4) (lifted by factor 2 -> gcd=2)
        ok = gsi.verify_circulant_weighing_matrix(7, 4, [1, 2, 4], [0])
        self.assertTrue(ok["proper"])
        self.assertEqual(ok["row_sum"], 2)
        improp = gsi.verify_circulant_weighing_matrix(14, 4, [2, 4, 8], [0], require_proper=False)
        self.assertFalse(improp["proper"])
        self.assertEqual(improp["support_gcd"], 2)

        for args, kw, code in (
            (("7", 4, [1, 2, 4], [0]), {}, "CW_INVALID_ORDER"),
            ((1, 1, [0], []), {}, "CW_INVALID_ORDER"),
            ((7, True, [1, 2, 4], [0]), {}, "CW_INVALID_WEIGHT"),
            ((7, 0, [], []), {}, "CW_INVALID_WEIGHT"),
            ((7, 8, [1, 2, 4], [0]), {}, "CW_INVALID_WEIGHT"),
            ((7, 4, (1, 2, 4), [0]), {}, "CW_SUPPORT_NOT_LIST"),
            ((7, 4, [1, 2, 4], (0,)), {}, "CW_SUPPORT_NOT_LIST"),
            ((7, 4, [1, 2, 4], [0]), {"require_proper": 1}, "CW_INVALID_PROPER_FLAG"),
            ((7, 4, [True, 2, 4], [0]), {}, "CW_INVALID_POS_INDEX"),
            ((7, 4, [-1, 2, 4], [0]), {}, "CW_INVALID_POS_INDEX"),
            ((7, 4, [7, 2, 4], [0]), {}, "CW_INVALID_POS_INDEX"),
            ((7, 4, [1, 2, 4], [True]), {}, "CW_INVALID_NEG_INDEX"),
            ((7, 4, [1, 2, 4], [-1]), {}, "CW_INVALID_NEG_INDEX"),
            ((7, 4, [1, 2, 4], [7]), {}, "CW_INVALID_NEG_INDEX"),
            ((7, 4, [1, 1, 4], [0]), {}, "CW_DUPLICATE_INDEX"),
            ((7, 4, [1, 2], [0, 0]), {}, "CW_DUPLICATE_INDEX"),
            ((7, 4, [0, 2, 4], [0]), {}, "CW_OVERLAPPING_SUPPORTS"),
            ((7, 4, [1, 2], [0]), {}, "CW_WEIGHT_MISMATCH"),
            ((7, 4, [1, 2, 3], [0]), {}, "CW_NONZERO_PAF_AT_"),
            ((14, 4, [2, 4, 8], [0]), {"require_proper": True}, "CW_NOT_PROPER"),
        ):
            with self.assertRaisesRegex(ValueError, code):
                gsi.verify_circulant_weighing_matrix(*args, **kw)  # type: ignore[arg-type]

        # Orbit inequivalence (shifted/negated duplicate rejected!)
        c_ok = gsi.verify_cw_class_set_inequivalent(7, 4, [{"P": [1, 2, 4], "N": [0]}])
        self.assertEqual(c_ok["distinct_orbits"], 1)
        for bad_cls, code in (
            ("not-list", "CW_CLASSES_EMPTY_OR_NOT_LIST"),
            ([], "CW_CLASSES_EMPTY_OR_NOT_LIST"),
            (["not-dict"], "CW_CLASS_SCHEMA_MISMATCH"),
            ([{"P": [1]}], "CW_CLASS_SCHEMA_MISMATCH"),
            ([{"P": [1, 2, 4], "N": [0]}, {"P": [2, 3, 5], "N": [1]}], "CW_EQUIVALENT_DUPLICATE_CLASS"),
        ):
            with self.assertRaisesRegex(ValueError, code):
                gsi.verify_cw_class_set_inequivalent(7, 4, bad_cls)  # type: ignore[arg-type]

        # Sparse weighing-matrix siliquant rotation witness (exact pure-Q 1-hot & 2-hot + fail-closed guards)
        rot1 = gsi.verify_weighing_matrix_siliquant_rotation(7, 4, [1, 2, 4], [0], [10, 0, 0, 0, 0, 0, 0])
        self.assertTrue(rot1["energy_conserved"])
        self.assertTrue(rot1["cauchy_schwarz_bound_holds"])
        self.assertEqual(rot1["y_norm_sq"], 400)
        self.assertEqual(rot1["actual_peak_sq_ratio"], "1/4")
        self.assertEqual(rot1["t_sparse_cauchy_schwarz_bound"], "1/4")
        self.assertEqual(rot1["signed_add_density"], "4/7")
        self.assertEqual(rot1["dense_op_reduction_factor"], "7/4")

        rot2 = gsi.verify_weighing_matrix_siliquant_rotation(7, 4, [1, 2, 4], [0], [10, 3, 0, 0, 0, 0, 0])
        self.assertTrue(rot2["energy_conserved"])
        self.assertTrue(rot2["cauchy_schwarz_bound_holds"])
        self.assertEqual(rot2["input_support_size"], 2)
        self.assertEqual(rot2["y_norm_sq"], 436)
        self.assertEqual(rot2["actual_peak_sq_ratio"], "169/436")
        self.assertEqual(rot2["t_sparse_cauchy_schwarz_bound"], "1/2")

        for bad_vec, code in (
            ((10, 0, 0, 0, 0, 0, 0), "WROT_INVALID_INPUT_VEC"),
            ([10, 0, 0, 0, 0, 0], "WROT_INVALID_INPUT_VEC"),
            ([True, 0, 0, 0, 0, 0, 0], "WROT_INPUT_NON_INT"),
            ([0, 0, 0, 0, 0, 0, 0], "WROT_ZERO_INPUT_VEC"),
        ):
            with self.assertRaisesRegex(ValueError, code):
                gsi.verify_weighing_matrix_siliquant_rotation(7, 4, [1, 2, 4], [0], bad_vec)  # type: ignore[arg-type]

    def test_02_good_williamson_tmatrix_and_bordered_wt(self) -> None:
        g3 = gsi.verify_good_or_williamson_quadruple(3, [0, 0, 1, 1], first_skew=True)
        self.assertEqual(g3["hadamard_order"], 12)
        w3 = gsi.verify_good_or_williamson_quadruple(3, [0, 1, 1, 1], first_skew=False)
        self.assertEqual(w3["kind"], "williamson_matrices")

        for args, kw, code in (
            (("3", [0, 0, 1, 1]), {}, "GW_INVALID_ODD_ORDER"),
            ((1, [0, 0, 1, 1]), {}, "GW_INVALID_ODD_ORDER"),
            ((4, [0, 0, 1, 1]), {}, "GW_INVALID_ODD_ORDER"),
            ((3, (0, 0, 1, 1)), {}, "GW_WORDS_NOT_FOUR"),
            ((3, [0, 0, 1]), {}, "GW_WORDS_NOT_FOUR"),
            ((3, [0, 0, 1, 1]), {"first_skew": 1}, "GW_INVALID_SKEW_FLAG"),
            ((3, [True, 0, 1, 1]), {}, "GW_WORD_OUT_OF_RANGE"),
            ((3, [-1, 0, 1, 1]), {}, "GW_WORD_OUT_OF_RANGE"),
            ((3, [2, 0, 1, 1]), {}, "GW_WORD_OUT_OF_RANGE"),
            ((3, [0, 0, 0, 0]), {"first_skew": True}, "GW_NONZERO_PAF_AT_"),
        ):
            with self.assertRaisesRegex(ValueError, code):
                gsi.verify_good_or_williamson_quadruple(*args, **kw)  # type: ignore[arg-type]

        t1 = gsi.verify_t_matrix_quadruple(1, ["+", "0", "0", "0"])
        self.assertEqual(t1["od_order"], 4)
        t3 = gsi.verify_t_matrix_quadruple(3, ["+00", "0+0", "00+", "000"])
        self.assertEqual(t3["od_order"], 12)
        for args, code in (
            ((True, ["+00", "0+0", "00+", "000"]), "TMAT_INVALID_ORDER"),
            ((0, ["", "", "", ""]), "TMAT_INVALID_ORDER"),
            ((3, ("+00", "0+0", "00+", "000")), "TMAT_ROWS_NOT_FOUR"),
            ((3, ["+00", "0+0", "00+"]), "TMAT_ROWS_NOT_FOUR"),
            ((3, [123, "0+0", "00+", "000"]), "TMAT_INVALID_ROW_LEN"),
            ((3, ["+0", "0+0", "00+", "000"]), "TMAT_INVALID_ROW_LEN"),
            ((3, ["+0x", "0+0", "00+", "000"]), "TMAT_INVALID_ENTRY_CHAR"),
            ((3, ["++0", "0+0", "00+", "000"]), "TMAT_PARTITION_VIOLATION_AT_"),
            ((3, ["+++", "000", "000", "000"]), "TMAT_NONZERO_PAF_AT_"),
        ):
            with self.assertRaisesRegex(ValueError, code):
                gsi.verify_t_matrix_quadruple(*args)  # type: ignore[arg-type]

        bwt = gsi.verify_bordered_williamson_type(5, ["+++-", "++--", "+-+-", "+--+"], [2, 0, 0, 0])
        self.assertEqual(bwt["core_offdiag_paf_sum"], -4)
        for args, code in (
            (("5", ["+++-", "++--", "+-+-", "+--+"], [2, 0, 0, 0]), "BWT_INVALID_ORDER"),
            ((1, ["", "", "", ""], [0, 0, 0, 0]), "BWT_INVALID_ORDER"),
            ((4, ["+++", "++-", "+--", "---"], [3, 1, -1, -3]), "BWT_INVALID_ORDER"),
            ((5, ("+++-", "++--", "+-+-", "+--+"), [2, 0, 0, 0]), "BWT_SEQUENCES_NOT_FOUR"),
            ((5, ["+++-", "++--", "+-+-"], [2, 0, 0, 0]), "BWT_SEQUENCES_NOT_FOUR"),
            ((5, ["+++-", "++--", "+-+-", "+--+"], (2, 0, 0, 0)), "BWT_ROWSUMS_NOT_FOUR"),
            ((5, ["+++-", "++--", "+-+-", "+--+"], [2, 0, 0]), "BWT_ROWSUMS_NOT_FOUR"),
            ((5, ["+++-", "++--", "+-+-", "+--+"], [True, 0, 0, 0]), "BWT_INVALID_ROWSUM_INT"),
            ((5, [123, "++--", "+-+-", "+--+"], [2, 0, 0, 0]), "BWT_INVALID_SEQ_LEN"),
            ((5, ["+++", "++--", "+-+-", "+--+"], [2, 0, 0, 0]), "BWT_INVALID_SEQ_LEN"),
            ((5, ["+++0", "++--", "+-+-", "+--+"], [2, 0, 0, 0]), "BWT_INVALID_SEQ_CHAR"),
            ((5, ["+++-", "++--", "+-+-", "+--+"], [0, 0, 0, 0]), "BWT_ROWSUM_MISMATCH"),
            ((5, ["++++", "++++", "++++", "++++"], [4, 4, 4, 4]), "BWT_INVALID_CORE_PAF_AT_"),
        ):
            with self.assertRaisesRegex(ValueError, code):
                gsi.verify_bordered_williamson_type(*args)  # type: ignore[arg-type]

    def test_03_rds_projection_and_binary_codes(self) -> None:
        r_ok = gsi.verify_relative_difference_set(4, 2, 3, 1, [0, 1, 3])
        self.assertEqual(r_ok["non_forbidden_diffs_verified"], 6)
        for args, code in (
            (("4", 2, 3, 1, [0, 1, 3]), "RDS_INVALID_V"),
            ((1, 2, 3, 1, [0, 1, 3]), "RDS_INVALID_V"),
            ((4, "2", 3, 1, [0, 1, 3]), "RDS_INVALID_N_KER"),
            ((4, 1, 3, 1, [0, 1, 3]), "RDS_INVALID_N_KER"),
            ((4, 2, "3", 1, [0, 1, 3]), "RDS_INVALID_K"),
            ((4, 2, 1, 1, [0]), "RDS_INVALID_K"),
            ((4, 2, 3, True, [0, 1, 3]), "RDS_INVALID_MU"),
            ((4, 2, 3, 0, [0, 1, 3]), "RDS_INVALID_MU"),
            ((4, 2, 3, 2, [0, 1, 3]), "RDS_COUNTING_IDENTITY_FAILED"),
            ((4, 2, 3, 1, (0, 1, 3)), "RDS_ELEMENT_COUNT_MISMATCH"),
            ((4, 2, 3, 1, [0, 1]), "RDS_ELEMENT_COUNT_MISMATCH"),
            ((4, 2, 3, 1, [True, 1, 3]), "RDS_ELEMENT_OUT_OF_RANGE"),
            ((4, 2, 3, 1, [-1, 1, 3]), "RDS_ELEMENT_OUT_OF_RANGE"),
            ((4, 2, 3, 1, [8, 1, 3]), "RDS_ELEMENT_OUT_OF_RANGE"),
            ((4, 2, 3, 1, [0, 0, 3]), "RDS_DUPLICATE_ELEMENT"),
            ((4, 2, 3, 1, [0, 1, 4]), "RDS_DIFF_MULTIPLICITY_FAILED_AT_"),
        ):
            with self.assertRaisesRegex(ValueError, code):
                gsi.verify_relative_difference_set(*args)  # type: ignore[arg-type]

        p_ok = gsi.verify_cyclic_ds_projection_orbit(5, 2, 4, [-2, 0, 0, 0, 0])
        self.assertEqual(p_ok["sum"], -2)
        for args, code in (
            (("5", 2, 4, [2, 0, 0, 0, 0]), "PROJ_INVALID_P"),
            ((1, 2, 4, [2]), "PROJ_INVALID_P"),
            ((5, True, 4, [2, 0, 0, 0, 0]), "PROJ_INVALID_SUM_TARGET"),
            ((5, -1, 4, [2, 0, 0, 0, 0]), "PROJ_INVALID_SUM_TARGET"),
            ((5, 2, True, [2, 0, 0, 0, 0]), "PROJ_INVALID_SQ_TARGET"),
            ((5, 2, 0, [2, 0, 0, 0, 0]), "PROJ_INVALID_SQ_TARGET"),
            ((5, 2, 4, (2, 0, 0, 0, 0)), "PROJ_VECTOR_LEN_MISMATCH"),
            ((5, 2, 4, [2, 0, 0, 0]), "PROJ_VECTOR_LEN_MISMATCH"),
            ((5, 2, 4, [True, 0, 0, 0, 0]), "PROJ_VECTOR_NON_INT"),
            ((5, 2, 4, [1, 0, 0, 0, 0]), "PROJ_SUM_MISMATCH"),
            ((5, 2, 4, [1, 1, 0, 0, 0]), "PROJ_SQ_SUM_MISMATCH"),
            ((5, 2, 8, [1, 1, 1, 1, -2]), "PROJ_NONZERO_PAF_AT_"),
        ):
            with self.assertRaisesRegex(ValueError, code):
                gsi.verify_cyclic_ds_projection_orbit(*args)  # type: ignore[arg-type]

        c_ok = gsi.verify_binary_linear_code_generator(7, 4, ["47", "2b", "1d", "0e"], 3)
        self.assertEqual(c_ok["gf2_rank"], 4)
        self.assertFalse(c_ok["exhaustive_dmin_proved"])
        for args, code in (
            (("7", 1, ["3"], 1), "CODE_INVALID_N"),
            ((1, 1, ["1"], 1), "CODE_INVALID_N"),
            ((7, True, ["47"], 3), "CODE_INVALID_K"),
            ((7, 0, [], 3), "CODE_INVALID_K"),
            ((7, 8, ["47"] * 8, 3), "CODE_INVALID_K"),
            ((7, 4, ["47", "2b", "1d", "0e"], True), "CODE_INVALID_CLAIMED_D"),
            ((7, 4, ["47", "2b", "1d", "0e"], 0), "CODE_INVALID_CLAIMED_D"),
            ((7, 4, ["47", "2b", "1d", "0e"], 8), "CODE_INVALID_CLAIMED_D"),
            ((7, 4, ("47", "2b", "1d", "0e"), 3), "CODE_ROW_COUNT_MISMATCH"),
            ((7, 4, ["47", "2b", "1d"], 3), "CODE_ROW_COUNT_MISMATCH"),
            ((7, 4, [47, "2b", "1d", "0e"], 3), "CODE_INVALID_HEX_ROW"),
            ((7, 4, ["", "2b", "1d", "0e"], 3), "CODE_INVALID_HEX_ROW"),
            ((7, 4, ["zz", "2b", "1d", "0e"], 3), "CODE_INVALID_HEX_ROW"),
            ((7, 4, ["0", "2b", "1d", "0e"], 3), "CODE_ROW_OUT_OF_RANGE"),
            ((7, 4, ["80", "2b", "1d", "0e"], 3), "CODE_ROW_OUT_OF_RANGE"),
            ((7, 4, ["47", "2b", "1d", "03"], 3), "CODE_GENERATOR_ROW_BELOW_CLAIMED_D"),
            ((7, 4, ["47", "47", "1d", "0e"], 3), "CODE_RANK_DEFICIENT"),
        ):
            with self.assertRaisesRegex(ValueError, code):
                gsi.verify_binary_linear_code_generator(*args)  # type: ignore[arg-type]

    def test_04_ising_cluster_lean_and_standalone(self) -> None:
        # Ising guard coverage (real 4x4x4 verified in live mode; unit tests cover every guard/error!)
        for args, code in (
            (([4, 4, 4], [(0, 2)]), "ISING_INVALID_DIMS"),
            (((4, 4), [(0, 2)]), "ISING_INVALID_DIMS"),
            (((True, 4, 4), [(0, 2)]), "ISING_DIM_BELOW_4"),
            (((3, 4, 4), [(0, 2)]), "ISING_DIM_BELOW_4"),
            (((4, 4, 4), "bad"), "ISING_EMPTY_PAIRS"),
            (((4, 4, 4), []), "ISING_EMPTY_PAIRS"),
            (((4, 4, 4), [[0, 2]]), "ISING_PAIR_SCHEMA"),
            (((4, 4, 4), [(0,)]), "ISING_PAIR_SCHEMA"),
            (((4, 4, 4), [(True, 2)]), "ISING_INVALID_BROKEN_BONDS"),
            (((4, 4, 4), [(-1, 2)]), "ISING_INVALID_BROKEN_BONDS"),
            (((4, 4, 4), [(193, 2)]), "ISING_INVALID_BROKEN_BONDS"),
            (((4, 4, 4), [(0, True)]), "ISING_NONPOSITIVE_COUNT"),
            (((4, 4, 4), [(0, 0)]), "ISING_NONPOSITIVE_COUNT"),
            (((4, 4, 4), [(0, 2), (0, 2)]), "ISING_DUPLICATE_ENERGY_LEVEL"),
            (((4, 4, 4), [(0, 2)]), "ISING_M0_SUM_MISMATCH"),
            (((4, 4, 4), [(0, 4), (192, (1 << 64) - 4)]), "ISING_GROUND_STATE_DEG_MISMATCH"),
            (((4, 4, 4), [(0, 2), (192, (1 << 64) - 2)]), "ISING_ONE_FLIP_DEG_MISMATCH"),
            (((4, 4, 4), [(0, 2), (6, 128), (192, (1 << 64) - 130)]), "ISING_M1_NONZERO"),
            (((4, 4, 4), [(0, 2), (6, 128), (96, (1 << 64) - 260), (186, 128), (192, 2)]), "ISING_M2_MISMATCH"),
        ):
            with self.assertRaisesRegex(ValueError, code):
                gsi.verify_ising_3d_dos_moments(*args)  # type: ignore[arg-type]

        # Test m3, m4, and bipartite-symmetry guards directly on exact-moment synthetic distributions
        import math
        n64 = 64
        e64 = 192
        p2 = 1 << n64
        rem0 = p2 - 130
        rem1 = -(2 * (-192) + 128 * (-180))
        rem2 = e64 * p2 - (2 * (192 ** 2) + 128 * (180 ** 2))
        # E_a = -16 (b=88), E_b = +32 (b=112), E_0 = 0 (b=96): exact positive counts with m1=0, m2=192*p2, m3!=0
        cb = (rem2 + 16 * rem1) // 1536
        ca = 2 * cb - rem1 // 16
        c0 = rem0 - ca - cb
        with self.assertRaisesRegex(ValueError, "ISING_M3_NONZERO"):
            gsi.verify_ising_3d_dos_moments((4, 4, 4), [(0, 2), (6, 128), (88, ca), (96, c0), (112, cb)])

        # Symmetric distribution matching m0, gs, flip, m1=0, m2=192*p2, m3=0, but wrong m4!
        # E = +-16 (b=88, 104): 2 * 256 * cs = rem2_sym -> cs < p2 / 2
        rem2_sym = e64 * p2 - 2 * (2 * (192 ** 2) + 128 * (180 ** 2))
        cs = rem2_sym // 512
        c96 = p2 - 260 - 2 * cs
        with self.assertRaisesRegex(ValueError, "ISING_M4_MISMATCH"):
            gsi.verify_ising_3d_dos_moments((4, 4, 4), [(0, 2), (6, 128), (88, cs), (96, c96), (104, cs), (186, 128), (192, 2)])

        # Match exact m0..m4 on (5,5,4) with a SYMMETRIC distribution (must fail ISING_BIPARTITE_SYMMETRY_MISMATCH!)
        n100 = 100
        e100 = 300
        p2_100 = 1 << n100
        p4_100 = 3 * n100 + 25
        m4_tgt = (e100 * (3 * e100 - 2) + 24 * p4_100) * p2_100
        rem2_100 = e100 * p2_100 - 2 * (2 * (300 ** 2) + 200 * (288 ** 2))
        rem4_100 = m4_tgt - 2 * (2 * (300 ** 4) + 200 * (288 ** 4))
        e1, e2, e3 = 20, 32, 38
        A_c = 2 * (e2 ** 2) * (e2 ** 2 - e1 ** 2)
        B_c = 2 * (e3 ** 2) * (e3 ** 2 - e1 ** 2)
        rhs = rem4_100 - (e1 ** 2) * rem2_100
        g_ab = math.gcd(A_c, B_c)
        inv = pow(B_c // g_ab, -1, A_c // g_ab)
        c3_base = ((rhs // g_ab) * inv) % (A_c // g_ab)
        step = A_c // g_ab
        k_mul = (rhs // (2 * B_c) - c3_base) // step
        c3 = c3_base + k_mul * step
        c2 = (rhs - B_c * c3) // A_c
        c1 = (rem2_100 - 2 * (e2 ** 2) * c2 - 2 * (e3 ** 2) * c3) // (2 * (e1 ** 2))
        c150 = p2_100 - 404 - 2 * (c1 + c2 + c3)
        with self.assertRaisesRegex(ValueError, "ISING_BIPARTITE_SYMMETRY_MISMATCH"):
            gsi.verify_ising_3d_dos_moments(
                (5, 5, 4),
                [
                    (0, 2), (6, 200),
                    (150 - e3 // 2, c3), (150 - e2 // 2, c2), (150 - e1 // 2, c1),
                    (150, c150),
                    (150 + e1 // 2, c1), (150 + e2 // 2, c2), (150 + e3 // 2, c3),
                    (294, 200), (300, 2),
                ],
            )

        # Cluster-expansion guards
        ce_ok = gsi.verify_cluster_expansion_pair_energy([2, 2], 4, [0, 4, 4, 2], -5, "1100", -6, expected_occupied=2)
        self.assertEqual(ce_ok["exact_energy"], -6)
        with self.assertRaisesRegex(ValueError, "CE_OCCUPIED_COUNT_MISMATCH"):
            gsi.verify_cluster_expansion_pair_energy([2, 2], 4, [0, 4, 4, 2], -5, "1100", -6, expected_occupied=True)  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "CE_OCCUPIED_COUNT_MISMATCH"):
            gsi.verify_cluster_expansion_pair_energy([2, 2], 4, [0, 4, 4, 2], -5, "1100", -6, expected_occupied=3)
        for args, code in (
            (((2, 2), 4, [0, 4, 4, 2], -5, "1100", -6), "CE_INVALID_DIMS"),
            (([], 0, [], -5, "", 0), "CE_INVALID_DIMS"),
            (([True, 2], 2, [0, 4], -5, "11", -6), "CE_INVALID_DIMS"),
            (([0, 2], 0, [], -5, "", 0), "CE_INVALID_DIMS"),
            (([1], True, [0], -5, "1", -5), "CE_N_SITES_MISMATCH"),
            (([2, 2], 5, [0, 4, 4, 2], -5, "1100", -6), "CE_N_SITES_MISMATCH"),
            (([2, 2], 4, (0, 4, 4, 2), -5, "1100", -6), "CE_INVALID_JD_TABLE"),
            (([2, 2], 4, [0, 4, 4], -5, "1100", -6), "CE_INVALID_JD_TABLE"),
            (([2, 2], 4, [0, True, 4, 2], -5, "1100", -6), "CE_INVALID_JD_TABLE"),
            (([2, 2], 4, [0, 4, 4, 2], True, "1100", -6), "CE_INVALID_INT_COEFF"),
            (([2, 2], 4, [0, 4, 4, 2], -5, "1100", True), "CE_INVALID_INT_COEFF"),
            (([2, 2], 4, [0, 4, 4, 2], -5, 1100, -6), "CE_INVALID_CONFIG_BITS"),
            (([2, 2], 4, [0, 4, 4, 2], -5, "110", -6), "CE_INVALID_CONFIG_BITS"),
            (([2, 2], 4, [0, 4, 4, 2], -5, "1102", -6), "CE_INVALID_CONFIG_BITS"),
            (([3], 3, [0, 1, 2], -5, "110", -9), "CE_ODD_PAIR_SUM"),
            (([2, 2], 4, [0, 4, 4, 2], -5, "1100", -5), "CE_ENERGY_MISMATCH"),
        ):
            with self.assertRaisesRegex(ValueError, code):
                gsi.verify_cluster_expansion_pair_energy(*args)  # type: ignore[arg-type]

        # Lean purity guards (incl. GSI101-BYPASS-02: string-masked --, nested /--/, sorryAx, native_decide, ofReduceBool)
        self.assertTrue(gsi.verify_lean_file_purity("-- sorry in comment\n/- /- sorry -/ block -/\ndef s := \"a \\\" -- ok\"\ndef x := 1\n")["clean"])
        for bad_lean, code in (
            (123, "LEAN_EMPTY_OR_NOT_STR"),
            ("   \n", "LEAN_EMPTY_OR_NOT_STR"),
            ('def s := "unclosed\n', "LEAN_UNCLOSED_DELIMITER"),
            ("/- unclosed block\n", "LEAN_UNCLOSED_DELIMITER"),
            ("theorem bad : True := by sorry\n", "LEAN_IMPURE_TOKENS"),
            ('def x := "--" ; sorry\n', "LEAN_IMPURE_TOKENS"),
            ("theorem t : False := sorryAx False false\n", "LEAN_IMPURE_TOKENS"),
            ("theorem t : True := by native_decide\n", "LEAN_IMPURE_TOKENS"),
            ("def x := Lean.ofReduceBool\n", "LEAN_IMPURE_TOKENS"),
        ):
            with self.assertRaisesRegex(ValueError, code):
                gsi.verify_lean_file_purity(bad_lean)  # type: ignore[arg-type]

        # Offline standalone known-answer self-check & manifest/catalog helper guards
        import hashlib
        import tempfile

        self.assertEqual(gsi.parse_williamson_sol_line("SOL 0a 0b 0c 0d\n"), [10, 11, 12, 13])
        with self.assertRaisesRegex(ValueError, "W75_SOL_NOT_FOUND"):
            gsi.parse_williamson_sol_line("no sol line here")

        # Quantum witness guards (incl. GSI101-BYPASS-03: bool n_faults, sector, hollow/non-dict/duplicate faults)
        good_qw = {"sector": "X", "n_faults": 2, "faults": [{"cycle": 1, "pauli": "X"}, {"cycle": 2, "pauli": "X"}]}
        self.assertEqual(gsi.verify_quantum_fault_witness(good_qw, expected_faults=2)["n_faults"], 2)
        self.assertEqual(gsi.verify_quantum_fault_witness({"sector": "Z", "n_faults": 1, "faults": [{"q": 1}]}, expected_faults=1)["sector"], "Z")
        for bad_q, exp_f, code in (
            (good_qw, True, "QUANTUM_WITNESS_INVALID_EXPECTED"),
            (good_qw, 0, "QUANTUM_WITNESS_INVALID_EXPECTED"),
            ("not-dict", 2, "QUANTUM_WITNESS_NOT_DICT"),
            ({"n_faults": 2, "faults": [{"a": 1}, {"a": 2}]}, 2, "QUANTUM_WITNESS_INVALID_SECTOR"),
            ({"sector": "Y", "n_faults": 2, "faults": [{"a": 1}, {"a": 2}]}, 2, "QUANTUM_WITNESS_INVALID_SECTOR"),
            ({"sector": "X", "n_faults": True, "faults": [{"a": 1}]}, 1, "QUANTUM_WITNESS_FAULT_COUNT"),
            ({"sector": "X", "n_faults": 1, "faults": [{"a": 1}, {"a": 2}]}, 2, "QUANTUM_WITNESS_FAULT_COUNT"),
            ({"sector": "X", "n_faults": 2, "faults": "12"}, 2, "QUANTUM_WITNESS_FAULT_COUNT"),
            ({"sector": "X", "n_faults": 2, "faults": [{"a": 1}]}, 2, "QUANTUM_WITNESS_FAULT_COUNT"),
            ({"sector": "X", "n_faults": 2, "faults": [None, {"a": 1}]}, 2, "QUANTUM_WITNESS_INVALID_FAULT_ENTRY"),
            ({"sector": "X", "n_faults": 2, "faults": [{}, {"a": 1}]}, 2, "QUANTUM_WITNESS_INVALID_FAULT_ENTRY"),
            ({"sector": "X", "n_faults": 2, "faults": [{"a": 1}, {"a": 1}]}, 2, "QUANTUM_WITNESS_DUPLICATE_FAULT"),
        ):
            with self.assertRaisesRegex(ValueError, code):
                gsi.verify_quantum_fault_witness(bad_q, expected_faults=exp_f)  # type: ignore[arg-type]

        # SHA256SUMS manifest guards (incl. GSI101-BYPASS-01: empty, malformed, hex, abs/backslash/.. traversal, symlink escape, missing)
        with tempfile.TemporaryDirectory() as td:
            outer = Path(td)
            outside_f = outer / "outside.txt"
            outside_f.write_bytes(b"secret\n")
            outside_sha = hashlib.sha256(b"secret\n").hexdigest()
            root = outer / "base"
            root.mkdir()
            (root / "a.txt").write_bytes(b"hello\n")
            (root / "sub").mkdir()
            (root / "sub\\a.txt").write_bytes(b"hello\n")
            (root / "escape.txt").symlink_to(outside_f)
            good_sha = hashlib.sha256(b"hello\n").hexdigest()
            self.assertEqual(gsi.verify_sha256sums_manifest(root, f"\n{good_sha}  a.txt\n"), 1)
            for bad_manifest, code in (
                (123, "SHA256SUMS_NOT_STR"),
                ("   \n\n  ", "SHA256SUMS_EMPTY_MANIFEST"),
                (f"{good_sha}\n", "SHA256SUMS_MALFORMED_LINE"),
                (f"{good_sha[:63]}  a.txt\n", "SHA256SUMS_INVALID_HEX"),
                (f"{good_sha.upper()}  a.txt\n", "SHA256SUMS_INVALID_HEX"),
                (f"{good_sha}  {root / 'a.txt'}\n", "SHA256SUMS_PATH_TRAVERSAL"),
                (f"{good_sha}  sub\\a.txt\n", "SHA256SUMS_PATH_TRAVERSAL"),
                (f"{good_sha}  sub/../a.txt\n", "SHA256SUMS_PATH_TRAVERSAL"),
                (f"{outside_sha}  ../outside.txt\n", "SHA256SUMS_PATH_TRAVERSAL"),
                (f"{outside_sha}  {outside_f}\n", "SHA256SUMS_PATH_TRAVERSAL"),
                (f"{outside_sha}  escape.txt\n", "SHA256SUMS_TARGET_OUTSIDE_OR_MISSING"),
                (f"{good_sha}  missing.txt\n", "SHA256SUMS_TARGET_OUTSIDE_OR_MISSING"),
                (f"{'0' * 64}  a.txt\n", "SHA256SUMS_MISMATCH"),
            ):
                with self.assertRaisesRegex(ValueError, code):
                    gsi.verify_sha256sums_manifest(root, bad_manifest)  # type: ignore[arg-type]

            with self.assertRaisesRegex(ValueError, "INTAKE_FILES_MISSING"):
                gsi.build_live_catalog(root)
            (root / "raw_pages").mkdir()
            (root / "raw_pages" / "llms-full.txt").write_text("## Results\n## Papers and notes\n### only one\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "INTAKE_FILES_MISSING"):
                gsi.build_live_catalog(root)
            (root / "raw").mkdir()
            (root / "raw" / "sitemap.txt").write_text("<loc>https://www.generalised.si/research/x</loc>\n", encoding="utf-8")
            (root / "raw_pages" / "llms-full.txt").unlink()
            with self.assertRaisesRegex(ValueError, "INTAKE_FILES_MISSING"):
                gsi.build_live_catalog(root)
            p31 = "## Results\n## Papers and notes\n" + "".join(f"### P{i}\n" for i in range(31))
            (root / "raw_pages" / "llms-full.txt").write_text(p31, encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "CATALOG_EXPECTED_31_DOMAINS"):
                gsi.build_live_catalog(root)
            (root / "raw_pages" / "llms-full.txt").write_text("## Results\n## Papers and notes\n### only one\n", encoding="utf-8")
            s31 = "".join(f"<loc>https://www.generalised.si/research/d{i}</loc>\n" for i in range(31))
            (root / "raw" / "sitemap.txt").write_text(s31, encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "CATALOG_EXPECTED_31_DOMAINS"):
                gsi.build_live_catalog(root)

        st = gsi.run_standalone_known_answer()
        _assert_no_floats(self, st)
        self.assertEqual(st["mode"], "standalone_known_answer_offline")
        self.assertEqual(st["honest_novelty_tier"], "N0")


if __name__ == "__main__":
    unittest.main()
