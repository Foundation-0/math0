#!/usr/bin/env python3
"""
R1-R5 Mutation-Killing & Dual-Oracle Verification Suite for AUDIT-070
(`zenodo_rns_pnp_audit.py`).

Safe under `python3 -I -B`, `python3 -I -O -B`, `python3 -I -B -W error`, `python3 -I -O -B -W error`.
Zero external dependencies, zero bare asserts.
"""
from __future__ import annotations

from contextlib import redirect_stdout
from fractions import Fraction
import io
import itertools
import json
from pathlib import Path
import random
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))

import zenodo_rns_pnp_audit as mod  # noqa: E402


def _assert_no_floats(obj: object, path: str = "root") -> None:
    if isinstance(obj, float):
        raise AssertionError(f"float leaked at {path}: {obj!r}")
    if isinstance(obj, dict):
        for k, v in obj.items():
            _assert_no_floats(v, f"{path}.{k}")
    elif isinstance(obj, (list, tuple)):
        for i, v in enumerate(obj):
            _assert_no_floats(v, f"{path}[{i}]")


class TestPrimitivesAndDualOracles(unittest.TestCase):
    def test_exact_int_and_isqrt_round(self) -> None:
        self.assertEqual(mod.require_exact_int(0, "x", allow_zero=True), 0)
        self.assertEqual(mod.require_exact_int(1, "x", allow_zero=False), 1)
        for bad in (True, 1.0, "1", None):
            with self.assertRaises(mod.RnsAuditError):
                mod.require_exact_int(bad, "x")
        with self.assertRaises(mod.RnsAuditError):
            mod.require_exact_int(-1, "x", allow_zero=True)
        with self.assertRaises(mod.RnsAuditError):
            mod.require_exact_int(0, "x", allow_zero=False)

        # Verify exact rounding of sqrt(n_sq): sqrt(2)=1.414->1, sqrt(3)=1.732->2, sqrt(289)=17
        self.assertEqual(mod.isqrt_round_nearest(0), 0)
        self.assertEqual(mod.isqrt_round_nearest(2), 1)
        self.assertEqual(mod.isqrt_round_nearest(3), 2)
        self.assertEqual(mod.isqrt_round_nearest(289), 17)
        self.assertEqual(mod.dist_euc2d_exact((0, 8), (15, 0)), 17)

    def test_bareiss_vs_faddeev_leverrier_and_matrix_refusals(self) -> None:
        for bad in ([], "x", [[1, 2]], [[1.0]], [[True]], [[1, 2], [3, 1]]):
            with self.assertRaises(mod.RnsAuditError):
                mod.require_symmetric_int_matrix(bad, "M")

        cases = [
            [[0, 0], [0, 0]],
            [[0, 3], [3, 0]],
            [[0, -2], [-2, 0]],
            [[0, 2, 1], [2, 0, 1], [1, 1, 0]],
            [[2, 1, 0, 0], [1, 2, 0, 0], [0, 0, 0, 4], [0, 0, 4, 0]],
            [[0, 0, 5], [0, 0, 0], [5, 0, 0]],
        ]
        rng = random.Random(20261121)
        for _ in range(25):
            n = rng.randint(1, 5)
            M = [[0] * n for _ in range(n)]
            for i in range(n):
                for j in range(i, n):
                    v = rng.randint(-4, 4)
                    M[i][j] = M[j][i] = v
            cases.append(M)
        for M in cases:
            self.assertEqual(mod.bareiss_symmetric_inertia_exact(M), mod.faddeev_leverrier_inertia_exact(M))


class TestPillarsAndRefusals(unittest.TestCase):
    def test_pillar_a_tseitin_k4_and_cnf_gf2_refusals(self) -> None:
        res = mod.verify_tseitin_k4_gramian_blindness()
        self.assertEqual(res["models_sat"], 8)
        self.assertEqual(res["models_unsat"], 0)
        self.assertTrue(res["gramians_bit_identical"])
        self.assertTrue(res["linear_biases_identical_zero"])
        self.assertTrue(res["gf2_cohomology_separates"])

        # Refusal controls for build_tseitin_k4_3cnf, validate_cnf, count_sat_models_exact, gf2
        for bad_p in (True, -1, 2):
            with self.assertRaises(mod.RnsAuditError):
                mod.build_tseitin_k4_3cnf(bad_p)  # type: ignore[arg-type]
        for bad_n, bad_cl in (
            (0, [(1,)]),
            (3, []),
            (3, [()]),
            (3, [(0,)]),
            (3, [(4,)]),
            (3, [(-4,)]),
            (3, [(True,)]),
        ):
            with self.assertRaises(mod.RnsAuditError):
                mod.validate_cnf(bad_n, bad_cl)
        # Exact boundaries: n=1 and n=12 succeed; n=13 rejected with N_VARS_TOO_LARGE
        self.assertEqual(mod.count_sat_models_exact(1, [(1,)]), 1)
        self.assertEqual(mod.count_sat_models_exact(12, [(1,), (-1,)]), 0)
        with self.assertRaises(mod.RnsAuditError) as ctx_n13:
            mod.count_sat_models_exact(13, [(1,)])
        self.assertEqual(ctx_n13.exception.code, "N_VARS_TOO_LARGE")

        # GF(2) refusal controls
        with self.assertRaises(mod.RnsAuditError):
            mod.gf2_system_consistent([], [])
        with self.assertRaises(mod.RnsAuditError):
            mod.gf2_system_consistent([[1]], [0, 1])
        with self.assertRaises(mod.RnsAuditError):
            mod.gf2_system_consistent([[]], [0])
        with self.assertRaises(mod.RnsAuditError):
            mod.gf2_system_consistent([[2]], [0])
        with self.assertRaises(mod.RnsAuditError):
            mod.gf2_system_consistent([[1]], [2])

    def test_pillar_b_self_loop_inversion(self) -> None:
        res = mod.verify_self_loop_square_inversion()
        self.assertTrue(res["dual_oracles_agree"])
        self.assertTrue(res["proves_lambda_min_sq_gt_9_gt_lambda2_sq"])
        self.assertTrue(res["steelman_A_plus_dmaxI_psd"])

    def test_pillar_c_held_karp_sidewalk_and_tsp_audit(self) -> None:
        # Cross-check Held-Karp vs brute-force permutations on 3-node (min boundary + zero off-diag), 5-node, and 10-node (max boundary)
        D3 = [[0, 2, 5], [2, 0, 3], [5, 3, 0]]
        self.assertEqual(mod.held_karp_tsp_exact(D3)["opt_cost"], 10)
        D3_zero = [[0, 0, 5], [0, 0, 5], [5, 5, 0]]
        self.assertEqual(mod.held_karp_tsp_exact(D3_zero)["opt_cost"], 10)
        D10 = [[0 if i == j else 1 for j in range(10)] for i in range(10)]
        self.assertEqual(mod.held_karp_tsp_exact(D10)["opt_cost"], 10)
        # Large integer distances (> 10**18) must not collide with any hardcoded sentinel (DEFECT-03)
        big = 10**18
        D_big = [[0, big, big], [big, 0, big], [big, big, 0]]
        self.assertEqual(mod.held_karp_tsp_exact(D_big)["opt_cost"], 3 * big)
        self.assertTrue(mod.verify_sidewalk_theorem_refutation(far_M=10**20)["teorema_4_1_falsified"])
        res = mod.verify_sidewalk_theorem_refutation(far_M=100)
        self.assertTrue(res["teorema_4_1_falsified"])
        self.assertFalse(res["shortest_edge_01_in_opt_tour"])

        # Brute-force verify on M=8008 (g0=8000, sigma0=1000)
        pts = [(0, 0), (0, 8), (-15, 0), (15, 0), (0, 8008)]
        D5 = [[mod.dist_euc2d_exact(a, b) for b in pts] for a in pts]
        bf_best = min(
            sum(D5[t[i]][t[(i + 1) % 5]] for i in range(5))
            for perm in itertools.permutations([1, 2, 3, 4])
            for t in ([0] + list(perm),)
        )
        self.assertEqual(mod.held_karp_tsp_exact(D5)["opt_cost"], bf_best)
        sw = mod.verify_sidewalk_theorem_refutation(far_M=8008)
        self.assertEqual(sw["g0_exact"], 8000)
        self.assertEqual(sw["sigma0_exact"]["exact"], "1000/1")
        self.assertEqual(sw["held_karp_opt_cost"], 16055)
        self.assertEqual(sw["best_cost_forcing_shortest_edge_01"], 16056)
        self.assertEqual(sw["euc2d_penalty_forcing_shortest_edge_01"], 1)

        # Held-Karp & sidewalk boundary/refusal controls
        with self.assertRaises(mod.RnsAuditError) as ctx_n2:
            mod.held_karp_tsp_exact([[0, 1], [1, 0]])
        self.assertEqual(ctx_n2.exception.code, "TSP_N_RANGE")
        with self.assertRaises(mod.RnsAuditError) as ctx_n11:
            mod.held_karp_tsp_exact([[0] * 11 for _ in range(11)])
        self.assertEqual(ctx_n11.exception.code, "TSP_N_RANGE")
        with self.assertRaises(mod.RnsAuditError) as ctx_diag:
            mod.held_karp_tsp_exact([[1, 2, 2], [2, 0, 2], [2, 2, 0]])
        self.assertEqual(ctx_diag.exception.code, "NONZERO_DIAG_DIST")
        with self.assertRaises(mod.RnsAuditError) as ctx_neg:
            mod.held_karp_tsp_exact([[0, -1, 2], [-1, 0, 2], [2, 2, 0]])
        self.assertEqual(ctx_neg.exception.code, "NEGATIVE_DIST")
        with self.assertRaises(mod.RnsAuditError):
            mod.verify_sidewalk_theorem_refutation(far_M=99)
        with self.assertRaises(mod.RnsAuditError):
            mod.verify_sidewalk_theorem_refutation(far_M=True)  # type: ignore[arg-type]

        tsp70 = mod.verify_tsp_70x_complexity_audit()
        self.assertEqual(tsp70["matrix_entry_reduction_ratio"]["exact"], "3600/73")
        self.assertEqual(tsp70["sequential_patch_outer_du_calls"], 73500)
        self.assertEqual(tsp70["sequential_patch_edge_pairs_O_N2"], 4410000)
        self.assertEqual(tsp70["sequential_patch_distance_euc_calls"], 22123500)
        self.assertTrue(tsp70["patch_calls_exceed_global_matrix_entries"])

    def test_pillar_d_knapsack_scheduling_and_refusals(self) -> None:
        # Verify exact 1-1 & 1-2 improvement paths AND failure counterexamples
        self.assertEqual(mod.knapsack_exact_dp([51, 34, 33, 33], [51, 34, 33, 33], 100), 100)
        self.assertEqual(mod.rns_knapsack_1to2_exact([51, 34, 33, 33], [51, 34, 33, 33], 100), (100, 100))
        self.assertEqual(mod.rns_knapsack_1to2_exact([6, 5], [6, 5], 6), (6, 6))
        # 1-1 improvement case: w=[4, 5], v=[5, 6], C=5 -> greedy takes 4(v=5), 1-1 swaps to 5(v=6)
        self.assertEqual(mod.rns_knapsack_1to2_exact([4, 5], [5, 6], 5), (6, 5))
        # Failure counterexamples
        self.assertEqual(mod.rns_knapsack_1to2_exact([1, 1, 1000], [2, 2, 1000], 1000), (4, 2))
        self.assertEqual(mod.knapsack_exact_dp([1, 1, 1000], [2, 2, 1000], 1000), 1000)
        self.assertEqual(mod.rns_knapsack_1to2_exact([52, 25, 25, 25, 25], [52, 25, 25, 25, 25], 100), (77, 77))

        # Knapsack refusal controls
        for fn in (mod.knapsack_exact_dp, mod.rns_knapsack_1to2_exact):
            with self.assertRaises(mod.RnsAuditError):
                fn([], [], 10)
            with self.assertRaises(mod.RnsAuditError):
                fn([1, 2], [1], 10)
            with self.assertRaises(mod.RnsAuditError):
                fn([0], [1], 10)
            with self.assertRaises(mod.RnsAuditError):
                fn([1], [-1], 10)

        # Scheduling positive (1-1 & 2-1 hits) + negative CEs + refusal controls
        # 1-1 swap hit: [10, 8, 6, 4] on M=2 -> LPT [10, 4]=14, [8, 6]=14 already; try [10, 7, 7, 4] -> LPT [10,4]=14,[7,7]=14
        # Try [12, 9, 8, 7, 6] sum=42, ideal=21: LPT M0=[12,7]=19, M1=[9,8,6]=23 -> diff=4, target=2 -> 1-1 swap 9<->7!
        loads_11, ideal_11 = mod.rns_scheduling_elastic_exact([12, 9, 8, 7, 6], 2, max_pivots=2)
        self.assertEqual(max(loads_11), ideal_11)
        # 2-1 swap hit: [12, 11, 10, 10, 9, 8] -> check [36, 29, 24, 16, 14, 12, 11] fails
        loads_ce2, ideal_ce2 = mod.rns_scheduling_elastic_exact([36, 29, 24, 16, 14, 12, 11], 2, max_pivots=2)
        self.assertGreater(max(loads_ce2), ideal_ce2)
        # M=3 2-1 hit on [12, 11, 11, 10, 10, 10, 9, 9, 8]
        loads_21, ideal_21 = mod.rns_scheduling_elastic_exact([12, 11, 11, 10, 10, 10, 9, 9, 8], 3, max_pivots=2)
        self.assertEqual(max(loads_21), ideal_21)

        with self.assertRaises(mod.RnsAuditError):
            mod.rns_scheduling_elastic_exact([], 2)
        with self.assertRaises(mod.RnsAuditError):
            mod.rns_scheduling_elastic_exact([5], 0)
        with self.assertRaises(mod.RnsAuditError) as ctx_empty_d:
            mod.verify_partition_certificate([], [[5]])
        self.assertEqual(ctx_empty_d.exception.code, "EMPTY_DURATIONS")
        with self.assertRaises(mod.RnsAuditError) as ctx_float_p:
            mod.verify_partition_certificate([1.5, 1.5], [[1.5], [1.5]])  # type: ignore[list-item]
        self.assertEqual(ctx_float_p.exception.code, "INVALID_INT")
        with self.assertRaises(mod.RnsAuditError) as ctx_bool_d:
            mod.verify_partition_certificate([True, True], [[True], [True]])
        self.assertEqual(ctx_bool_d.exception.code, "INVALID_INT")
        with self.assertRaises(mod.RnsAuditError) as ctx_bool_p:
            mod.verify_partition_certificate([1, 1], [[True], [True]])
        self.assertEqual(ctx_bool_p.exception.code, "INVALID_INT")
        with self.assertRaises(mod.RnsAuditError) as ctx_zero_p:
            mod.verify_partition_certificate([0, 0], [[0], [0]])
        self.assertEqual(ctx_zero_p.exception.code, "NONPOSITIVE_INT")
        with self.assertRaises(mod.RnsAuditError) as ctx_empty_p:
            mod.verify_partition_certificate([5, 5], [])
        self.assertEqual(ctx_empty_p.exception.code, "EMPTY_PART")
        with self.assertRaises(mod.RnsAuditError) as ctx_empty_g:
            mod.verify_partition_certificate([5], [[5], []])
        self.assertEqual(ctx_empty_g.exception.code, "EMPTY_PART_GROUP")
        with self.assertRaises(mod.RnsAuditError) as ctx_mis_p:
            mod.verify_partition_certificate([5, 5], [[6], [6]])
        self.assertEqual(ctx_mis_p.exception.code, "PARTITION_MISMATCH")
        with self.assertRaises(mod.RnsAuditError) as ctx_uneq_p:
            mod.verify_partition_certificate([5, 7], [[5], [7]])
        self.assertEqual(ctx_uneq_p.exception.code, "UNEQUAL_PARTITION")

    def test_pillar_e_mycielski_and_cli_zero_float(self) -> None:
        res = mod.verify_mycielski_and_deposit_refutation()
        self.assertEqual(res["mycielski_m4"]["exact_omega"], 2)
        self.assertEqual(res["mycielski_m4"]["exact_chi"], 4)
        self.assertTrue(res["teorema_6_1_symmetric_K4_counterexample"]["deterministic_collapse_fails"])
        with self.assertRaises(mod.RnsAuditError):
            mod.graph_is_k_colorable_exact([[0, 1], [1, 0]], 0)
        with self.assertRaises(mod.RnsAuditError) as ctx_loop:
            mod.graph_is_k_colorable_exact([[1, 0], [0, 0]], 1)
        self.assertEqual(ctx_loop.exception.code, "SELF_LOOP_ADJ")
        with self.assertRaises(mod.RnsAuditError) as ctx_nonbin:
            mod.graph_is_k_colorable_exact([[0, 2], [2, 0]], 1)
        self.assertEqual(ctx_nonbin.exception.code, "INVALID_ADJ_ENTRY")
        with self.assertRaises(mod.RnsAuditError) as ctx_negadj:
            mod.graph_is_k_colorable_exact([[0, -1], [-1, 0]], 1)
        self.assertEqual(ctx_negadj.exception.code, "INVALID_ADJ_ENTRY")

        cert = mod.build_audit_certificate(standalone=True)
        _assert_no_floats(cert)
        with tempfile.TemporaryDirectory() as td:
            self.assertEqual(mod._inspect_zenodo_staging_readonly(Path(td)), {"zenodo_staging_present": False})
            out_p = Path(td) / "cert.json"
            buf = io.StringIO()
            with redirect_stdout(buf):
                rc = mod.main(["--standalone", "--write-cert", str(out_p)])
            self.assertEqual(rc, 0)
            parsed = json.loads(out_p.read_text(encoding="utf-8"))
            _assert_no_floats(parsed)
            self.assertEqual(parsed["certificate_sha256"], cert["certificate_sha256"])


if __name__ == "__main__":
    suite = unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=0).run(suite)
    raise SystemExit(0 if result.wasSuccessful() else 1)
