#!/usr/bin/env python3
"""
R5 Refusal-Site & Exact-Invariant Test Suite for openresearch_index_oracle.py (AUDIT-069).

- Zero bare `assert` statements (unittest assertions only).
- `-I -O -B -W error` safe.
- Kills 100% of refusal-site deletions and boundary-operator flips under
  `aletheia v1.4.0 mutate openresearch_index_oracle.py --add-cwd`.
"""
from __future__ import annotations

from fractions import Fraction
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest

_SCRIPT_DIR = Path(__file__).resolve().parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))

from openresearch_index_audit import (  # noqa: E402
    EMBEDDED_HEATMAP_ROWS,
    EMBEDDED_MODELS,
    PINNED_OPENRESEARCH_COMMIT,
    _audit_openresearch_repo_readonly,
    build_certificate,
    parse_blog_bundle_texts,
    verify_pinned_artifact_digests,
)
from openresearch_index_oracle import (  # noqa: E402
    DEFAULT_INDEX_WEIGHTS,
    IndexOracleError,
    VERIFIED_INTERNET_STATUS,
    audit_bipartite_confounding_exact,
    audit_ci_separability_and_pareto_stability,
    audit_missing_attempts_and_cost_extrapolation,
    audit_task_leverage_asymmetry,
    audit_weight_sensitivity_simplex,
    canonical_sha256,
    compute_composite_index_exact,
    compute_pareto_frontier_exact,
    evaluate_tao_observability_gate,
    exact_simplex_region_fraction,
    format_exact_decimal,
    frac_str,
    require_exact_fraction,
    require_exact_int,
    require_non_empty_str,
    verify_no_floats,
)


class TestPrimitivesAndNoFloat(unittest.TestCase):
    def test_verify_no_floats(self) -> None:
        verify_no_floats({"a": [1, "x", (Fraction(1, 2), None)]})
        with self.assertRaises(IndexOracleError) as cm:
            verify_no_floats(0.5)
        self.assertEqual(cm.exception.code, "FLOAT_FORBIDDEN")
        with self.assertRaises(IndexOracleError):
            verify_no_floats({"nested": [1, {"bad": float("nan")}]})
        with self.assertRaises(IndexOracleError):
            verify_no_floats({1.25: "bad_key"})

    def test_require_non_empty_str(self) -> None:
        self.assertEqual(require_non_empty_str("Opus 5.5", "m"), "Opus 5.5")
        with self.assertRaises(IndexOracleError) as cm1:
            require_non_empty_str(123, "m")
        self.assertEqual(cm1.exception.code, "INVALID_STR")
        with self.assertRaises(IndexOracleError) as cm2:
            require_non_empty_str("   \t\n ", "m")
        self.assertEqual(cm2.exception.code, "EMPTY_STR")

    def test_require_exact_int_boundaries(self) -> None:
        self.assertEqual(require_exact_int(0, "x", min_value=0, max_value=10), 0)
        self.assertEqual(require_exact_int(10, "x", min_value=0, max_value=10), 10)
        with self.assertRaises(IndexOracleError):
            require_exact_int(True, "x")
        with self.assertRaises(IndexOracleError):
            require_exact_int("5", "x")
        with self.assertRaises(IndexOracleError) as cm_lo:
            require_exact_int(-1, "x", min_value=0)
        self.assertEqual(cm_lo.exception.code, "INT_BELOW_MIN")
        with self.assertRaises(IndexOracleError) as cm_hi:
            require_exact_int(11, "x", max_value=10)
        self.assertEqual(cm_hi.exception.code, "INT_ABOVE_MAX")

    def test_require_exact_fraction_boundaries(self) -> None:
        self.assertEqual(require_exact_fraction(Fraction(0), "f", Fraction(0), Fraction(1)), Fraction(0))
        self.assertEqual(require_exact_fraction(1, "f", Fraction(0), Fraction(1)), Fraction(1))
        self.assertEqual(require_exact_fraction("0.6183", "f", Fraction(0), Fraction(1)), Fraction(6183, 10000))
        self.assertEqual(require_exact_fraction("-3/4", "f"), Fraction(-3, 4))
        with self.assertRaises(IndexOracleError) as cm_b:
            require_exact_fraction(False, "f")
        self.assertEqual(cm_b.exception.code, "BOOL_NOT_FRACTION")
        with self.assertRaises(IndexOracleError) as cm_t:
            require_exact_fraction(0.5, "f")
        self.assertEqual(cm_t.exception.code, "INVALID_FRACTION_TYPE")
        for bad in ("0.5\n", "1/0", ".5", "NaN", "1e-3", "01"):
            with self.assertRaises(IndexOracleError) as cm_s:
                require_exact_fraction(bad, "f")
            self.assertEqual(cm_s.exception.code, "INVALID_FRACTION_STR")
        with self.assertRaises(IndexOracleError) as cm_lo:
            require_exact_fraction(Fraction(-1, 100), "f", min_value=Fraction(0))
        self.assertEqual(cm_lo.exception.code, "FRACTION_BELOW_MIN")
        with self.assertRaises(IndexOracleError) as cm_hi:
            require_exact_fraction(Fraction(101, 100), "f", max_value=Fraction(1))
        self.assertEqual(cm_hi.exception.code, "FRACTION_ABOVE_MAX")

    def test_formatting_and_canonical_digest(self) -> None:
        self.assertEqual(frac_str(Fraction(2, 4)), "1/2")
        self.assertEqual(format_exact_decimal(Fraction(41, 120), 4), "0.3417")
        self.assertEqual(format_exact_decimal(Fraction(-3, 2), 0), "-2")
        self.assertEqual(format_exact_decimal(Fraction(0), 2), "0.00")
        d1 = canonical_sha256({"b": 1, "a": 2})
        d2 = canonical_sha256({"a": 2, "b": 1})
        self.assertEqual(d1, d2)
        self.assertEqual(len(d1), 64)


class TestCompositeAndLeverage(unittest.TestCase):
    def test_composite_exact_and_refusals(self) -> None:
        val = compute_composite_index_exact("0.5833", "0.6559", "0.6132", DEFAULT_INDEX_WEIGHTS)
        self.assertEqual(val, Fraction(61832, 100000))
        self.assertEqual(compute_composite_index_exact(0, 0, 0), Fraction(0))
        self.assertEqual(compute_composite_index_exact(1, 1, 1), Fraction(1))
        with self.assertRaises(IndexOracleError) as cm_len:
            compute_composite_index_exact("0.5", "0.5", "0.5", weights=(Fraction(1, 2), Fraction(1, 2)))
        self.assertEqual(cm_len.exception.code, "WEIGHT_COUNT_INVALID")
        with self.assertRaises(IndexOracleError) as cm_sum:
            compute_composite_index_exact("0.5", "0.5", "0.5", weights=(Fraction(1, 2), Fraction(1, 2), Fraction(1, 10)))
        self.assertEqual(cm_sum.exception.code, "WEIGHT_SUM_NOT_ONE")

    def test_task_leverage_asymmetry(self) -> None:
        res = audit_task_leverage_asymmetry(
            {"science": Fraction(2, 5), "post_training": Fraction(2, 5), "literature": Fraction(1, 5)},
            {"science": 20, "post_training": 6, "literature": 3},
        )
        self.assertEqual(res["max_to_min_task_leverage_exact"], "10/3")
        self.assertEqual(res["total_tasks"], 29)
        with self.assertRaises(IndexOracleError) as cm1:
            audit_task_leverage_asymmetry({"only": Fraction(1)}, {"only": 1})
        self.assertEqual(cm1.exception.code, "TOO_FEW_TRACKS")
        with self.assertRaises(IndexOracleError) as cm2:
            audit_task_leverage_asymmetry({"a": Fraction(1, 2), "b": Fraction(1, 2)}, {"a": 1, "c": 1})
        self.assertEqual(cm2.exception.code, "TRACK_KEY_MISMATCH")
        with self.assertRaises(IndexOracleError) as cm3:
            audit_task_leverage_asymmetry({"a": Fraction(0), "b": Fraction(1)}, {"a": 1, "b": 1})
        self.assertEqual(cm3.exception.code, "ZERO_TRACK_WEIGHT")
        with self.assertRaises(IndexOracleError) as cm4:
            audit_task_leverage_asymmetry({"a": Fraction(1, 2), "b": Fraction(1, 3)}, {"a": 1, "b": 1})
        self.assertEqual(cm4.exception.code, "TRACK_WEIGHT_SUM_NOT_ONE")


class TestSimplexPolytope(unittest.TestCase):
    def test_exact_simplex_clipping(self) -> None:
        self.assertEqual(exact_simplex_region_fraction([]), Fraction(1))
        # w_S >= 1/2 cuts off right triangle of side 1/2 -> area fraction = 1/4
        self.assertEqual(exact_simplex_region_fraction([(1, 0, Fraction(-1, 2))]), Fraction(1, 4))
        # Infeasible halfspace -> exact 0
        self.assertEqual(exact_simplex_region_fraction([(1, 0, -2)]), Fraction(0))
        with self.assertRaises(IndexOracleError) as cm:
            exact_simplex_region_fraction([(1, 0)])  # type: ignore[list-item]
        self.assertEqual(cm.exception.code, "HALFSPACE_ARITY")

    def test_simplex_conservation_and_refusals(self) -> None:
        models = [
            {"name": m["name"], "science": m["science_score"], "post_training": m["post_training_score"], "literature": m["literature_score"]}
            for m in EMBEDDED_MODELS
        ]
        res = audit_weight_sensitivity_simplex(models)
        # Conservation law: sum of #1 fractions over Delta_2 == 1
        self.assertEqual(res["winner_fraction_sum_exact"], "1/1")
        self.assertEqual(res["positive_winner_models"], ["Opus 5.5", "GPT-6 Astra"])
        self.assertEqual(res["baseline_ranking"][0], "Opus 5.5")
        self.assertEqual(res["baseline_ranking"][1], "GPT-6 Astra")
        # Only 2-model boundary test (exactly 2 models must pass)
        res2 = audit_weight_sensitivity_simplex(models[:2])
        self.assertEqual(res2["winner_fraction_sum_exact"], "1/1")
        with self.assertRaises(IndexOracleError) as cm_few:
            audit_weight_sensitivity_simplex(models[:1])
        self.assertEqual(cm_few.exception.code, "TOO_FEW_MODELS")
        with self.assertRaises(IndexOracleError) as cm_dup:
            audit_weight_sensitivity_simplex([models[0], models[0]])
        self.assertEqual(cm_dup.exception.code, "DUPLICATE_MODEL")


class TestParetoAndCISeparability(unittest.TestCase):
    def test_pareto_and_refusals(self) -> None:
        entries = [
            {"name": "A", "cost": "10", "score": "0.5"},
            {"name": "B", "cost": "10", "score": "0.6"},  # tied cost, higher score
            {"name": "C", "cost": "20", "score": "0.55"},  # dominated
            {"name": "D", "cost": "30", "score": "0.8"},
        ]
        f = compute_pareto_frontier_exact(entries)
        self.assertEqual([x["name"] for x in f], ["B", "D"])
        with self.assertRaises(IndexOracleError) as cm_e:
            compute_pareto_frontier_exact([])
        self.assertEqual(cm_e.exception.code, "EMPTY_ENTRIES")
        with self.assertRaises(IndexOracleError) as cm_d:
            compute_pareto_frontier_exact([entries[0], entries[0]])
        self.assertEqual(cm_d.exception.code, "DUPLICATE_ENTRY")
        with self.assertRaises(IndexOracleError) as cm_c:
            compute_pareto_frontier_exact([{"name": "Z", "cost": "0", "score": "0.5"}])
        self.assertEqual(cm_c.exception.code, "NON_POSITIVE_COST")

    def test_ci_audit_live_and_refusals(self) -> None:
        ci_entries = [
            {"name": m["name"], "cost": m["full_usd"], "score": m["index_score"], "ci_lo": m["index_lo"], "ci_hi": m["index_hi"]}
            for m in EMBEDDED_MODELS
        ]
        res = audit_ci_separability_and_pareto_stability(ci_entries)
        self.assertEqual(res["total_pairs"], 28)
        self.assertEqual(res["overlapping_pair_count"], 9)
        self.assertEqual(
            res["largest_contiguous_rank_ci_clique"],
            ["GPT-6 Astra", "GPT-6.1 Sol", "Gemini 4 Argon", "Fable 5.1"],
        )
        self.assertEqual(res["headline_pareto_frontier"], ["DeepSeek V4.1 Flash", "GPT-6.1 Sol", "Opus 5.5"])
        self.assertEqual(len(res["pareto_ci_fragilities"]), 1)
        self.assertEqual(res["pareto_ci_fragilities"][0]["cheaper_model"], "GPT-6.1 Sol")
        self.assertEqual(res["pareto_ci_fragilities"][0]["pricier_model"], "Opus 5.5")
        self.assertEqual(res["smallest_clean_separation"]["gap_dec"], "0.0004")

        # Boundary tests: exactly 2 entries with exact ci_lo == score == ci_hi must PASS
        exact_pt = [
            {"name": "P1", "cost": "1", "score": "0.5", "ci_lo": "0.5", "ci_hi": "0.5"},
            {"name": "P2", "cost": "2", "score": "0.6", "ci_lo": "0.6", "ci_hi": "0.6"},
        ]
        res_pt = audit_ci_separability_and_pareto_stability(exact_pt)
        self.assertEqual(res_pt["overlapping_pair_count"], 0)

        # Refusals
        with self.assertRaises(IndexOracleError) as cm1:
            audit_ci_separability_and_pareto_stability(exact_pt[:1])
        self.assertEqual(cm1.exception.code, "TOO_FEW_CI_ENTRIES")
        with self.assertRaises(IndexOracleError) as cm2:
            audit_ci_separability_and_pareto_stability([exact_pt[0], exact_pt[0]])
        self.assertEqual(cm2.exception.code, "DUPLICATE_CI_ENTRY")
        with self.assertRaises(IndexOracleError) as cm3:
            audit_ci_separability_and_pareto_stability(
                [{"name": "Z", "cost": "0", "score": "0.5", "ci_lo": "0.5", "ci_hi": "0.5"}, exact_pt[1]]
            )
        self.assertEqual(cm3.exception.code, "NON_POSITIVE_CI_COST")
        with self.assertRaises(IndexOracleError) as cm4:
            audit_ci_separability_and_pareto_stability(
                [{"name": "B1", "cost": "1", "score": "0.5", "ci_lo": "0.6", "ci_hi": "0.7"}, exact_pt[1]]
            )
        self.assertEqual(cm4.exception.code, "CI_LO_GT_SCORE")
        with self.assertRaises(IndexOracleError) as cm5:
            audit_ci_separability_and_pareto_stability(
                [{"name": "B2", "cost": "1", "score": "0.5", "ci_lo": "0.3", "ci_hi": "0.4"}, exact_pt[1]]
            )
        self.assertEqual(cm5.exception.code, "CI_HI_LT_SCORE")


class TestBipartiteConfounding(unittest.TestCase):
    def test_published_confounding_and_2_bridge_recovery(self) -> None:
        obs = [(m["name"], m["harness"]) for m in EMBEDDED_MODELS]
        pub = audit_bipartite_confounding_exact(obs)
        self.assertEqual(pub["design_rank"], 8)
        self.assertEqual(pub["nullspace_dim"], 3)
        self.assertEqual(pub["min_bridge_cells_needed"], 2)
        self.assertFalse(pub["fully_identifiable_cross_harness"])
        self.assertEqual(pub["identifiable_model_pair_count"], 8)
        self.assertEqual(pub["unidentifiable_model_pair_count"], 20)
        self.assertEqual(pub["identifiable_harness_pair_count"], 0)
        self.assertEqual(pub["unidentifiable_harness_pair_count"], 3)

        bridged = audit_bipartite_confounding_exact(obs + [("Opus 5.5", "OpenCode"), ("GPT-6 Astra", "OpenCode")])
        self.assertEqual(bridged["design_rank"], 10)
        self.assertEqual(bridged["nullspace_dim"], 1)
        self.assertEqual(bridged["min_bridge_cells_needed"], 0)
        self.assertTrue(bridged["fully_identifiable_cross_harness"])
        self.assertEqual(bridged["identifiable_model_pair_count"], 28)
        self.assertEqual(bridged["unidentifiable_model_pair_count"], 0)
        self.assertEqual(bridged["identifiable_harness_pair_count"], 3)

    def test_bipartite_refusals(self) -> None:
        with self.assertRaises(IndexOracleError) as cm1:
            audit_bipartite_confounding_exact([])
        self.assertEqual(cm1.exception.code, "EMPTY_OBSERVATIONS")
        with self.assertRaises(IndexOracleError) as cm2:
            audit_bipartite_confounding_exact([("M1",)])  # type: ignore[list-item]
        self.assertEqual(cm2.exception.code, "INVALID_OBS_PAIR")
        with self.assertRaises(IndexOracleError) as cm3:
            audit_bipartite_confounding_exact([("M1", "H1"), ("M1", "H1")])
        self.assertEqual(cm3.exception.code, "DUPLICATE_OBSERVATION")


class TestMissingAttemptsAudit(unittest.TestCase):
    def test_fable_missing_and_refusals(self) -> None:
        res = audit_missing_attempts_and_cost_extrapolation(
            completed_attempts=74,
            full_attempts=87,
            observed_index_score="0.5107",
            reported_full_cost="1738.7",
            reported_per_attempt_cost="20.07",
            track_attempt_counts=(60, 18, 9),
            track_per_attempt_costs=("23.3", "13.36", "11.15"),
        )
        self.assertEqual(res["missing_attempts"], 13)
        self.assertEqual(res["reconstructed_full_pass_cost_dec"], "1738.83")
        self.assertEqual(res["actual_completed_spend_estimate_dec"], "1485.18")
        self.assertEqual(res["cost_extrapolation_gap_dec"], "253.52")
        self.assertEqual(res["single_track_worst_case_delta_exact"]["science"], "13/150")
        self.assertEqual(res["single_track_worst_case_delta_exact"]["post_training"], "13/45")
        self.assertEqual(res["single_track_worst_case_delta_exact"]["literature"], "1/5")

        with self.assertRaises(IndexOracleError) as cm_len1:
            audit_missing_attempts_and_cost_extrapolation(10, 10, "0.5", "10", "1", (5, 5), ("1", "1", "1"))
        self.assertEqual(cm_len1.exception.code, "TRACK_LENGTH_INVALID")
        with self.assertRaises(IndexOracleError) as cm_len2:
            audit_missing_attempts_and_cost_extrapolation(10, 10, "0.5", "10", "1", (5, 3, 2), ("1", "1"))
        self.assertEqual(cm_len2.exception.code, "TRACK_LENGTH_INVALID")
        with self.assertRaises(IndexOracleError) as cm_len3:
            audit_missing_attempts_and_cost_extrapolation(
                10, 10, "0.5", "10", "1", (5, 3, 2), ("1", "1", "1"), track_weights=(Fraction(1, 2), Fraction(1, 2))
            )
        self.assertEqual(cm_len3.exception.code, "TRACK_LENGTH_INVALID")
        with self.assertRaises(IndexOracleError) as cm_sum:
            audit_missing_attempts_and_cost_extrapolation(10, 10, "0.5", "10", "1", (5, 3, 1), ("1", "1", "1"))
        self.assertEqual(cm_sum.exception.code, "TRACK_COUNT_SUM_MISMATCH")
        with self.assertRaises(IndexOracleError) as cm_w:
            audit_missing_attempts_and_cost_extrapolation(
                10, 10, "0.5", "10", "1", (5, 3, 2), ("1", "1", "1"),
                track_weights=(Fraction(1, 2), Fraction(1, 2), Fraction(1, 2)),
            )
        self.assertEqual(cm_w.exception.code, "MISSING_AUDIT_WEIGHT_SUM")


class TestTaoObservabilityGate(unittest.TestCase):
    def _good_receipt(self) -> dict[str, object]:
        return {
            "frozen_contract_sha256": "0123456789abcdef" * 4,
            "split_leakage_count": 0,
            "internet_contamination_audit": VERIFIED_INTERNET_STATUS,
            "goodhart_kl_delta_bps": 500,  # exact boundary == max_kl_delta_bps must PASS
            "max_kl_delta_bps": 500,
            "r4_isolated_parity_runs": 3,  # exact boundary == 3 must PASS
            "r5_mutation_killed": 1,       # exact boundary == total == 1 must PASS
            "r5_mutation_total": 1,
        }

    def test_pass_exact_boundaries(self) -> None:
        res = evaluate_tao_observability_gate("0.6183", self._good_receipt())
        self.assertEqual(res["verdict"], "PROMOTED")
        self.assertTrue(res["admissible"])
        self.assertEqual(res["process_gates_passed"], 5)
        self.assertEqual(res["observable_adjusted_score_exact"], "6183/10000")

    def test_schema_refusals(self) -> None:
        with self.assertRaises(IndexOracleError) as cm_t:
            evaluate_tao_observability_gate("0.5", ["not", "a", "mapping"])  # type: ignore[arg-type]
        self.assertEqual(cm_t.exception.code, "INVALID_RECEIPT_TYPE")
        bad_extra = self._good_receipt()
        bad_extra["extra_key"] = 1
        with self.assertRaises(IndexOracleError) as cm_k:
            evaluate_tao_observability_gate("0.5", bad_extra)
        self.assertEqual(cm_k.exception.code, "RECEIPT_KEY_MISMATCH")

    def test_each_individual_gate_rejection(self) -> None:
        # G1 non-str and bad hex (including trailing newline!)
        for bad_sha in (123, "a" * 63, ("a" * 64) + "\n", "A" * 64):
            r = self._good_receipt()
            r["frozen_contract_sha256"] = bad_sha
            out = evaluate_tao_observability_gate("0.65", r)
            self.assertEqual(out["verdict"], "REJECTED_BLACK_BOX")
            self.assertEqual(out["failed_gates"], ["G1_FROZEN_CONTRACT_MISSING"])
            self.assertEqual(out["observable_adjusted_score_exact"], "0/1")

        # G2 split leakage == 1
        r2 = self._good_receipt()
        r2["split_leakage_count"] = 1
        out2 = evaluate_tao_observability_gate("0.65", r2)
        self.assertEqual(out2["failed_gates"], ["G2_SPLIT_LEAKAGE_DETECTED"])

        # G3 internet audit non-str and wrong str
        for bad_net in (None, "UNRESTRICTED_4H_INTERNET"):
            r3 = self._good_receipt()
            r3["internet_contamination_audit"] = bad_net
            out3 = evaluate_tao_observability_gate("0.65", r3)
            self.assertEqual(out3["failed_gates"], ["G3_UNAUDITED_INTERNET_ACCESS"])

        # G4 KL delta strictly above max (501 > 500)
        r4 = self._good_receipt()
        r4["goodhart_kl_delta_bps"] = 501
        out4 = evaluate_tao_observability_gate("0.65", r4)
        self.assertEqual(out4["failed_gates"], ["G4_GOODHART_KL_EXCEEDED"])

        # G5a r4_isolated_parity_runs == 2 (< 3)
        r5a = self._good_receipt()
        r5a["r4_isolated_parity_runs"] = 2
        self.assertEqual(evaluate_tao_observability_gate("0.65", r5a)["failed_gates"], ["G5A_R4_PARITY_BELOW_3"])

        # G5b r5_mutation_total == 0
        r5b = self._good_receipt()
        r5b["r5_mutation_total"] = 0
        r5b["r5_mutation_killed"] = 0
        self.assertEqual(evaluate_tao_observability_gate("0.65", r5b)["failed_gates"], ["G5B_R5_MUTATION_TOTAL_ZERO"])

        # G5c r5_mutation_killed < r5_mutation_total
        r5c = self._good_receipt()
        r5c["r5_mutation_total"] = 10
        r5c["r5_mutation_killed"] = 9
        self.assertEqual(evaluate_tao_observability_gate("0.65", r5c)["failed_gates"], ["G5C_R5_MUTATION_INCOMPLETE"])


class TestAuditParserAndRepoProvenanceR5(unittest.TestCase):
    @staticmethod
    def _synth_rt_js(models: list[dict[str, object]]) -> str:
        parts: list[str] = []
        for m in models:
            parts.append(
                f"{{model:`{m['name']}`,logo:h,harness:`{m['harness']}`,attempts:{m['attempts']},"
                f"score:{{mean:{m['index_score']},se:{m['index_se']}}},"
                f"cost:{{mean:{m['cost_mean']},se:{m['cost_se']}}},"
                f"inputTokens:{{mean:{m['input_tokens_mean']},se:100}},"
                f"outputTokens:{{mean:{m['output_tokens_mean']},se:10}},"
                f"minutes:{{mean:{m['minutes_mean']},se:1.0}}}}"
            )
        return "[" + ",".join(parts) + "]"

    @staticmethod
    def _synth_cs_js(models: list[dict[str, object]]) -> str:
        parts: list[str] = []
        for m in models:
            comp = "0" if m["complete"] else "1"
            parts.append(
                f"{{name:`{m['name']}`,color:`#000`,shape:`circle`,complete:!{comp},"
                f"index:{{score:{m['index_score']},lo:{m['index_lo']},hi:{m['index_hi']},usd:{m['full_usd']}}},"
                f"science:{{score:{m['science_score']},usd:{m['science_usd']}}},"
                f"postTraining:{{score:{m['post_training_score']},usd:{m['post_training_usd']}}},"
                f"literature:{{score:{m['literature_score']},usd:{m['literature_usd']}}}}}"
            )
        return "[" + ",".join(parts) + "]"

    @staticmethod
    def _synth_rh_js(rows: dict[str, list[str]]) -> str:
        parts: list[str] = []
        for lbl, scores in rows.items():
            parts.append(f"{{label:`{lbl}`,scores:[{','.join(scores)}],ranks:[1,2,3,4,5,6,7,8]}}")
        return "[" + ",".join(parts) + "]"

    @staticmethod
    def _synth_html() -> str:
        return (
            '<meta property="og:image" content="https://www.alphaxiv.org/assets/blog/'
            'introducing-openresearch-intelligence-index/cost-vs-score.png"/>'
            '<meta name="twitter:image" content="https://www.alphaxiv.org/assets/blog/'
            'introducing-openresearch-intelligence-index/cost-vs-score.png"/>'
            "learned almost nothing mathematically Its source code is coming soon"
        )

    @staticmethod
    def _populate_repo_files(repo_dir: Path) -> None:
        (repo_dir / "SKILL.md").write_text(
            "The run command *and* the environment are a fixed contract", encoding="utf-8"
        )
        (repo_dir / "src" / "commands").mkdir(parents=True, exist_ok=True)
        (repo_dir / "src" / "local").mkdir(parents=True, exist_ok=True)
        (repo_dir / "src" / "commands" / "create_experiment.rs").write_text(
            "run_command: args.run_command", encoding="utf-8"
        )
        (repo_dir / "src" / "local" / "experiments.rs").write_text(
            "let run_command = run_command", encoding="utf-8"
        )
        (repo_dir / "src" / "commands" / "metrics.rs").write_text(
            "It logs only if the code calls trackio.init", encoding="utf-8"
        )

    def test_verify_pinned_artifact_digests_pass_and_refusals(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            f1 = root / "a.txt"
            payload = b"exact-pinned-bytes"
            f1.write_bytes(payload)
            digest = hashlib.sha256(payload).hexdigest()

            ok = verify_pinned_artifact_digests(root, {"a.txt": digest})
            self.assertEqual(ok, {"a.txt": digest})

            with self.assertRaises(IndexOracleError) as cm_miss:
                verify_pinned_artifact_digests(root, {"missing.txt": digest})
            self.assertEqual(cm_miss.exception.code, "MISSING_PINNED_FILE")

            with self.assertRaises(IndexOracleError) as cm_bad:
                verify_pinned_artifact_digests(root, {"a.txt": "0" * 64})
            self.assertEqual(cm_bad.exception.code, "SHA256_MISMATCH")

    def test_parse_blog_bundle_texts_pass_and_all_refusals(self) -> None:
        rt_ok = self._synth_rt_js(EMBEDDED_MODELS)
        cs_ok = self._synth_cs_js(EMBEDDED_MODELS)
        rh_ok = self._synth_rh_js(EMBEDDED_HEATMAP_ROWS)
        html_ok = self._synth_html()

        models, hmap, flags = parse_blog_bundle_texts(rt_ok, cs_ok, rh_ok, html_ok)
        self.assertEqual(models, EMBEDDED_MODELS)
        self.assertEqual(hmap, EMBEDDED_HEATMAP_ROWS)
        self.assertTrue(all(flags.values()))

        # 1. ResultsTable row count != 8
        with self.assertRaises(IndexOracleError) as cm_rt:
            parse_blog_bundle_texts(self._synth_rt_js(EMBEDDED_MODELS[:-1]), cs_ok, rh_ok, html_ok)
        self.assertEqual(cm_rt.exception.code, "PARSE_RT_COUNT")

        # 2. CostScoreChart model name missing from ResultsTable
        bad_name_models = [dict(m) for m in EMBEDDED_MODELS]
        bad_name_models[0]["name"] = "Unknown Model"
        with self.assertRaises(IndexOracleError) as cm_nm:
            parse_blog_bundle_texts(rt_ok, self._synth_cs_js(bad_name_models), rh_ok, html_ok)
        self.assertEqual(cm_nm.exception.code, "PARSE_NAME_MISMATCH")

        # 3. Cross-bundle index score drift between ResultsTable and CostScoreChart
        bad_score_models = [dict(m) for m in EMBEDDED_MODELS]
        bad_score_models[0]["index_score"] = "0.9999"
        with self.assertRaises(IndexOracleError) as cm_sc:
            parse_blog_bundle_texts(rt_ok, self._synth_cs_js(bad_score_models), rh_ok, html_ok)
        self.assertEqual(cm_sc.exception.code, "CROSS_BUNDLE_SCORE_DRIFT")

        # 4. CostScoreChart row count != 8
        with self.assertRaises(IndexOracleError) as cm_cs:
            parse_blog_bundle_texts(rt_ok, self._synth_cs_js(EMBEDDED_MODELS[:-1]), rh_ok, html_ok)
        self.assertEqual(cm_cs.exception.code, "PARSE_CS_COUNT")

        # 5. RankHeatmap row count mismatch
        short_rh = {k: v for i, (k, v) in enumerate(EMBEDDED_HEATMAP_ROWS.items()) if i > 0}
        with self.assertRaises(IndexOracleError) as cm_rh:
            parse_blog_bundle_texts(rt_ok, cs_ok, self._synth_rh_js(short_rh), html_ok)
        self.assertEqual(cm_rh.exception.code, "PARSE_RH_COUNT")

        # 6. Embedded model drift (e.g. full_usd changed while index_score & row counts stay valid)
        drift_models = [dict(m) for m in EMBEDDED_MODELS]
        drift_models[0]["full_usd"] = "9999.9"
        with self.assertRaises(IndexOracleError) as cm_md:
            parse_blog_bundle_texts(rt_ok, self._synth_cs_js(drift_models), rh_ok, html_ok)
        self.assertEqual(cm_md.exception.code, "EMBEDDED_MODEL_DRIFT")

        # 7. Embedded heatmap drift (value changed while row count stays valid)
        drift_rh = {k: list(v) for k, v in EMBEDDED_HEATMAP_ROWS.items()}
        drift_rh["Navigational"][0] = "0.111"
        with self.assertRaises(IndexOracleError) as cm_hd:
            parse_blog_bundle_texts(rt_ok, cs_ok, self._synth_rh_js(drift_rh), html_ok)
        self.assertEqual(cm_hd.exception.code, "EMBEDDED_HEATMAP_DRIFT")

    def test_audit_openresearch_repo_readonly_head_and_file_guards(self) -> None:
        # 1. Valid detached HEAD
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / ".git").mkdir()
            (root / ".git" / "HEAD").write_text(PINNED_OPENRESEARCH_COMMIT + "\n", encoding="utf-8")
            self._populate_repo_files(root)
            res = _audit_openresearch_repo_readonly(root)
            self.assertEqual(res["pinned_commit_sha"], PINNED_OPENRESEARCH_COMMIT)
            self.assertTrue(res["head_ref_verified"])
            self.assertTrue(res["create_experiment_cli_allows_run_command_override"])

        # 2. Valid symbolic ref -> loose ref file
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / ".git" / "refs" / "heads").mkdir(parents=True)
            (root / ".git" / "HEAD").write_text("ref: refs/heads/main\n", encoding="utf-8")
            (root / ".git" / "refs" / "heads" / "main").write_text(PINNED_OPENRESEARCH_COMMIT + "\n", encoding="utf-8")
            self._populate_repo_files(root)
            self.assertEqual(_audit_openresearch_repo_readonly(root)["pinned_commit_sha"], PINNED_OPENRESEARCH_COMMIT)

        # 3. Valid symbolic ref -> packed-refs fallback
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / ".git").mkdir()
            (root / ".git" / "HEAD").write_text("ref: refs/heads/main\n", encoding="utf-8")
            (root / ".git" / "packed-refs").write_text(
                f"# pack-refs\n{PINNED_OPENRESEARCH_COMMIT} refs/heads/main\n^0000000000000000000000000000000000000000\n",
                encoding="utf-8",
            )
            self._populate_repo_files(root)
            self.assertEqual(_audit_openresearch_repo_readonly(root)["pinned_commit_sha"], PINNED_OPENRESEARCH_COMMIT)

        # 4. Missing .git/HEAD
        with tempfile.TemporaryDirectory() as td:
            with self.assertRaises(IndexOracleError) as cm_miss:
                _audit_openresearch_repo_readonly(Path(td))
            self.assertEqual(cm_miss.exception.code, "MISSING_REPO")

        # 5. Unsafe traversal symbolic ref
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / ".git").mkdir()
            (root / ".git" / "HEAD").write_text("ref: ../outside\n", encoding="utf-8")
            with self.assertRaises(IndexOracleError) as cm_inv:
                _audit_openresearch_repo_readonly(root)
            self.assertEqual(cm_inv.exception.code, "INVALID_GIT_REF")

        # 6. Missing symbolic ref target (neither loose nor packed)
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / ".git").mkdir()
            (root / ".git" / "HEAD").write_text("ref: refs/heads/missing\n", encoding="utf-8")
            with self.assertRaises(IndexOracleError) as cm_mref:
                _audit_openresearch_repo_readonly(root)
            self.assertEqual(cm_mref.exception.code, "MISSING_GIT_REF")

        # 7. Detached HEAD wrong commit SHA (verifier repro: "0"*40)
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / ".git").mkdir()
            (root / ".git" / "HEAD").write_text(("0" * 40) + "\n", encoding="utf-8")
            self._populate_repo_files(root)
            with self.assertRaises(IndexOracleError) as cm_det:
                _audit_openresearch_repo_readonly(root)
            self.assertEqual(cm_det.exception.code, "COMMIT_MISMATCH")

        # 8. Symbolic ref wrong commit SHA
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / ".git" / "refs" / "heads").mkdir(parents=True)
            (root / ".git" / "HEAD").write_text("ref: refs/heads/main\n", encoding="utf-8")
            (root / ".git" / "refs" / "heads" / "main").write_text(("f" * 40) + "\n", encoding="utf-8")
            self._populate_repo_files(root)
            with self.assertRaises(IndexOracleError) as cm_sym:
                _audit_openresearch_repo_readonly(root)
            self.assertEqual(cm_sym.exception.code, "COMMIT_MISMATCH")

        # 9. Valid HEAD but missing required source file
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / ".git").mkdir()
            (root / ".git" / "HEAD").write_text(PINNED_OPENRESEARCH_COMMIT + "\n", encoding="utf-8")
            self._populate_repo_files(root)
            (root / "SKILL.md").unlink()
            with self.assertRaises(IndexOracleError) as cm_file:
                _audit_openresearch_repo_readonly(root)
            self.assertEqual(cm_file.exception.code, "MISSING_REPO_FILE")


class TestCertificateEndToEnd(unittest.TestCase):
    def test_standalone_certificate_exact_invariants(self) -> None:
        cert = build_certificate(
            models=EMBEDDED_MODELS,
            heatmap_rows=EMBEDDED_HEATMAP_ROWS,
            mode="standalone",
            verified_digests=None,
            html_flags=None,
            openresearch_audit=None,
        )
        verify_no_floats(cert)
        body = cert["certificate"]
        self.assertEqual(body["fable_missing_attempts_audit"]["exact_fable_science_rational"], "41/120")
        self.assertTrue(body["fable_missing_attempts_audit"]["matches_published_0_3417"])
        self.assertEqual(body["bipartite_confounding_published"]["nullspace_dim"], 3)
        self.assertEqual(body["bipartite_confounding_with_2_opencode_bridges"]["nullspace_dim"], 1)
        self.assertEqual(body["subtask_coverage_and_saturation"]["literature_navigational_rank1_model"], "Qwen3.8-Flash")


if __name__ == "__main__":
    unittest.main(verbosity=1)
