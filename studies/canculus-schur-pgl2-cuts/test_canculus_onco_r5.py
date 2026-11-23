#!/usr/bin/env python3
"""
R5 Refusal-Site Mutation Test Suite for canculus_onco_bridge.py (AUDIT-050).
Pure unittest stdlib, zero bare asserts; tests every refusal guard, boundary condition,
and algebraic invariant across all 4 parts.
"""
from __future__ import annotations

from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import canculus_onco_bridge as mod  # noqa: E402


class TestCanculusNormalFormAndClosure(unittest.TestCase):
    def test_route_idempotence_delimiter_and_refusals(self) -> None:
        self.assertEqual(mod.make_route(["B", "B"]), mod.make_route(["B"]))
        self.assertNotEqual(mod.make_route(["A+B"]), mod.make_route(["A", "B"]))
        with self.assertRaisesRegex(TypeError, "iterable collection"):
            mod.make_route("B")  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "non-empty str"):
            mod.make_route(["B", "   "])
        with self.assertRaisesRegex(ValueError, "non-empty str"):
            mod.make_route([123])  # type: ignore[list-item]

    def test_transversals_coverage_and_closure_refusals(self) -> None:
        self.assertEqual(mod.minimal_transversals([frozenset()], ["A", "B"]), [])
        with self.assertRaisesRegex(ValueError, "non-empty"):
            mod.minimal_transversals([mod.make_route(["A"])], [])
        with self.assertRaisesRegex(ValueError, "non-empty"):
            mod.rules_encoded_exact([], [], {})
        # Exact boundary |V| == 12 allowed; |V| == 13 refused
        self.assertEqual(mod.rules_encoded_exact([], [f"c{i}" for i in range(12)], {}), [])
        with self.assertRaisesRegex(ValueError, r"\|V\| <= 12"):
            mod.rules_encoded_exact([], [f"c{i}" for i in range(13)], {})
        with self.assertRaisesRegex(ValueError, "non-empty"):
            mod.semantic_adaptation_closure([], [], frozenset(), {}, [])
        with self.assertRaisesRegex(ValueError, "non-empty"):
            mod.minimal_robust_cuts_exact([], [], {}, [])


class TestSchurPgl2FeedbackAndTropical(unittest.TestCase):
    def test_schur_feedback_alpha_crit_and_cross_ratio(self) -> None:
        # Exact zero boundary accepted; negative rejected
        z = mod.solve_feedback_schur_exact(Fraction(0), Fraction(0), Fraction(0), Fraction(0))
        self.assertTrue(z["conservation_residual_zero"])
        for bad in (
            (Fraction(-1), Fraction(1), Fraction(1), Fraction(1)),
            (Fraction(0), Fraction(-1), Fraction(1), Fraction(1)),
            (Fraction(0), Fraction(1), Fraction(-1), Fraction(1)),
            (Fraction(0), Fraction(1), Fraction(1), Fraction(-1)),
        ):
            with self.assertRaisesRegex(ValueError, "non-negative"):
                mod.solve_feedback_schur_exact(*bad)

        # alpha_crit regimes: never (u < theta), always (u == theta*(1+gh), g*h == 0), intermediate
        self.assertEqual(mod.alpha_crit_exact(Fraction(1, 2), Fraction(3), Fraction(2), Fraction(3, 5))["regime"], "never")
        self.assertEqual(mod.alpha_crit_exact(Fraction(7), Fraction(3), Fraction(2), Fraction(1))["regime"], "always")
        self.assertEqual(mod.alpha_crit_exact(Fraction(1), Fraction(0), Fraction(2), Fraction(1))["regime"], "always")
        inter = mod.alpha_crit_exact(Fraction(1), Fraction(3), Fraction(3), Fraction(3, 10))
        self.assertEqual(inter["regime"], "intermediate")
        self.assertEqual(inter["alpha_crit"], "7/27")
        with self.assertRaisesRegex(ValueError, "strictly positive"):
            mod.alpha_crit_exact(Fraction(1), Fraction(1), Fraction(1), Fraction(0))
        with self.assertRaisesRegex(ValueError, "non-negative"):
            mod.alpha_crit_exact(Fraction(-1), Fraction(1), Fraction(1), Fraction(1))

        with self.assertRaisesRegex(ValueError, "degenerate cross-ratio"):
            mod.cross_ratio_exact(Fraction(1), Fraction(2), Fraction(3), Fraction(1))

    def test_tropical_timed_closure_refusals(self) -> None:
        neg_rule = mod.AdaptationRule(
            rule_id="neg",
            prereq_routes=(),
            guard=lambda U, c: True,
            guard_label="always",
            consequences=(mod.make_route(["X"]),),
            delay=Fraction(-1),
            level="L0",
        )
        with self.assertRaisesRegex(ValueError, "negative delay"):
            mod.earliest_activation_times_exact([], [neg_rule], frozenset(), {})

        # Zero delay & zero horizon boundaries pass; negative horizon refused; empty prereq & unmet prereq exercised
        zero_rule = mod.AdaptationRule(
            rule_id="zero_d",
            prereq_routes=(),
            guard=lambda U, c: True,
            guard_label="always",
            consequences=(mod.make_route(["X"]),),
            delay=Fraction(0),
            level="L0",
        )
        unmet_rule = mod.AdaptationRule(
            rule_id="unmet",
            prereq_routes=(mod.make_route(["MISSING"]),),
            guard=lambda U, c: True,
            guard_label="always",
            consequences=(mod.make_route(["Y"]),),
            delay=Fraction(1),
            level="L0",
        )
        self.assertFalse(mod.robust_at_horizon_exact([], [zero_rule, unmet_rule], frozenset(), {}, Fraction(0)))
        self.assertTrue(mod.robust_at_horizon_exact([], [zero_rule, unmet_rule], mod.make_route(["X"]), {}, Fraction(0)))
        with self.assertRaisesRegex(ValueError, "non-negative"):
            mod.robust_at_horizon_exact([], [], frozenset(), {}, Fraction(-1))


class TestOnCoEpistemicGraphGates(unittest.TestCase):
    def test_graph_validator_refusals(self) -> None:
        base = {"id": "a-1", "kind": "drug", "asOf": "2026-11-21", "links": [{"label": "src", "url": "https://x.org"}]}
        with self.assertRaisesRegex(ValueError, "non-empty"):
            mod.validate_cited_epistemic_graph([])
        with self.assertRaisesRegex(ValueError, "kebab-case"):
            mod.validate_cited_epistemic_graph([{**base, "id": "Bad_ID"}])
        with self.assertRaisesRegex(ValueError, "duplicate entity id"):
            mod.validate_cited_epistemic_graph([base, base])
        with self.assertRaisesRegex(ValueError, "missing kind"):
            mod.validate_cited_epistemic_graph([{**base, "kind": ""}])
        with self.assertRaisesRegex(ValueError, "invalid ISO asOf"):
            mod.validate_cited_epistemic_graph([{**base, "asOf": "2026/11/21"}])
        with self.assertRaisesRegex(ValueError, "mandatory primary source"):
            mod.validate_cited_epistemic_graph([{**base, "links": []}])
        with self.assertRaisesRegex(ValueError, "must be a list"):
            mod.validate_cited_epistemic_graph([{**base, "cancers": "crc"}])
        with self.assertRaisesRegex(ValueError, "dangling reference"):
            mod.validate_cited_epistemic_graph([{**base, "cancers": ["missing"]}])
        # Self-link allowed (not added as backlink)
        self_ok = mod.validate_cited_epistemic_graph([{**base, "drugs": ["a-1"]}])
        self.assertTrue(self_ok["valid"])
        self.assertEqual(self_ok["backlink_count"], 0)

    def test_change_classifier_and_deep_compare(self) -> None:
        c_prod = mod.classify_change_semantic(["src/lib/graph.ts"])
        self.assertTrue(c_prod["requires_owner_approval"])
        with self.assertRaisesRegex(ValueError, "non-empty"):
            mod.classify_change_semantic([])
        with self.assertRaisesRegex(ValueError, "non-empty str"):
            mod.classify_change_semantic(["   "])

        self.assertTrue(mod.deep_compare_records({"a": 1}, {"a": 1})["identical"])
        self.assertFalse(mod.deep_compare_records({"a": None}, {})["identical"])
        with self.assertRaisesRegex(TypeError, "must be dicts"):
            mod.deep_compare_records([], {})  # type: ignore[arg-type]

    def test_main_entrypoint(self) -> None:
        rep = mod.run_full_bridge_matrix()
        p1 = rep["part_1_canculus_normal_form_and_closure"]
        self.assertTrue(p1["demorgan_involution_Tr_Tr_M_eq_M"])
        self.assertEqual(p1["demorgan_involution_tested_hypergraphs"], 2)
        cert_path = HERE / "canculus_onco_results.json"
        self.assertTrue(cert_path.is_file())
        raw = json.loads(cert_path.read_text(encoding="utf-8"))
        saved_sha = raw.pop("canonical_sha256")
        recomputed = hashlib.sha256(
            json.dumps(raw, sort_keys=True, separators=(",", ":"), allow_nan=False).encode("utf-8")
        ).hexdigest()
        self.assertEqual(saved_sha, recomputed)
        self.assertEqual(rep["canonical_sha256"], saved_sha)
        self.assertEqual(mod.main(["--json"]), 0)
        self.assertEqual(mod.main([]), 0)


if __name__ == "__main__":
    unittest.main()
