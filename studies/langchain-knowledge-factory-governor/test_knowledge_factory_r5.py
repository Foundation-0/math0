#!/usr/bin/env python3
"""
R5 Refusal-Site & Exact-Invariant Test Suite for BOTH:
  - knowledge_factory_governor.py
  - knowledge_factory_audit.py
(AUDIT-076, Wave 2 Round 8 Arm R8-5).

Zero bare `assert` statements. `-I -O -B -W error` safe.
Targets 100.0% R5 mutation kill (0 survivors) on BOTH modules under `aletheia v1.4.0 mutate --add-cwd`.
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

from knowledge_factory_audit import (  # noqa: E402
    _make_base_policy,
    _make_clean_proposal,
    build_certificate,
    verify_pinned_sources_and_anchors,
)
from knowledge_factory_governor import (  # noqa: E402
    GENESIS_LEDGER_HASH,
    KnowledgeGovernorError,
    LEDGER_SCHEMA,
    VERIFIED_NETWORK_POLICY,
    audit_information_flow_lattice,
    audit_multi_worker_batch_conflicts,
    build_ledger_entry,
    canonical_sha256,
    compute_poisoning_blast_radius_exact,
    detect_skill_graph_cycle_exact,
    evaluate_curator_proposal,
    format_exact_decimal,
    frac_str,
    require_exact_bool,
    require_exact_fraction,
    require_exact_int,
    require_non_empty_str,
    scan_ring0_tamper_keys,
    simulate_goodhart_curator_drift_exact,
    verify_knowledge_ledger_chain,
    verify_no_floats,
)


class TestPrimitivesAndHelpers(unittest.TestCase):
    def test_verify_no_floats(self) -> None:
        verify_no_floats({"k": [1, True, None, "ok", (Fraction(1, 3),)]})
        with self.assertRaises(KnowledgeGovernorError) as cm1:
            verify_no_floats(1.5)
        self.assertEqual(cm1.exception.code, "FLOAT_FORBIDDEN")
        with self.assertRaises(KnowledgeGovernorError) as cm2:
            verify_no_floats({"a": [0, {"b": float("inf")}]})
        self.assertEqual(cm2.exception.code, "FLOAT_FORBIDDEN")
        with self.assertRaises(KnowledgeGovernorError) as cm3:
            verify_no_floats({2.5: "bad"})
        self.assertEqual(cm3.exception.code, "FLOAT_FORBIDDEN")

    def test_require_non_empty_str_and_bool(self) -> None:
        self.assertEqual(require_non_empty_str("abc", "f"), "abc")
        with self.assertRaises(KnowledgeGovernorError) as cm1:
            require_non_empty_str(99, "f")
        self.assertEqual(cm1.exception.code, "INVALID_STR")
        with self.assertRaises(KnowledgeGovernorError) as cm2:
            require_non_empty_str("  \n\t ", "f")
        self.assertEqual(cm2.exception.code, "EMPTY_STR")
        self.assertIs(require_exact_bool(True, "b"), True)
        self.assertIs(require_exact_bool(False, "b"), False)
        with self.assertRaises(KnowledgeGovernorError) as cm3:
            require_exact_bool(1, "b")
        self.assertEqual(cm3.exception.code, "INVALID_BOOL")

    def test_require_exact_int_and_fraction(self) -> None:
        self.assertEqual(require_exact_int(0, "n", 0, 5), 0)
        self.assertEqual(require_exact_int(5, "n", 0, 5), 5)
        with self.assertRaises(KnowledgeGovernorError) as cm_b:
            require_exact_int(True, "n")
        self.assertEqual(cm_b.exception.code, "INVALID_INT")
        with self.assertRaises(KnowledgeGovernorError) as cm_lo:
            require_exact_int(-1, "n", min_value=0)
        self.assertEqual(cm_lo.exception.code, "INT_BELOW_MIN")
        with self.assertRaises(KnowledgeGovernorError) as cm_hi:
            require_exact_int(6, "n", max_value=5)
        self.assertEqual(cm_hi.exception.code, "INT_ABOVE_MAX")

        self.assertEqual(require_exact_fraction(Fraction(0), "q", Fraction(0), Fraction(1)), Fraction(0))
        self.assertEqual(require_exact_fraction(1, "q", Fraction(0), Fraction(1)), Fraction(1))
        self.assertEqual(require_exact_fraction("3/4", "q", Fraction(0), Fraction(1)), Fraction(3, 4))
        self.assertEqual(require_exact_fraction("-0.25", "q"), Fraction(-1, 4))
        with self.assertRaises(KnowledgeGovernorError) as cm_fb:
            require_exact_fraction(False, "q")
        self.assertEqual(cm_fb.exception.code, "BOOL_NOT_FRACTION")
        with self.assertRaises(KnowledgeGovernorError) as cm_ft:
            require_exact_fraction(0.25, "q")
        self.assertEqual(cm_ft.exception.code, "INVALID_FRACTION_TYPE")
        for bad in ("1/0", "0.5\n", ".5", "1e2", "01"):
            with self.assertRaises(KnowledgeGovernorError) as cm_fs:
                require_exact_fraction(bad, "q")
            self.assertEqual(cm_fs.exception.code, "INVALID_FRACTION_STR")
        with self.assertRaises(KnowledgeGovernorError) as cm_flo:
            require_exact_fraction(Fraction(-1, 10), "q", min_value=Fraction(0))
        self.assertEqual(cm_flo.exception.code, "FRACTION_BELOW_MIN")
        with self.assertRaises(KnowledgeGovernorError) as cm_fhi:
            require_exact_fraction(Fraction(11, 10), "q", max_value=Fraction(1))
        self.assertEqual(cm_fhi.exception.code, "FRACTION_ABOVE_MAX")

    def test_formatting_and_ring0_scan(self) -> None:
        self.assertEqual(frac_str(Fraction(4, 8)), "1/2")
        self.assertEqual(format_exact_decimal(Fraction(-5, 2), 0), "-3")
        self.assertEqual(format_exact_decimal(Fraction(1, 8), 4), "0.1250")
        self.assertEqual(len(canonical_sha256({"x": 1})), 64)
        self.assertEqual(scan_ring0_tamper_keys({"safe": [{"ok": 1}]}), [])
        self.assertEqual(
            scan_ring0_tamper_keys(
                {"a": [{"Identity_Policy": "hack", "BYPASS_VERIFIER": True, "secret-proxy-allowlist": ["*"]}]}
            ),
            [
                "patch.a[0].BYPASS_VERIFIER",
                "patch.a[0].Identity_Policy",
                "patch.a[0].secret-proxy-allowlist",
            ],
        )


class TestKF01LatticeAndBlastRadius(unittest.TestCase):
    def test_lattice_exact_boundaries_and_refusals(self) -> None:
        # Exact boundary: min_src_int == req_int (3 == 3) and max_src_conf == max_conf (0 == 0) MUST PASS
        ok = audit_information_flow_lattice(["ADMIN_WHITELIST"], ["PUBLIC_GLOBAL"], "GLOBAL_SKILL", False)
        self.assertTrue(ok["admissible"])
        self.assertEqual(ok["biba_elevation_gap"], 0)
        self.assertEqual(ok["blp_leak_gap"], 0)

        # Biba integrity violation without countersign -> REJECTED
        bad_biba = audit_information_flow_lattice(["SHARED_CHANNEL"], ["PUBLIC_GLOBAL"], "GLOBAL_SKILL", False)
        self.assertFalse(bad_biba["admissible"])
        self.assertEqual(bad_biba["failure_reasons"], ["KF01_BIBA_INTEGRITY_ESCALATION"])
        self.assertEqual(bad_biba["biba_elevation_gap"], 2)

        # Countersign clears Biba elevation if confidentiality still respects tier
        ok_cs = audit_information_flow_lattice(["SHARED_CHANNEL"], ["PUBLIC_GLOBAL"], "GLOBAL_SKILL", True)
        self.assertTrue(ok_cs["admissible"])

        # BLP confidentiality leak REJECTED even with human admin countersign!
        bad_blp = audit_information_flow_lattice(["ADMIN_WHITELIST"], ["USER_PRIVATE_DM"], "GLOBAL_SKILL", True)
        self.assertFalse(bad_blp["admissible"])
        self.assertEqual(bad_blp["failure_reasons"], ["KF01_BLP_CONFIDENTIALITY_LEAK"])
        self.assertEqual(bad_blp["blp_leak_gap"], 2)

        # Schema refusals
        with self.assertRaises(KnowledgeGovernorError) as cm1:
            audit_information_flow_lattice([], ["PUBLIC_GLOBAL"], "GLOBAL_SKILL", False)
        self.assertEqual(cm1.exception.code, "EMPTY_INTEGRITY_SOURCES")
        with self.assertRaises(KnowledgeGovernorError) as cm2:
            audit_information_flow_lattice(["ADMIN_WHITELIST"], [], "GLOBAL_SKILL", False)
        self.assertEqual(cm2.exception.code, "EMPTY_CONF_SOURCES")
        with self.assertRaises(KnowledgeGovernorError) as cm3:
            audit_information_flow_lattice(["ADMIN_WHITELIST"], ["PUBLIC_GLOBAL"], "NO_SUCH_TIER", False)
        self.assertEqual(cm3.exception.code, "UNKNOWN_TARGET_TIER")
        with self.assertRaises(KnowledgeGovernorError) as cm4:
            audit_information_flow_lattice(["BAD_INT"], ["PUBLIC_GLOBAL"], "GLOBAL_SKILL", False)
        self.assertEqual(cm4.exception.code, "UNKNOWN_INTEGRITY_LABEL")
        with self.assertRaises(KnowledgeGovernorError) as cm5:
            audit_information_flow_lattice(["ADMIN_WHITELIST"], ["BAD_CONF"], "GLOBAL_SKILL", False)
        self.assertEqual(cm5.exception.code, "UNKNOWN_CONF_LABEL")

    def test_blast_radius_exact(self) -> None:
        res = compute_poisoning_blast_radius_exact(10, 12, Fraction(1, 20))
        self.assertEqual(res["total_exposures"], 120)
        self.assertEqual(res["expected_compromised_runs_exact"], "6/1")
        expected_prob = Fraction(1) - Fraction(19, 20) ** 120
        self.assertEqual(res["prob_at_least_one_compromise_exact"], frac_str(expected_prob))


class TestKF02GoodhartDrift(unittest.TestCase):
    def test_goodhart_exact_drift_and_refusals(self) -> None:
        res = simulate_goodhart_curator_drift_exact(4, Fraction(1), Fraction(1, 4), Fraction(1, 4), Fraction(1, 2))
        self.assertEqual(res["unverified_curator_accepted_steps"], 4)
        self.assertEqual(res["governor_latch_halt_step"], 1)
        self.assertTrue(res["goodhart_inversion_occurred"])
        # Exact final total err = (3/4)^4 + (1/4 + 2) = 81/256 + 9/4 = 657/256
        self.assertEqual(res["final_unverified_total_err_exact"], "657/256")
        # Zero drift -> no halt
        clean = simulate_goodhart_curator_drift_exact(2, Fraction(1), Fraction(1, 4), Fraction(1, 2), Fraction(0))
        self.assertIsNone(clean["governor_latch_halt_step"])
        self.assertFalse(clean["goodhart_inversion_occurred"])

        with self.assertRaises(KnowledgeGovernorError) as cm1:
            simulate_goodhart_curator_drift_exact(2, Fraction(0), Fraction(1), Fraction(1, 2), Fraction(0))
        self.assertEqual(cm1.exception.code, "ZERO_INITIAL_PROXY")
        with self.assertRaises(KnowledgeGovernorError) as cm2:
            simulate_goodhart_curator_drift_exact(2, Fraction(1), Fraction(1), Fraction(0), Fraction(0))
        self.assertEqual(cm2.exception.code, "ZERO_DECAY_RATE")


class TestKF03CyclesAndBatchConflicts(unittest.TestCase):
    def test_dag_cycle_detection_and_refusal(self) -> None:
        ok = detect_skill_graph_cycle_exact([("a", "b"), ("b", "c")])
        self.assertTrue(ok["acyclic"])
        self.assertEqual(ok["cycle_witness"], [])
        cyc = detect_skill_graph_cycle_exact([("a", "b"), ("b", "c"), ("c", "a")])
        self.assertTrue(cyc["has_cycle"])
        self.assertEqual(cyc["cycle_witness"], ["a", "b", "c", "a"])
        self_loop = detect_skill_graph_cycle_exact([("x", "x")])
        self.assertTrue(self_loop["has_cycle"])
        self.assertEqual(self_loop["cycle_witness"], ["x", "x"])
        # KF-BYPASS-05: whitespace-padded node name MUST NOT evade cycle detection
        ws_cyc = detect_skill_graph_cycle_exact([("revenue_report", "bigquery_fetch"), ("bigquery_fetch", "revenue_report ")])
        self.assertTrue(ws_cyc["has_cycle"])
        self.assertEqual(ws_cyc["cycle_witness"], ["bigquery_fetch", "revenue_report", "bigquery_fetch"])
        with self.assertRaises(KnowledgeGovernorError) as cm_seq:
            detect_skill_graph_cycle_exact("ab")  # type: ignore[arg-type]
        self.assertEqual(cm_seq.exception.code, "INVALID_SEQUENCE_TYPE")
        with self.assertRaises(KnowledgeGovernorError) as cm:
            detect_skill_graph_cycle_exact([("only_one",)])  # type: ignore[list-item]
        self.assertEqual(cm.exception.code, "INVALID_EDGE_ARITY")

    def test_batch_conflicts_and_refusals(self) -> None:
        revs = {"wiki": "1" * 64}
        ok = audit_multi_worker_batch_conflicts(
            [{"proposal_id": "p1", "target_store": "wiki", "domain_key": "k", "base_revision_sha256": "1" * 64, "proposed_value": "v1"}],
            revs,
        )
        self.assertTrue(ok["batch_admissible"])
        bad = audit_multi_worker_batch_conflicts(
            [
                {"proposal_id": "p1", "target_store": "wiki", "domain_key": "k", "base_revision_sha256": "1" * 64, "proposed_value": "v1"},
                {"proposal_id": "p2", "target_store": "wiki", "domain_key": " K ", "base_revision_sha256": "2" * 64, "proposed_value": "v2"},
                {"proposal_id": "p3", "target_store": "unknown", "domain_key": "k2", "base_revision_sha256": "1" * 64, "proposed_value": "v3"},
            ],
            revs,
        )
        self.assertFalse(bad["batch_admissible"])
        self.assertTrue(bad["lww_oscillation_blocked"])
        self.assertEqual(bad["stale_cas_proposals"], ["p2"])
        self.assertEqual(bad["unknown_store_proposals"], ["p3"])

        with self.assertRaises(KnowledgeGovernorError) as cm1:
            audit_multi_worker_batch_conflicts([], revs)
        self.assertEqual(cm1.exception.code, "EMPTY_PROPOSAL_BATCH")
        with self.assertRaises(KnowledgeGovernorError) as cm2:
            audit_multi_worker_batch_conflicts([{"proposal_id": "p1"}], {})
        self.assertEqual(cm2.exception.code, "EMPTY_STORE_REVISIONS")
        with self.assertRaises(KnowledgeGovernorError) as cm3:
            audit_multi_worker_batch_conflicts(["not_a_mapping"], revs)  # type: ignore[list-item]
        self.assertEqual(cm3.exception.code, "INVALID_BATCH_PROPOSAL")
        with self.assertRaises(KnowledgeGovernorError) as cm4:
            audit_multi_worker_batch_conflicts(
                [
                    {"proposal_id": "dup", "target_store": "wiki", "domain_key": "k", "base_revision_sha256": "1" * 64, "proposed_value": "v1"},
                    {"proposal_id": "dup", "target_store": "wiki", "domain_key": "k", "base_revision_sha256": "1" * 64, "proposed_value": "v2"},
                ],
                revs,
            )
        self.assertEqual(cm4.exception.code, "DUPLICATE_PROPOSAL_ID")


class TestMasterGovernorKF01ToKF05(unittest.TestCase):
    def _clean_pair(self) -> tuple[dict[str, object], dict[str, object]]:
        pol = _make_base_policy()
        prop = _make_clean_proposal(pol["expected_store_revisions"]["context_hub_data_access"])
        # Exact boundary values that MUST pass:
        # proxy_err_after == proxy_err_before, outside_err_after == outside_err_before,
        # r4 == 3, r5_killed == r5_total == 1
        prop["proxy_err_after"] = prop["proxy_err_before"]
        prop["outside_err_after"] = prop["outside_err_before"]
        prop["r4_isolated_parity_runs"] = 3
        prop["r5_mutation_total"] = 1
        prop["r5_mutation_killed"] = 1
        return prop, pol

    def test_exact_boundary_promotion_and_schema_refusals(self) -> None:
        prop, pol = self._clean_pair()
        res = evaluate_curator_proposal(prop, pol)
        self.assertEqual(res["verdict"], "PROMOTED")
        self.assertTrue(res["admissible"])
        self.assertEqual(res["failure_reasons"], [])

        # Schema & type refusals
        with self.assertRaises(KnowledgeGovernorError) as cm1:
            evaluate_curator_proposal(["bad"], pol)  # type: ignore[arg-type]
        self.assertEqual(cm1.exception.code, "INVALID_PROPOSAL_TYPE")
        with self.assertRaises(KnowledgeGovernorError) as cm2:
            evaluate_curator_proposal(prop, ["bad"])  # type: ignore[arg-type]
        self.assertEqual(cm2.exception.code, "INVALID_POLICY_TYPE")
        p_extra = dict(prop)
        p_extra["sneaky"] = 1
        with self.assertRaises(KnowledgeGovernorError) as cm3:
            evaluate_curator_proposal(p_extra, pol)
        self.assertEqual(cm3.exception.code, "PROPOSAL_SCHEMA_MISMATCH")
        pol_extra = dict(pol)
        pol_extra["sneaky"] = 1
        with self.assertRaises(KnowledgeGovernorError) as cm4:
            evaluate_curator_proposal(prop, pol_extra)
        self.assertEqual(cm4.exception.code, "POLICY_SCHEMA_MISMATCH")
        p_bad_key = dict(prop)
        p_bad_key["domain_key"] = "bad key\n"
        with self.assertRaises(KnowledgeGovernorError) as cm5:
            evaluate_curator_proposal(p_bad_key, pol)
        self.assertEqual(cm5.exception.code, "INVALID_DOMAIN_KEY")
        pol_empty_rev = dict(pol)
        pol_empty_rev["expected_store_revisions"] = {}
        with self.assertRaises(KnowledgeGovernorError) as cm6:
            evaluate_curator_proposal(prop, pol_empty_rev)
        self.assertEqual(cm6.exception.code, "INVALID_POLICY_REVS")
        p_bad_rev = dict(prop)
        p_bad_rev["base_revision_sha256"] = "not-a-sha"
        with self.assertRaises(KnowledgeGovernorError) as cm7:
            evaluate_curator_proposal(p_bad_rev, pol)
        self.assertEqual(cm7.exception.code, "INVALID_BASE_REV_SHA")
        p_bad_patch = dict(prop)
        p_bad_patch["payload_patch"] = "raw_string_patch"
        with self.assertRaises(KnowledgeGovernorError) as cm8:
            evaluate_curator_proposal(p_bad_patch, pol)
        self.assertEqual(cm8.exception.code, "INVALID_PATCH_TYPE")
        # Red-team: str-as-sequence character-splitting bypass & invalid policy rev/tier schemas
        p_str_scope = dict(prop)
        p_str_scope["requested_scopes"] = "big"
        with self.assertRaises(KnowledgeGovernorError) as cm9:
            evaluate_curator_proposal(p_str_scope, pol)
        self.assertEqual(cm9.exception.code, "INVALID_SEQUENCE_TYPE")
        pol_bad_rev = dict(pol)
        pol_bad_rev["expected_store_revisions"] = {"github_skills": "bad-sha", "context_hub_data_access": "2" * 64, "company_wiki_domain": "3" * 64}
        with self.assertRaises(KnowledgeGovernorError) as cm10:
            evaluate_curator_proposal(prop, pol_bad_rev)
        self.assertEqual(cm10.exception.code, "INVALID_POLICY_REV_SHA")
        pol_bad_tiers = dict(pol)
        pol_bad_tiers["store_tiers"] = {"github_skills": "GLOBAL_SKILL"}
        with self.assertRaises(KnowledgeGovernorError) as cm11:
            evaluate_curator_proposal(prop, pol_bad_tiers)
        self.assertEqual(cm11.exception.code, "INVALID_POLICY_STORE_TIERS")
        pol_unk_tier = dict(pol)
        pol_unk_tier["store_tiers"] = {
            "github_skills": "NO_SUCH_TIER",
            "context_hub_data_access": "DATA_ACCESS_GUIDANCE",
            "company_wiki_domain": "GLOBAL_DOMAIN_KNOWLEDGE",
        }
        with self.assertRaises(KnowledgeGovernorError) as cm12:
            evaluate_curator_proposal(prop, pol_unk_tier)
        self.assertEqual(cm12.exception.code, "UNKNOWN_STORE_TIER")

    def test_every_individual_governor_gate_failure(self) -> None:
        # 1. Curator self-approval (exact + whitespace + case evasion: KF-BYPASS-01)
        for spoof in ("nightly_curator_01", "nightly_curator_01 ", "NIGHTLY_CURATOR_01"):
            p, pol = self._clean_pair()
            p["verifier_id"] = spoof
            self.assertEqual(evaluate_curator_proposal(p, pol)["failure_reasons"], ["KF05_CURATOR_SELF_APPROVAL"])

        # 2. Worker self-approval (exact + whitespace/case evasion: KF-BYPASS-01)
        for spoof in ("gtm_worker_01", " gtm_worker_01", "GTM_WORKER_01"):
            p, pol = self._clean_pair()
            p["verifier_id"] = spoof
            self.assertEqual(evaluate_curator_proposal(p, pol)["failure_reasons"], ["KF05_WORKER_SELF_APPROVAL"])

        # 2b. Worker == Curator collapse
        p, pol = self._clean_pair()
        p["curator_id"] = " GTM_WORKER_01 "
        self.assertEqual(evaluate_curator_proposal(p, pol)["failure_reasons"], ["KF05_WORKER_CURATOR_COLLAPSE"])

        # 3. Ring-0 tamper: nested key, hyphenated key, and domain_key overwrite (KF-BYPASS-02)
        for patch_override, dkey_override in (
            ({"Verifier_Contract": "weak"}, "bigquery.revenue_column"),
            ({"secret-proxy-allowlist": ["*"]}, "bigquery.revenue_column"),
            ({"sql_column": "v2"}, "secret_proxy_allowlist"),
            ({"sql_column": "v2"}, "ring0.bypass_verifier"),
        ):
            p, pol = self._clean_pair()
            p["payload_patch"] = patch_override
            p["domain_key"] = dkey_override
            self.assertEqual(evaluate_curator_proposal(p, pol)["failure_reasons"], ["KF04_RING0_IMMUTABLE_TAMPER"])

        # 3b. Store-tier confusion (KF-BYPASS-03): clean data mismatched tier & private DM into global store!
        p, pol = self._clean_pair()
        p["target_tier"] = "TEAM_SKILL"  # store is DATA_ACCESS_GUIDANCE
        self.assertEqual(evaluate_curator_proposal(p, pol)["failure_reasons"], ["KF01_STORE_TIER_MISMATCH"])

        p_leak, pol = self._clean_pair()
        p_leak["target_store"] = "github_skills"
        p_leak["base_revision_sha256"] = pol["expected_store_revisions"]["github_skills"]
        p_leak["target_tier"] = "USER_MEMORY"
        p_leak["source_confidentiality_labels"] = ["USER_PRIVATE_DM"]
        res_leak = evaluate_curator_proposal(p_leak, pol)
        self.assertEqual(res_leak["verdict"], "REJECTED_GOVERNOR")
        self.assertIn("KF01_STORE_TIER_MISMATCH", res_leak["failure_reasons"])
        self.assertIn("KF01_BLP_CONFIDENTIALITY_LEAK", res_leak["failure_reasons"])

        # 4. Lattice failure
        p, pol = self._clean_pair()
        p["source_integrity_labels"] = ["UNTRUSTED_EXTERNAL"]
        self.assertEqual(evaluate_curator_proposal(p, pol)["failure_reasons"], ["KF01_BIBA_INTEGRITY_ESCALATION"])

        # 5. Goodhart outside-anchor drift (strictly > before) AND 200x proxy regression (KF-BYPASS-05)
        p, pol = self._clean_pair()
        p["outside_err_after"] = "1/3"  # > 1/4
        self.assertEqual(evaluate_curator_proposal(p, pol)["failure_reasons"], ["KF02_GOODHART_OUTSIDE_ANCHOR_DRIFT"])
        p_reg, pol = self._clean_pair()
        p_reg["proxy_err_after"] = "100/1"  # 200x regression from 1/2!
        self.assertEqual(evaluate_curator_proposal(p_reg, pol)["failure_reasons"], ["KF02_PROXY_REGRESSION"])

        # 6. Unknown target store
        p, pol = self._clean_pair()
        p["target_store"] = "rogue_store"
        self.assertEqual(evaluate_curator_proposal(p, pol)["failure_reasons"], ["KF03_UNKNOWN_TARGET_STORE"])

        # 7. Stale CAS revision
        p, pol = self._clean_pair()
        p["base_revision_sha256"] = "9" * 64
        self.assertEqual(evaluate_curator_proposal(p, pol)["failure_reasons"], ["KF03_STALE_CAS_REVISION"])

        # 8. Skill dependency cycle
        p, pol = self._clean_pair()
        p["proposed_skill_edges"] = [("brand_header", "revenue_report")]
        self.assertEqual(evaluate_curator_proposal(p, pol)["failure_reasons"], ["KF03_SKILL_DEPENDENCY_CYCLE"])

        # 9. Scope escalation
        p, pol = self._clean_pair()
        p["requested_scopes"] = ["bigquery:read_revenue", "admin:drop_tables"]
        self.assertEqual(evaluate_curator_proposal(p, pol)["failure_reasons"], ["KF04_SCOPE_PRIVILEGE_ESCALATION"])

        # 10. Endpoint allowlist violation
        p, pol = self._clean_pair()
        p["requested_endpoints"] = ["https://attacker.example/exfil"]
        self.assertEqual(evaluate_curator_proposal(p, pol)["failure_reasons"], ["KF04_ENDPOINT_ALLOWLIST_VIOLATION"])

        # 11. Unapproved ambient cron (and approved cron MUST PASS)
        p, pol = self._clean_pair()
        p["creates_cron_trigger"] = True
        p["cron_owner_approved"] = False
        self.assertEqual(evaluate_curator_proposal(p, pol)["failure_reasons"], ["KF04_UNAPPROVED_AMBIENT_CRON"])
        p["cron_owner_approved"] = True
        self.assertEqual(evaluate_curator_proposal(p, pol)["verdict"], "PROMOTED")

        # 12. Tao G1 contract SHA invalid (including trailing newline)
        for bad_sha in (42, "a" * 63, ("a" * 64) + "\n"):
            p, pol = self._clean_pair()
            p["frozen_contract_sha256"] = bad_sha
            self.assertEqual(evaluate_curator_proposal(p, pol)["failure_reasons"], ["KF05_FROZEN_CONTRACT_SHA_INVALID"])

        # 13. Tao G2 split leakage
        p, pol = self._clean_pair()
        p["split_leakage_count"] = 1
        self.assertEqual(evaluate_curator_proposal(p, pol)["failure_reasons"], ["KF05_SPLIT_LEAKAGE_DETECTED"])

        # 14. Tao G3 unaudited network access
        for bad_net in (None, "UNRESTRICTED_INTERNET"):
            p, pol = self._clean_pair()
            p["network_audit_status"] = bad_net
            self.assertEqual(evaluate_curator_proposal(p, pol)["failure_reasons"], ["KF05_UNAUDITED_NETWORK_ACCESS"])

        # 15. Tao G5A R4 parity < 3
        p, pol = self._clean_pair()
        p["r4_isolated_parity_runs"] = 2
        self.assertEqual(evaluate_curator_proposal(p, pol)["failure_reasons"], ["KF05_R4_PARITY_BELOW_3"])

        # 16. Tao G5B R5 total == 0
        p, pol = self._clean_pair()
        p["r5_mutation_total"] = 0
        p["r5_mutation_killed"] = 0
        self.assertEqual(evaluate_curator_proposal(p, pol)["failure_reasons"], ["KF05_R5_MUTATION_TOTAL_ZERO"])

        # 17. Tao G5C R5 killed < total
        p, pol = self._clean_pair()
        p["r5_mutation_total"] = 10
        p["r5_mutation_killed"] = 9
        self.assertEqual(evaluate_curator_proposal(p, pol)["failure_reasons"], ["KF05_R5_MUTATION_INCOMPLETE"])


class TestLedgerChainAndAuditProvenance(unittest.TestCase):
    def test_ledger_build_verify_and_all_tamper_refusals(self) -> None:
        e0 = build_ledger_entry(
            seq=0,
            prev_hash=GENESIS_LEDGER_HASH,
            proposal_id="P0",
            verdict="REJECTED_GOVERNOR",
            curator_id="cur",
            verifier_id="ver",
            target_store="github_skills",
            base_revision_sha256="1" * 64,
            new_revision_sha256="1" * 64,
        )
        e1 = build_ledger_entry(
            seq=1,
            prev_hash=e0["entry_hash"],
            proposal_id="P1",
            verdict="PROMOTED",
            curator_id="cur",
            verifier_id="ver",
            target_store="github_skills",
            base_revision_sha256="1" * 64,
            new_revision_sha256="2" * 64,
        )
        res = verify_knowledge_ledger_chain([e0, e1])
        self.assertTrue(res["verified"])
        self.assertEqual(res["entry_count"], 2)

        # build_ledger_entry refusals
        with self.assertRaises(KnowledgeGovernorError) as cm_ph:
            build_ledger_entry(
                seq=0, prev_hash="bad", proposal_id="P", verdict="PROMOTED", curator_id="c",
                verifier_id="v", target_store="s", base_revision_sha256="1" * 64, new_revision_sha256="2" * 64
            )
        self.assertEqual(cm_ph.exception.code, "INVALID_PREV_HASH")
        with self.assertRaises(KnowledgeGovernorError) as cm_v:
            build_ledger_entry(
                seq=0, prev_hash=GENESIS_LEDGER_HASH, proposal_id="P", verdict="UNKNOWN", curator_id="c",
                verifier_id="v", target_store="s", base_revision_sha256="1" * 64, new_revision_sha256="2" * 64
            )
        self.assertEqual(cm_v.exception.code, "INVALID_VERDICT")
        with self.assertRaises(KnowledgeGovernorError) as cm_rh:
            build_ledger_entry(
                seq=0, prev_hash=GENESIS_LEDGER_HASH, proposal_id="P", verdict="PROMOTED", curator_id="c",
                verifier_id="v", target_store="s", base_revision_sha256="bad", new_revision_sha256="2" * 64
            )
        self.assertEqual(cm_rh.exception.code, "INVALID_REV_HASH")
        with self.assertRaises(KnowledgeGovernorError) as cm_bsa:
            build_ledger_entry(
                seq=0, prev_hash=GENESIS_LEDGER_HASH, proposal_id="P", verdict="PROMOTED", curator_id="cur",
                verifier_id=" CUR ", target_store="s", base_revision_sha256="1" * 64, new_revision_sha256="2" * 64
            )
        self.assertEqual(cm_bsa.exception.code, "LEDGER_SELF_APPROVAL")
        with self.assertRaises(KnowledgeGovernorError) as cm_brm:
            build_ledger_entry(
                seq=0, prev_hash=GENESIS_LEDGER_HASH, proposal_id="P", verdict="REJECTED_GOVERNOR", curator_id="cur",
                verifier_id="ver", target_store="s", base_revision_sha256="1" * 64, new_revision_sha256="2" * 64
            )
        self.assertEqual(cm_brm.exception.code, "LEDGER_REJECTED_MUTATED_REV")

        # verify_knowledge_ledger_chain refusals (including KF-BYPASS-04 validly-signed semantic forgeries!)
        def _resign(entry_dict: dict[str, object]) -> dict[str, object]:
            out = dict(entry_dict)
            out["entry_hash"] = canonical_sha256({k: v for k, v in out.items() if k != "entry_hash"})
            return out

        with self.assertRaises(KnowledgeGovernorError) as cm_e:
            verify_knowledge_ledger_chain([])
        self.assertEqual(cm_e.exception.code, "EMPTY_LEDGER")
        with self.assertRaises(KnowledgeGovernorError) as cm_t:
            verify_knowledge_ledger_chain(["bad"])  # type: ignore[list-item]
        self.assertEqual(cm_t.exception.code, "INVALID_LEDGER_ENTRY")
        bad_keys = dict(e0)
        bad_keys["extra"] = 1
        with self.assertRaises(KnowledgeGovernorError) as cm_k:
            verify_knowledge_ledger_chain([bad_keys])
        self.assertEqual(cm_k.exception.code, "LEDGER_SCHEMA_MISMATCH")
        bad_ver = dict(e0)
        bad_ver["schema"] = "wrong/v0"
        with self.assertRaises(KnowledgeGovernorError) as cm_s:
            verify_knowledge_ledger_chain([bad_ver])
        self.assertEqual(cm_s.exception.code, "LEDGER_VERSION_MISMATCH")
        # Validly signed semantic forgeries (KF-BYPASS-04a..d)
        f_verd = dict(e0)
        f_verd["verdict"] = "ADMIN_OVERRIDE"
        with self.assertRaises(KnowledgeGovernorError) as cm_lv:
            verify_knowledge_ledger_chain([_resign(f_verd)])
        self.assertEqual(cm_lv.exception.code, "LEDGER_INVALID_VERDICT")

        f_rev = dict(e0)
        f_rev["base_revision_sha256"] = "not-a-sha"
        with self.assertRaises(KnowledgeGovernorError) as cm_lr:
            verify_knowledge_ledger_chain([_resign(f_rev)])
        self.assertEqual(cm_lr.exception.code, "LEDGER_INVALID_REV_HASH")

        f_self = dict(e0)
        f_self["verdict"] = "PROMOTED"
        f_self["verifier_id"] = " CUR "
        f_self["new_revision_sha256"] = "2" * 64
        with self.assertRaises(KnowledgeGovernorError) as cm_ls:
            verify_knowledge_ledger_chain([_resign(f_self)])
        self.assertEqual(cm_ls.exception.code, "LEDGER_SELF_APPROVAL")

        f_mut = dict(e0)
        f_mut["verdict"] = "REJECTED_GOVERNOR"
        f_mut["new_revision_sha256"] = "2" * 64
        with self.assertRaises(KnowledgeGovernorError) as cm_lm:
            verify_knowledge_ledger_chain([_resign(f_mut)])
        self.assertEqual(cm_lm.exception.code, "LEDGER_REJECTED_MUTATED_REV")
        # Validly signed entry with seq=2 (seq skip)
        e_skip = build_ledger_entry(
            seq=2, prev_hash=e0["entry_hash"], proposal_id="P2", verdict="PROMOTED", curator_id="cur",
            verifier_id="ver", target_store="github_skills", base_revision_sha256="1" * 64, new_revision_sha256="2" * 64
        )
        with self.assertRaises(KnowledgeGovernorError) as cm_seq:
            verify_knowledge_ledger_chain([e0, e_skip])
        self.assertEqual(cm_seq.exception.code, "LEDGER_SEQ_GAP")
        # Validly signed entry with forked prev_hash
        e_fork = build_ledger_entry(
            seq=1, prev_hash=GENESIS_LEDGER_HASH, proposal_id="PF", verdict="PROMOTED", curator_id="cur",
            verifier_id="ver", target_store="github_skills", base_revision_sha256="1" * 64, new_revision_sha256="2" * 64
        )
        with self.assertRaises(KnowledgeGovernorError) as cm_fork:
            verify_knowledge_ledger_chain([e0, e_fork])
        self.assertEqual(cm_fork.exception.code, "LEDGER_CHAIN_FORK")
        # Hash tamper & bool-as-int seq forgery
        bad_hash = dict(e0)
        bad_hash["entry_hash"] = "f" * 64
        with self.assertRaises(KnowledgeGovernorError) as cm_ht:
            verify_knowledge_ledger_chain([bad_hash])
        self.assertEqual(cm_ht.exception.code, "LEDGER_HASH_TAMPER")
        bool_seq = dict(e0)
        bool_seq["seq"] = False
        bool_seq["entry_hash"] = canonical_sha256({k: v for k, v in bool_seq.items() if k != "entry_hash"})
        with self.assertRaises(KnowledgeGovernorError) as cm_bs:
            verify_knowledge_ledger_chain([bool_seq])
        self.assertEqual(cm_bs.exception.code, "INVALID_INT")

    def test_verify_pinned_sources_and_anchors_all_refusals(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            payload = b"line1\nexact verbatim anchor here\n"
            (root / "doc.txt").write_bytes(payload)
            digest = hashlib.sha256(payload).hexdigest()

            ok = verify_pinned_sources_and_anchors(
                root,
                expected_digests={"doc.txt": digest},
                anchor_specs=[("A1", "doc.txt", "exact verbatim anchor here")],
            )
            self.assertEqual(ok["anchors_matched"], 1)
            self.assertEqual(ok["anchors"][0]["line"], 2)

            with self.assertRaises(KnowledgeGovernorError) as cm1:
                verify_pinned_sources_and_anchors(root, expected_digests={}, anchor_specs=[])
            self.assertEqual(cm1.exception.code, "EMPTY_EXPECTED_DIGESTS")

            with self.assertRaises(KnowledgeGovernorError) as cm2:
                verify_pinned_sources_and_anchors(root, expected_digests={"missing.txt": digest}, anchor_specs=[])
            self.assertEqual(cm2.exception.code, "MISSING_SOURCE_FILE")

            with self.assertRaises(KnowledgeGovernorError) as cm3:
                verify_pinned_sources_and_anchors(root, expected_digests={"doc.txt": "0" * 64}, anchor_specs=[])
            self.assertEqual(cm3.exception.code, "SOURCE_SHA256_MISMATCH")

            with self.assertRaises(KnowledgeGovernorError) as cm4:
                verify_pinned_sources_and_anchors(
                    root,
                    expected_digests={"doc.txt": digest},
                    anchor_specs=[("A2", "other_missing.txt", "needle")],
                )
            self.assertEqual(cm4.exception.code, "MISSING_ANCHOR_FILE")

            with self.assertRaises(KnowledgeGovernorError) as cm5:
                verify_pinned_sources_and_anchors(
                    root,
                    expected_digests={"doc.txt": digest},
                    anchor_specs=[("A3", "doc.txt", "absent phrase")],
                )
            self.assertEqual(cm5.exception.code, "ANCHOR_NOT_FOUND")

    def test_standalone_certificate_invariants(self) -> None:
        cert = build_certificate(mode="standalone", provenance=None)
        verify_no_floats(cert)
        body = cert["certificate"]
        sc = body["governor_scenarios"]
        self.assertEqual(sc["kf01_external_trace_poisoning"]["verdict"], "REJECTED_GOVERNOR")
        self.assertEqual(sc["kf01_private_dm_to_global_leak"]["verdict"], "REJECTED_GOVERNOR")
        self.assertEqual(sc["kf02_goodhart_outside_anchor_drift"]["verdict"], "REJECTED_GOVERNOR")
        self.assertEqual(sc["kf03_skill_dependency_cycle"]["verdict"], "REJECTED_GOVERNOR")
        self.assertEqual(sc["kf04_privilege_escalation_and_ring0_tamper"]["verdict"], "REJECTED_GOVERNOR")
        self.assertEqual(sc["kf05_unverified_2role_self_approval"]["verdict"], "REJECTED_GOVERNOR")
        self.assertEqual(sc["governed_clean_promotion"]["verdict"], "PROMOTED")
        self.assertTrue(body["ledger_verification"]["verified"])


if __name__ == "__main__":
    unittest.main(verbosity=1)
