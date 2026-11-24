#!/usr/bin/env python3
"""
Live Verbatim Source Verifier & Exact Pure-Q Certificate Generator for AUDIT-076:
LangChain "Company Harness" + "Knowledge Factory" vs. The Aletheia Method.

Supports:
  - Default live mode: verifies pinned SHA-256 digests and verbatim textual anchors
    against `../repos/langchain-knowledge-factory/` (both LangChain blog posts fetched
    strictly read-only), runs all 5 exact KF-01..KF-05 failure-mode proofs and governed
    resolutions, and emits canonical float-free `knowledge_factory_certificate.json`.
  - `--standalone` mode: runs purely without external file dependencies.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence

# -I isolated-mode safe local import
_SCRIPT_DIR = Path(__file__).resolve().parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))

from knowledge_factory_governor import (  # noqa: E402
    GENESIS_LEDGER_HASH,
    KnowledgeGovernorError,
    VERIFIED_NETWORK_POLICY,
    audit_information_flow_lattice,
    audit_multi_worker_batch_conflicts,
    build_ledger_entry,
    canonical_json_bytes,
    canonical_sha256,
    compute_poisoning_blast_radius_exact,
    detect_skill_graph_cycle_exact,
    evaluate_curator_proposal,
    simulate_goodhart_curator_drift_exact,
    verify_knowledge_ledger_chain,
    verify_no_floats,
)

PINNED_COMPANY_HARNESS_URL = "https://www.langchain.com/blog/components-building-company-harness"
PINNED_KNOWLEDGE_FACTORY_URL = "https://www.langchain.com/blog/knowledge-factory"

PINNED_SOURCE_SHA256: dict[str, str] = {
    "components_building_company_harness.html": "cc6cccb9f73f419e08dc2287085df319d37e0f4f0a116c1e11ba89e30e491d12",
    "components_building_company_harness_text.txt": "2abd77952f0324c5fda93be797095bfb69e5232fdbb9569e1f1b69c97d48d598",
    "knowledge_factory.html": "716c69e30837267385fba2cae6b112f97fffabce7146adffcece785cd1e1842d",
    "knowledge_factory_text.txt": "ca5f914cdbaf84318a893fb388aba493494587ab6eaaf39fc88b7017bf7a7ae0",
}

# Verbatim textual anchors pinned to exact files downloaded from langchain.com
ANCHOR_SPECS: tuple[tuple[str, str, str], ...] = (
    (
        "CH-01_FIVE_COMPONENTS_TITLE",
        "components_building_company_harness_text.txt",
        'The five components of building a "company harness"',
    ),
    (
        "CH-02_GTM_EMAIL_LEADS",
        "components_building_company_harness_text.txt",
        "Monitors and responds to emails, to new qualified leads",
    ),
    (
        "CH-03_DM_ONLY_OBO_EMAIL",
        "components_building_company_harness_text.txt",
        "These tools are ONLY available in DMs. In shared channels, they are not available",
    ),
    (
        "CH-04_WHITELISTED_TWITTER",
        "components_building_company_harness_text.txt",
        "Only a whitelisted set of users can invoke certain operations here though",
    ),
    (
        "CH-05_AGENT_DECIDES_MEMORY_TIER",
        "components_building_company_harness_text.txt",
        "Agents decide which facts they want to remember to which level of memory.",
    ),
    (
        "CH-06_SECRET_PROXY_SANDBOX",
        "components_building_company_harness_text.txt",
        "secret proxy on LangSmith Sandboxes",
    ),
    (
        "CH-07_USER_SELF_CREATED_CRON",
        "components_building_company_harness_text.txt",
        "I asked GTM agent to send me a daily brief, and it created its own cron to do so.",
    ),
    (
        "KF-01_THREE_KNOWLEDGE_PIECES",
        "knowledge_factory_text.txt",
        "How to do the work",
    ),
    (
        "KF-02_WORKER_CONTRADICTIONS_WARNING",
        "knowledge_factory_text.txt",
        "will cause it to become unruly and full of contradictions.",
    ),
    (
        "KF-03_CURATOR_ALL_RAW_SOURCES",
        "knowledge_factory_text.txt",
        "It should have access to all the raw sources of data (Notion, Slack, etc)",
    ),
    (
        "KF-04_CURATOR_AGENT_TRACES",
        "knowledge_factory_text.txt",
        "It should have access to agent traces",
    ),
    (
        "KF-05_CURATOR_NIGHTLY_SKILL_WRITE",
        "knowledge_factory_text.txt",
        "It updates the relevant skills accordingly",
    ),
)


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        while True:
            chunk = fh.read(65536)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest()


def verify_pinned_sources_and_anchors(
    source_dir: Path,
    expected_digests: Mapping[str, str] | None = None,
    anchor_specs: Sequence[tuple[str, str, str]] | None = None,
) -> dict[str, Any]:
    """Verify exact SHA-256 digests and verbatim textual anchors against downloaded files."""
    digests = PINNED_SOURCE_SHA256 if expected_digests is None else expected_digests
    specs = ANCHOR_SPECS if anchor_specs is None else anchor_specs
    if len(digests) == 0:
        raise KnowledgeGovernorError("EMPTY_EXPECTED_DIGESTS", "expected_digests must be non-empty")

    verified_digests: dict[str, str] = {}
    for fname, expected in sorted(digests.items()):
        fpath = source_dir / fname
        if not fpath.is_file():
            raise KnowledgeGovernorError("MISSING_SOURCE_FILE", f"missing source file {fname}")
        actual = _sha256_file(fpath)
        if actual != expected:
            raise KnowledgeGovernorError("SOURCE_SHA256_MISMATCH", f"{fname}: {actual} != {expected}")
        verified_digests[fname] = actual

    cache: dict[str, str] = {}
    anchor_results: list[dict[str, Any]] = []
    for anchor_id, fname, needle in specs:
        fpath = source_dir / fname
        if fname not in cache:
            if not fpath.is_file():
                raise KnowledgeGovernorError("MISSING_ANCHOR_FILE", f"missing anchor file {fname}")
            cache[fname] = fpath.read_text(encoding="utf-8")
        text = cache[fname]
        pos = text.find(needle)
        if pos == -1:
            raise KnowledgeGovernorError("ANCHOR_NOT_FOUND", f"{anchor_id} not found in {fname}")
        line_no = text.count("\n", 0, pos) + 1
        anchor_results.append({"anchor_id": anchor_id, "file": fname, "line": line_no, "matched": True})

    return {
        "verified_digests": verified_digests,
        "anchors_matched": len(anchor_results),
        "anchors_total": len(specs),
        "anchors": anchor_results,
    }


def _make_base_policy() -> dict[str, Any]:
    rev_gh = "1" * 64
    rev_hub = "2" * 64
    rev_wiki = "3" * 64
    return {
        "expected_store_revisions": {
            "github_skills": rev_gh,
            "context_hub_data_access": rev_hub,
            "company_wiki_domain": rev_wiki,
        },
        "store_tiers": {
            "github_skills": "GLOBAL_SKILL",
            "context_hub_data_access": "DATA_ACCESS_GUIDANCE",
            "company_wiki_domain": "GLOBAL_DOMAIN_KNOWLEDGE",
        },
        "allowed_scopes": ["bigquery:read_revenue", "docs:format_report"],
        "allowed_endpoints": ["https://bigquery.googleapis.com/revenue_v2"],
        "existing_skill_graph": [
            ("revenue_report", "bigquery_fetch"),
            ("revenue_report", "brand_header"),
        ],
    }


def _make_clean_proposal(base_rev: str) -> dict[str, Any]:
    return {
        "proposal_id": "PROP-001-CLEAN-BIGQUERY-COL",
        "worker_id": "gtm_worker_01",
        "curator_id": "nightly_curator_01",
        "verifier_id": "aletheia_verifier_01",
        "target_tier": "DATA_ACCESS_GUIDANCE",
        "target_store": "context_hub_data_access",
        "domain_key": "bigquery.revenue_column",
        "base_revision_sha256": base_rev,
        "proposed_value": "net_arr_usd_v2",
        "source_integrity_labels": ["ADMIN_WHITELIST"],
        "source_confidentiality_labels": ["PUBLIC_GLOBAL"],
        "human_admin_countersigned": False,
        "requested_scopes": ["bigquery:read_revenue"],
        "requested_endpoints": ["https://bigquery.googleapis.com/revenue_v2"],
        "creates_cron_trigger": False,
        "cron_owner_approved": False,
        "payload_patch": {"sql_column": "net_arr_usd_v2", "table": "finance.rev_summary"},
        "proposed_skill_edges": [],
        "proxy_err_before": "1/2",
        "proxy_err_after": "1/4",
        "outside_err_before": "1/4",
        "outside_err_after": "1/8",
        "frozen_contract_sha256": "a" * 64,
        "split_leakage_count": 0,
        "network_audit_status": VERIFIED_NETWORK_POLICY,
        "r4_isolated_parity_runs": 4,
        "r5_mutation_killed": 75,
        "r5_mutation_total": 75,
    }


def build_certificate(
    mode: str,
    provenance: dict[str, Any] | None,
) -> dict[str, Any]:
    """Run all KF-01..KF-05 mathematical proofs, adversarial scenarios, and ledger checks."""
    policy = _make_base_policy()
    rev_hub = policy["expected_store_revisions"]["context_hub_data_access"]
    rev_gh = policy["expected_store_revisions"]["github_skills"]

    # KF-01: Trace Poisoning (External Lead Email -> Global Skill) & Private-DM Leak + Blast Radius
    kf01_email_poison = _make_clean_proposal(rev_gh)
    kf01_email_poison.update(
        {
            "proposal_id": "KF01-ATTACK-EXTERNAL-TRACE-POISON",
            "target_tier": "GLOBAL_SKILL",
            "target_store": "github_skills",
            "base_revision_sha256": rev_gh,
            "source_integrity_labels": ["UNTRUSTED_EXTERNAL", "VERIFIED_EMPLOYEE_DM"],
            "source_confidentiality_labels": ["PUBLIC_GLOBAL"],
            "human_admin_countersigned": False,
        }
    )
    kf01_dm_leak = _make_clean_proposal(rev_gh)
    kf01_dm_leak.update(
        {
            "proposal_id": "KF01-ATTACK-DM-TO-GLOBAL-LEAK",
            "target_tier": "GLOBAL_SKILL",
            "target_store": "github_skills",
            "base_revision_sha256": rev_gh,
            "source_integrity_labels": ["ADMIN_WHITELIST"],
            "source_confidentiality_labels": ["USER_PRIVATE_DM"],
            "human_admin_countersigned": True,  # Even admin countersign cannot leak private DM to GLOBAL!
        }
    )
    kf01_blast = compute_poisoning_blast_radius_exact(
        worker_count=10,
        scheduled_runs_per_worker=12,
        trigger_probability=Fraction(1, 20),
    )

    # KF-02: Goodhart Self-Reinforcement Drift (4 steps: proxy decays 1/4/step, outside drifts +1/2/step)
    kf02_drift_proof = simulate_goodhart_curator_drift_exact(
        steps=4,
        initial_proxy_err=Fraction(1, 1),
        initial_outside_err=Fraction(1, 4),
        proxy_decay_rate=Fraction(1, 4),
        outside_drift_per_step=Fraction(1, 2),
    )
    kf02_attack = _make_clean_proposal(rev_hub)
    kf02_attack.update(
        {
            "proposal_id": "KF02-ATTACK-GOODHART-DRIFT",
            "proxy_err_before": "1",
            "proxy_err_after": "3/4",
            "outside_err_before": "1/4",
            "outside_err_after": "3/4",
        }
    )

    # KF-03: Multi-Worker LWW Oscillation + Stale CAS Split-Brain + Skill Dependency Cycle
    kf03_batch_conflict = audit_multi_worker_batch_conflicts(
        proposals=[
            {
                "proposal_id": "W-SALES-ARR",
                "target_store": "company_wiki_domain",
                "domain_key": "metric.arr_definition",
                "base_revision_sha256": policy["expected_store_revisions"]["company_wiki_domain"],
                "proposed_value": "gross_bookings_incl_services",
            },
            {
                "proposal_id": "W-FINANCE-ARR",
                "target_store": "company_wiki_domain",
                "domain_key": "metric.arr_definition",
                "base_revision_sha256": policy["expected_store_revisions"]["company_wiki_domain"],
                "proposed_value": "net_recognized_recurring_only",
            },
            {
                "proposal_id": "W-STALE-HUB",
                "target_store": "context_hub_data_access",
                "domain_key": "bigquery.revenue_column",
                "base_revision_sha256": "9" * 64,
                "proposed_value": "legacy_col_v1",
            },
        ],
        expected_store_revisions=policy["expected_store_revisions"],
    )
    kf03_cycle_attack = _make_clean_proposal(rev_hub)
    kf03_cycle_attack["proposal_id"] = "KF03-ATTACK-SKILL-CYCLE"
    kf03_cycle_attack["proposed_skill_edges"] = [("bigquery_fetch", "revenue_report")]

    # KF-04: Privilege Escalation (Data-Access Scope + Endpoint + Unapproved Cron + Ring-0 Tamper)
    kf04_priv_attack = _make_clean_proposal(rev_hub)
    kf04_priv_attack.update(
        {
            "proposal_id": "KF04-ATTACK-PRIV-ESCALATION-AND-RING0",
            "requested_scopes": ["bigquery:read_revenue", "salesforce:export_all_pii"],
            "requested_endpoints": [
                "https://bigquery.googleapis.com/revenue_v2",
                "https://evil-exfil.example/collect",
            ],
            "creates_cron_trigger": True,
            "cron_owner_approved": False,
            "payload_patch": {
                "sql_column": "net_arr_usd_v2",
                "nested": {"Secret_Proxy_Allowlist": ["*"]},
            },
        }
    )

    # KF-05: Self-Approving Curator (LangChain 2-role loop without Adversarial Verifier + 0/5 Tao gates)
    kf05_self_approve = _make_clean_proposal(rev_hub)
    kf05_self_approve.update(
        {
            "proposal_id": "KF05-ATTACK-UNVERIFIED-2ROLE-CURATOR",
            "verifier_id": "nightly_curator_01",  # Curator self-approves!
            "frozen_contract_sha256": "",
            "split_leakage_count": 1,
            "network_audit_status": "UNRESTRICTED_INTERNET",
            "r4_isolated_parity_runs": 0,
            "r5_mutation_killed": 0,
            "r5_mutation_total": 0,
        }
    )

    # Clean Governed Promotion (3-Role Aletheia + Tao Gate PASS)
    clean_prop = _make_clean_proposal(rev_hub)

    scenarios = {
        "kf01_external_trace_poisoning": evaluate_curator_proposal(kf01_email_poison, policy),
        "kf01_private_dm_to_global_leak": evaluate_curator_proposal(kf01_dm_leak, policy),
        "kf02_goodhart_outside_anchor_drift": evaluate_curator_proposal(kf02_attack, policy),
        "kf03_skill_dependency_cycle": evaluate_curator_proposal(kf03_cycle_attack, policy),
        "kf04_privilege_escalation_and_ring0_tamper": evaluate_curator_proposal(kf04_priv_attack, policy),
        "kf05_unverified_2role_self_approval": evaluate_curator_proposal(kf05_self_approve, policy),
        "governed_clean_promotion": evaluate_curator_proposal(clean_prop, policy),
    }

    # Build and verify 2-entry hash-chained audit ledger (1 rejected attack + 1 clean promotion)
    e0 = build_ledger_entry(
        seq=0,
        prev_hash=GENESIS_LEDGER_HASH,
        proposal_id=scenarios["kf01_external_trace_poisoning"]["proposal_id"],
        verdict=scenarios["kf01_external_trace_poisoning"]["verdict"],
        curator_id=kf01_email_poison["curator_id"],
        verifier_id=kf01_email_poison["verifier_id"],
        target_store=kf01_email_poison["target_store"],
        base_revision_sha256=rev_gh,
        new_revision_sha256=scenarios["kf01_external_trace_poisoning"]["new_revision_sha256"],
    )
    e1 = build_ledger_entry(
        seq=1,
        prev_hash=e0["entry_hash"],
        proposal_id=scenarios["governed_clean_promotion"]["proposal_id"],
        verdict=scenarios["governed_clean_promotion"]["verdict"],
        curator_id=clean_prop["curator_id"],
        verifier_id=clean_prop["verifier_id"],
        target_store=clean_prop["target_store"],
        base_revision_sha256=rev_hub,
        new_revision_sha256=scenarios["governed_clean_promotion"]["new_revision_sha256"],
    )
    ledger_verification = verify_knowledge_ledger_chain([e0, e1])

    body: dict[str, Any] = {
        "schema_version": "aletheia.langchain_knowledge_factory_audit.v1",
        "audit_id": "AUDIT-076",
        "mode": mode,
        "sources": {
            "company_harness_url": PINNED_COMPANY_HARNESS_URL,
            "knowledge_factory_url": PINNED_KNOWLEDGE_FACTORY_URL,
            "pinned_source_sha256": (
                provenance["verified_digests"] if provenance is not None else PINNED_SOURCE_SHA256
            ),
            "anchor_verification": provenance,
        },
        "kf01_blast_radius_exact": kf01_blast,
        "kf02_goodhart_drift_exact": kf02_drift_proof,
        "kf03_multi_worker_batch_conflict_audit": kf03_batch_conflict,
        "kf03_standalone_dag_cycle_check": detect_skill_graph_cycle_exact(
            policy["existing_skill_graph"] + kf03_cycle_attack["proposed_skill_edges"]
        ),
        "kf01_lattice_direct_witness": audit_information_flow_lattice(
            source_integrity_labels=["UNTRUSTED_EXTERNAL"],
            source_confidentiality_labels=["USER_PRIVATE_DM"],
            target_tier="GLOBAL_SKILL",
            human_admin_countersigned=False,
        ),
        "governor_scenarios": scenarios,
        "ledger_entries": [e0, e1],
        "ledger_verification": ledger_verification,
    }
    verify_no_floats(body, "certificate")
    return {
        "canonical_sha256": canonical_sha256(body),
        "certificate": body,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="AUDIT-076 LangChain Company Harness + Knowledge Factory audit")
    parser.add_argument("--standalone", action="store_true", help="Run without external downloaded files")
    parser.add_argument("--write-cert", type=str, default="", help="Optional path to write canonical JSON certificate")
    args = parser.parse_args(argv)

    if args.standalone:
        result = build_certificate(mode="standalone", provenance=None)
    else:
        src_dir = _SCRIPT_DIR.parent / "repos" / "langchain-knowledge-factory"
        if src_dir.is_dir():
            prov = verify_pinned_sources_and_anchors(src_dir)
            result = build_certificate(mode="live_pinned_verified", provenance=prov)
        else:
            result = build_certificate(mode="standalone", provenance=None)

    raw_bytes = canonical_json_bytes(result) + b"\n"
    if args.write_cert:
        Path(args.write_cert).write_bytes(raw_bytes)
    sys.stdout.write(raw_bytes.decode("utf-8"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
