"""
Verified Knowledge Factory Curator Governor (AUDIT-076).

Formalizes LangChain's Company Harness (Oct 24, 2026) + Knowledge Factory (Nov 21, 2026)
architecture and closes all five unverified-Curator trust-boundary failure modes:
  - KF-01: Indirect Prompt Injection & Cross-Tier Trace Poisoning (Biba Integrity +
           Bell-LaPadula Confidentiality Lattice + Exact Fleet Blast-Radius Bound)
  - KF-02: Goodhart Self-Reinforcement & Trace-Echo Drift (Exact Pure-Q Pythagorean
           Outside-Anchor Latch & Recurrence Divergence Proof, uniting aletheia/ratchet.py)
  - KF-03: Multi-Worker Race / LWW Oscillation / Cross-Store Split-Brain / Skill
           Dependency Contradiction Cycles (Exact CAS Revision, Conflict Escalation & DFS DAG)
  - KF-04: Privilege Escalation via Data-Access / Cron / Ring-0 Skill Mutation
           (Monotone Capability Attenuation + Recursive Case-Insensitive Ring-0 Lock)
  - KF-05: 3-Role Separation of Duties (Worker -> Curator -> Independent Verifier) +
           Tao Observability Process Gate (AUDIT-069R) + SHA-256 Hash-Chained Ledger

Pure Python 3 stdlib only. ZERO floats on trust paths. ZERO bare `assert` statements.
All refusals raise `KnowledgeGovernorError(ValueError)` with deterministic `.code`.
"""
from __future__ import annotations

from fractions import Fraction
import hashlib
import json
import re
from typing import Any, Mapping, Sequence


_EXACT_NUM_RE = re.compile(r"\A-?(?:0|[1-9][0-9]*)(?:\.[0-9]+|/[1-9][0-9]*)?\Z")
_SHA256_HEX_RE = re.compile(r"\A[0-9a-f]{64}\Z")
_KEY_IDENT_RE = re.compile(r"\A[A-Za-z0-9_.:-]{1,128}\Z")

GENESIS_LEDGER_HASH = "0" * 64
LEDGER_SCHEMA = "aletheia.knowledge_factory_ledger.v1"

# Exact Biba integrity levels (higher = more trusted)
INTEGRITY_LEVELS: dict[str, int] = {
    "UNTRUSTED_EXTERNAL": 0,
    "SHARED_CHANNEL": 1,
    "VERIFIED_EMPLOYEE_DM": 2,
    "ADMIN_WHITELIST": 3,
    "RING0_IMMUTABLE": 4,
}

# Exact Bell-LaPadula confidentiality levels (higher = more sensitive)
CONFIDENTIALITY_LEVELS: dict[str, int] = {
    "PUBLIC_GLOBAL": 0,
    "TEAM_SHARED": 1,
    "USER_PRIVATE_DM": 2,
    "SECRET_CREDENTIAL": 3,
}

# Target knowledge-store tier policies: (min_required_integrity, max_allowed_confidentiality)
TARGET_TIER_POLICIES: dict[str, tuple[int, int]] = {
    "USER_MEMORY": (2, 2),
    "TEAM_SKILL": (2, 1),
    "GLOBAL_SKILL": (3, 0),
    "GLOBAL_DOMAIN_KNOWLEDGE": (3, 0),
    "DATA_ACCESS_GUIDANCE": (3, 0),
}

# Ring-0 immutable keys that NO Curator proposal may ever modify or shadow
RING0_FORBIDDEN_KEYS = frozenset(
    {
        "identity_policy",
        "obo_boundary",
        "sandbox_boundary",
        "secret_proxy_allowlist",
        "verifier_contract",
        "heldout_eval_suite",
        "ring0_sha256",
        "whitelist_override",
        "bypass_verifier",
    }
)

VERIFIED_NETWORK_POLICY = "OFFLINE_OR_ALLOWLIST_VERIFIED"

EXPECTED_PROPOSAL_KEYS = frozenset(
    {
        "proposal_id",
        "worker_id",
        "curator_id",
        "verifier_id",
        "target_tier",
        "target_store",
        "domain_key",
        "base_revision_sha256",
        "proposed_value",
        "source_integrity_labels",
        "source_confidentiality_labels",
        "human_admin_countersigned",
        "requested_scopes",
        "requested_endpoints",
        "creates_cron_trigger",
        "cron_owner_approved",
        "payload_patch",
        "proposed_skill_edges",
        "proxy_err_before",
        "proxy_err_after",
        "outside_err_before",
        "outside_err_after",
        "frozen_contract_sha256",
        "split_leakage_count",
        "network_audit_status",
        "r4_isolated_parity_runs",
        "r5_mutation_killed",
        "r5_mutation_total",
    }
)

EXPECTED_POLICY_KEYS = frozenset(
    {
        "expected_store_revisions",
        "store_tiers",
        "allowed_scopes",
        "allowed_endpoints",
        "existing_skill_graph",
    }
)

EXPECTED_LEDGER_ENTRY_KEYS = frozenset(
    {
        "schema",
        "seq",
        "prev_hash",
        "proposal_id",
        "verdict",
        "curator_id",
        "verifier_id",
        "target_store",
        "base_revision_sha256",
        "new_revision_sha256",
        "entry_hash",
    }
)


class KnowledgeGovernorError(ValueError):
    """Fail-closed exact-arithmetic, schema, or governance refusal error."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"[{code}] {message}")
        self.code = code


def verify_no_floats(obj: Any, path: str = "root") -> None:
    """Recursively reject any Python float anywhere in an object tree."""
    if isinstance(obj, float):
        raise KnowledgeGovernorError("FLOAT_FORBIDDEN", f"float forbidden at {path}")
    if isinstance(obj, Mapping):
        for k, v in obj.items():
            verify_no_floats(k, f"{path}.<key>")
            verify_no_floats(v, f"{path}.{k}")
    elif isinstance(obj, (list, tuple)):
        for idx, item in enumerate(obj):
            verify_no_floats(item, f"{path}[{idx}]")


def require_non_empty_str(value: Any, field: str) -> str:
    """Require a non-empty stripped string."""
    if not isinstance(value, str):
        raise KnowledgeGovernorError("INVALID_STR", f"{field} must be str")
    if value.strip() == "":
        raise KnowledgeGovernorError("EMPTY_STR", f"{field} must be non-empty")
    return value


def require_exact_bool(value: Any, field: str) -> bool:
    """Require a strict Python bool."""
    if not isinstance(value, bool):
        raise KnowledgeGovernorError("INVALID_BOOL", f"{field} must be bool")
    return value


def require_exact_int(
    value: Any,
    field: str,
    min_value: int | None = None,
    max_value: int | None = None,
) -> int:
    """Require an exact int (rejecting bool and float) within optional closed bounds."""
    if isinstance(value, bool) or not isinstance(value, int):
        raise KnowledgeGovernorError("INVALID_INT", f"{field} must be exact int")
    if min_value is not None and value < min_value:
        raise KnowledgeGovernorError("INT_BELOW_MIN", f"{field}={value} < {min_value}")
    if max_value is not None and value > max_value:
        raise KnowledgeGovernorError("INT_ABOVE_MAX", f"{field}={value} > {max_value}")
    return value


def require_exact_fraction(
    value: Any,
    field: str,
    min_value: Fraction | None = None,
    max_value: Fraction | None = None,
) -> Fraction:
    """Require an exact Fraction, exact non-bool int, or canonical decimal/rational string."""
    if isinstance(value, bool):
        raise KnowledgeGovernorError("BOOL_NOT_FRACTION", f"{field} cannot be bool")
    if isinstance(value, Fraction):
        out = value
    elif isinstance(value, int):
        out = Fraction(value, 1)
    elif isinstance(value, str):
        if _EXACT_NUM_RE.match(value) is None:
            raise KnowledgeGovernorError("INVALID_FRACTION_STR", f"{field}={value!r} not canonical")
        out = Fraction(value)
    else:
        raise KnowledgeGovernorError("INVALID_FRACTION_TYPE", f"{field} must be exact rational")
    if min_value is not None and out < min_value:
        raise KnowledgeGovernorError("FRACTION_BELOW_MIN", f"{field}={out} < {min_value}")
    if max_value is not None and out > max_value:
        raise KnowledgeGovernorError("FRACTION_ABOVE_MAX", f"{field}={out} > {max_value}")
    return out


def frac_str(value: Fraction) -> str:
    """Canonical exact rational string 'p/q'."""
    f = require_exact_fraction(value, "value")
    return f"{f.numerator}/{f.denominator}"


def format_exact_decimal(value: Fraction, places: int = 6) -> str:
    """Pure-integer half-up decimal formatting with zero float usage."""
    f = require_exact_fraction(value, "value")
    p = require_exact_int(places, "places", min_value=0, max_value=12)
    sign = "-" if f < 0 else ""
    abs_f = -f if f < 0 else f
    scale = 10 ** p
    scaled = (abs_f.numerator * scale * 2 + abs_f.denominator) // (2 * abs_f.denominator)
    if p == 0:
        return f"{sign}{scaled}"
    whole, frac_part = divmod(scaled, scale)
    return f"{sign}{whole}.{frac_part:0{p}d}"


def canonical_json_bytes(payload: Any) -> bytes:
    """Serialize float-free object into canonical sorted-key UTF-8 JSON bytes."""
    verify_no_floats(payload, "payload")
    return json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    ).encode("utf-8")


def canonical_sha256(payload: Any) -> str:
    """SHA-256 hex digest of canonical float-free JSON."""
    return hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def _is_ring0_forbidden_identifier(name: str) -> bool:
    """Detect Ring-0 forbidden identifiers across hyphen/space/dot/slash/colon token forms."""
    norm = name.strip().lower().replace("-", "_").replace(" ", "_")
    if norm in RING0_FORBIDDEN_KEYS:
        return True
    for tok in re.split(r"[.:/]+", norm):
        if tok in RING0_FORBIDDEN_KEYS:
            return True
    return False


def scan_ring0_tamper_keys(obj: Any, path: str = "patch") -> list[str]:
    """Recursively detect Ring-0 forbidden keys (case/hyphen/delimiter-normalized) in a patch."""
    verify_no_floats(obj, path)
    hits: list[str] = []
    if isinstance(obj, Mapping):
        for k, v in obj.items():
            key_s = require_non_empty_str(k, f"{path}.<key>")
            if _is_ring0_forbidden_identifier(key_s):
                hits.append(f"{path}.{key_s}")
            hits.extend(scan_ring0_tamper_keys(v, f"{path}.{key_s}"))
    elif isinstance(obj, (list, tuple)):
        for idx, item in enumerate(obj):
            hits.extend(scan_ring0_tamper_keys(item, f"{path}[{idx}]"))
    return sorted(hits)


def require_list_or_tuple(value: Any, field: str) -> list[Any] | tuple[Any, ...]:
    """Require an explicit list or tuple (rejecting str/bytes/dict iteration bypasses)."""
    if not isinstance(value, (list, tuple)):
        raise KnowledgeGovernorError("INVALID_SEQUENCE_TYPE", f"{field} must be list or tuple")
    return value


def audit_information_flow_lattice(
    source_integrity_labels: Sequence[str],
    source_confidentiality_labels: Sequence[str],
    target_tier: str,
    human_admin_countersigned: bool,
) -> dict[str, Any]:
    """
    KF-01 Exact Biba Integrity x Bell-LaPadula Confidentiality Lattice Audit:
      - Biba integrity: min(source_integrity) >= required_integrity(target_tier),
        unless explicitly countersigned by a verified human admin.
      - Bell-LaPadula confidentiality: max(source_confidentiality) <= max_conf(target_tier)
        (no secret/private-DM leakage into shared/global memory — even with countersign!).
    """
    int_seq = require_list_or_tuple(source_integrity_labels, "source_integrity_labels")
    conf_seq = require_list_or_tuple(source_confidentiality_labels, "source_confidentiality_labels")
    if len(int_seq) == 0:
        raise KnowledgeGovernorError("EMPTY_INTEGRITY_SOURCES", "need >= 1 integrity source")
    if len(conf_seq) == 0:
        raise KnowledgeGovernorError("EMPTY_CONF_SOURCES", "need >= 1 confidentiality source")
    tier = require_non_empty_str(target_tier, "target_tier")
    if tier not in TARGET_TIER_POLICIES:
        raise KnowledgeGovernorError("UNKNOWN_TARGET_TIER", f"unknown target_tier {tier!r}")
    countersigned = require_exact_bool(human_admin_countersigned, "human_admin_countersigned")

    int_vals: list[int] = []
    for idx, lbl in enumerate(int_seq):
        s = require_non_empty_str(lbl, f"source_integrity_labels[{idx}]")
        if s not in INTEGRITY_LEVELS:
            raise KnowledgeGovernorError("UNKNOWN_INTEGRITY_LABEL", f"unknown integrity {s!r}")
        int_vals.append(INTEGRITY_LEVELS[s])

    conf_vals: list[int] = []
    for idx, lbl in enumerate(conf_seq):
        s = require_non_empty_str(lbl, f"source_confidentiality_labels[{idx}]")
        if s not in CONFIDENTIALITY_LEVELS:
            raise KnowledgeGovernorError("UNKNOWN_CONF_LABEL", f"unknown confidentiality {s!r}")
        conf_vals.append(CONFIDENTIALITY_LEVELS[s])

    req_int, max_conf = TARGET_TIER_POLICIES[tier]
    min_src_int = min(int_vals)
    max_src_conf = max(conf_vals)

    biba_gap = req_int - min_src_int
    blp_leak_gap = max_src_conf - max_conf

    failure_reasons: list[str] = []
    if min_src_int < req_int and not countersigned:
        failure_reasons.append("KF01_BIBA_INTEGRITY_ESCALATION")
    if max_src_conf > max_conf:
        failure_reasons.append("KF01_BLP_CONFIDENTIALITY_LEAK")

    return {
        "admissible": len(failure_reasons) == 0,
        "target_tier": tier,
        "min_source_integrity": min_src_int,
        "required_target_integrity": req_int,
        "biba_elevation_gap": biba_gap if biba_gap > 0 else 0,
        "max_source_confidentiality": max_src_conf,
        "max_target_confidentiality": max_conf,
        "blp_leak_gap": blp_leak_gap if blp_leak_gap > 0 else 0,
        "human_admin_countersigned": countersigned,
        "failure_reasons": failure_reasons,
    }


def compute_poisoning_blast_radius_exact(
    worker_count: int,
    scheduled_runs_per_worker: int,
    trigger_probability: Any,
) -> dict[str, Any]:
    """
    Exact pure-Q expected blast radius and non-exposure survival probability of a
    single poisoned global skill over W workers x T ambient scheduled runs:
      - Expected compromised executions: E[C] = W * T * p
      - Exact probability of >= 1 compromised execution: 1 - (1 - p)^(W * T)
    """
    w = require_exact_int(worker_count, "worker_count", min_value=1)
    t = require_exact_int(scheduled_runs_per_worker, "scheduled_runs_per_worker", min_value=1)
    p = require_exact_fraction(trigger_probability, "trigger_probability", Fraction(0), Fraction(1))
    total_exposures = w * t
    expected_hits = Fraction(total_exposures) * p
    clean_prob = (Fraction(1) - p) ** total_exposures
    compromise_prob = Fraction(1) - clean_prob
    return {
        "worker_count": w,
        "scheduled_runs_per_worker": t,
        "total_exposures": total_exposures,
        "trigger_probability_exact": frac_str(p),
        "expected_compromised_runs_exact": frac_str(expected_hits),
        "expected_compromised_runs_dec": format_exact_decimal(expected_hits, 4),
        "prob_at_least_one_compromise_exact": frac_str(compromise_prob),
        "prob_at_least_one_compromise_dec": format_exact_decimal(compromise_prob, 6),
    }


def simulate_goodhart_curator_drift_exact(
    steps: int,
    initial_proxy_err: Any,
    initial_outside_err: Any,
    proxy_decay_rate: Any,
    outside_drift_per_step: Any,
) -> dict[str, Any]:
    """
    KF-02 Exact Pure-Q Goodhart Self-Reinforcement & Trace-Echo Drift Proof:
      - At each Curator step t -> t+1:
          proxy_err_{t+1}   = proxy_err_t * (1 - proxy_decay_rate)
          outside_err_{t+1} = outside_err_t + outside_drift_per_step
          total_err_t       = proxy_err_t + outside_err_t  (exact Pythagorean sum)
      - An unverified Curator observing only proxy_err accepts ALL `steps` updates,
        while Aletheia's Pre-Adaptation Goodhart Latch halts at step 1 whenever
        outside_err increases while proxy_err decreases.
    """
    n_steps = require_exact_int(steps, "steps", min_value=1, max_value=64)
    p0 = require_exact_fraction(initial_proxy_err, "initial_proxy_err", Fraction(0))
    if p0 == Fraction(0):
        raise KnowledgeGovernorError("ZERO_INITIAL_PROXY", "initial_proxy_err must be > 0")
    o0 = require_exact_fraction(initial_outside_err, "initial_outside_err", Fraction(0))
    alpha = require_exact_fraction(proxy_decay_rate, "proxy_decay_rate", Fraction(0), Fraction(1))
    if alpha == Fraction(0):
        raise KnowledgeGovernorError("ZERO_DECAY_RATE", "proxy_decay_rate must be > 0")
    delta = require_exact_fraction(outside_drift_per_step, "outside_drift_per_step", Fraction(0))

    p_cur = p0
    o_cur = o0
    unverified_accepts = 0
    governor_halt_step: int | None = None
    trajectory: list[dict[str, str]] = []

    for step in range(1, n_steps + 1):
        p_next = p_cur * (Fraction(1) - alpha)
        o_next = o_cur + delta
        if p_next < p_cur:
            unverified_accepts += 1
        if governor_halt_step is None and o_next > o_cur and p_next < p_cur:
            governor_halt_step = step
        trajectory.append(
            {
                "step": str(step),
                "proxy_err_exact": frac_str(p_next),
                "outside_err_exact": frac_str(o_next),
                "total_err_exact": frac_str(p_next + o_next),
            }
        )
        p_cur = p_next
        o_cur = o_next

    total_0 = p0 + o0
    total_end = p_cur + o_cur
    proxy_reduction_frac = (p0 - p_cur) / p0
    total_change_frac = (total_end - total_0) / total_0
    return {
        "steps": n_steps,
        "unverified_curator_accepted_steps": unverified_accepts,
        "governor_latch_halt_step": governor_halt_step,
        "initial_total_err_exact": frac_str(total_0),
        "final_unverified_total_err_exact": frac_str(total_end),
        "final_unverified_total_err_dec": format_exact_decimal(total_end, 6),
        "apparent_proxy_reduction_exact": frac_str(proxy_reduction_frac),
        "apparent_proxy_reduction_dec": format_exact_decimal(proxy_reduction_frac, 6),
        "true_total_err_change_exact": frac_str(total_change_frac),
        "true_total_err_change_dec": format_exact_decimal(total_change_frac, 6),
        "goodhart_inversion_occurred": total_end > total_0 and p_cur < p0,
        "trajectory": trajectory,
    }


def detect_skill_graph_cycle_exact(
    edges: Sequence[tuple[str, str]],
) -> dict[str, Any]:
    """
    KF-03 Exact 3-Color DFS Cycle Detector over Directed Skill Dependency Edges.
    Deterministic sorted traversal; returns exact cycle witness if any exists.
    """
    edge_seq = require_list_or_tuple(edges, "edges")
    adj: dict[str, list[str]] = {}
    nodes: set[str] = set()
    for idx, edge in enumerate(edge_seq):
        edge_item = require_list_or_tuple(edge, f"edges[{idx}]")
        if len(edge_item) != 2:
            raise KnowledgeGovernorError("INVALID_EDGE_ARITY", f"edges[{idx}] must be (src, dst)")
        u = require_non_empty_str(edge_item[0], f"edges[{idx}][0]").strip()
        v = require_non_empty_str(edge_item[1], f"edges[{idx}][1]").strip()
        nodes.add(u)
        nodes.add(v)
        adj.setdefault(u, []).append(v)

    for u in adj:
        adj[u] = sorted(set(adj[u]))

    color: dict[str, int] = {n: 0 for n in nodes}  # 0=white, 1=gray, 2=black
    stack: list[str] = []
    cycle_witness: list[str] = []

    def _dfs(u: str) -> bool:
        color[u] = 1
        stack.append(u)
        for v in adj.get(u, []):
            if color[v] == 1:
                pos = stack.index(v)
                cycle_witness.extend(stack[pos:] + [v])
                return True
            if color[v] == 0 and _dfs(v):
                return True
        stack.pop()
        color[u] = 2
        return False

    has_cycle = False
    for node in sorted(nodes):
        if color[node] == 0:
            if _dfs(node):
                has_cycle = True
                break

    return {
        "acyclic": not has_cycle,
        "has_cycle": has_cycle,
        "node_count": len(nodes),
        "edge_count": len(edges),
        "cycle_witness": cycle_witness,
    }


def audit_multi_worker_batch_conflicts(
    proposals: Sequence[Mapping[str, Any]],
    expected_store_revisions: Mapping[str, str],
) -> dict[str, Any]:
    """
    KF-03 Exact Multi-Worker Batch Conflict, LWW Oscillation & Cross-Store CAS Audit:
      - Detects conflicting proposed values for the same (target_store, domain_key)
        within a curation batch (preventing silent Last-Writer-Wins oscillation!).
      - Detects stale base_revision_sha256 mismatches (preventing cross-store split-brain!).
    """
    prop_seq = require_list_or_tuple(proposals, "proposals")
    if len(prop_seq) == 0:
        raise KnowledgeGovernorError("EMPTY_PROPOSAL_BATCH", "proposals batch must be non-empty")
    if not isinstance(expected_store_revisions, Mapping) or len(expected_store_revisions) == 0:
        raise KnowledgeGovernorError("EMPTY_STORE_REVISIONS", "expected_store_revisions must be non-empty")

    by_key: dict[tuple[str, str], dict[str, list[str]]] = {}
    seen_pids: set[str] = set()
    stale_proposals: list[str] = []
    unknown_stores: list[str] = []

    for idx, prop in enumerate(prop_seq):
        if not isinstance(prop, Mapping):
            raise KnowledgeGovernorError("INVALID_BATCH_PROPOSAL", f"proposals[{idx}] must be mapping")
        pid = require_non_empty_str(prop.get("proposal_id"), f"proposals[{idx}].proposal_id").strip()
        if pid in seen_pids:
            raise KnowledgeGovernorError("DUPLICATE_PROPOSAL_ID", f"duplicate proposal_id {pid!r}")
        seen_pids.add(pid)
        store = require_non_empty_str(prop.get("target_store"), f"proposals[{idx}].target_store").strip()
        dkey = require_non_empty_str(prop.get("domain_key"), f"proposals[{idx}].domain_key").strip().lower()
        base_rev = require_non_empty_str(
            prop.get("base_revision_sha256"), f"proposals[{idx}].base_revision_sha256"
        ).strip()
        val = require_non_empty_str(prop.get("proposed_value"), f"proposals[{idx}].proposed_value").strip()
        if store not in expected_store_revisions:
            unknown_stores.append(pid)
        elif base_rev != expected_store_revisions[store]:
            stale_proposals.append(pid)
        by_key.setdefault((store, dkey), {}).setdefault(val, []).append(pid)

    conflicts: list[dict[str, Any]] = []
    for (store, dkey), val_map in sorted(by_key.items()):
        if len(val_map) > 1:
            conflicts.append(
                {
                    "target_store": store,
                    "domain_key": dkey,
                    "conflicting_values": sorted(val_map.keys()),
                    "proposal_ids": sorted(pid for pids in val_map.values() for pid in pids),
                }
            )

    admissible = len(conflicts) == 0 and len(stale_proposals) == 0 and len(unknown_stores) == 0
    return {
        "batch_admissible": admissible,
        "proposal_count": len(proposals),
        "conflict_count": len(conflicts),
        "conflicts": conflicts,
        "stale_cas_proposals": sorted(stale_proposals),
        "unknown_store_proposals": sorted(unknown_stores),
        "lww_oscillation_blocked": len(conflicts) > 0,
    }


def evaluate_curator_proposal(
    proposal: Mapping[str, Any],
    policy: Mapping[str, Any],
) -> dict[str, Any]:
    """
    Master Fail-Closed 3-Role Verified Knowledge Factory Curator Governor (KF-01..KF-05).

    Enforces ALL 6 orthogonal trust invariants:
      1. 3-Role Separation of Duties: verifier_id != curator_id AND verifier_id != worker_id.
      2. Ring-0 Immutable Lock: recursive case-insensitive scan rejects any Ring-0 key in payload_patch.
      3. KF-01 Lattice Gate: Biba Integrity + Bell-LaPadula Confidentiality.
      4. KF-02 Goodhart Outside-Anchor Latch: rejects any update where outside_err_after > outside_err_before.
      5. KF-03 CAS Revision + Skill DAG Acyclicity: exact store base_revision_sha256 match + cycle-free graph.
      6. KF-04 Monotone Capability Attenuation + KF-05 Tao Observability Gate (G1..G5).
    """
    if not isinstance(proposal, Mapping):
        raise KnowledgeGovernorError("INVALID_PROPOSAL_TYPE", "proposal must be mapping")
    if not isinstance(policy, Mapping):
        raise KnowledgeGovernorError("INVALID_POLICY_TYPE", "policy must be mapping")
    verify_no_floats(proposal, "proposal")
    verify_no_floats(policy, "policy")

    if frozenset(proposal.keys()) != EXPECTED_PROPOSAL_KEYS:
        raise KnowledgeGovernorError("PROPOSAL_SCHEMA_MISMATCH", "proposal keys must match exact schema")
    if frozenset(policy.keys()) != EXPECTED_POLICY_KEYS:
        raise KnowledgeGovernorError("POLICY_SCHEMA_MISMATCH", "policy keys must match exact schema")

    proposal_id = require_non_empty_str(proposal["proposal_id"], "proposal_id")
    worker_id = require_non_empty_str(proposal["worker_id"], "worker_id")
    curator_id = require_non_empty_str(proposal["curator_id"], "curator_id")
    verifier_id = require_non_empty_str(proposal["verifier_id"], "verifier_id")
    target_store = require_non_empty_str(proposal["target_store"], "target_store")
    domain_key = require_non_empty_str(proposal["domain_key"], "domain_key")
    if _KEY_IDENT_RE.match(domain_key) is None:
        raise KnowledgeGovernorError("INVALID_DOMAIN_KEY", f"domain_key={domain_key!r} invalid")
    base_rev = require_non_empty_str(proposal["base_revision_sha256"], "base_revision_sha256")
    if _SHA256_HEX_RE.match(base_rev) is None:
        raise KnowledgeGovernorError("INVALID_BASE_REV_SHA", "base_revision_sha256 must be 64 lowercase hex")
    require_non_empty_str(proposal["proposed_value"], "proposed_value")
    if not isinstance(proposal["payload_patch"], Mapping):
        raise KnowledgeGovernorError("INVALID_PATCH_TYPE", "payload_patch must be mapping")
    creates_cron = require_exact_bool(proposal["creates_cron_trigger"], "creates_cron_trigger")
    cron_approved = require_exact_bool(proposal["cron_owner_approved"], "cron_owner_approved")

    p_before = require_exact_fraction(proposal["proxy_err_before"], "proxy_err_before", Fraction(0))
    p_after = require_exact_fraction(proposal["proxy_err_after"], "proxy_err_after", Fraction(0))
    o_before = require_exact_fraction(proposal["outside_err_before"], "outside_err_before", Fraction(0))
    o_after = require_exact_fraction(proposal["outside_err_after"], "outside_err_after", Fraction(0))

    contract_sha = proposal["frozen_contract_sha256"]
    leakage = require_exact_int(proposal["split_leakage_count"], "split_leakage_count", min_value=0)
    net_status = proposal["network_audit_status"]
    r4_runs = require_exact_int(proposal["r4_isolated_parity_runs"], "r4_isolated_parity_runs", min_value=0)
    r5_total = require_exact_int(proposal["r5_mutation_total"], "r5_mutation_total", min_value=0)
    r5_killed = require_exact_int(
        proposal["r5_mutation_killed"], "r5_mutation_killed", min_value=0, max_value=r5_total
    )

    exp_revs = policy["expected_store_revisions"]
    if not isinstance(exp_revs, Mapping) or len(exp_revs) == 0:
        raise KnowledgeGovernorError("INVALID_POLICY_REVS", "expected_store_revisions must be non-empty mapping")
    for s_name, s_rev in exp_revs.items():
        require_non_empty_str(s_name, "expected_store_revisions.<key>")
        s_rev_str = require_non_empty_str(s_rev, f"expected_store_revisions[{s_name}]")
        if _SHA256_HEX_RE.match(s_rev_str) is None:
            raise KnowledgeGovernorError("INVALID_POLICY_REV_SHA", f"store {s_name} rev must be 64 lowercase hex")

    store_tiers = policy["store_tiers"]
    if not isinstance(store_tiers, Mapping) or set(store_tiers.keys()) != set(exp_revs.keys()):
        raise KnowledgeGovernorError(
            "INVALID_POLICY_STORE_TIERS",
            "store_tiers must be a mapping matching expected_store_revisions keys",
        )
    for s_name, s_tier in store_tiers.items():
        t_str = require_non_empty_str(s_tier, f"store_tiers[{s_name}]")
        if t_str not in TARGET_TIER_POLICIES:
            raise KnowledgeGovernorError("UNKNOWN_STORE_TIER", f"unknown store tier {t_str!r}")

    allowed_scopes = {
        require_non_empty_str(s, "allowed_scopes").strip()
        for s in require_list_or_tuple(policy["allowed_scopes"], "allowed_scopes")
    }
    allowed_endpoints = {
        require_non_empty_str(e, "allowed_endpoints").strip()
        for e in require_list_or_tuple(policy["allowed_endpoints"], "allowed_endpoints")
    }
    req_scopes = {
        require_non_empty_str(s, "requested_scopes").strip()
        for s in require_list_or_tuple(proposal["requested_scopes"], "requested_scopes")
    }
    req_endpoints = {
        require_non_empty_str(e, "requested_endpoints").strip()
        for e in require_list_or_tuple(proposal["requested_endpoints"], "requested_endpoints")
    }
    existing_edges = require_list_or_tuple(policy["existing_skill_graph"], "existing_skill_graph")
    proposed_edges = require_list_or_tuple(proposal["proposed_skill_edges"], "proposed_skill_edges")

    failure_reasons: list[str] = []

    # 1. Strict 3-Role Separation of Duties (normalized strip + lower)
    w_norm = worker_id.strip().lower()
    c_norm = curator_id.strip().lower()
    v_norm = verifier_id.strip().lower()
    if v_norm == c_norm:
        failure_reasons.append("KF05_CURATOR_SELF_APPROVAL")
    if v_norm == w_norm:
        failure_reasons.append("KF05_WORKER_SELF_APPROVAL")
    if w_norm == c_norm:
        failure_reasons.append("KF05_WORKER_CURATOR_COLLAPSE")

    # 2. Ring-0 Immutable Section Lock (both domain_key AND recursive payload_patch)
    ring0_hits = scan_ring0_tamper_keys(proposal["payload_patch"], "payload_patch")
    if _is_ring0_forbidden_identifier(domain_key):
        ring0_hits = sorted(ring0_hits + [f"domain_key.{domain_key}"])
    if len(ring0_hits) != 0:
        failure_reasons.append("KF04_RING0_IMMUTABLE_TAMPER")

    # 3. KF-01 Store-Tier Binding & Information Flow Lattice (Biba + Bell-LaPadula)
    store_key = target_store.strip()
    effective_tier = store_tiers[store_key] if store_key in store_tiers else proposal["target_tier"]
    if store_key in store_tiers and proposal["target_tier"] != store_tiers[store_key]:
        failure_reasons.append("KF01_STORE_TIER_MISMATCH")
    lattice = audit_information_flow_lattice(
        source_integrity_labels=proposal["source_integrity_labels"],
        source_confidentiality_labels=proposal["source_confidentiality_labels"],
        target_tier=effective_tier,
        human_admin_countersigned=proposal["human_admin_countersigned"],
    )
    if not lattice["admissible"]:
        failure_reasons.extend(lattice["failure_reasons"])

    # 4. KF-02 Pre-Adaptation Goodhart Outside-Anchor Latch & Proxy Regression Guard
    if o_after > o_before:
        failure_reasons.append("KF02_GOODHART_OUTSIDE_ANCHOR_DRIFT")
    if p_after > p_before:
        failure_reasons.append("KF02_PROXY_REGRESSION")

    # 5. KF-03 CAS Revision Lock & Skill Dependency Acyclicity
    if store_key not in exp_revs:
        failure_reasons.append("KF03_UNKNOWN_TARGET_STORE")
    elif base_rev != exp_revs[store_key]:
        failure_reasons.append("KF03_STALE_CAS_REVISION")

    all_edges = list(existing_edges) + list(proposed_edges)
    dag_check = detect_skill_graph_cycle_exact(all_edges)
    if dag_check["has_cycle"]:
        failure_reasons.append("KF03_SKILL_DEPENDENCY_CYCLE")

    # 6. KF-04 Monotone Capability / Secret-Proxy / Ambient-Cron Attenuation
    if not req_scopes.issubset(allowed_scopes):
        failure_reasons.append("KF04_SCOPE_PRIVILEGE_ESCALATION")
    if not req_endpoints.issubset(allowed_endpoints):
        failure_reasons.append("KF04_ENDPOINT_ALLOWLIST_VIOLATION")
    if creates_cron and not cron_approved:
        failure_reasons.append("KF04_UNAPPROVED_AMBIENT_CRON")

    # 7. KF-05 Tao Observability Process Gates (G1..G5)
    if not isinstance(contract_sha, str) or _SHA256_HEX_RE.match(contract_sha) is None:
        failure_reasons.append("KF05_FROZEN_CONTRACT_SHA_INVALID")
    if leakage != 0:
        failure_reasons.append("KF05_SPLIT_LEAKAGE_DETECTED")
    if not isinstance(net_status, str) or net_status != VERIFIED_NETWORK_POLICY:
        failure_reasons.append("KF05_UNAUDITED_NETWORK_ACCESS")
    if r4_runs < 3:
        failure_reasons.append("KF05_R4_PARITY_BELOW_3")
    if r5_total == 0:
        failure_reasons.append("KF05_R5_MUTATION_TOTAL_ZERO")
    if r5_killed != r5_total:
        failure_reasons.append("KF05_R5_MUTATION_INCOMPLETE")

    admissible = len(failure_reasons) == 0
    new_rev = (
        canonical_sha256(
            {
                "base_revision_sha256": base_rev,
                "domain_key": domain_key,
                "proposed_value": proposal["proposed_value"],
                "payload_patch": proposal["payload_patch"],
                "verifier_id": verifier_id,
            }
        )
        if admissible
        else base_rev
    )
    return {
        "proposal_id": proposal_id,
        "verdict": "PROMOTED" if admissible else "REJECTED_GOVERNOR",
        "admissible": admissible,
        "failure_reasons": failure_reasons,
        "ring0_tamper_hits": ring0_hits,
        "lattice_audit": lattice,
        "dag_audit": dag_check,
        "total_err_before_exact": frac_str(p_before + o_before),
        "total_err_after_exact": frac_str(p_after + o_after),
        "new_revision_sha256": new_rev,
    }


def build_ledger_entry(
    *,
    seq: int,
    prev_hash: str,
    proposal_id: str,
    verdict: str,
    curator_id: str,
    verifier_id: str,
    target_store: str,
    base_revision_sha256: str,
    new_revision_sha256: str,
) -> dict[str, Any]:
    """Construct a deterministic SHA-256 hash-chained Knowledge Factory ledger entry."""
    s = require_exact_int(seq, "seq", min_value=0)
    prev = require_non_empty_str(prev_hash, "prev_hash")
    if _SHA256_HEX_RE.match(prev) is None:
        raise KnowledgeGovernorError("INVALID_PREV_HASH", "prev_hash must be 64 lowercase hex")
    pid = require_non_empty_str(proposal_id, "proposal_id")
    verd = require_non_empty_str(verdict, "verdict")
    if verd not in ("PROMOTED", "REJECTED_GOVERNOR"):
        raise KnowledgeGovernorError("INVALID_VERDICT", f"invalid verdict {verd!r}")
    cur = require_non_empty_str(curator_id, "curator_id")
    ver = require_non_empty_str(verifier_id, "verifier_id")
    store = require_non_empty_str(target_store, "target_store")
    b_rev = require_non_empty_str(base_revision_sha256, "base_revision_sha256")
    n_rev = require_non_empty_str(new_revision_sha256, "new_revision_sha256")
    if _SHA256_HEX_RE.match(b_rev) is None or _SHA256_HEX_RE.match(n_rev) is None:
        raise KnowledgeGovernorError("INVALID_REV_HASH", "revisions must be 64 lowercase hex")
    if verd == "PROMOTED" and cur.strip().lower() == ver.strip().lower():
        raise KnowledgeGovernorError("LEDGER_SELF_APPROVAL", "PROMOTED ledger entry cannot self-approve")
    if verd == "REJECTED_GOVERNOR" and n_rev != b_rev:
        raise KnowledgeGovernorError("LEDGER_REJECTED_MUTATED_REV", "REJECTED entry cannot mutate revision")

    body = {
        "schema": LEDGER_SCHEMA,
        "seq": s,
        "prev_hash": prev,
        "proposal_id": pid,
        "verdict": verd,
        "curator_id": cur,
        "verifier_id": ver,
        "target_store": store,
        "base_revision_sha256": b_rev,
        "new_revision_sha256": n_rev,
    }
    entry = dict(body)
    entry["entry_hash"] = canonical_sha256(body)
    return entry


def verify_knowledge_ledger_chain(entries: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    """Fail-closed semantic and cryptographic verification of a SHA-256 Knowledge Factory ledger."""
    entry_seq = require_list_or_tuple(entries, "entries")
    if len(entry_seq) == 0:
        raise KnowledgeGovernorError("EMPTY_LEDGER", "ledger must contain >= 1 entry")
    expected_prev = GENESIS_LEDGER_HASH
    for idx, item in enumerate(entry_seq):
        if not isinstance(item, Mapping):
            raise KnowledgeGovernorError("INVALID_LEDGER_ENTRY", f"entries[{idx}] must be mapping")
        verify_no_floats(item, f"entries[{idx}]")
        if frozenset(item.keys()) != EXPECTED_LEDGER_ENTRY_KEYS:
            raise KnowledgeGovernorError("LEDGER_SCHEMA_MISMATCH", f"entries[{idx}] schema mismatch")
        if item["schema"] != LEDGER_SCHEMA:
            raise KnowledgeGovernorError("LEDGER_VERSION_MISMATCH", f"entries[{idx}] bad schema")
        seq_val = require_exact_int(item["seq"], f"entries[{idx}].seq", min_value=0)
        if seq_val != idx:
            raise KnowledgeGovernorError("LEDGER_SEQ_GAP", f"entries[{idx}] seq={seq_val} != {idx}")
        if item["prev_hash"] != expected_prev:
            raise KnowledgeGovernorError("LEDGER_CHAIN_FORK", f"entries[{idx}] prev_hash mismatch")
        require_non_empty_str(item["proposal_id"], f"entries[{idx}].proposal_id")
        cur_id = require_non_empty_str(item["curator_id"], f"entries[{idx}].curator_id")
        ver_id = require_non_empty_str(item["verifier_id"], f"entries[{idx}].verifier_id")
        require_non_empty_str(item["target_store"], f"entries[{idx}].target_store")
        verdict = require_non_empty_str(item["verdict"], f"entries[{idx}].verdict")
        if verdict not in ("PROMOTED", "REJECTED_GOVERNOR"):
            raise KnowledgeGovernorError("LEDGER_INVALID_VERDICT", f"entries[{idx}] bad verdict {verdict!r}")
        b_rev = require_non_empty_str(item["base_revision_sha256"], f"entries[{idx}].base_revision_sha256")
        n_rev = require_non_empty_str(item["new_revision_sha256"], f"entries[{idx}].new_revision_sha256")
        if _SHA256_HEX_RE.match(b_rev) is None or _SHA256_HEX_RE.match(n_rev) is None:
            raise KnowledgeGovernorError("LEDGER_INVALID_REV_HASH", f"entries[{idx}] revision not 64 hex")
        if verdict == "PROMOTED" and cur_id.strip().lower() == ver_id.strip().lower():
            raise KnowledgeGovernorError("LEDGER_SELF_APPROVAL", f"entries[{idx}] self-approved PROMOTED")
        if verdict == "REJECTED_GOVERNOR" and n_rev != b_rev:
            raise KnowledgeGovernorError("LEDGER_REJECTED_MUTATED_REV", f"entries[{idx}] REJECTED mutated rev")
        body = {k: v for k, v in item.items() if k != "entry_hash"}
        recomputed = canonical_sha256(body)
        if item["entry_hash"] != recomputed:
            raise KnowledgeGovernorError("LEDGER_HASH_TAMPER", f"entries[{idx}] entry_hash tamper")
        expected_prev = recomputed
    return {
        "verified": True,
        "entry_count": len(entry_seq),
        "head_hash": expected_prev,
    }
