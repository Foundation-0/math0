"""Pure-Z / Pure-Q Oracle for Track S11 (AUDIT-110): Erlang/OTP Supervision Tree Semantics.

Formalizes Erlang/OTP supervision tree operational semantics in exact integer and
rational arithmetic (zero IEEE-754 floats, zero bare assert statements, pure Python 3
stdlib only), bridging Moissanite-Labs/exo#1200 SupervisionPolicy and
Foundation-0/aletheia v2.1+ Two-Zone Hybrid Swarms:

  Pillar 1 (p1_restart_policy_matrix):
    Exhaustive 3x3 restart transition operator over
    {permanent, transient, temporary} x {normal, shutdown, abnormal}, plus
    must-fail controls for illegal temporary and clean-transient restarts.

  Pillar 2 (p2_restart_strategies_and_non_churn):
    Deterministic ordered-child semantics for all three OTP strategies
    (one_for_one, one_for_all, rest_for_one) with reverse-order termination and
    forward-order restart traces, certifying the Frozen-Snapshot rest_for_one
    Non-Churn Invariant against a one_for_one mid-audit snapshot-churn control.

  Pillar 3 (p3_sliding_window_intensity_escalation):
    Exact pure-Z/Q sliding-window restart intensity (max_restarts, window_ticks)
    matching OTP supervisor.erl inclusive boundary (t_now - t_restart <= window_ticks),
    non-dyadic rational ticks (e.g. 1/3), monotonic multi-level tree escalation
    (worker -> sub_sup -> root_sup), plus intensity-bypass and non-monotonic controls.

  Pillar 4 (p4_monitor_vs_link_fault_isolation):
    Exact process-table signal propagation comparing unidirectional monitor
    (Zone-B verifier crash or external exit(verifier_1, kill) -> reason "killed"
    emits DOWN + blocks promotion with 0 collateral kills) against bidirectional
    link with trap_exit=False (kills coordinator + siblings) and trap_exit=True
    (traps abnormal EXIT and propagated "killed" from external exit(verifier_1, kill),
    while an explicit direct untrappable "kill" signal targeting coordinator still
    terminates coordinator with reason "killed").

  Pillar 5 (p5_exo1200_aletheia_bridge):
    Exact operational bridge extending Moissanite-Labs/exo#1200 SupervisionPolicy
    (pinned group_supervision.py semantics) and Foundation-0/aletheia v2.1+
    Two-Zone Hybrid Swarms, certifying clean end-to-end supervision plus three
    adversarial must-fail controls (promotion while DOWN, stopped-task restart,
    unreconciled external effects).

Honest Law-4 novelty tier:
  - N0: Classical Erlang/OTP supervision tree semantics (Armstrong 2003;
    Armstrong, Virding, Wikstrom & Williams 1996; Erlang/OTP supervisor.erl)
    and self-contained pure-Z/Q operational restatement/certifier bridging
    exo#1200 + aletheia v2.1+ (no new mathematical claim above N0).
"""
from __future__ import annotations

import copy
import hashlib
import json
import math
import re
from collections import deque
from fractions import Fraction
from typing import Any

SCHEMA_VERSION = "erlang-otp-supervision-oracle/v1"
TRACK_ID = "track-s11-erlang-otp-supervision"
AUDIT_ID = "AUDIT-110"

HEX64_RE = re.compile(r"^[0-9a-f]{64}$")
FRAC_RE = re.compile(r"^(0|[1-9][0-9]*)/([1-9][0-9]*)$")

RESTART_POLICIES: tuple[str, ...] = ("permanent", "transient", "temporary")
EXIT_REASONS: tuple[str, ...] = ("normal", "shutdown", "abnormal")
SIGNAL_EXIT_REASONS: tuple[str, ...] = ("normal", "shutdown", "abnormal", "kill", "killed")
RESTART_STRATEGIES: tuple[str, ...] = ("one_for_one", "one_for_all", "rest_for_one")

EXO1200_FAILURE_CLASSES: frozenset[str] = frozenset({
    "unknown", "transient", "denied", "spend_limit", "cancelled", "permanent",
})
EXO1200_EFFECT_CLASSES: frozenset[str] = frozenset({
    "unknown", "not_dispatched", "external",
})

# Pinned primary reference metadata from Moissanite-Labs/exo#1200.
EXO1200_REF_COMMIT = "ccdc929ace0a62152e23e10b0fd219d76df7b6f1"
EXO1200_SUPERVISION_SHA256 = "b5c38a6f60151093eb320e431577fe48f1f5022c66058b87f99f55559c38f9e8"

# Deterministic non-uniform 64-hex fixture digests for snapshot verification.
SNAPSHOT_SHA_V1 = hashlib.sha256(b"aletheia-airlock-snapshot-v1").hexdigest()
SNAPSHOT_SHA_V2 = hashlib.sha256(b"aletheia-airlock-snapshot-v2").hexdigest()


class OtpSupervisionError(ValueError):
    """Typed fail-closed error carrying an explicit machine-readable error code."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


# ---------------------------------------------------------------------------
# Strict Pure-Z / Pure-Q Validation & Serialization Primitives
# ---------------------------------------------------------------------------

def _is_nonempty_str(val: Any) -> bool:
    return type(val) is str and len(val.strip()) > 0


def _in_str_set(val: Any, allowed: Any) -> bool:
    return type(val) is str and val in allowed


def _is_hex64(val: Any) -> bool:
    return type(val) is str and bool(HEX64_RE.fullmatch(val)) and len(set(val)) > 1


def contains_float(obj: Any) -> bool:
    """Return True if obj contains any float, complex, set, frozenset, or non-JSON type."""
    if obj is None or type(obj) in (bool, int, str):
        return False
    if type(obj) is dict:
        return any(contains_float(k) or contains_float(v) for k, v in obj.items())
    if type(obj) in (list, tuple):
        return any(contains_float(v) for v in obj)
    return True


def canonical_json_bytes(obj: Any) -> bytes:
    if contains_float(obj):
        raise OtpSupervisionError("ERR_FLOAT_FORBIDDEN", "float or non-JSON value forbidden")
    try:
        rendered = json.dumps(
            obj,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        )
    except (TypeError, ValueError) as exc:
        raise OtpSupervisionError("ERR_CANONICAL_JSON", str(exc)) from exc
    return rendered.encode("ascii")


def canonical_sha256(obj: Any) -> str:
    return hashlib.sha256(canonical_json_bytes(obj)).hexdigest()


def frac_to_str(q: Fraction) -> str:
    if type(q) is not Fraction:
        raise OtpSupervisionError("ERR_INVALID_FRACTION", "expected Fraction")
    return f"{q.numerator}/{q.denominator}"


def parse_nonneg_fraction(val: Any, label: str = "tick") -> Fraction:
    """Convert strict non-negative int, Fraction, or reduced 'p/q' str to exact Fraction."""
    if type(val) is int:
        if val < 0:
            raise OtpSupervisionError("ERR_NEGATIVE_TICK", f"{label} must be >= 0")
        return Fraction(val, 1)
    if type(val) is Fraction:
        if val < 0:
            raise OtpSupervisionError("ERR_NEGATIVE_TICK", f"{label} must be >= 0")
        return val
    if type(val) is str:
        if len(val) > 64 or not FRAC_RE.fullmatch(val):
            raise OtpSupervisionError("ERR_INVALID_FRACTION_STR", f"{label} invalid fraction string")
        num_s, den_s = val.split("/")
        num = int(num_s)
        den = int(den_s)
        if math.gcd(num, den) != 1:
            raise OtpSupervisionError("ERR_UNREDUCED_FRACTION", f"{label} must be reduced")
        return Fraction(num, den)
    raise OtpSupervisionError("ERR_INVALID_TICK_TYPE", f"{label} must be int, Fraction, or p/q str")


def _req_exact_keys(mapping: Any, expected: set[str] | frozenset[str], label: str) -> dict[str, Any]:
    if type(mapping) is not dict or set(mapping.keys()) != set(expected):
        raise OtpSupervisionError("ERR_SCHEMA_KEYS", f"{label} keyset mismatch")
    return mapping


def _req_strict_str_eq(val: Any, expected: str, label: str) -> None:
    if type(val) is not str or val != expected:
        raise OtpSupervisionError("ERR_SCHEMA_STR", f"{label} must equal {expected!r}")


def _req_strict_int_range(val: Any, low: int, high: int | None, label: str) -> int:
    if type(val) is not int or val < low:
        raise OtpSupervisionError("ERR_SCHEMA_INT", f"{label} must be int >= {low}")
    if high is not None and val > high:
        raise OtpSupervisionError("ERR_SCHEMA_INT", f"{label} must be int <= {high}")
    return val


def _req_bool_eq(val: Any, expected: bool, label: str) -> None:
    if val is not expected:
        raise OtpSupervisionError("ERR_SCHEMA_BOOL", f"{label} must be {expected!r}")


def _req_str_list(val: Any, expected: list[str] | None, label: str) -> list[str]:
    if type(val) is not list or any(not _is_nonempty_str(item) for item in val):
        raise OtpSupervisionError("ERR_SCHEMA_LIST", f"{label} must be list[nonempty str]")
    if expected is not None and val != expected:
        raise OtpSupervisionError("ERR_SCHEMA_LIST", f"{label} mismatch")
    return val


def _req_strict_int_list(val: Any, expected: list[int], label: str) -> list[int]:
    if type(val) is not list or any(type(item) is not int for item in val) or val != expected:
        raise OtpSupervisionError("ERR_SCHEMA_INT_LIST", f"{label} mismatch")
    return val


def _req_hex64(val: Any, label: str) -> str:
    if not _is_hex64(val):
        raise OtpSupervisionError("ERR_INVALID_SHA256", f"{label} must be non-uniform 64-hex")
    return val


# ---------------------------------------------------------------------------
# Pillar 1: Exact 3x3 OTP Restart Policy x Exit Reason Operator
# ---------------------------------------------------------------------------

def otp_should_restart(policy: str, exit_reason: str) -> dict[str, Any]:
    """Exact Erlang/OTP child restart predicate over policy x exit_reason."""
    if not _in_str_set(policy, RESTART_POLICIES):
        raise OtpSupervisionError("ERR_INVALID_POLICY", f"unknown restart policy: {policy!r}")
    if not _in_str_set(exit_reason, EXIT_REASONS):
        raise OtpSupervisionError("ERR_INVALID_EXIT_REASON", f"unknown exit reason: {exit_reason!r}")

    if policy == "permanent":
        restart = True
    elif policy == "transient":
        restart = exit_reason == "abnormal"
    else:
        restart = False

    return {
        "policy": policy,
        "exit_reason": exit_reason,
        "should_restart": restart,
        "action": "restart" if restart else "drop_child",
    }


def certify_restart_decision(policy: str, exit_reason: str, observed_restarted: bool) -> dict[str, Any]:
    """Fail-closed verifier checking an observed restart decision against OTP semantics."""
    if type(observed_restarted) is not bool:
        raise OtpSupervisionError("ERR_INVALID_OBSERVED_BOOL", "observed_restarted must be bool")
    expected = otp_should_restart(policy, exit_reason)
    if observed_restarted is expected["should_restart"]:
        return {
            "passed": True,
            "error_code": None,
            "policy": policy,
            "exit_reason": exit_reason,
            "expected_restart": expected["should_restart"],
            "observed_restart": observed_restarted,
        }
    if policy == "temporary":
        code = "ERR_TEMPORARY_CHILD_RESTARTED"
    elif observed_restarted:
        code = "ERR_TRANSIENT_CLEAN_EXIT_RESTARTED"
    else:
        code = "ERR_REQUIRED_RESTART_SKIPPED"
    return {
        "passed": False,
        "error_code": code,
        "policy": policy,
        "exit_reason": exit_reason,
        "expected_restart": expected["should_restart"],
        "observed_restart": observed_restarted,
    }


def run_pillar_1() -> dict[str, Any]:
    cells: list[dict[str, Any]] = []
    restart_count = 0
    for policy in RESTART_POLICIES:
        for reason in EXIT_REASONS:
            row = otp_should_restart(policy, reason)
            if row["should_restart"]:
                restart_count += 1
            cells.append(row)

    mf_temp = certify_restart_decision("temporary", "abnormal", True)
    mf_trans_normal = certify_restart_decision("transient", "normal", True)
    mf_trans_shutdown = certify_restart_decision("transient", "shutdown", True)
    trans_rejected = all([
        mf_trans_normal["passed"] is False,
        mf_trans_shutdown["passed"] is False,
    ])

    return {
        "passed": all([
            len(cells) == 9,
            restart_count == 4,
            mf_temp["passed"] is False,
            trans_rejected,
        ]),
        "matrix_cells_verified": len(cells),
        "restart_true_count": restart_count,
        "restart_false_count": len(cells) - restart_count,
        "transition_table": cells,
        "must_fail_temporary_restarted": {
            "rejected": mf_temp["passed"] is False,
            "error_code": mf_temp["error_code"],
        },
        "must_fail_transient_clean_exit_restarted": {
            "rejected": trans_rejected,
            "normal_error_code": mf_trans_normal["error_code"],
            "shutdown_error_code": mf_trans_shutdown["error_code"],
        },
    }


# ---------------------------------------------------------------------------
# Pillar 2: All 3 OTP Restart Strategies & Frozen-Snapshot Non-Churn Invariant
# ---------------------------------------------------------------------------

def _validate_child_specs(children: Any) -> list[dict[str, Any]]:
    if type(children) is not list or len(children) == 0:
        raise OtpSupervisionError("ERR_INVALID_CHILDREN", "children must be nonempty list")
    seen: set[str] = set()
    cleaned: list[dict[str, Any]] = []
    expected_keys = {"id", "policy", "generation", "snapshot_sha256", "alive"}
    for idx, ch in enumerate(children):
        _req_exact_keys(ch, expected_keys, f"child[{idx}]")
        cid = ch["id"]
        if not _is_nonempty_str(cid) or cid in seen:
            raise OtpSupervisionError("ERR_INVALID_CHILD_ID", f"invalid or duplicate child id {cid!r}")
        seen.add(cid)
        if not _in_str_set(ch["policy"], RESTART_POLICIES):
            raise OtpSupervisionError("ERR_INVALID_POLICY", f"bad policy on {cid}")
        _req_strict_int_range(ch["generation"], 1, None, f"child[{idx}].generation")
        _req_hex64(ch["snapshot_sha256"], f"child[{idx}].snapshot_sha256")
        if type(ch["alive"]) is not bool:
            raise OtpSupervisionError("ERR_INVALID_ALIVE", f"child[{idx}].alive must be bool")
        cleaned.append(copy.deepcopy(ch))
    return cleaned


def _should_strategy_restart(child_policy: str, is_crashed: bool, was_alive: bool) -> bool:
    """Exact OTP supervisor.erl restart rule for sibling/crashed children under strategy restarts.

    Temporary children are never restarted; permanent children are always restarted;
    transient children are restarted iff they crashed or were running when terminated.
    """
    if child_policy == "temporary":
        return False
    if child_policy == "permanent":
        return True
    return is_crashed or was_alive


def apply_strategy_crash(
    strategy: str,
    children: list[dict[str, Any]],
    crashed_id: str,
    exit_reason: str,
    new_snapshot_sha256: str | None = None,
) -> dict[str, Any]:
    """Apply an exact Erlang/OTP strategy transition when crashed_id terminates."""
    if not _in_str_set(strategy, RESTART_STRATEGIES):
        raise OtpSupervisionError("ERR_INVALID_STRATEGY", f"unknown strategy {strategy!r}")
    state = _validate_child_specs(children)
    if new_snapshot_sha256 is not None:
        _req_hex64(new_snapshot_sha256, "new_snapshot_sha256")

    idx_map = {c["id"]: i for i, c in enumerate(state)}
    if not _in_str_set(crashed_id, idx_map):
        raise OtpSupervisionError("ERR_UNKNOWN_CHILD", f"unknown crashed child {crashed_id!r}")
    idx = idx_map[crashed_id]
    if not state[idx]["alive"]:
        raise OtpSupervisionError("ERR_CHILD_ALREADY_DEAD", f"child {crashed_id!r} already dead")

    decision = otp_should_restart(state[idx]["policy"], exit_reason)
    state[idx]["alive"] = False

    terminated_order: list[str] = []
    restarted_order: list[str] = []

    if decision["should_restart"]:
        was_alive = [c["alive"] for c in state]
        if strategy == "one_for_one":
            terminate_indices: list[int] = []
            candidate_restart = [idx]
        elif strategy == "one_for_all":
            terminate_indices = [i for i in range(len(state) - 1, -1, -1) if state[i]["alive"]]
            candidate_restart = list(range(len(state)))
        else:
            # rest_for_one: terminate downstream children in reverse start order,
            # leaving upstream children [0 .. idx-1] untouched.
            terminate_indices = [i for i in range(len(state) - 1, idx, -1) if state[i]["alive"]]
            candidate_restart = list(range(idx, len(state)))

        restart_indices = [
            i for i in candidate_restart
            if _should_strategy_restart(state[i]["policy"], i == idx, was_alive[i])
        ]

        for ti in terminate_indices:
            state[ti]["alive"] = False
            terminated_order.append(state[ti]["id"])

        for ri in restart_indices:
            state[ri]["alive"] = True
            state[ri]["generation"] += 1
            if new_snapshot_sha256 is not None:
                state[ri]["snapshot_sha256"] = new_snapshot_sha256
            restarted_order.append(state[ri]["id"])

    return {
        "strategy": strategy,
        "crashed_id": crashed_id,
        "exit_reason": exit_reason,
        "restarted": decision["should_restart"],
        "terminated_order": terminated_order,
        "restarted_order": restarted_order,
        "children_after": state,
    }


def verify_snapshot_non_churn(
    children_after: list[dict[str, Any]],
    author_id: str,
    downstream_ids: list[str],
) -> dict[str, Any]:
    """Certify that every alive downstream snapshot/verifier child matches author's SHA-256."""
    state = _validate_child_specs(children_after)
    by_id = {c["id"]: c for c in state}
    if not _in_str_set(author_id, by_id):
        raise OtpSupervisionError("ERR_UNKNOWN_AUTHOR", f"unknown author {author_id!r}")
    if type(downstream_ids) is not list or len(downstream_ids) == 0:
        raise OtpSupervisionError("ERR_INVALID_DOWNSTREAM", "downstream_ids must be nonempty list")
    author_sha = by_id[author_id]["snapshot_sha256"]
    stale: list[str] = []
    for did in downstream_ids:
        if not _in_str_set(did, by_id):
            raise OtpSupervisionError("ERR_UNKNOWN_DOWNSTREAM", f"unknown downstream {did!r}")
        if by_id[did]["alive"] and by_id[did]["snapshot_sha256"] != author_sha:
            stale.append(did)
    return {
        "passed": len(stale) == 0,
        "error_code": None if len(stale) == 0 else "ERR_SNAPSHOT_CHURN",
        "author_snapshot_sha256": author_sha,
        "stale_downstream_ids": stale,
        "stale_count": len(stale),
    }


def run_pillar_2() -> dict[str, Any]:
    base_pipeline = [
        {"id": "planner", "policy": "permanent", "generation": 1, "snapshot_sha256": SNAPSHOT_SHA_V1, "alive": True},
        {"id": "author", "policy": "transient", "generation": 1, "snapshot_sha256": SNAPSHOT_SHA_V1, "alive": True},
        {"id": "airlock_snapshot", "policy": "permanent", "generation": 1, "snapshot_sha256": SNAPSHOT_SHA_V1, "alive": True},
        {"id": "verifier_a", "policy": "permanent", "generation": 1, "snapshot_sha256": SNAPSHOT_SHA_V1, "alive": True},
        {"id": "verifier_b", "policy": "permanent", "generation": 1, "snapshot_sha256": SNAPSHOT_SHA_V1, "alive": True},
    ]
    downstream = ["airlock_snapshot", "verifier_a", "verifier_b"]

    res_o4o = apply_strategy_crash("one_for_one", base_pipeline, "author", "abnormal", SNAPSHOT_SHA_V2)
    res_o4a = apply_strategy_crash("one_for_all", base_pipeline, "author", "abnormal", SNAPSHOT_SHA_V2)
    res_r4o = apply_strategy_crash("rest_for_one", base_pipeline, "author", "abnormal", SNAPSHOT_SHA_V2)

    non_churn_r4o = verify_snapshot_non_churn(res_r4o["children_after"], "author", downstream)
    churn_o4o = verify_snapshot_non_churn(res_o4o["children_after"], "author", downstream)
    planner_untouched = all([
        res_r4o["children_after"][0]["generation"] == 1,
        res_r4o["children_after"][0]["snapshot_sha256"] == SNAPSHOT_SHA_V1,
    ])

    return {
        "passed": all([
            non_churn_r4o["passed"] is True,
            planner_untouched is True,
            churn_o4o["passed"] is False,
            churn_o4o["error_code"] == "ERR_SNAPSHOT_CHURN",
        ]),
        "snapshot_sha_v1": SNAPSHOT_SHA_V1,
        "snapshot_sha_v2": SNAPSHOT_SHA_V2,
        "one_for_one": {
            "terminated_order": res_o4o["terminated_order"],
            "restarted_order": res_o4o["restarted_order"],
            "generations_after": [c["generation"] for c in res_o4o["children_after"]],
        },
        "one_for_all": {
            "terminated_order": res_o4a["terminated_order"],
            "restarted_order": res_o4a["restarted_order"],
            "generations_after": [c["generation"] for c in res_o4a["children_after"]],
        },
        "rest_for_one": {
            "terminated_order": res_r4o["terminated_order"],
            "restarted_order": res_r4o["restarted_order"],
            "generations_after": [c["generation"] for c in res_r4o["children_after"]],
            "upstream_planner_untouched": planner_untouched,
            "stale_downstream_count": non_churn_r4o["stale_count"],
        },
        "must_fail_mid_audit_snapshot_churn": {
            "rejected": churn_o4o["passed"] is False,
            "error_code": churn_o4o["error_code"],
            "stale_downstream_ids": churn_o4o["stale_downstream_ids"],
            "stale_count": churn_o4o["stale_count"],
        },
    }


# ---------------------------------------------------------------------------
# Pillar 3: Pure-Z / Pure-Q Sliding-Window Intensity & Tree Escalation
# ---------------------------------------------------------------------------

def step_restart_intensity(
    history: list[Any],
    now_tick: Any,
    max_restarts: int,
    window_ticks: Any,
) -> dict[str, Any]:
    """Exact OTP supervisor.erl add_restart semantics in pure rational Q.

    A prior restart timestamp t stays inside the window iff t >= now_tick - window_ticks
    (equivalently now_tick - t <= window_ticks, inclusive boundary). Escalates to
    MAX_RESTART_INTENSITY_EXCEEDED iff active restart count > max_restarts.
    """
    if type(history) is not list:
        raise OtpSupervisionError("ERR_INVALID_HISTORY", "history must be list")
    _req_strict_int_range(max_restarts, 0, None, "max_restarts")
    now_q = parse_nonneg_fraction(now_tick, "now_tick")
    win_q = parse_nonneg_fraction(window_ticks, "window_ticks")
    if win_q <= 0:
        raise OtpSupervisionError("ERR_NON_POSITIVE_WINDOW", "window_ticks must be > 0")

    parsed_hist: list[Fraction] = []
    for idx, item in enumerate(history):
        q = parse_nonneg_fraction(item, f"history[{idx}]")
        if parsed_hist and q < parsed_hist[-1]:
            raise OtpSupervisionError("ERR_NON_MONOTONIC_TICK", "history timestamps must be non-decreasing")
        parsed_hist.append(q)
    if parsed_hist and now_q < parsed_hist[-1]:
        raise OtpSupervisionError("ERR_NON_MONOTONIC_TICK", "now_tick precedes previous restart")

    threshold = now_q - win_q
    retained = [t for t in parsed_hist if t >= threshold]
    active = retained + [now_q]
    evicted = len(parsed_hist) - len(retained)
    escalated = len(active) > max_restarts
    return {
        "now_tick": frac_to_str(now_q),
        "window_ticks": frac_to_str(win_q),
        "max_restarts": max_restarts,
        "active_count": len(active),
        "evicted_count": evicted,
        "active_window": [frac_to_str(t) for t in active],
        "decision": "MAX_RESTART_INTENSITY_EXCEEDED" if escalated else "RESTART_ALLOWED",
        "escalated": escalated,
        "exit_reason": "reached_max_restart_intensity" if escalated else None,
    }


def certify_intensity_trace(
    max_restarts: int,
    window_ticks: Any,
    events: list[dict[str, Any]],
) -> dict[str, Any]:
    """Replay and certify an observed restart-intensity trace (fail-closed)."""
    _req_strict_int_range(max_restarts, 0, None, "max_restarts")
    win_q = parse_nonneg_fraction(window_ticks, "window_ticks")
    if win_q <= 0:
        raise OtpSupervisionError("ERR_NON_POSITIVE_WINDOW", "window_ticks must be > 0")
    if type(events) is not list or len(events) == 0:
        raise OtpSupervisionError("ERR_INVALID_EVENTS", "events must be nonempty list")

    history: list[Fraction] = []
    trace: list[dict[str, Any]] = []
    escalated_already = False
    for idx, ev in enumerate(events):
        if escalated_already:
            return {
                "passed": False,
                "error_code": "ERR_EVENT_AFTER_ESCALATION",
                "step_index": idx,
                "trace": trace,
            }
        _req_exact_keys(ev, {"tick", "claimed_decision"}, f"intensity_event[{idx}]")
        claimed = ev["claimed_decision"]
        if not _in_str_set(claimed, ("RESTART_ALLOWED", "MAX_RESTART_INTENSITY_EXCEEDED")):
            raise OtpSupervisionError("ERR_INVALID_DECISION", f"bad claimed_decision {claimed!r}")
        try:
            step = step_restart_intensity(history, ev["tick"], max_restarts, win_q)
        except OtpSupervisionError as exc:
            return {
                "passed": False,
                "error_code": exc.code,
                "step_index": idx,
                "trace": trace,
            }
        trace.append(step)
        if claimed != step["decision"]:
            code = (
                "ERR_INTENSITY_LIMIT_BYPASS"
                if step["escalated"]
                else "ERR_SPURIOUS_ESCALATION"
            )
            return {
                "passed": False,
                "error_code": code,
                "step_index": idx,
                "trace": trace,
            }
        history = [parse_nonneg_fraction(s, "active") for s in step["active_window"]]
        if step["escalated"]:
            escalated_already = True

    return {
        "passed": True,
        "error_code": None,
        "step_index": len(trace) - 1,
        "trace": trace,
    }


def simulate_tree_escalation(
    crash_ticks: list[Any],
    sub_max_restarts: int,
    sub_window: Any,
    root_max_restarts: int,
    root_window: Any,
) -> dict[str, Any]:
    """Simulate a 2-level supervision tree: worker -> sub_sup -> root_sup."""
    _req_strict_int_range(sub_max_restarts, 0, None, "sub_max_restarts")
    _req_strict_int_range(root_max_restarts, 0, None, "root_max_restarts")
    sub_win_q = parse_nonneg_fraction(sub_window, "sub_window")
    root_win_q = parse_nonneg_fraction(root_window, "root_window")
    if sub_win_q <= 0 or root_win_q <= 0:
        raise OtpSupervisionError("ERR_NON_POSITIVE_WINDOW", "windows must be > 0")
    if type(crash_ticks) is not list or len(crash_ticks) == 0:
        raise OtpSupervisionError("ERR_INVALID_CRASH_TICKS", "crash_ticks must be nonempty list")

    sub_hist: list[Fraction] = []
    root_hist: list[Fraction] = []
    sub_restarts_by_root = 0
    sub_escalations = 0
    root_terminated = False
    root_terminated_at: str | None = None

    for raw_tick in crash_ticks:
        t_q = parse_nonneg_fraction(raw_tick, "crash_tick")
        sub_step = step_restart_intensity(sub_hist, t_q, sub_max_restarts, sub_win_q)
        if not sub_step["escalated"]:
            sub_hist = [parse_nonneg_fraction(s, "sub_active") for s in sub_step["active_window"]]
            continue

        # sub_sup exceeded intensity -> escalates to root_sup
        sub_escalations += 1
        root_step = step_restart_intensity(root_hist, t_q, root_max_restarts, root_win_q)
        if not root_step["escalated"]:
            sub_restarts_by_root += 1
            root_hist = [parse_nonneg_fraction(s, "root_active") for s in root_step["active_window"]]
            sub_hist = []  # fresh restarted sub_sup starts with empty restart window
        else:
            root_terminated = True
            root_terminated_at = frac_to_str(t_q)
            break

    return {
        "sub_escalations": sub_escalations,
        "sub_restarts_by_root": sub_restarts_by_root,
        "root_terminated": root_terminated,
        "root_terminated_at": root_terminated_at,
    }


def run_pillar_3() -> dict[str, Any]:
    int_trace = certify_intensity_trace(
        max_restarts=2,
        window_ticks=5,
        events=[
            {"tick": 0, "claimed_decision": "RESTART_ALLOWED"},
            {"tick": 5, "claimed_decision": "RESTART_ALLOWED"},
            {"tick": 6, "claimed_decision": "RESTART_ALLOWED"},
            {"tick": 10, "claimed_decision": "MAX_RESTART_INTENSITY_EXCEEDED"},
        ],
    )
    rat_trace = certify_intensity_trace(
        max_restarts=2,
        window_ticks=Fraction(1, 3),
        events=[
            {"tick": Fraction(0, 1), "claimed_decision": "RESTART_ALLOWED"},
            {"tick": Fraction(1, 3), "claimed_decision": "RESTART_ALLOWED"},
            {"tick": Fraction(2, 3), "claimed_decision": "RESTART_ALLOWED"},
            {"tick": Fraction(5, 6), "claimed_decision": "RESTART_ALLOWED"},
            {"tick": Fraction(1, 1), "claimed_decision": "MAX_RESTART_INTENSITY_EXCEEDED"},
        ],
    )
    tree_res = simulate_tree_escalation(
        crash_ticks=[0, 1, 2, 3, 4, 5],
        sub_max_restarts=2,
        sub_window=5,
        root_max_restarts=1,
        root_window=10,
    )
    mf_bypass = certify_intensity_trace(
        max_restarts=2,
        window_ticks=5,
        events=[
            {"tick": 0, "claimed_decision": "RESTART_ALLOWED"},
            {"tick": 2, "claimed_decision": "RESTART_ALLOWED"},
            {"tick": 4, "claimed_decision": "RESTART_ALLOWED"},
        ],
    )
    mf_backwards = certify_intensity_trace(
        max_restarts=2,
        window_ticks=5,
        events=[
            {"tick": 5, "claimed_decision": "RESTART_ALLOWED"},
            {"tick": 4, "claimed_decision": "RESTART_ALLOWED"},
        ],
    )

    return {
        "passed": all([
            int_trace["passed"] is True,
            rat_trace["passed"] is True,
            tree_res["root_terminated"] is True,
            mf_bypass["passed"] is False,
            mf_backwards["passed"] is False,
        ]),
        "integer_boundary_trace": {
            "max_restarts": 2,
            "window_ticks": "5/1",
            "steps_checked": len(int_trace["trace"]),
            "inclusive_boundary_active_at_t5": int_trace["trace"][1]["active_count"],
            "evicted_at_t6": int_trace["trace"][2]["evicted_count"],
            "final_decision": int_trace["trace"][-1]["decision"],
            "final_active_window": int_trace["trace"][-1]["active_window"],
        },
        "rational_q_trace": {
            "max_restarts": 2,
            "window_ticks": "1/3",
            "steps_checked": len(rat_trace["trace"]),
            "inclusive_boundary_active_at_1_3": rat_trace["trace"][1]["active_count"],
            "evicted_at_2_3": rat_trace["trace"][2]["evicted_count"],
            "final_decision": rat_trace["trace"][-1]["decision"],
            "final_active_window": rat_trace["trace"][-1]["active_window"],
        },
        "two_level_tree_escalation": tree_res,
        "must_fail_intensity_bypass": {
            "rejected": mf_bypass["passed"] is False,
            "error_code": mf_bypass["error_code"],
            "step_index": mf_bypass["step_index"],
        },
        "must_fail_non_monotonic_tick": {
            "rejected": mf_backwards["passed"] is False,
            "error_code": mf_backwards["error_code"],
            "step_index": mf_backwards["step_index"],
        },
    }


# ---------------------------------------------------------------------------
# Pillar 4: Asymmetric Fault-Isolation Theorem (monitor vs link +- trap_exit)
# ---------------------------------------------------------------------------

def simulate_process_fault(
    processes: dict[str, dict[str, Any]],
    links: list[list[str]],
    monitors: list[dict[str, str]],
    crash_pid: str,
    exit_reason: str,
) -> dict[str, Any]:
    """Exact Erlang/OTP process signal propagation for links and monitors."""
    if type(processes) is not dict or len(processes) == 0:
        raise OtpSupervisionError("ERR_INVALID_PROCESSES", "processes must be nonempty dict")
    if not _in_str_set(exit_reason, SIGNAL_EXIT_REASONS):
        raise OtpSupervisionError("ERR_INVALID_EXIT_REASON", f"unknown exit reason {exit_reason!r}")

    proc_state: dict[str, dict[str, Any]] = {}
    for pid, meta in processes.items():
        if not _is_nonempty_str(pid):
            raise OtpSupervisionError("ERR_INVALID_PID", "pid must be nonempty str")
        _req_exact_keys(meta, {"role", "trap_exit"}, f"process[{pid}]")
        if not _is_nonempty_str(meta["role"]) or type(meta["trap_exit"]) is not bool:
            raise OtpSupervisionError("ERR_INVALID_PROCESS_META", f"bad meta for {pid}")
        proc_state[pid] = {
            "role": meta["role"],
            "trap_exit": meta["trap_exit"],
            "state": "ALIVE",
            "exit_reason": None,
            "inbox": [],
            "promotion_blocked": False,
        }

    if not _in_str_set(crash_pid, proc_state):
        raise OtpSupervisionError("ERR_UNKNOWN_PID", f"unknown crash_pid {crash_pid!r}")

    adj: dict[str, list[str]] = {pid: [] for pid in proc_state}
    if type(links) is not list:
        raise OtpSupervisionError("ERR_INVALID_LINKS", "links must be list")
    for idx, pair in enumerate(links):
        if type(pair) is not list or len(pair) != 2:
            raise OtpSupervisionError("ERR_INVALID_LINK_PAIR", f"links[{idx}] must be [a, b]")
        a, b = pair
        if not _in_str_set(a, proc_state) or not _in_str_set(b, proc_state) or a == b:
            raise OtpSupervisionError("ERR_INVALID_LINK_ENDPOINTS", f"bad link endpoints {pair!r}")
        if b not in adj[a]:
            adj[a].append(b)
        if a not in adj[b]:
            adj[b].append(a)

    if type(monitors) is not list:
        raise OtpSupervisionError("ERR_INVALID_MONITORS", "monitors must be list")
    mon_by_target: dict[str, list[tuple[str, str]]] = {pid: [] for pid in proc_state}
    seen_refs: set[str] = set()
    for idx, mon in enumerate(monitors):
        _req_exact_keys(mon, {"watcher", "target", "ref"}, f"monitor[{idx}]")
        w, t, ref = mon["watcher"], mon["target"], mon["ref"]
        if not _in_str_set(w, proc_state) or not _in_str_set(t, proc_state) or w == t:
            raise OtpSupervisionError("ERR_INVALID_MONITOR_ENDPOINTS", f"bad monitor {mon!r}")
        if not _is_nonempty_str(ref) or ref in seen_refs:
            raise OtpSupervisionError("ERR_INVALID_MONITOR_REF", f"bad or duplicate ref {ref!r}")
        seen_refs.add(ref)
        mon_by_target[t].append((w, ref))

    proc_state[crash_pid]["state"] = "TERMINATED"
    proc_state[crash_pid]["exit_reason"] = exit_reason
    queue: deque[tuple[str, str]] = deque([(crash_pid, exit_reason)])
    collateral_kills: list[str] = []

    while queue:
        src, reason = queue.popleft()
        # 1. Deliver unidirectional DOWN messages to alive watchers (never kills watcher)
        for watcher, ref in mon_by_target[src]:
            w_rec = proc_state[watcher]
            if w_rec["state"] == "ALIVE":
                w_rec["inbox"].append({
                    "tag": "DOWN",
                    "ref": ref,
                    "target": src,
                    "reason": reason,
                })
                if (
                    w_rec["role"] == "zone_a_coordinator"
                    and proc_state[src]["role"] == "zone_b_verifier"
                    and reason != "normal"
                ):
                    w_rec["promotion_blocked"] = True

        # 2. Propagate bidirectional link exit signals
        for peer in adj[src]:
            p_rec = proc_state[peer]
            if p_rec["state"] != "ALIVE":
                continue
            if reason == "kill":
                # Untrappable in OTP: kills peer with propagated reason "killed"
                p_rec["state"] = "TERMINATED"
                p_rec["exit_reason"] = "killed"
                collateral_kills.append(peer)
                queue.append((peer, "killed"))
            elif reason == "normal":
                if p_rec["trap_exit"]:
                    p_rec["inbox"].append({"tag": "EXIT", "from": src, "reason": "normal"})
            else:
                if p_rec["trap_exit"]:
                    p_rec["inbox"].append({"tag": "EXIT", "from": src, "reason": reason})
                else:
                    p_rec["state"] = "TERMINATED"
                    p_rec["exit_reason"] = reason
                    collateral_kills.append(peer)
                    queue.append((peer, reason))

    return {
        "crash_pid": crash_pid,
        "exit_reason": exit_reason,
        "collateral_kills": collateral_kills,
        "collateral_kill_count": len(collateral_kills),
        "processes": proc_state,
    }


def certify_zone_b_isolation(sim_result: Any, coordinator_pid: str) -> dict[str, Any]:
    """Certify that a Zone-B verifier crash does not kill coordinator and blocks promotion."""
    _req_exact_keys(
        sim_result,
        {"crash_pid", "exit_reason", "collateral_kills", "collateral_kill_count", "processes"},
        "sim_result",
    )
    procs = sim_result["processes"]
    if type(procs) is not dict or not _in_str_set(coordinator_pid, procs):
        raise OtpSupervisionError("ERR_UNKNOWN_COORDINATOR", f"unknown coordinator {coordinator_pid!r}")
    coord = procs[coordinator_pid]
    _req_exact_keys(
        coord,
        {"role", "trap_exit", "state", "exit_reason", "inbox", "promotion_blocked"},
        "coordinator_proc",
    )
    kills = _req_strict_int_range(sim_result["collateral_kill_count"], 0, None, "collateral_kill_count")
    if coord["state"] != "ALIVE":
        return {
            "passed": False,
            "error_code": "ERR_COORDINATOR_COLLATERAL_KILL",
            "coordinator_state": coord["state"],
            "collateral_kill_count": kills,
        }
    if kills != 0:
        return {
            "passed": False,
            "error_code": "ERR_SIBLING_COLLATERAL_KILL",
            "coordinator_state": coord["state"],
            "collateral_kill_count": kills,
        }
    if coord["promotion_blocked"] is not True:
        return {
            "passed": False,
            "error_code": "ERR_DOWN_PROMOTION_NOT_BLOCKED",
            "coordinator_state": coord["state"],
            "collateral_kill_count": 0,
        }
    return {
        "passed": True,
        "error_code": None,
        "coordinator_state": coord["state"],
        "collateral_kill_count": 0,
    }


def run_pillar_4() -> dict[str, Any]:
    procs_no_trap = {
        "coordinator": {"role": "zone_a_coordinator", "trap_exit": False},
        "verifier_1": {"role": "zone_b_verifier", "trap_exit": False},
        "verifier_2": {"role": "zone_b_verifier", "trap_exit": False},
    }
    procs_trap = {
        "coordinator": {"role": "zone_a_coordinator", "trap_exit": True},
        "verifier_1": {"role": "zone_b_verifier", "trap_exit": False},
        "verifier_2": {"role": "zone_b_verifier", "trap_exit": False},
    }
    monitors = [
        {"watcher": "coordinator", "target": "verifier_1", "ref": "mon-v1"},
        {"watcher": "coordinator", "target": "verifier_2", "ref": "mon-v2"},
    ]
    links = [
        ["coordinator", "verifier_1"],
        ["coordinator", "verifier_2"],
    ]

    sim_monitor = simulate_process_fault(procs_no_trap, [], monitors, "verifier_1", "abnormal")
    cert_monitor = certify_zone_b_isolation(sim_monitor, "coordinator")

    # External exit(verifier_1, kill) terminates verifier_1 with exit reason "killed".
    # Unidirectional monitor delivers DOWN(..., "killed") with 0 collateral kills and blocks promotion.
    sim_monitor_killed = simulate_process_fault(procs_no_trap, [], monitors, "verifier_1", "killed")
    cert_monitor_killed = certify_zone_b_isolation(sim_monitor_killed, "coordinator")

    sim_link_trap_abn = simulate_process_fault(procs_trap, links, [], "verifier_1", "abnormal")
    coord_trap_abn = sim_link_trap_abn["processes"]["coordinator"]

    # Erlang/OTP distinction: when verifier_1 is killed externally by exit(verifier_1, kill),
    # its propagated link exit reason is "killed", which a linked coordinator with trap_exit=True CAN trap.
    sim_link_trap_killed = simulate_process_fault(procs_trap, links, [], "verifier_1", "killed")
    coord_trap_killed = sim_link_trap_killed["processes"]["coordinator"]

    sim_link_notrap = simulate_process_fault(procs_no_trap, links, [], "verifier_1", "abnormal")
    cert_link_notrap = certify_zone_b_isolation(sim_link_notrap, "coordinator")

    # Direct untrappable "kill" signal targeting coordinator (as in direct exit(coordinator, kill)):
    # bypasses trap_exit=True, kills coordinator with exit_reason "killed", and cascades to verifier_2.
    sim_link_trap_kill = simulate_process_fault(procs_trap, links, [], "verifier_1", "kill")
    cert_link_trap_kill = certify_zone_b_isolation(sim_link_trap_kill, "coordinator")

    return {
        "passed": all([
            cert_monitor["passed"] is True,
            cert_monitor_killed["passed"] is True,
            coord_trap_abn["state"] == "ALIVE",
            len(coord_trap_abn["inbox"]) == 1,
            coord_trap_abn["inbox"][0]["tag"] == "EXIT",
            coord_trap_killed["state"] == "ALIVE",
            len(coord_trap_killed["inbox"]) == 1,
            coord_trap_killed["inbox"][0]["tag"] == "EXIT",
            coord_trap_killed["inbox"][0]["reason"] == "killed",
            cert_link_notrap["passed"] is False,
            cert_link_trap_kill["passed"] is False,
        ]),
        "monitor_zone_b_isolation": {
            "coordinator_state": sim_monitor["processes"]["coordinator"]["state"],
            "sibling_verifier_state": sim_monitor["processes"]["verifier_2"]["state"],
            "collateral_kill_count": sim_monitor["collateral_kill_count"],
            "promotion_blocked": sim_monitor["processes"]["coordinator"]["promotion_blocked"],
            "down_messages_received": len(sim_monitor["processes"]["coordinator"]["inbox"]),
            "down_tag": sim_monitor["processes"]["coordinator"]["inbox"][0]["tag"],
            "down_ref": sim_monitor["processes"]["coordinator"]["inbox"][0]["ref"],
        },
        "monitor_zone_b_isolation_on_killed": {
            "coordinator_state": sim_monitor_killed["processes"]["coordinator"]["state"],
            "sibling_verifier_state": sim_monitor_killed["processes"]["verifier_2"]["state"],
            "collateral_kill_count": sim_monitor_killed["collateral_kill_count"],
            "promotion_blocked": sim_monitor_killed["processes"]["coordinator"]["promotion_blocked"],
            "down_messages_received": len(sim_monitor_killed["processes"]["coordinator"]["inbox"]),
            "down_tag": sim_monitor_killed["processes"]["coordinator"]["inbox"][0]["tag"],
            "down_ref": sim_monitor_killed["processes"]["coordinator"]["inbox"][0]["ref"],
            "down_reason": sim_monitor_killed["processes"]["coordinator"]["inbox"][0]["reason"],
        },
        "link_with_trap_exit_abnormal": {
            "coordinator_state": coord_trap_abn["state"],
            "sibling_verifier_state": sim_link_trap_abn["processes"]["verifier_2"]["state"],
            "collateral_kill_count": sim_link_trap_abn["collateral_kill_count"],
            "exit_messages_received": len(coord_trap_abn["inbox"]),
            "exit_tag": coord_trap_abn["inbox"][0]["tag"],
        },
        "link_with_trap_exit_outside_killed": {
            "coordinator_state": coord_trap_killed["state"],
            "sibling_verifier_state": sim_link_trap_killed["processes"]["verifier_2"]["state"],
            "collateral_kill_count": sim_link_trap_killed["collateral_kill_count"],
            "exit_messages_received": len(coord_trap_killed["inbox"]),
            "exit_tag": coord_trap_killed["inbox"][0]["tag"],
            "exit_reason": coord_trap_killed["inbox"][0]["reason"],
        },
        "must_fail_link_without_trap_exit_kills_coordinator": {
            "rejected": cert_link_notrap["passed"] is False,
            "error_code": cert_link_notrap["error_code"],
            "coordinator_state": cert_link_notrap["coordinator_state"],
            "collateral_kills": sim_link_notrap["collateral_kills"],
            "collateral_kill_count": sim_link_notrap["collateral_kill_count"],
        },
        "must_fail_kill_bypasses_trap_exit": {
            "rejected": cert_link_trap_kill["passed"] is False,
            "error_code": cert_link_trap_kill["error_code"],
            "coordinator_state": cert_link_trap_kill["coordinator_state"],
            "coordinator_exit_reason": sim_link_trap_kill["processes"]["coordinator"]["exit_reason"],
            "collateral_kills": sim_link_trap_kill["collateral_kills"],
            "collateral_kill_count": sim_link_trap_kill["collateral_kill_count"],
        },
    }


# ---------------------------------------------------------------------------
# Pillar 5: exo#1200 SupervisionPolicy x aletheia v2.1+ Two-Zone Hybrid Swarm
# ---------------------------------------------------------------------------

def exo1200_otp_retry_gate(
    *,
    task_state: str,
    failure_class: str,
    effect_class: str,
    attempt_number: int,
    max_retries: int,
    stop_requested: bool,
    otp_policy: str,
    exit_reason: str,
) -> dict[str, Any]:
    """Combined gate intersecting exo#1200 SupervisionPolicy (I2 safety) with OTP policy.

    Sticky stop (I2), non-transient/terminal failure classes, and post-dispatch
    uncertain/external effects unconditionally override OTP restart rules.
    """
    if not _is_nonempty_str(task_state):
        raise OtpSupervisionError("ERR_INVALID_TASK_STATE", "task_state must be nonempty str")
    if not _in_str_set(failure_class, EXO1200_FAILURE_CLASSES):
        raise OtpSupervisionError("ERR_INVALID_FAILURE_CLASS", f"bad failure_class {failure_class!r}")
    if not _in_str_set(effect_class, EXO1200_EFFECT_CLASSES):
        raise OtpSupervisionError("ERR_INVALID_EFFECT_CLASS", f"bad effect_class {effect_class!r}")
    _req_strict_int_range(attempt_number, 1, None, "attempt_number")
    _req_strict_int_range(max_retries, 0, 10, "max_retries")
    if type(stop_requested) is not bool:
        raise OtpSupervisionError("ERR_INVALID_STOP_FLAG", "stop_requested must be bool")

    otp_dec = otp_should_restart(otp_policy, exit_reason)
    uncertain_effects = effect_class != "not_dispatched"

    if stop_requested or task_state in ("stopped", "cancelled"):
        return {"action": "final", "reason": "cancelled", "reconcile": uncertain_effects, "otp_would_restart": otp_dec["should_restart"]}
    if failure_class in ("cancelled", "denied", "spend_limit", "permanent"):
        return {"action": "final", "reason": failure_class, "reconcile": uncertain_effects, "otp_would_restart": otp_dec["should_restart"]}
    if task_state == "completed":
        return {"action": "final", "reason": "completed", "reconcile": False, "otp_would_restart": otp_dec["should_restart"]}
    if task_state != "failed":
        return {"action": "reconcile", "reason": "not_settled_failure", "reconcile": True, "otp_would_restart": otp_dec["should_restart"]}
    if uncertain_effects:
        return {"action": "reconcile", "reason": "effects_require_reconciliation", "reconcile": True, "otp_would_restart": otp_dec["should_restart"]}
    if failure_class != "transient":
        return {"action": "reconcile", "reason": "failure_requires_classification", "reconcile": True, "otp_would_restart": otp_dec["should_restart"]}
    if not otp_dec["should_restart"]:
        return {"action": "final", "reason": "otp_policy_forbids_restart", "reconcile": False, "otp_would_restart": False}
    if attempt_number > max_retries:
        return {"action": "final", "reason": "retry_budget_exhausted", "reconcile": False, "otp_would_restart": True}
    return {"action": "retry", "reason": "transient_pre_dispatch_failure", "reconcile": False, "otp_would_restart": True}


def certify_hybrid_swarm_run(spec: dict[str, Any]) -> dict[str, Any]:
    """End-to-end certifier for an OTP-supervised exo#1200 + aletheia v2.1+ Two-Zone run."""
    _req_exact_keys(
        spec,
        {"max_retries", "max_restarts", "window_ticks", "initial_snapshot_sha256", "events"},
        "hybrid_spec",
    )
    max_retries = _req_strict_int_range(spec["max_retries"], 0, 10, "max_retries")
    max_restarts = _req_strict_int_range(spec["max_restarts"], 0, None, "max_restarts")
    win_q = parse_nonneg_fraction(spec["window_ticks"], "window_ticks")
    if win_q <= 0:
        raise OtpSupervisionError("ERR_NON_POSITIVE_WINDOW", "window_ticks must be > 0")
    active_sha = _req_hex64(spec["initial_snapshot_sha256"], "initial_snapshot_sha256")
    events = spec["events"]
    if type(events) is not list or len(events) == 0:
        raise OtpSupervisionError("ERR_INVALID_EVENTS", "events must be nonempty list")

    zone_a_children = [
        {"id": "author", "policy": "transient", "generation": 1, "snapshot_sha256": active_sha, "alive": True},
        {"id": "airlock_snapshot", "policy": "permanent", "generation": 1, "snapshot_sha256": active_sha, "alive": True},
    ]
    verifiers: dict[str, dict[str, Any]] = {
        "verifier_1": {"snapshot_sha256": active_sha, "state": "ALIVE", "verdict": None},
        "verifier_2": {"snapshot_sha256": active_sha, "state": "ALIVE", "verdict": None},
    }
    author_attempts = 1
    stop_requested = False
    promotion_blocked_code: str | None = None
    promoted = False
    restart_hist: list[Fraction] = []
    zone_a_restarts = 0
    down_events_observed = 0

    for idx, ev in enumerate(events):
        if promoted:
            return {
                "passed": False,
                "error_code": "ERR_EVENT_AFTER_PROMOTE",
                "step_index": idx,
                "promoted": False,
            }
        if type(ev) is not dict or not _in_str_set(ev.get("op"), ("stop_plan", "verifier_crash", "author_crash_restart", "verifier_verdict", "promote")):
            raise OtpSupervisionError("ERR_INVALID_EVENT", f"event[{idx}] invalid or unknown op")
        op = ev["op"]

        if op == "stop_plan":
            _req_exact_keys(ev, {"op"}, f"event[{idx}]")
            stop_requested = True
            continue

        if op == "verifier_crash":
            _req_exact_keys(ev, {"op", "verifier_id", "reason"}, f"event[{idx}]")
            vid = ev["verifier_id"]
            if not _in_str_set(vid, verifiers):
                raise OtpSupervisionError("ERR_UNKNOWN_VERIFIER", f"unknown verifier {vid!r}")
            if verifiers[vid]["state"] != "ALIVE":
                raise OtpSupervisionError("ERR_VERIFIER_ALREADY_DEAD", f"verifier {vid!r} already dead")
            sim = simulate_process_fault(
                {
                    "coordinator": {"role": "zone_a_coordinator", "trap_exit": False},
                    vid: {"role": "zone_b_verifier", "trap_exit": False},
                },
                [],
                [{"watcher": "coordinator", "target": vid, "ref": f"mon-{idx}"}],
                vid,
                ev["reason"],
            )
            verifiers[vid]["state"] = "TERMINATED"
            down_events_observed += 1
            if sim["processes"]["coordinator"]["promotion_blocked"]:
                promotion_blocked_code = "ERR_PROMOTION_BLOCKED_BY_DOWN"
            continue

        if op == "author_crash_restart":
            _req_exact_keys(
                ev,
                {"op", "tick", "failure_class", "effect_class", "new_snapshot_sha256"},
                f"event[{idx}]",
            )
            gate = exo1200_otp_retry_gate(
                task_state="failed",
                failure_class=ev["failure_class"],
                effect_class=ev["effect_class"],
                attempt_number=author_attempts,
                max_retries=max_retries,
                stop_requested=stop_requested,
                otp_policy="transient",
                exit_reason="abnormal",
            )
            if gate["action"] != "retry":
                if stop_requested:
                    code = "ERR_STOPPED_TASK_RESTARTED"
                elif ev["effect_class"] != "not_dispatched":
                    code = "ERR_UNRECONCILED_EXTERNAL_EFFECTS"
                else:
                    code = "ERR_RETRY_GATE_DENIED"
                return {
                    "passed": False,
                    "error_code": code,
                    "step_index": idx,
                    "promoted": False,
                }

            step = step_restart_intensity(restart_hist, ev["tick"], max_restarts, win_q)
            if step["escalated"]:
                return {
                    "passed": False,
                    "error_code": "ERR_INTENSITY_ESCALATED",
                    "step_index": idx,
                    "promoted": False,
                }
            restart_hist = [parse_nonneg_fraction(s, "hist") for s in step["active_window"]]

            new_sha = _req_hex64(ev["new_snapshot_sha256"], "new_snapshot_sha256")
            r4o = apply_strategy_crash("rest_for_one", zone_a_children, "author", "abnormal", new_sha)
            zone_a_children = r4o["children_after"]
            active_sha = new_sha
            author_attempts += 1
            zone_a_restarts += 1
            for vid in verifiers:
                verifiers[vid] = {"snapshot_sha256": new_sha, "state": "ALIVE", "verdict": None}
            promotion_blocked_code = None
            continue

        if op == "verifier_verdict":
            _req_exact_keys(ev, {"op", "verifier_id", "snapshot_sha256", "verdict"}, f"event[{idx}]")
            vid = ev["verifier_id"]
            if not _in_str_set(vid, verifiers):
                raise OtpSupervisionError("ERR_UNKNOWN_VERIFIER", f"unknown verifier {vid!r}")
            v_rec = verifiers[vid]
            if v_rec["state"] != "ALIVE":
                return {
                    "passed": False,
                    "error_code": "ERR_DEAD_VERIFIER_VERDICT",
                    "step_index": idx,
                    "promoted": False,
                }
            if ev["snapshot_sha256"] != active_sha:
                return {
                    "passed": False,
                    "error_code": "ERR_STALE_VERDICT_SNAPSHOT",
                    "step_index": idx,
                    "promoted": False,
                }
            if not _in_str_set(ev["verdict"], ("VERIFIED", "FALSIFIED")):
                raise OtpSupervisionError("ERR_INVALID_VERDICT", f"bad verdict {ev['verdict']!r}")
            v_rec["verdict"] = ev["verdict"]
            if ev["verdict"] != "VERIFIED":
                promotion_blocked_code = "ERR_PROMOTION_BLOCKED_BY_FALSIFIED"
            continue

        _req_exact_keys(ev, {"op", "snapshot_sha256"}, f"event[{idx}]")
        if stop_requested:
            return {
                "passed": False,
                "error_code": "ERR_PROMOTE_ON_STOPPED_PLAN",
                "step_index": idx,
                "promoted": False,
            }
        if promotion_blocked_code is not None:
            return {
                "passed": False,
                "error_code": promotion_blocked_code,
                "step_index": idx,
                "promoted": False,
            }
        if ev["snapshot_sha256"] != active_sha:
            return {
                "passed": False,
                "error_code": "ERR_PROMOTE_SNAPSHOT_MISMATCH",
                "step_index": idx,
                "promoted": False,
            }
        if any(v["verdict"] != "VERIFIED" for v in verifiers.values()):
            return {
                "passed": False,
                "error_code": "ERR_INCOMPLETE_VERIFICATION",
                "step_index": idx,
                "promoted": False,
            }
        promoted = True

    return {
        "passed": True,
        "error_code": None,
        "step_index": len(events) - 1,
        "promoted": promoted,
        "final_snapshot_sha256": active_sha,
        "zone_a_restarts": zone_a_restarts,
        "down_events_observed": down_events_observed,
        "author_attempts": author_attempts,
    }


def run_pillar_5() -> dict[str, Any]:
    exo_default_zero = exo1200_otp_retry_gate(
        task_state="failed",
        failure_class="transient",
        effect_class="not_dispatched",
        attempt_number=1,
        max_retries=0,
        stop_requested=False,
        otp_policy="transient",
        exit_reason="abnormal",
    )

    clean_run = certify_hybrid_swarm_run({
        "max_retries": 2,
        "max_restarts": 2,
        "window_ticks": 10,
        "initial_snapshot_sha256": SNAPSHOT_SHA_V1,
        "events": [
            {"op": "verifier_crash", "verifier_id": "verifier_1", "reason": "abnormal"},
            {
                "op": "author_crash_restart",
                "tick": 4,
                "failure_class": "transient",
                "effect_class": "not_dispatched",
                "new_snapshot_sha256": SNAPSHOT_SHA_V2,
            },
            {"op": "verifier_verdict", "verifier_id": "verifier_1", "snapshot_sha256": SNAPSHOT_SHA_V2, "verdict": "VERIFIED"},
            {"op": "verifier_verdict", "verifier_id": "verifier_2", "snapshot_sha256": SNAPSHOT_SHA_V2, "verdict": "VERIFIED"},
            {"op": "promote", "snapshot_sha256": SNAPSHOT_SHA_V2},
        ],
    })

    mf_promote_down = certify_hybrid_swarm_run({
        "max_retries": 2,
        "max_restarts": 2,
        "window_ticks": 10,
        "initial_snapshot_sha256": SNAPSHOT_SHA_V1,
        "events": [
            {"op": "verifier_crash", "verifier_id": "verifier_1", "reason": "abnormal"},
            {"op": "verifier_verdict", "verifier_id": "verifier_2", "snapshot_sha256": SNAPSHOT_SHA_V1, "verdict": "VERIFIED"},
            {"op": "promote", "snapshot_sha256": SNAPSHOT_SHA_V1},
        ],
    })

    mf_stopped_restart = certify_hybrid_swarm_run({
        "max_retries": 2,
        "max_restarts": 2,
        "window_ticks": 10,
        "initial_snapshot_sha256": SNAPSHOT_SHA_V1,
        "events": [
            {"op": "stop_plan"},
            {
                "op": "author_crash_restart",
                "tick": 1,
                "failure_class": "transient",
                "effect_class": "not_dispatched",
                "new_snapshot_sha256": SNAPSHOT_SHA_V2,
            },
        ],
    })

    mf_external_effects = certify_hybrid_swarm_run({
        "max_retries": 2,
        "max_restarts": 2,
        "window_ticks": 10,
        "initial_snapshot_sha256": SNAPSHOT_SHA_V1,
        "events": [
            {
                "op": "author_crash_restart",
                "tick": 1,
                "failure_class": "transient",
                "effect_class": "external",
                "new_snapshot_sha256": SNAPSHOT_SHA_V2,
            },
        ],
    })

    return {
        "passed": all([
            exo_default_zero["action"] == "final",
            exo_default_zero["reason"] == "retry_budget_exhausted",
            clean_run["passed"] is True,
            clean_run["promoted"] is True,
            mf_promote_down["passed"] is False,
            mf_stopped_restart["passed"] is False,
            mf_external_effects["passed"] is False,
        ]),
        "exo1200_ref_commit": EXO1200_REF_COMMIT,
        "exo1200_group_supervision_sha256": EXO1200_SUPERVISION_SHA256,
        "exo1200_zero_retry_default_action": exo_default_zero["action"],
        "exo1200_zero_retry_default_reason": exo_default_zero["reason"],
        "hybrid_clean_run": {
            "promoted": clean_run["promoted"],
            "final_snapshot_sha256": clean_run["final_snapshot_sha256"],
            "zone_a_restarts": clean_run["zone_a_restarts"],
            "down_events_observed": clean_run["down_events_observed"],
            "author_attempts": clean_run["author_attempts"],
        },
        "must_fail_hybrid_promotion_while_down": {
            "rejected": mf_promote_down["passed"] is False,
            "error_code": mf_promote_down["error_code"],
            "step_index": mf_promote_down["step_index"],
        },
        "must_fail_hybrid_exo1200_stopped_restart": {
            "rejected": mf_stopped_restart["passed"] is False,
            "error_code": mf_stopped_restart["error_code"],
            "step_index": mf_stopped_restart["step_index"],
        },
        "must_fail_hybrid_exo1200_external_effects": {
            "rejected": mf_external_effects["passed"] is False,
            "error_code": mf_external_effects["error_code"],
            "step_index": mf_external_effects["step_index"],
        },
    }


# ---------------------------------------------------------------------------
# Certificate Builder & Strict Fail-Closed Validator
# ---------------------------------------------------------------------------

def _count_verified_must_fail_controls(pillars: dict[str, dict[str, Any]]) -> int:
    count = 0
    for pdata in pillars.values():
        for key, val in pdata.items():
            if key.startswith("must_fail_") and type(val) is dict and val.get("rejected") is True:
                count += 1
    return count


def build_erlang_otp_supervision_certificate() -> dict[str, Any]:
    pillars = {
        "p1_restart_policy_matrix": run_pillar_1(),
        "p2_restart_strategies_and_non_churn": run_pillar_2(),
        "p3_sliding_window_intensity_escalation": run_pillar_3(),
        "p4_monitor_vs_link_fault_isolation": run_pillar_4(),
        "p5_exo1200_aletheia_bridge": run_pillar_5(),
    }
    pillars_passed = sum(1 for p in pillars.values() if p["passed"] is True)
    controls_verified = _count_verified_must_fail_controls(pillars)

    body = {
        "schema_version": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "audit_id": AUDIT_ID,
        "novelty_tier": {
            "classical_semantics": "N0",
            "pure_q_hybrid_bridge": "N0",
        },
        "primary_sources": {
            "armstrong_2003_kth_urn": "urn:nbn:se:kth:diva-3658",
            "armstrong_2003_isrn": "KTH/IMIT/LECS/AVH-03/09-SE",
            "armstrong_1996_isbn13": "978-0-13-508301-7",
            "otp_module": "stdlib/src/supervisor.erl",
            "exo1200_ref_commit": EXO1200_REF_COMMIT,
            "exo1200_group_supervision_sha256": EXO1200_SUPERVISION_SHA256,
        },
        "pillars": pillars,
        "summary": {
            "all_passed": all([pillars_passed == 5, controls_verified == 10]),
            "pillars_passed": pillars_passed,
            "pillars_total": 5,
            "must_fail_controls_verified": controls_verified,
            "floats_used": 0,
        },
    }
    cert = dict(body)
    cert["canonical_sha256"] = canonical_sha256(body)
    return cert


def _validate_p1(p1: Any) -> None:
    _req_exact_keys(
        p1,
        {
            "passed",
            "matrix_cells_verified",
            "restart_true_count",
            "restart_false_count",
            "transition_table",
            "must_fail_temporary_restarted",
            "must_fail_transient_clean_exit_restarted",
        },
        "p1",
    )
    _req_bool_eq(p1["passed"], True, "p1.passed")
    _req_strict_int_range(p1["matrix_cells_verified"], 9, 9, "p1.matrix_cells_verified")
    _req_strict_int_range(p1["restart_true_count"], 4, 4, "p1.restart_true_count")
    _req_strict_int_range(p1["restart_false_count"], 5, 5, "p1.restart_false_count")

    table = p1["transition_table"]
    if type(table) is not list or len(table) != 9:
        raise OtpSupervisionError("ERR_P1_TABLE", "p1.transition_table must have 9 cells")
    seen_pairs: set[tuple[str, str]] = set()
    for idx, cell in enumerate(table):
        _req_exact_keys(cell, {"policy", "exit_reason", "should_restart", "action"}, f"p1.cell[{idx}]")
        expected = otp_should_restart(cell["policy"], cell["exit_reason"])
        pair = (cell["policy"], cell["exit_reason"])
        if pair in seen_pairs:
            raise OtpSupervisionError("ERR_P1_DUP_CELL", f"duplicate transition cell {pair!r}")
        seen_pairs.add(pair)
        _req_bool_eq(cell["should_restart"], expected["should_restart"], f"p1.cell[{idx}].should_restart")
        _req_strict_str_eq(cell["action"], expected["action"], f"p1.cell[{idx}].action")

    mf1 = _req_exact_keys(p1["must_fail_temporary_restarted"], {"rejected", "error_code"}, "p1.mf1")
    _req_bool_eq(mf1["rejected"], True, "p1.mf1.rejected")
    _req_strict_str_eq(mf1["error_code"], "ERR_TEMPORARY_CHILD_RESTARTED", "p1.mf1.error_code")

    mf2 = _req_exact_keys(
        p1["must_fail_transient_clean_exit_restarted"],
        {"rejected", "normal_error_code", "shutdown_error_code"},
        "p1.mf2",
    )
    _req_bool_eq(mf2["rejected"], True, "p1.mf2.rejected")
    _req_strict_str_eq(mf2["normal_error_code"], "ERR_TRANSIENT_CLEAN_EXIT_RESTARTED", "p1.mf2.normal")
    _req_strict_str_eq(mf2["shutdown_error_code"], "ERR_TRANSIENT_CLEAN_EXIT_RESTARTED", "p1.mf2.shutdown")


def _validate_p2(p2: Any) -> None:
    _req_exact_keys(
        p2,
        {
            "passed",
            "snapshot_sha_v1",
            "snapshot_sha_v2",
            "one_for_one",
            "one_for_all",
            "rest_for_one",
            "must_fail_mid_audit_snapshot_churn",
        },
        "p2",
    )
    _req_bool_eq(p2["passed"], True, "p2.passed")
    _req_strict_str_eq(p2["snapshot_sha_v1"], SNAPSHOT_SHA_V1, "p2.snapshot_sha_v1")
    _req_strict_str_eq(p2["snapshot_sha_v2"], SNAPSHOT_SHA_V2, "p2.snapshot_sha_v2")

    o4o = _req_exact_keys(p2["one_for_one"], {"terminated_order", "restarted_order", "generations_after"}, "p2.o4o")
    _req_str_list(o4o["terminated_order"], [], "p2.o4o.terminated_order")
    _req_str_list(o4o["restarted_order"], ["author"], "p2.o4o.restarted_order")
    _req_strict_int_list(o4o["generations_after"], [1, 2, 1, 1, 1], "p2.o4o.generations")

    o4a = _req_exact_keys(p2["one_for_all"], {"terminated_order", "restarted_order", "generations_after"}, "p2.o4a")
    _req_str_list(o4a["terminated_order"], ["verifier_b", "verifier_a", "airlock_snapshot", "planner"], "p2.o4a.term")
    _req_str_list(o4a["restarted_order"], ["planner", "author", "airlock_snapshot", "verifier_a", "verifier_b"], "p2.o4a.rest")
    _req_strict_int_list(o4a["generations_after"], [2, 2, 2, 2, 2], "p2.o4a.generations")

    r4o = _req_exact_keys(
        p2["rest_for_one"],
        {
            "terminated_order",
            "restarted_order",
            "generations_after",
            "upstream_planner_untouched",
            "stale_downstream_count",
        },
        "p2.r4o",
    )
    _req_str_list(r4o["terminated_order"], ["verifier_b", "verifier_a", "airlock_snapshot"], "p2.r4o.term")
    _req_str_list(r4o["restarted_order"], ["author", "airlock_snapshot", "verifier_a", "verifier_b"], "p2.r4o.rest")
    _req_strict_int_list(r4o["generations_after"], [1, 2, 2, 2, 2], "p2.r4o.generations")
    _req_bool_eq(r4o["upstream_planner_untouched"], True, "p2.r4o.upstream_planner_untouched")
    _req_strict_int_range(r4o["stale_downstream_count"], 0, 0, "p2.r4o.stale_downstream_count")

    mf = _req_exact_keys(
        p2["must_fail_mid_audit_snapshot_churn"],
        {"rejected", "error_code", "stale_downstream_ids", "stale_count"},
        "p2.mf",
    )
    _req_bool_eq(mf["rejected"], True, "p2.mf.rejected")
    _req_strict_str_eq(mf["error_code"], "ERR_SNAPSHOT_CHURN", "p2.mf.error_code")
    _req_str_list(mf["stale_downstream_ids"], ["airlock_snapshot", "verifier_a", "verifier_b"], "p2.mf.stale_ids")
    _req_strict_int_range(mf["stale_count"], 3, 3, "p2.mf.stale_count")


def _validate_p3(p3: Any) -> None:
    _req_exact_keys(
        p3,
        {
            "passed",
            "integer_boundary_trace",
            "rational_q_trace",
            "two_level_tree_escalation",
            "must_fail_intensity_bypass",
            "must_fail_non_monotonic_tick",
        },
        "p3",
    )
    _req_bool_eq(p3["passed"], True, "p3.passed")

    it = _req_exact_keys(
        p3["integer_boundary_trace"],
        {
            "max_restarts",
            "window_ticks",
            "steps_checked",
            "inclusive_boundary_active_at_t5",
            "evicted_at_t6",
            "final_decision",
            "final_active_window",
        },
        "p3.int",
    )
    _req_strict_int_range(it["max_restarts"], 2, 2, "p3.int.max_restarts")
    _req_strict_str_eq(it["window_ticks"], "5/1", "p3.int.window_ticks")
    _req_strict_int_range(it["steps_checked"], 4, 4, "p3.int.steps_checked")
    _req_strict_int_range(it["inclusive_boundary_active_at_t5"], 2, 2, "p3.int.t5")
    _req_strict_int_range(it["evicted_at_t6"], 1, 1, "p3.int.t6")
    _req_strict_str_eq(it["final_decision"], "MAX_RESTART_INTENSITY_EXCEEDED", "p3.int.final_decision")
    _req_str_list(it["final_active_window"], ["5/1", "6/1", "10/1"], "p3.int.window")

    rt = _req_exact_keys(
        p3["rational_q_trace"],
        {
            "max_restarts",
            "window_ticks",
            "steps_checked",
            "inclusive_boundary_active_at_1_3",
            "evicted_at_2_3",
            "final_decision",
            "final_active_window",
        },
        "p3.rat",
    )
    _req_strict_int_range(rt["max_restarts"], 2, 2, "p3.rat.max_restarts")
    _req_strict_str_eq(rt["window_ticks"], "1/3", "p3.rat.window_ticks")
    _req_strict_int_range(rt["steps_checked"], 5, 5, "p3.rat.steps_checked")
    _req_strict_int_range(rt["inclusive_boundary_active_at_1_3"], 2, 2, "p3.rat.t13")
    _req_strict_int_range(rt["evicted_at_2_3"], 1, 1, "p3.rat.t23")
    _req_strict_str_eq(rt["final_decision"], "MAX_RESTART_INTENSITY_EXCEEDED", "p3.rat.final_decision")
    _req_str_list(rt["final_active_window"], ["2/3", "5/6", "1/1"], "p3.rat.window")

    tr = _req_exact_keys(
        p3["two_level_tree_escalation"],
        {"sub_escalations", "sub_restarts_by_root", "root_terminated", "root_terminated_at"},
        "p3.tree",
    )
    _req_strict_int_range(tr["sub_escalations"], 2, 2, "p3.tree.sub_escalations")
    _req_strict_int_range(tr["sub_restarts_by_root"], 1, 1, "p3.tree.sub_restarts_by_root")
    _req_bool_eq(tr["root_terminated"], True, "p3.tree.root_terminated")
    _req_strict_str_eq(tr["root_terminated_at"], "5/1", "p3.tree.root_terminated_at")

    mf1 = _req_exact_keys(p3["must_fail_intensity_bypass"], {"rejected", "error_code", "step_index"}, "p3.mf1")
    _req_bool_eq(mf1["rejected"], True, "p3.mf1.rejected")
    _req_strict_str_eq(mf1["error_code"], "ERR_INTENSITY_LIMIT_BYPASS", "p3.mf1.error_code")
    _req_strict_int_range(mf1["step_index"], 2, 2, "p3.mf1.step_index")

    mf2 = _req_exact_keys(p3["must_fail_non_monotonic_tick"], {"rejected", "error_code", "step_index"}, "p3.mf2")
    _req_bool_eq(mf2["rejected"], True, "p3.mf2.rejected")
    _req_strict_str_eq(mf2["error_code"], "ERR_NON_MONOTONIC_TICK", "p3.mf2.error_code")
    _req_strict_int_range(mf2["step_index"], 1, 1, "p3.mf2.step_index")


def _validate_p4(p4: Any) -> None:
    _req_exact_keys(
        p4,
        {
            "passed",
            "monitor_zone_b_isolation",
            "monitor_zone_b_isolation_on_killed",
            "link_with_trap_exit_abnormal",
            "link_with_trap_exit_outside_killed",
            "must_fail_link_without_trap_exit_kills_coordinator",
            "must_fail_kill_bypasses_trap_exit",
        },
        "p4",
    )
    _req_bool_eq(p4["passed"], True, "p4.passed")

    mon = _req_exact_keys(
        p4["monitor_zone_b_isolation"],
        {
            "coordinator_state",
            "sibling_verifier_state",
            "collateral_kill_count",
            "promotion_blocked",
            "down_messages_received",
            "down_tag",
            "down_ref",
        },
        "p4.mon",
    )
    _req_strict_str_eq(mon["coordinator_state"], "ALIVE", "p4.mon.coord")
    _req_strict_str_eq(mon["sibling_verifier_state"], "ALIVE", "p4.mon.sibling")
    _req_strict_int_range(mon["collateral_kill_count"], 0, 0, "p4.mon.kills")
    _req_bool_eq(mon["promotion_blocked"], True, "p4.mon.promotion_blocked")
    _req_strict_int_range(mon["down_messages_received"], 1, 1, "p4.mon.down_cnt")
    _req_strict_str_eq(mon["down_tag"], "DOWN", "p4.mon.down_tag")
    _req_strict_str_eq(mon["down_ref"], "mon-v1", "p4.mon.down_ref")

    mon_k = _req_exact_keys(
        p4["monitor_zone_b_isolation_on_killed"],
        {
            "coordinator_state",
            "sibling_verifier_state",
            "collateral_kill_count",
            "promotion_blocked",
            "down_messages_received",
            "down_tag",
            "down_ref",
            "down_reason",
        },
        "p4.mon_killed",
    )
    _req_strict_str_eq(mon_k["coordinator_state"], "ALIVE", "p4.mon_killed.coord")
    _req_strict_str_eq(mon_k["sibling_verifier_state"], "ALIVE", "p4.mon_killed.sibling")
    _req_strict_int_range(mon_k["collateral_kill_count"], 0, 0, "p4.mon_killed.kills")
    _req_bool_eq(mon_k["promotion_blocked"], True, "p4.mon_killed.promotion_blocked")
    _req_strict_int_range(mon_k["down_messages_received"], 1, 1, "p4.mon_killed.down_cnt")
    _req_strict_str_eq(mon_k["down_tag"], "DOWN", "p4.mon_killed.down_tag")
    _req_strict_str_eq(mon_k["down_ref"], "mon-v1", "p4.mon_killed.down_ref")
    _req_strict_str_eq(mon_k["down_reason"], "killed", "p4.mon_killed.down_reason")

    lt = _req_exact_keys(
        p4["link_with_trap_exit_abnormal"],
        {
            "coordinator_state",
            "sibling_verifier_state",
            "collateral_kill_count",
            "exit_messages_received",
            "exit_tag",
        },
        "p4.lt",
    )
    _req_strict_str_eq(lt["coordinator_state"], "ALIVE", "p4.lt.coord")
    _req_strict_str_eq(lt["sibling_verifier_state"], "ALIVE", "p4.lt.sibling")
    _req_strict_int_range(lt["collateral_kill_count"], 0, 0, "p4.lt.kills")
    _req_strict_int_range(lt["exit_messages_received"], 1, 1, "p4.lt.exit_cnt")
    _req_strict_str_eq(lt["exit_tag"], "EXIT", "p4.lt.exit_tag")

    lt_k = _req_exact_keys(
        p4["link_with_trap_exit_outside_killed"],
        {
            "coordinator_state",
            "sibling_verifier_state",
            "collateral_kill_count",
            "exit_messages_received",
            "exit_tag",
            "exit_reason",
        },
        "p4.lt_killed",
    )
    _req_strict_str_eq(lt_k["coordinator_state"], "ALIVE", "p4.lt_killed.coord")
    _req_strict_str_eq(lt_k["sibling_verifier_state"], "ALIVE", "p4.lt_killed.sibling")
    _req_strict_int_range(lt_k["collateral_kill_count"], 0, 0, "p4.lt_killed.kills")
    _req_strict_int_range(lt_k["exit_messages_received"], 1, 1, "p4.lt_killed.exit_cnt")
    _req_strict_str_eq(lt_k["exit_tag"], "EXIT", "p4.lt_killed.exit_tag")
    _req_strict_str_eq(lt_k["exit_reason"], "killed", "p4.lt_killed.exit_reason")

    mf1 = _req_exact_keys(
        p4["must_fail_link_without_trap_exit_kills_coordinator"],
        {"rejected", "error_code", "coordinator_state", "collateral_kills", "collateral_kill_count"},
        "p4.mf1",
    )
    _req_bool_eq(mf1["rejected"], True, "p4.mf1.rejected")
    _req_strict_str_eq(mf1["error_code"], "ERR_COORDINATOR_COLLATERAL_KILL", "p4.mf1.error_code")
    _req_strict_str_eq(mf1["coordinator_state"], "TERMINATED", "p4.mf1.coord")
    _req_str_list(mf1["collateral_kills"], ["coordinator", "verifier_2"], "p4.mf1.kills_list")
    _req_strict_int_range(mf1["collateral_kill_count"], 2, 2, "p4.mf1.kills_cnt")

    mf2 = _req_exact_keys(
        p4["must_fail_kill_bypasses_trap_exit"],
        {
            "rejected",
            "error_code",
            "coordinator_state",
            "coordinator_exit_reason",
            "collateral_kills",
            "collateral_kill_count",
        },
        "p4.mf2",
    )
    _req_bool_eq(mf2["rejected"], True, "p4.mf2.rejected")
    _req_strict_str_eq(mf2["error_code"], "ERR_COORDINATOR_COLLATERAL_KILL", "p4.mf2.error_code")
    _req_strict_str_eq(mf2["coordinator_state"], "TERMINATED", "p4.mf2.coord")
    _req_strict_str_eq(mf2["coordinator_exit_reason"], "killed", "p4.mf2.reason")
    _req_str_list(mf2["collateral_kills"], ["coordinator", "verifier_2"], "p4.mf2.kills_list")
    _req_strict_int_range(mf2["collateral_kill_count"], 2, 2, "p4.mf2.kills_cnt")


def _validate_p5(p5: Any) -> None:
    _req_exact_keys(
        p5,
        {
            "passed",
            "exo1200_ref_commit",
            "exo1200_group_supervision_sha256",
            "exo1200_zero_retry_default_action",
            "exo1200_zero_retry_default_reason",
            "hybrid_clean_run",
            "must_fail_hybrid_promotion_while_down",
            "must_fail_hybrid_exo1200_stopped_restart",
            "must_fail_hybrid_exo1200_external_effects",
        },
        "p5",
    )
    _req_bool_eq(p5["passed"], True, "p5.passed")
    _req_strict_str_eq(p5["exo1200_ref_commit"], EXO1200_REF_COMMIT, "p5.exo_commit")
    _req_strict_str_eq(p5["exo1200_group_supervision_sha256"], EXO1200_SUPERVISION_SHA256, "p5.exo_sha")
    _req_strict_str_eq(p5["exo1200_zero_retry_default_action"], "final", "p5.exo_action")
    _req_strict_str_eq(p5["exo1200_zero_retry_default_reason"], "retry_budget_exhausted", "p5.exo_reason")

    clean = _req_exact_keys(
        p5["hybrid_clean_run"],
        {"promoted", "final_snapshot_sha256", "zone_a_restarts", "down_events_observed", "author_attempts"},
        "p5.clean",
    )
    _req_bool_eq(clean["promoted"], True, "p5.clean.promoted")
    _req_strict_str_eq(clean["final_snapshot_sha256"], SNAPSHOT_SHA_V2, "p5.clean.sha")
    _req_strict_int_range(clean["zone_a_restarts"], 1, 1, "p5.clean.restarts")
    _req_strict_int_range(clean["down_events_observed"], 1, 1, "p5.clean.downs")
    _req_strict_int_range(clean["author_attempts"], 2, 2, "p5.clean.attempts")

    mf1 = _req_exact_keys(p5["must_fail_hybrid_promotion_while_down"], {"rejected", "error_code", "step_index"}, "p5.mf1")
    _req_bool_eq(mf1["rejected"], True, "p5.mf1.rejected")
    _req_strict_str_eq(mf1["error_code"], "ERR_PROMOTION_BLOCKED_BY_DOWN", "p5.mf1.error_code")
    _req_strict_int_range(mf1["step_index"], 2, 2, "p5.mf1.step")

    mf2 = _req_exact_keys(p5["must_fail_hybrid_exo1200_stopped_restart"], {"rejected", "error_code", "step_index"}, "p5.mf2")
    _req_bool_eq(mf2["rejected"], True, "p5.mf2.rejected")
    _req_strict_str_eq(mf2["error_code"], "ERR_STOPPED_TASK_RESTARTED", "p5.mf2.error_code")
    _req_strict_int_range(mf2["step_index"], 1, 1, "p5.mf2.step")

    mf3 = _req_exact_keys(p5["must_fail_hybrid_exo1200_external_effects"], {"rejected", "error_code", "step_index"}, "p5.mf3")
    _req_bool_eq(mf3["rejected"], True, "p5.mf3.rejected")
    _req_strict_str_eq(mf3["error_code"], "ERR_UNRECONCILED_EXTERNAL_EFFECTS", "p5.mf3.error_code")
    _req_strict_int_range(mf3["step_index"], 0, 0, "p5.mf3.step")


def validate_certificate(cert: Any) -> bool:
    """Fail-closed deep schema, semantic, and SHA-256 integrity validator."""
    if contains_float(cert):
        raise OtpSupervisionError("ERR_CERT_FLOAT", "certificate contains float or non-JSON value")
    _req_exact_keys(
        cert,
        {
            "schema_version",
            "track_id",
            "audit_id",
            "novelty_tier",
            "primary_sources",
            "pillars",
            "summary",
            "canonical_sha256",
        },
        "certificate",
    )
    _req_strict_str_eq(cert["schema_version"], SCHEMA_VERSION, "schema_version")
    _req_strict_str_eq(cert["track_id"], TRACK_ID, "track_id")
    _req_strict_str_eq(cert["audit_id"], AUDIT_ID, "audit_id")

    nt = _req_exact_keys(cert["novelty_tier"], {"classical_semantics", "pure_q_hybrid_bridge"}, "novelty_tier")
    _req_strict_str_eq(nt["classical_semantics"], "N0", "novelty_tier.classical_semantics")
    _req_strict_str_eq(nt["pure_q_hybrid_bridge"], "N0", "novelty_tier.pure_q_hybrid_bridge")

    ps = _req_exact_keys(
        cert["primary_sources"],
        {
            "armstrong_2003_kth_urn",
            "armstrong_2003_isrn",
            "armstrong_1996_isbn13",
            "otp_module",
            "exo1200_ref_commit",
            "exo1200_group_supervision_sha256",
        },
        "primary_sources",
    )
    _req_strict_str_eq(ps["armstrong_2003_kth_urn"], "urn:nbn:se:kth:diva-3658", "ps.urn")
    _req_strict_str_eq(ps["armstrong_2003_isrn"], "KTH/IMIT/LECS/AVH-03/09-SE", "ps.isrn")
    _req_strict_str_eq(ps["armstrong_1996_isbn13"], "978-0-13-508301-7", "ps.isbn13")
    _req_strict_str_eq(ps["otp_module"], "stdlib/src/supervisor.erl", "ps.otp_module")
    _req_strict_str_eq(ps["exo1200_ref_commit"], EXO1200_REF_COMMIT, "ps.exo_commit")
    _req_strict_str_eq(ps["exo1200_group_supervision_sha256"], EXO1200_SUPERVISION_SHA256, "ps.exo_sha")

    pillars = _req_exact_keys(
        cert["pillars"],
        {
            "p1_restart_policy_matrix",
            "p2_restart_strategies_and_non_churn",
            "p3_sliding_window_intensity_escalation",
            "p4_monitor_vs_link_fault_isolation",
            "p5_exo1200_aletheia_bridge",
        },
        "pillars",
    )
    _validate_p1(pillars["p1_restart_policy_matrix"])
    _validate_p2(pillars["p2_restart_strategies_and_non_churn"])
    _validate_p3(pillars["p3_sliding_window_intensity_escalation"])
    _validate_p4(pillars["p4_monitor_vs_link_fault_isolation"])
    _validate_p5(pillars["p5_exo1200_aletheia_bridge"])

    summary = _req_exact_keys(
        cert["summary"],
        {"all_passed", "pillars_passed", "pillars_total", "must_fail_controls_verified", "floats_used"},
        "summary",
    )
    _req_bool_eq(summary["all_passed"], True, "summary.all_passed")
    _req_strict_int_range(summary["pillars_passed"], 5, 5, "summary.pillars_passed")
    _req_strict_int_range(summary["pillars_total"], 5, 5, "summary.pillars_total")
    dyn_controls = _count_verified_must_fail_controls(pillars)
    _req_strict_int_range(summary["must_fail_controls_verified"], dyn_controls, dyn_controls, "summary.controls")
    _req_strict_int_range(summary["floats_used"], 0, 0, "summary.floats_used")

    claimed_sha = _req_hex64(cert["canonical_sha256"], "canonical_sha256")
    body = {k: v for k, v in cert.items() if k != "canonical_sha256"}
    expected_sha = canonical_sha256(body)
    if claimed_sha != expected_sha:
        raise OtpSupervisionError("ERR_CERT_SHA_MISMATCH", "canonical_sha256 mismatch")
    return True
