"""R5 Assertion-Free Verification & Mutation-Killing Suite for Track S11 (AUDIT-110).

Runs under `python3 -I -O -B -W error` (zero bare assert statements, zero floats).
Independently verifies all 5 pillars, all 10 must-fail controls, edge-case OTP
semantics, strict pure-Z/Q typing, fail-closed certificate validation, and CLI modes.
"""
from __future__ import annotations

import copy
import io
import json
import os
import sys
import tempfile
from contextlib import redirect_stdout
from fractions import Fraction

_SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
if _SCRIPT_DIR not in sys.path:
    sys.path.insert(0, _SCRIPT_DIR)

import erlang_otp_supervision_certifier as certifier  # noqa: E402
import erlang_otp_supervision_oracle as oracle  # noqa: E402


class _SubStr(str):
    pass


class _SubInt(int):
    pass


class _SubList(list):
    pass


class _SubDict(dict):
    pass


class _SubFrac(Fraction):
    pass


def _check(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"TEST_FAILURE: {msg}")


def _expect_err(fn, expected_code: str, msg: str) -> None:
    try:
        fn()
    except oracle.OtpSupervisionError as exc:
        if exc.code != expected_code:
            raise RuntimeError(f"{msg}: expected {expected_code}, got {exc.code} ({exc.detail})") from exc
        return
    raise RuntimeError(f"{msg}: expected OtpSupervisionError({expected_code}), but succeeded")


def _resign(cert: dict) -> dict:
    body = {k: v for k, v in cert.items() if k != "canonical_sha256"}
    cert["canonical_sha256"] = oracle.canonical_sha256(body)
    return cert


# ---------------------------------------------------------------------------
# Test 1: Pure-Z / Pure-Q Primitives & Fail-Closed Type Helpers
# ---------------------------------------------------------------------------

def test_primitives_and_helpers() -> None:
    _check(oracle._is_nonempty_str("abc"), "nonempty str")
    _check(not oracle._is_nonempty_str("   "), "whitespace rejected")
    _check(not oracle._is_nonempty_str(_SubStr("abc")), "str subclass rejected")
    _check(not oracle._is_nonempty_str(123), "int rejected")

    _check(oracle._in_str_set("a", ("a", "b")), "in str set")
    _check(not oracle._in_str_set(_SubStr("a"), ("a", "b")), "substr rejected in str set")
    _check(not oracle._in_str_set("c", ("a", "b")), "missing rejected in str set")
    _check(not oracle._in_str_set([], ("a", "b")), "unhashable rejected in str set")

    _check(oracle._is_hex64(oracle.SNAPSHOT_SHA_V1), "valid hex64")
    _check(not oracle._is_hex64(_SubStr(oracle.SNAPSHOT_SHA_V1)), "substr hex64 rejected")
    _check(not oracle._is_hex64("not-a-hex"), "non-hex rejected")
    _check(not oracle._is_hex64("0" * 64), "uniform zero hex64 rejected")
    _check(not oracle._is_hex64("f" * 64), "uniform f hex64 rejected")

    _check(not oracle.contains_float(None), "None ok")
    _check(not oracle.contains_float(True), "bool ok")
    _check(not oracle.contains_float(42), "int ok")
    _check(not oracle.contains_float("ok"), "str ok")
    _check(not oracle.contains_float({"a": [1, (2, None, False)]}), "nested clean ok")
    _check(oracle.contains_float(1.5), "float rejected")
    _check(oracle.contains_float(1j), "complex rejected")
    _check(oracle.contains_float({1}), "set rejected")
    _check(oracle.contains_float(frozenset({1})), "frozenset rejected")
    _check(oracle.contains_float(_SubInt(1)), "int subclass rejected")
    _check(oracle.contains_float({1.5: "v"}), "float dict key rejected")
    _check(oracle.contains_float({"k": 1.5}), "float dict val rejected")
    _check(oracle.contains_float([1, 2.0]), "float list val rejected")
    _check(oracle.contains_float((1, 2.0)), "float tuple val rejected")

    _expect_err(lambda: oracle.canonical_json_bytes({"x": 1.25}), "ERR_FLOAT_FORBIDDEN", "float in canonical json")
    _expect_err(lambda: oracle.canonical_json_bytes({1: "a", "b": 2}), "ERR_CANONICAL_JSON", "mixed key sort error")
    _check(oracle.canonical_json_bytes({"b": 1, "a": 2}) == b'{"a":2,"b":1}', "canonical json bytes")
    _check(len(oracle.canonical_sha256({"a": 1})) == 64, "canonical sha256")

    _check(oracle.frac_to_str(Fraction(2, 3)) == "2/3", "frac_to_str")
    _expect_err(lambda: oracle.frac_to_str(_SubFrac(1, 2)), "ERR_INVALID_FRACTION", "subfrac rejected")
    _expect_err(lambda: oracle.frac_to_str(1), "ERR_INVALID_FRACTION", "int rejected in frac_to_str")

    _check(oracle.parse_nonneg_fraction(0) == Fraction(0, 1), "int 0")
    _check(oracle.parse_nonneg_fraction(Fraction(3, 5)) == Fraction(3, 5), "frac 3/5")
    _check(oracle.parse_nonneg_fraction("0/1") == Fraction(0, 1), "str 0/1")
    _check(oracle.parse_nonneg_fraction("5/6") == Fraction(5, 6), "str 5/6")
    _expect_err(lambda: oracle.parse_nonneg_fraction(-1), "ERR_NEGATIVE_TICK", "neg int")
    _expect_err(lambda: oracle.parse_nonneg_fraction(Fraction(-1, 3)), "ERR_NEGATIVE_TICK", "neg frac")
    _expect_err(lambda: oracle.parse_nonneg_fraction("1/" + "9" * 64), "ERR_INVALID_FRACTION_STR", "overlong frac str")
    _expect_err(lambda: oracle.parse_nonneg_fraction("abc"), "ERR_INVALID_FRACTION_STR", "bad frac str")
    _expect_err(lambda: oracle.parse_nonneg_fraction("2/4"), "ERR_UNREDUCED_FRACTION", "unreduced frac str")
    _expect_err(lambda: oracle.parse_nonneg_fraction(1.5), "ERR_INVALID_TICK_TYPE", "float tick")
    _expect_err(lambda: oracle.parse_nonneg_fraction(True), "ERR_INVALID_TICK_TYPE", "bool tick")

    # Direct helper clause isolation
    _expect_err(lambda: oracle._req_exact_keys(_SubDict({"a": 1}), {"a"}, "k"), "ERR_SCHEMA_KEYS", "subdict rejected")
    _expect_err(lambda: oracle._req_exact_keys({"a": 1, "b": 2}, {"a"}, "k"), "ERR_SCHEMA_KEYS", "extra key rejected")
    _expect_err(lambda: oracle._req_strict_str_eq(_SubStr("a"), "a", "s"), "ERR_SCHEMA_STR", "substr eq rejected")
    _expect_err(lambda: oracle._req_strict_str_eq("b", "a", "s"), "ERR_SCHEMA_STR", "wrong str rejected")
    _expect_err(lambda: oracle._req_strict_int_range(True, 0, 5, "i"), "ERR_SCHEMA_INT", "bool int rejected")
    _expect_err(lambda: oracle._req_strict_int_range(-1, 0, 5, "i"), "ERR_SCHEMA_INT", "below low rejected")
    _expect_err(lambda: oracle._req_strict_int_range(6, 0, 5, "i"), "ERR_SCHEMA_INT", "above high rejected")
    _check(oracle._req_strict_int_range(5, 0, None, "i") == 5, "high None ok")
    _expect_err(lambda: oracle._req_bool_eq(1, True, "b"), "ERR_SCHEMA_BOOL", "int 1 not True")
    _expect_err(lambda: oracle._req_str_list(_SubList(["a"]), ["a"], "l"), "ERR_SCHEMA_LIST", "sublist rejected")
    _expect_err(lambda: oracle._req_str_list([""], None, "l"), "ERR_SCHEMA_LIST", "empty elem rejected")
    _expect_err(lambda: oracle._req_str_list(["a"], ["b"], "l"), "ERR_SCHEMA_LIST", "list value mismatch")
    _check(oracle._req_str_list(["a"], None, "l") == ["a"], "expected None ok")
    _expect_err(lambda: oracle._req_strict_int_list(_SubList([1]), [1], "il"), "ERR_SCHEMA_INT_LIST", "sublist int list")
    _expect_err(lambda: oracle._req_strict_int_list([True], [1], "il"), "ERR_SCHEMA_INT_LIST", "bool in int list")
    _expect_err(lambda: oracle._req_strict_int_list([2], [1], "il"), "ERR_SCHEMA_INT_LIST", "wrong int list")
    _expect_err(lambda: oracle._req_hex64("0" * 64, "h"), "ERR_INVALID_SHA256", "uniform sha rejected")


# ---------------------------------------------------------------------------
# Test 2: Pillar 1 — Exhaustive 3x3 Restart Policy Matrix & Controls
# ---------------------------------------------------------------------------

def test_pillar_1() -> None:
    expected_map = {
        ("permanent", "normal"): (True, "restart"),
        ("permanent", "shutdown"): (True, "restart"),
        ("permanent", "abnormal"): (True, "restart"),
        ("transient", "normal"): (False, "drop_child"),
        ("transient", "shutdown"): (False, "drop_child"),
        ("transient", "abnormal"): (True, "restart"),
        ("temporary", "normal"): (False, "drop_child"),
        ("temporary", "shutdown"): (False, "drop_child"),
        ("temporary", "abnormal"): (False, "drop_child"),
    }
    for (pol, rsn), (exp_b, exp_act) in expected_map.items():
        res = oracle.otp_should_restart(pol, rsn)
        _check(res["should_restart"] is exp_b and res["action"] == exp_act, f"cell {(pol, rsn)}")
        ok = oracle.certify_restart_decision(pol, rsn, exp_b)
        _check(ok["passed"] is True and ok["error_code"] is None, f"cert ok {(pol, rsn)}")

    _expect_err(lambda: oracle.otp_should_restart("unknown", "normal"), "ERR_INVALID_POLICY", "bad policy")
    _expect_err(lambda: oracle.otp_should_restart("permanent", "crash"), "ERR_INVALID_EXIT_REASON", "bad reason")
    _expect_err(lambda: oracle.certify_restart_decision("permanent", "normal", 1), "ERR_INVALID_OBSERVED_BOOL", "int obs")

    # Every error branch of certify_restart_decision
    bad_temp = oracle.certify_restart_decision("temporary", "abnormal", True)
    _check(not bad_temp["passed"] and bad_temp["error_code"] == "ERR_TEMPORARY_CHILD_RESTARTED", "temp restarted")
    bad_trans_norm = oracle.certify_restart_decision("transient", "normal", True)
    _check(not bad_trans_norm["passed"] and bad_trans_norm["error_code"] == "ERR_TRANSIENT_CLEAN_EXIT_RESTARTED", "trans norm")
    bad_trans_skip = oracle.certify_restart_decision("transient", "abnormal", False)
    _check(not bad_trans_skip["passed"] and bad_trans_skip["error_code"] == "ERR_REQUIRED_RESTART_SKIPPED", "trans skip")
    bad_perm_skip = oracle.certify_restart_decision("permanent", "normal", False)
    _check(not bad_perm_skip["passed"] and bad_perm_skip["error_code"] == "ERR_REQUIRED_RESTART_SKIPPED", "perm skip")


# ---------------------------------------------------------------------------
# Test 3: Pillar 2 — All 3 OTP Strategies & Frozen-Snapshot Non-Churn
# ---------------------------------------------------------------------------

def test_pillar_2() -> None:
    def _mk_children():
        return [
            {"id": "planner", "policy": "permanent", "generation": 1, "snapshot_sha256": oracle.SNAPSHOT_SHA_V1, "alive": True},
            {"id": "author", "policy": "transient", "generation": 1, "snapshot_sha256": oracle.SNAPSHOT_SHA_V1, "alive": True},
            {"id": "airlock_snapshot", "policy": "permanent", "generation": 1, "snapshot_sha256": oracle.SNAPSHOT_SHA_V1, "alive": True},
            {"id": "verifier_a", "policy": "permanent", "generation": 1, "snapshot_sha256": oracle.SNAPSHOT_SHA_V1, "alive": True},
            {"id": "verifier_b", "policy": "permanent", "generation": 1, "snapshot_sha256": oracle.SNAPSHOT_SHA_V1, "alive": True},
        ]

    # Exact orders for all 3 strategies
    o4o = oracle.apply_strategy_crash("one_for_one", _mk_children(), "author", "abnormal", oracle.SNAPSHOT_SHA_V2)
    _check(o4o["terminated_order"] == [] and o4o["restarted_order"] == ["author"], "o4o order")
    _check([c["generation"] for c in o4o["children_after"]] == [1, 2, 1, 1, 1], "o4o gens")

    o4a = oracle.apply_strategy_crash("one_for_all", _mk_children(), "author", "abnormal", oracle.SNAPSHOT_SHA_V2)
    _check(o4a["terminated_order"] == ["verifier_b", "verifier_a", "airlock_snapshot", "planner"], "o4a term order")
    _check(o4a["restarted_order"] == ["planner", "author", "airlock_snapshot", "verifier_a", "verifier_b"], "o4a restart order")

    r4o = oracle.apply_strategy_crash("rest_for_one", _mk_children(), "author", "abnormal", oracle.SNAPSHOT_SHA_V2)
    _check(r4o["terminated_order"] == ["verifier_b", "verifier_a", "airlock_snapshot"], "r4o term order")
    _check(r4o["restarted_order"] == ["author", "airlock_snapshot", "verifier_a", "verifier_b"], "r4o restart order")
    _check(r4o["children_after"][0]["generation"] == 1, "planner untouched")
    _check(r4o["children_after"][0]["snapshot_sha256"] == oracle.SNAPSHOT_SHA_V1, "planner sha untouched")

    # One-for-all & rest-for-one skip already-dead siblings during termination
    partial = _mk_children()
    partial[4]["alive"] = False
    o4a_dead = oracle.apply_strategy_crash("one_for_all", partial, "author", "abnormal", None)
    _check(o4a_dead["terminated_order"] == ["verifier_a", "airlock_snapshot", "planner"], "o4a skips dead")
    _check(o4a_dead["children_after"][1]["snapshot_sha256"] == oracle.SNAPSHOT_SHA_V1, "None sha preserves old sha")
    r4o_dead = oracle.apply_strategy_crash("rest_for_one", partial, "author", "abnormal", None)
    _check(r4o_dead["terminated_order"] == ["verifier_a", "airlock_snapshot"], "r4o skips dead")

    # OTP110-BUG-01: one_for_all & rest_for_one never resurrect dead temporary or dead transient children,
    # and never restart an alive temporary sibling terminated by strategy restart!
    mixed_children = [
        {"id": "perm_a", "policy": "permanent", "generation": 1, "snapshot_sha256": oracle.SNAPSHOT_SHA_V1, "alive": True},
        {"id": "auth", "policy": "transient", "generation": 1, "snapshot_sha256": oracle.SNAPSHOT_SHA_V1, "alive": True},
        {"id": "dead_temp", "policy": "temporary", "generation": 1, "snapshot_sha256": oracle.SNAPSHOT_SHA_V1, "alive": False},
        {"id": "live_temp", "policy": "temporary", "generation": 1, "snapshot_sha256": oracle.SNAPSHOT_SHA_V1, "alive": True},
        {"id": "dead_trans", "policy": "transient", "generation": 1, "snapshot_sha256": oracle.SNAPSHOT_SHA_V1, "alive": False},
        {"id": "live_trans", "policy": "transient", "generation": 1, "snapshot_sha256": oracle.SNAPSHOT_SHA_V1, "alive": True},
    ]
    r4o_mix = oracle.apply_strategy_crash("rest_for_one", mixed_children, "auth", "abnormal", oracle.SNAPSHOT_SHA_V2)
    _check(r4o_mix["terminated_order"] == ["live_trans", "live_temp"], "r4o terminates live downstream incl temp")
    _check(r4o_mix["restarted_order"] == ["auth", "live_trans"], "r4o skips dead/live temporary and dead transient")
    by_id_mix = {c["id"]: c for c in r4o_mix["children_after"]}
    _check(by_id_mix["dead_temp"]["alive"] is False and by_id_mix["dead_temp"]["generation"] == 1, "dead temp stays dead")
    _check(by_id_mix["live_temp"]["alive"] is False and by_id_mix["live_temp"]["generation"] == 1, "live temp dropped after term")
    _check(by_id_mix["dead_trans"]["alive"] is False and by_id_mix["dead_trans"]["generation"] == 1, "dead transient stays dead")
    _check(by_id_mix["live_trans"]["alive"] is True and by_id_mix["live_trans"]["generation"] == 2, "live transient restarted")
    o4a_mix = oracle.apply_strategy_crash("one_for_all", mixed_children, "auth", "abnormal", oracle.SNAPSHOT_SHA_V2)
    _check(o4a_mix["restarted_order"] == ["perm_a", "auth", "live_trans"], "o4a never resurrects dead temp/transient")

    # Non-restartable normal exit on transient child drops child with empty terminate/restart lists
    clean_exit = oracle.apply_strategy_crash("rest_for_one", _mk_children(), "author", "normal", oracle.SNAPSHOT_SHA_V2)
    _check(not clean_exit["restarted"] and clean_exit["terminated_order"] == [] and clean_exit["restarted_order"] == [], "clean transient drop")
    _check(clean_exit["children_after"][1]["alive"] is False, "author dropped")

    # Snapshot non-churn vs churn (also verify dead downstream is not flagged stale)
    nc_ok = oracle.verify_snapshot_non_churn(r4o["children_after"], "author", ["airlock_snapshot", "verifier_a", "verifier_b"])
    _check(nc_ok["passed"] is True and nc_ok["stale_count"] == 0, "r4o non-churn ok")
    nc_bad = oracle.verify_snapshot_non_churn(o4o["children_after"], "author", ["airlock_snapshot", "verifier_a", "verifier_b"])
    _check(nc_bad["passed"] is False and nc_bad["error_code"] == "ERR_SNAPSHOT_CHURN" and nc_bad["stale_count"] == 3, "o4o churn caught")
    o4o_dead_down = copy.deepcopy(o4o["children_after"])
    o4o_dead_down[4]["alive"] = False
    nc_partial = oracle.verify_snapshot_non_churn(o4o_dead_down, "author", ["verifier_b"])
    _check(nc_partial["passed"] is True, "dead downstream ignored")

    # Validation error paths
    _expect_err(lambda: oracle.apply_strategy_crash("bad_strat", _mk_children(), "author", "abnormal"), "ERR_INVALID_STRATEGY", "bad strategy")
    _expect_err(lambda: oracle.apply_strategy_crash("one_for_one", "not_list", "author", "abnormal"), "ERR_INVALID_CHILDREN", "children not list")
    _expect_err(lambda: oracle.apply_strategy_crash("one_for_one", [], "author", "abnormal"), "ERR_INVALID_CHILDREN", "empty children")
    dup = _mk_children()
    dup[1]["id"] = "planner"
    _expect_err(lambda: oracle.apply_strategy_crash("one_for_one", dup, "planner", "abnormal"), "ERR_INVALID_CHILD_ID", "dup id")
    bad_id = _mk_children()
    bad_id[0]["id"] = ""
    _expect_err(lambda: oracle.apply_strategy_crash("one_for_one", bad_id, "author", "abnormal"), "ERR_INVALID_CHILD_ID", "empty id")
    bad_pol = _mk_children()
    bad_pol[0]["policy"] = "bogus"
    _expect_err(lambda: oracle.apply_strategy_crash("one_for_one", bad_pol, "author", "abnormal"), "ERR_INVALID_POLICY", "bad child policy")
    bad_alive = _mk_children()
    bad_alive[0]["alive"] = 1
    _expect_err(lambda: oracle.apply_strategy_crash("one_for_one", bad_alive, "author", "abnormal"), "ERR_INVALID_ALIVE", "non-bool alive")
    _expect_err(lambda: oracle.apply_strategy_crash("one_for_one", _mk_children(), "ghost", "abnormal"), "ERR_UNKNOWN_CHILD", "unknown child")
    dead_auth = _mk_children()
    dead_auth[1]["alive"] = False
    _expect_err(lambda: oracle.apply_strategy_crash("one_for_one", dead_auth, "author", "abnormal"), "ERR_CHILD_ALREADY_DEAD", "dead crashed child")
    _expect_err(lambda: oracle.verify_snapshot_non_churn(_mk_children(), "ghost", ["verifier_a"]), "ERR_UNKNOWN_AUTHOR", "unknown author")
    _expect_err(lambda: oracle.verify_snapshot_non_churn(_mk_children(), "author", "not_list"), "ERR_INVALID_DOWNSTREAM", "downstream not list")
    _expect_err(lambda: oracle.verify_snapshot_non_churn(_mk_children(), "author", []), "ERR_INVALID_DOWNSTREAM", "downstream empty")
    _expect_err(lambda: oracle.verify_snapshot_non_churn(_mk_children(), "author", ["ghost"]), "ERR_UNKNOWN_DOWNSTREAM", "unknown downstream")


# ---------------------------------------------------------------------------
# Test 4: Pillar 3 — Pure-Z/Q Sliding-Window Intensity & Tree Escalation
# ---------------------------------------------------------------------------

def test_pillar_3() -> None:
    # Exact inclusive boundary check: now - then == window stays in window
    s1 = oracle.step_restart_intensity([0], 5, 2, 5)
    _check(s1["active_count"] == 2 and s1["evicted_count"] == 0 and not s1["escalated"], "inclusive boundary t=5")
    s2 = oracle.step_restart_intensity([0, 5], 6, 2, 5)
    _check(s2["active_count"] == 2 and s2["evicted_count"] == 1 and s2["active_window"] == ["5/1", "6/1"], "eviction at t=6")
    s3 = oracle.step_restart_intensity([5, 6], 10, 2, 5)
    _check(s3["escalated"] is True and s3["exit_reason"] == "reached_max_restart_intensity", "escalation at t=10")

    # max_restarts == 0 escalates on the very first restart
    s0 = oracle.step_restart_intensity([], 0, 0, 5)
    _check(s0["escalated"] is True and s0["active_count"] == 1, "max_restarts=0 escalates immediately")

    # Rational Q exact boundary: 1/3 + 1/3 = 2/3 without float rounding error
    sq = oracle.step_restart_intensity([Fraction(0, 1)], Fraction(1, 3), 2, Fraction(1, 3))
    _check(sq["active_count"] == 2 and sq["active_window"] == ["0/1", "1/3"], "exact 1/3 boundary")
    sq_ev = oracle.step_restart_intensity([Fraction(0, 1), Fraction(1, 3)], Fraction(2, 3), 2, Fraction(1, 3))
    _check(sq_ev["evicted_count"] == 1 and sq_ev["active_window"] == ["1/3", "2/3"], "exact 2/3 eviction")

    # Error checks on step_restart_intensity
    _expect_err(lambda: oracle.step_restart_intensity("not_list", 1, 2, 5), "ERR_INVALID_HISTORY", "history not list")
    _expect_err(lambda: oracle.step_restart_intensity([], 1, 2, 0), "ERR_NON_POSITIVE_WINDOW", "zero window")
    _expect_err(lambda: oracle.step_restart_intensity([5, 3], 6, 2, 5), "ERR_NON_MONOTONIC_TICK", "unsorted history")
    _expect_err(lambda: oracle.step_restart_intensity([5], 4, 2, 5), "ERR_NON_MONOTONIC_TICK", "now < prev")

    # certify_intensity_trace error & spurious escalation paths
    _expect_err(lambda: oracle.certify_intensity_trace(2, 0, [{"tick": 0, "claimed_decision": "RESTART_ALLOWED"}]), "ERR_NON_POSITIVE_WINDOW", "zero win trace")
    _expect_err(lambda: oracle.certify_intensity_trace(2, 5, "not_list"), "ERR_INVALID_EVENTS", "events not list")
    _expect_err(lambda: oracle.certify_intensity_trace(2, 5, []), "ERR_INVALID_EVENTS", "events empty")
    _expect_err(lambda: oracle.certify_intensity_trace(2, 5, [{"tick": 0, "claimed_decision": "BOGUS"}]), "ERR_INVALID_DECISION", "bad decision")

    spurious = oracle.certify_intensity_trace(2, 5, [{"tick": 0, "claimed_decision": "MAX_RESTART_INTENSITY_EXCEEDED"}])
    _check(not spurious["passed"] and spurious["error_code"] == "ERR_SPURIOUS_ESCALATION", "spurious escalation caught")

    # Clean trace ending without escalation
    ok_trace = oracle.certify_intensity_trace(2, 5, [{"tick": 0, "claimed_decision": "RESTART_ALLOWED"}])
    _check(ok_trace["passed"] is True and ok_trace["step_index"] == 0, "non-escalating trace ok")

    # OTP110-BUG-02: trailing events after MAX_RESTART_INTENSITY_EXCEEDED must fail closed
    trailing_esc = oracle.certify_intensity_trace(
        0,
        5,
        [
            {"tick": 0, "claimed_decision": "MAX_RESTART_INTENSITY_EXCEEDED"},
            {"tick": -999, "claimed_decision": "RESTART_ALLOWED"},
        ],
    )
    _check(
        not trailing_esc["passed"] and trailing_esc["error_code"] == "ERR_EVENT_AFTER_ESCALATION" and trailing_esc["step_index"] == 1,
        "trailing event after escalation rejected",
    )

    # Multi-level tree escalation (both terminating and surviving cases)
    tree_survive = oracle.simulate_tree_escalation([0, 1, 2], 2, 5, 1, 10)
    _check(tree_survive["sub_escalations"] == 1 and tree_survive["sub_restarts_by_root"] == 1 and not tree_survive["root_terminated"], "tree survives 1 sub escalation")
    tree_die = oracle.simulate_tree_escalation([0, 1, 2, 3, 4, 5], 2, 5, 1, 10)
    _check(tree_die["sub_escalations"] == 2 and tree_die["root_terminated"] is True and tree_die["root_terminated_at"] == "5/1", "tree terminates at t=5")

    _expect_err(lambda: oracle.simulate_tree_escalation([], 2, 0, 1, 10), "ERR_NON_POSITIVE_WINDOW", "sub win 0 before empty ticks")
    _expect_err(lambda: oracle.simulate_tree_escalation([0], 2, 5, 1, 0), "ERR_NON_POSITIVE_WINDOW", "root win 0")
    _expect_err(lambda: oracle.simulate_tree_escalation("bad", 2, 5, 1, 10), "ERR_INVALID_CRASH_TICKS", "ticks not list")
    _expect_err(lambda: oracle.simulate_tree_escalation([], 2, 5, 1, 10), "ERR_INVALID_CRASH_TICKS", "ticks empty")


# ---------------------------------------------------------------------------
# Test 5: Pillar 4 — Asymmetric Fault Isolation (monitor vs link +- trap_exit)
# ---------------------------------------------------------------------------

def test_pillar_4() -> None:
    procs_base = {
        "coordinator": {"role": "zone_a_coordinator", "trap_exit": False},
        "verifier_1": {"role": "zone_b_verifier", "trap_exit": False},
        "verifier_2": {"role": "zone_b_verifier", "trap_exit": False},
    }
    monitors = [
        {"watcher": "coordinator", "target": "verifier_1", "ref": "m1"},
        {"watcher": "coordinator", "target": "verifier_2", "ref": "m2"},
    ]

    # Normal exit via monitor does NOT set promotion_blocked
    sim_norm_mon = oracle.simulate_process_fault(procs_base, [], monitors, "verifier_1", "normal")
    _check(sim_norm_mon["processes"]["coordinator"]["promotion_blocked"] is False, "normal DOWN does not block promotion")
    cert_norm = oracle.certify_zone_b_isolation(sim_norm_mon, "coordinator")
    _check(not cert_norm["passed"] and cert_norm["error_code"] == "ERR_DOWN_PROMOTION_NOT_BLOCKED", "unblocked promotion rejected")

    # Non-coordinator watching verifier or coordinator watching non-verifier does not set promotion_blocked
    procs_roles = {
        "observer": {"role": "zone_a_worker", "trap_exit": False},
        "coordinator": {"role": "zone_a_coordinator", "trap_exit": False},
        "helper": {"role": "zone_a_worker", "trap_exit": False},
        "verifier_1": {"role": "zone_b_verifier", "trap_exit": False},
    }
    sim_obs = oracle.simulate_process_fault(
        procs_roles, [], [{"watcher": "observer", "target": "verifier_1", "ref": "r1"}], "verifier_1", "abnormal"
    )
    _check(sim_obs["processes"]["observer"]["promotion_blocked"] is False, "non-coordinator not promotion_blocked")
    sim_helper = oracle.simulate_process_fault(
        procs_roles, [], [{"watcher": "coordinator", "target": "helper", "ref": "r2"}], "helper", "abnormal"
    )
    _check(sim_helper["processes"]["coordinator"]["promotion_blocked"] is False, "non-verifier target not promotion_blocked")

    # Bidirectional link normal exit: ignored when trap_exit=False, delivered as EXIT when trap_exit=True
    sim_link_norm_nt = oracle.simulate_process_fault(procs_base, [["coordinator", "verifier_1"]], [], "verifier_1", "normal")
    _check(sim_link_norm_nt["processes"]["coordinator"]["state"] == "ALIVE" and sim_link_norm_nt["processes"]["coordinator"]["inbox"] == [], "normal link ignored")
    procs_trap = copy.deepcopy(procs_base)
    procs_trap["coordinator"]["trap_exit"] = True
    sim_link_norm_tr = oracle.simulate_process_fault(procs_trap, [["coordinator", "verifier_1"]], [], "verifier_1", "normal")
    _check(sim_link_norm_tr["processes"]["coordinator"]["inbox"] == [{"tag": "EXIT", "from": "verifier_1", "reason": "normal"}], "normal link trapped")

    # Monitor under external exit(verifier_1, kill) -> reason "killed" (and direct "kill"): 0 collateral kills + promotion blocked
    sim_mon_killed = oracle.simulate_process_fault(procs_base, [], monitors, "verifier_1", "killed")
    cert_mon_killed = oracle.certify_zone_b_isolation(sim_mon_killed, "coordinator")
    _check(cert_mon_killed["passed"] is True, "monitor isolates killed verifier")
    _check(sim_mon_killed["processes"]["coordinator"]["inbox"][0]["reason"] == "killed", "monitor DOWN reason killed")
    sim_mon_kill = oracle.simulate_process_fault(procs_base, [], monitors, "verifier_1", "kill")
    _check(oracle.certify_zone_b_isolation(sim_mon_kill, "coordinator")["passed"] is True, "monitor isolates kill")

    # External exit(verifier_1, kill) -> reason "killed" across link:
    # - trap_exit=True TRAPS "killed" and stays ALIVE (0 collateral kills)
    # - trap_exit=False dies with reason "killed" and cascades to verifier_2
    sim_link_trap_killed = oracle.simulate_process_fault(procs_trap, [["coordinator", "verifier_1"], ["coordinator", "verifier_2"]], [], "verifier_1", "killed")
    _check(sim_link_trap_killed["processes"]["coordinator"]["state"] == "ALIVE", "trap_exit=True traps propagated killed")
    _check(sim_link_trap_killed["processes"]["coordinator"]["inbox"] == [{"tag": "EXIT", "from": "verifier_1", "reason": "killed"}], "trapped killed EXIT msg")
    _check(sim_link_trap_killed["collateral_kill_count"] == 0, "0 collateral kills when trapping killed")

    sim_link_notrap_killed = oracle.simulate_process_fault(procs_base, [["coordinator", "verifier_1"], ["coordinator", "verifier_2"]], [], "verifier_1", "killed")
    _check(sim_link_notrap_killed["processes"]["coordinator"]["state"] == "TERMINATED", "trap_exit=False dies on killed")
    _check(sim_link_notrap_killed["processes"]["coordinator"]["exit_reason"] == "killed", "trap_exit=False exit reason killed")
    _check(sim_link_notrap_killed["collateral_kill_count"] == 2, "trap_exit=False cascades killed")

    # 3-hop kill propagation: verifier_1 -(kill)-> coordinator(trap=True) dies with "killed",
    # then propagates "killed" to verifier_2(trap=True) which TRAPS "killed" and survives!
    procs_both_trap = {
        "coordinator": {"role": "zone_a_coordinator", "trap_exit": True},
        "verifier_1": {"role": "zone_b_verifier", "trap_exit": False},
        "verifier_2": {"role": "zone_b_verifier", "trap_exit": True},
    }
    sim_3hop = oracle.simulate_process_fault(
        procs_both_trap,
        [["verifier_1", "coordinator"], ["coordinator", "verifier_2"]],
        [],
        "verifier_1",
        "kill",
    )
    _check(sim_3hop["processes"]["coordinator"]["state"] == "TERMINATED", "kill kills trap_exit coordinator")
    _check(sim_3hop["processes"]["coordinator"]["exit_reason"] == "killed", "reason becomes killed")
    _check(sim_3hop["processes"]["verifier_2"]["state"] == "ALIVE", "propagated killed is trappable downstream")
    _check(sim_3hop["processes"]["verifier_2"]["inbox"][0]["reason"] == "killed", "downstream trapped killed")

    # Sibling collateral kill while coordinator stays ALIVE (verifier_1 linked to verifier_2, monitored by coordinator)
    sim_sib = oracle.simulate_process_fault(
        procs_base, [["verifier_1", "verifier_2"]], monitors, "verifier_1", "abnormal"
    )
    cert_sib = oracle.certify_zone_b_isolation(sim_sib, "coordinator")
    _check(not cert_sib["passed"] and cert_sib["error_code"] == "ERR_SIBLING_COLLATERAL_KILL", "sibling kill rejected")

    # Dead watcher does not receive DOWN; duplicate links deduplicated; cycle does not infinite-loop
    sim_dead_watch = oracle.simulate_process_fault(
        procs_base,
        [["verifier_1", "coordinator"], ["verifier_1", "coordinator"], ["coordinator", "verifier_2"], ["verifier_2", "verifier_1"]],
        [{"watcher": "coordinator", "target": "verifier_2", "ref": "m-dead"}],
        "verifier_1",
        "abnormal",
    )
    _check(sim_dead_watch["processes"]["coordinator"]["inbox"] == [], "dead watcher gets no DOWN")

    # Input validation errors
    _expect_err(lambda: oracle.simulate_process_fault("bad", [], [], "a", "abnormal"), "ERR_INVALID_PROCESSES", "procs not dict")
    _expect_err(lambda: oracle.simulate_process_fault({}, [], [], "a", "abnormal"), "ERR_INVALID_PROCESSES", "procs empty")
    _expect_err(lambda: oracle.simulate_process_fault(procs_base, [], [], "verifier_1", "bogus"), "ERR_INVALID_EXIT_REASON", "bad signal reason")
    _expect_err(lambda: oracle.simulate_process_fault({"": {"role": "r", "trap_exit": False}}, [], [], "", "abnormal"), "ERR_INVALID_PID", "empty pid")
    _expect_err(lambda: oracle.simulate_process_fault({"p": {"role": "", "trap_exit": False}}, [], [], "p", "abnormal"), "ERR_INVALID_PROCESS_META", "empty role")
    _expect_err(lambda: oracle.simulate_process_fault({"p": {"role": "r", "trap_exit": 1}}, [], [], "p", "abnormal"), "ERR_INVALID_PROCESS_META", "non-bool trap_exit")
    _expect_err(lambda: oracle.simulate_process_fault(procs_base, [], [], "ghost", "abnormal"), "ERR_UNKNOWN_PID", "unknown crash pid")
    _expect_err(lambda: oracle.simulate_process_fault(procs_base, "bad", [], "verifier_1", "abnormal"), "ERR_INVALID_LINKS", "links not list")
    _expect_err(lambda: oracle.simulate_process_fault(procs_base, [("coordinator", "verifier_1")], [], "verifier_1", "abnormal"), "ERR_INVALID_LINK_PAIR", "link tuple len 2 not list")
    _expect_err(lambda: oracle.simulate_process_fault(procs_base, [["coordinator"]], [], "verifier_1", "abnormal"), "ERR_INVALID_LINK_PAIR", "link len 1")
    _expect_err(lambda: oracle.simulate_process_fault(procs_base, [["ghost", "verifier_1"]], [], "verifier_1", "abnormal"), "ERR_INVALID_LINK_ENDPOINTS", "link unknown a")
    _expect_err(lambda: oracle.simulate_process_fault(procs_base, [["verifier_1", "ghost"]], [], "verifier_1", "abnormal"), "ERR_INVALID_LINK_ENDPOINTS", "link unknown b")
    _expect_err(lambda: oracle.simulate_process_fault(procs_base, [["verifier_1", "verifier_1"]], [], "verifier_1", "abnormal"), "ERR_INVALID_LINK_ENDPOINTS", "self link")
    _expect_err(lambda: oracle.simulate_process_fault(procs_base, [], "bad", "verifier_1", "abnormal"), "ERR_INVALID_MONITORS", "monitors not list")
    _expect_err(lambda: oracle.simulate_process_fault(procs_base, [], [{"watcher": "ghost", "target": "verifier_1", "ref": "r"}], "verifier_1", "abnormal"), "ERR_INVALID_MONITOR_ENDPOINTS", "mon unknown w")
    _expect_err(lambda: oracle.simulate_process_fault(procs_base, [], [{"watcher": "coordinator", "target": "ghost", "ref": "r"}], "verifier_1", "abnormal"), "ERR_INVALID_MONITOR_ENDPOINTS", "mon unknown t")
    _expect_err(lambda: oracle.simulate_process_fault(procs_base, [], [{"watcher": "verifier_1", "target": "verifier_1", "ref": "r"}], "verifier_1", "abnormal"), "ERR_INVALID_MONITOR_ENDPOINTS", "self monitor")
    _expect_err(lambda: oracle.simulate_process_fault(procs_base, [], [{"watcher": "coordinator", "target": "verifier_1", "ref": ""}], "verifier_1", "abnormal"), "ERR_INVALID_MONITOR_REF", "empty ref")
    _expect_err(lambda: oracle.simulate_process_fault(procs_base, [], [{"watcher": "coordinator", "target": "verifier_1", "ref": "r1"}, {"watcher": "coordinator", "target": "verifier_2", "ref": "r1"}], "verifier_1", "abnormal"), "ERR_INVALID_MONITOR_REF", "dup ref")
    _expect_err(lambda: oracle.certify_zone_b_isolation({"crash_pid": "v", "exit_reason": "abnormal", "collateral_kills": [], "collateral_kill_count": 0, "processes": _SubDict(sim_norm_mon["processes"])}, "coordinator"), "ERR_UNKNOWN_COORDINATOR", "subdict procs")
    _expect_err(lambda: oracle.certify_zone_b_isolation(sim_norm_mon, "ghost"), "ERR_UNKNOWN_COORDINATOR", "unknown coord")


# ---------------------------------------------------------------------------
# Test 6: Pillar 5 — exo#1200 x aletheia v2.1+ Hybrid Swarm Bridge
# ---------------------------------------------------------------------------

def test_pillar_5() -> None:
    base_kw = dict(
        task_state="failed",
        failure_class="transient",
        effect_class="not_dispatched",
        attempt_number=1,
        max_retries=2,
        stop_requested=False,
        otp_policy="transient",
        exit_reason="abnormal",
    )
    _check(oracle.exo1200_otp_retry_gate(**base_kw)["action"] == "retry", "clean retry")
    _check(oracle.exo1200_otp_retry_gate(**{**base_kw, "attempt_number": 2, "max_retries": 2})["action"] == "retry", "exact attempt == max_retries allowed")
    _check(oracle.exo1200_otp_retry_gate(**{**base_kw, "stop_requested": True})["action"] == "final", "stop_requested overrides")
    _check(oracle.exo1200_otp_retry_gate(**{**base_kw, "task_state": "stopped"})["action"] == "final", "stopped task final")
    _check(oracle.exo1200_otp_retry_gate(**{**base_kw, "failure_class": "permanent"})["action"] == "final", "permanent failure final")
    _check(oracle.exo1200_otp_retry_gate(**{**base_kw, "task_state": "completed"})["action"] == "final", "completed final")
    _check(oracle.exo1200_otp_retry_gate(**{**base_kw, "task_state": "running"})["action"] == "reconcile", "non-failed reconcile")
    _check(oracle.exo1200_otp_retry_gate(**{**base_kw, "effect_class": "external"})["action"] == "reconcile", "external reconcile")
    _check(oracle.exo1200_otp_retry_gate(**{**base_kw, "failure_class": "unknown"})["action"] == "reconcile", "unknown failure reconcile")
    _check(oracle.exo1200_otp_retry_gate(**{**base_kw, "otp_policy": "temporary"})["reason"] == "otp_policy_forbids_restart", "otp policy forbids")
    _check(oracle.exo1200_otp_retry_gate(**{**base_kw, "max_retries": 0})["reason"] == "retry_budget_exhausted", "budget exhausted")

    _expect_err(lambda: oracle.exo1200_otp_retry_gate(**{**base_kw, "task_state": ""}), "ERR_INVALID_TASK_STATE", "empty task_state")
    _expect_err(lambda: oracle.exo1200_otp_retry_gate(**{**base_kw, "failure_class": "bad"}), "ERR_INVALID_FAILURE_CLASS", "bad failure")
    _expect_err(lambda: oracle.exo1200_otp_retry_gate(**{**base_kw, "effect_class": "bad"}), "ERR_INVALID_EFFECT_CLASS", "bad effect")
    _expect_err(lambda: oracle.exo1200_otp_retry_gate(**{**base_kw, "stop_requested": 1}), "ERR_INVALID_STOP_FLAG", "int stop flag")

    # certify_hybrid_swarm_run branches & errors
    def _mk_spec(events, max_retries=2, max_restarts=2, window_ticks=10):
        return {
            "max_retries": max_retries,
            "max_restarts": max_restarts,
            "window_ticks": window_ticks,
            "initial_snapshot_sha256": oracle.SNAPSHOT_SHA_V1,
            "events": events,
        }

    # Normal verifier exit does not block promotion
    res_norm_v = oracle.certify_hybrid_swarm_run(_mk_spec([
        {"op": "verifier_crash", "verifier_id": "verifier_1", "reason": "normal"},
    ]))
    _check(res_norm_v["passed"] is True and res_norm_v["down_events_observed"] == 1, "normal verifier exit")

    # Retry gate denied (budget exhausted)
    res_budget = oracle.certify_hybrid_swarm_run(_mk_spec([
        {"op": "author_crash_restart", "tick": 1, "failure_class": "transient", "effect_class": "not_dispatched", "new_snapshot_sha256": oracle.SNAPSHOT_SHA_V2},
    ], max_retries=0))
    _check(not res_budget["passed"] and res_budget["error_code"] == "ERR_RETRY_GATE_DENIED", "budget denied")

    # Intensity escalated
    res_int = oracle.certify_hybrid_swarm_run(_mk_spec([
        {"op": "author_crash_restart", "tick": 1, "failure_class": "transient", "effect_class": "not_dispatched", "new_snapshot_sha256": oracle.SNAPSHOT_SHA_V2},
    ], max_retries=2, max_restarts=0))
    _check(not res_int["passed"] and res_int["error_code"] == "ERR_INTENSITY_ESCALATED", "intensity escalated")

    # Dead verifier verdict, stale verdict snapshot, FALSIFIED verdict blocking promotion,
    # promote on stopped plan, promote snapshot mismatch, incomplete verification
    res_dead_v = oracle.certify_hybrid_swarm_run(_mk_spec([
        {"op": "verifier_crash", "verifier_id": "verifier_1", "reason": "abnormal"},
        {"op": "verifier_verdict", "verifier_id": "verifier_1", "snapshot_sha256": oracle.SNAPSHOT_SHA_V1, "verdict": "VERIFIED"},
    ]))
    _check(not res_dead_v["passed"] and res_dead_v["error_code"] == "ERR_DEAD_VERIFIER_VERDICT", "dead verifier verdict")

    res_stale_v = oracle.certify_hybrid_swarm_run(_mk_spec([
        {"op": "verifier_verdict", "verifier_id": "verifier_1", "snapshot_sha256": oracle.SNAPSHOT_SHA_V2, "verdict": "VERIFIED"},
    ]))
    _check(not res_stale_v["passed"] and res_stale_v["error_code"] == "ERR_STALE_VERDICT_SNAPSHOT", "stale verdict sha")

    res_fals = oracle.certify_hybrid_swarm_run(_mk_spec([
        {"op": "verifier_verdict", "verifier_id": "verifier_1", "snapshot_sha256": oracle.SNAPSHOT_SHA_V1, "verdict": "FALSIFIED"},
        {"op": "promote", "snapshot_sha256": oracle.SNAPSHOT_SHA_V1},
    ]))
    _check(not res_fals["passed"] and res_fals["error_code"] == "ERR_PROMOTION_BLOCKED_BY_FALSIFIED", "falsified blocks promote")

    res_stop_p = oracle.certify_hybrid_swarm_run(_mk_spec([
        {"op": "stop_plan"},
        {"op": "promote", "snapshot_sha256": oracle.SNAPSHOT_SHA_V1},
    ]))
    _check(not res_stop_p["passed"] and res_stop_p["error_code"] == "ERR_PROMOTE_ON_STOPPED_PLAN", "stopped blocks promote")

    res_mis_p = oracle.certify_hybrid_swarm_run(_mk_spec([
        {"op": "verifier_verdict", "verifier_id": "verifier_1", "snapshot_sha256": oracle.SNAPSHOT_SHA_V1, "verdict": "VERIFIED"},
        {"op": "verifier_verdict", "verifier_id": "verifier_2", "snapshot_sha256": oracle.SNAPSHOT_SHA_V1, "verdict": "VERIFIED"},
        {"op": "promote", "snapshot_sha256": oracle.SNAPSHOT_SHA_V2},
    ]))
    _check(not res_mis_p["passed"] and res_mis_p["error_code"] == "ERR_PROMOTE_SNAPSHOT_MISMATCH", "promote sha mismatch")

    res_inc_p = oracle.certify_hybrid_swarm_run(_mk_spec([
        {"op": "verifier_verdict", "verifier_id": "verifier_1", "snapshot_sha256": oracle.SNAPSHOT_SHA_V1, "verdict": "VERIFIED"},
        {"op": "promote", "snapshot_sha256": oracle.SNAPSHOT_SHA_V1},
    ]))
    _check(not res_inc_p["passed"] and res_inc_p["error_code"] == "ERR_INCOMPLETE_VERIFICATION", "incomplete verification")

    # OTP110-BUG-02: trailing event after promote must fail closed
    res_post_p = oracle.certify_hybrid_swarm_run(_mk_spec([
        {"op": "verifier_verdict", "verifier_id": "verifier_1", "snapshot_sha256": oracle.SNAPSHOT_SHA_V1, "verdict": "VERIFIED"},
        {"op": "verifier_verdict", "verifier_id": "verifier_2", "snapshot_sha256": oracle.SNAPSHOT_SHA_V1, "verdict": "VERIFIED"},
        {"op": "promote", "snapshot_sha256": oracle.SNAPSHOT_SHA_V1},
        {"op": "stop_plan"},
    ]))
    _check(not res_post_p["passed"] and res_post_p["error_code"] == "ERR_EVENT_AFTER_PROMOTE" and res_post_p["step_index"] == 3, "event after promote rejected")

    # Input validation errors
    _expect_err(lambda: oracle.certify_hybrid_swarm_run(_mk_spec([{"op": "stop_plan"}], window_ticks=0)), "ERR_NON_POSITIVE_WINDOW", "zero window")
    _expect_err(lambda: oracle.certify_hybrid_swarm_run(_mk_spec("not_list")), "ERR_INVALID_EVENTS", "events not list")
    _expect_err(lambda: oracle.certify_hybrid_swarm_run(_mk_spec([])), "ERR_INVALID_EVENTS", "events empty")
    _expect_err(lambda: oracle.certify_hybrid_swarm_run(_mk_spec(["not_dict"])), "ERR_INVALID_EVENT", "event not dict")
    _expect_err(lambda: oracle.certify_hybrid_swarm_run(_mk_spec([{"op": "unknown"}])), "ERR_INVALID_EVENT", "unknown op")
    _expect_err(lambda: oracle.certify_hybrid_swarm_run(_mk_spec([{"op": "verifier_crash", "verifier_id": "ghost", "reason": "abnormal"}])), "ERR_UNKNOWN_VERIFIER", "crash ghost")
    _expect_err(lambda: oracle.certify_hybrid_swarm_run(_mk_spec([{"op": "verifier_crash", "verifier_id": "verifier_1", "reason": "abnormal"}, {"op": "verifier_crash", "verifier_id": "verifier_1", "reason": "abnormal"}])), "ERR_VERIFIER_ALREADY_DEAD", "double crash")
    _expect_err(lambda: oracle.certify_hybrid_swarm_run(_mk_spec([{"op": "verifier_verdict", "verifier_id": "ghost", "snapshot_sha256": oracle.SNAPSHOT_SHA_V1, "verdict": "VERIFIED"}])), "ERR_UNKNOWN_VERIFIER", "verdict ghost")
    _expect_err(lambda: oracle.certify_hybrid_swarm_run(_mk_spec([{"op": "verifier_verdict", "verifier_id": "verifier_1", "snapshot_sha256": oracle.SNAPSHOT_SHA_V1, "verdict": "MAYBE"}])), "ERR_INVALID_VERDICT", "bad verdict")


# ---------------------------------------------------------------------------
# Test 7: Certificate Validator & Dynamic Must-Fail Counting
# ---------------------------------------------------------------------------

def test_certificate_validator() -> None:
    cert = oracle.build_erlang_otp_supervision_certificate()
    _check(oracle.validate_certificate(cert) is True, "fresh cert validates")
    _check(cert["novelty_tier"]["classical_semantics"] == "N0", "classical_semantics N0")
    _check(cert["novelty_tier"]["pure_q_hybrid_bridge"] == "N0", "pure_q_hybrid_bridge N0")
    _check(cert["summary"]["pillars_passed"] == 5, "5 pillars")
    _check(cert["summary"]["must_fail_controls_verified"] == 10, "10 controls")
    _check(cert["summary"]["floats_used"] == 0, "0 floats")

    # Novelty inflation & P4 new-control tampers rejected
    c_n1 = copy.deepcopy(cert)
    c_n1["novelty_tier"]["pure_q_hybrid_bridge"] = "N1"
    _expect_err(lambda: oracle.validate_certificate(_resign(c_n1)), "ERR_SCHEMA_STR", "novelty N1 rejected")

    c_p4_mk = copy.deepcopy(cert)
    c_p4_mk["pillars"]["p4_monitor_vs_link_fault_isolation"]["monitor_zone_b_isolation_on_killed"]["down_reason"] = "abnormal"
    _expect_err(lambda: oracle.validate_certificate(_resign(c_p4_mk)), "ERR_SCHEMA_STR", "p4 monitor killed reason tamper")

    c_p4_lk = copy.deepcopy(cert)
    c_p4_lk["pillars"]["p4_monitor_vs_link_fault_isolation"]["link_with_trap_exit_outside_killed"]["exit_reason"] = "kill"
    _expect_err(lambda: oracle.validate_certificate(_resign(c_p4_lk)), "ERR_SCHEMA_STR", "p4 link killed reason tamper")

    # Isolate all 3 clauses of _count_verified_must_fail_controls
    cnt = oracle._count_verified_must_fail_controls({
        "p": {
            "other_key": {"rejected": True},
            "must_fail_not_dict": "bad",
            "must_fail_not_rejected": {"rejected": False},
            "must_fail_ok": {"rejected": True},
        }
    })
    _check(cnt == 1, "must_fail counter clause isolation")

    # Float injection rejected
    c_flt = copy.deepcopy(cert)
    c_flt["summary"]["floats_used"] = 0.0
    _expect_err(lambda: oracle.validate_certificate(c_flt), "ERR_CERT_FLOAT", "float rejected")

    # SHA mismatch rejected
    c_sha = copy.deepcopy(cert)
    c_sha["canonical_sha256"] = oracle.SNAPSHOT_SHA_V1
    _expect_err(lambda: oracle.validate_certificate(c_sha), "ERR_CERT_SHA_MISMATCH", "sha mismatch")

    # P1 table length, non-list, duplicate cell
    c_p1_nl = copy.deepcopy(cert)
    c_p1_nl["pillars"]["p1_restart_policy_matrix"]["transition_table"] = tuple(
        c_p1_nl["pillars"]["p1_restart_policy_matrix"]["transition_table"]
    )
    _expect_err(lambda: oracle.validate_certificate(_resign(c_p1_nl)), "ERR_P1_TABLE", "p1 table tuple len 9 not list")

    c_p1_short = copy.deepcopy(cert)
    c_p1_short["pillars"]["p1_restart_policy_matrix"]["transition_table"].pop()
    _expect_err(lambda: oracle.validate_certificate(_resign(c_p1_short)), "ERR_P1_TABLE", "p1 table short")

    c_p1_dup = copy.deepcopy(cert)
    c_p1_dup["pillars"]["p1_restart_policy_matrix"]["transition_table"][1] = copy.deepcopy(
        c_p1_dup["pillars"]["p1_restart_policy_matrix"]["transition_table"][0]
    )
    _expect_err(lambda: oracle.validate_certificate(_resign(c_p1_dup)), "ERR_P1_DUP_CELL", "p1 dup cell")

    # P2 tampered v2 SHA and P5 tampered final_snapshot_sha256 rejected
    c_p2_eq = copy.deepcopy(cert)
    c_p2_eq["pillars"]["p2_restart_strategies_and_non_churn"]["snapshot_sha_v2"] = (
        c_p2_eq["pillars"]["p2_restart_strategies_and_non_churn"]["snapshot_sha_v1"]
    )
    _expect_err(lambda: oracle.validate_certificate(_resign(c_p2_eq)), "ERR_SCHEMA_STR", "p2 tampered v2 sha")

    c_p5_sha = copy.deepcopy(cert)
    c_p5_sha["pillars"]["p5_exo1200_aletheia_bridge"]["hybrid_clean_run"]["final_snapshot_sha256"] = oracle.SNAPSHOT_SHA_V1
    _expect_err(lambda: oracle.validate_certificate(_resign(c_p5_sha)), "ERR_SCHEMA_STR", "p5 tampered final sha")

    # Extra forged key at nested depth rejected
    c_extra = copy.deepcopy(cert)
    c_extra["pillars"]["p3_sliding_window_intensity_escalation"]["extra"] = 1
    _expect_err(lambda: oracle.validate_certificate(_resign(c_extra)), "ERR_SCHEMA_KEYS", "extra nested key")

    # Tampered summary count rejected
    c_sum = copy.deepcopy(cert)
    c_sum["summary"]["must_fail_controls_verified"] = 9
    _expect_err(lambda: oracle.validate_certificate(_resign(c_sum)), "ERR_SCHEMA_INT", "wrong dynamic count")


# ---------------------------------------------------------------------------
# Test 8: CLI Certifier (--json, --output, --check, strict JSON & drift)
# ---------------------------------------------------------------------------

def test_certifier_cli() -> None:
    cert = oracle.build_erlang_otp_supervision_certificate()
    pretty = certifier.format_pretty_json(cert)

    # Strict JSON loader rejects duplicates, floats, NaN, oversized ints, and invalid syntax
    _expect_err(lambda: certifier._load_strict_json('{"a": 1, "a": 2}'), "ERR_CERT_JSON", "dup json key")
    _expect_err(lambda: certifier._load_strict_json('{"a": 1.5}'), "ERR_CERT_FLOAT", "float json literal")
    _expect_err(lambda: certifier._load_strict_json('{"a": NaN}'), "ERR_CERT_FLOAT", "NaN json literal")
    _expect_err(lambda: certifier._load_strict_json('{bad json'), "ERR_CERT_JSON", "invalid json")
    _expect_err(lambda: certifier._load_strict_json(12345), "ERR_CERT_JSON", "non-str json")
    _check(certifier._load_strict_json('{"n": ' + ("9" * 1000) + "}")["n"] == int("9" * 1000), "1000-digit int accepted")
    _check(certifier._load_strict_json('{"n": -' + ("9" * 1000) + "}")["n"] == -int("9" * 1000), "-1000-digit int accepted")
    _expect_err(lambda: certifier._load_strict_json('{"n": ' + ("9" * 1001) + "}"), "ERR_CERT_JSON", "1001-digit int rejected")
    _expect_err(lambda: certifier._load_strict_json('{"n": ' + ("9" * 5000) + "}"), "ERR_CERT_JSON", "5000-digit int rejected")

    with tempfile.TemporaryDirectory() as tmpdir:
        out_path = os.path.join(tmpdir, "cert.json")

        # Default mode (prints JSON to stdout)
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = certifier.main([])
        _check(rc == 0 and buf.getvalue() == pretty, "default mode prints exact pretty JSON")

        # --output without --json writes file silently
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = certifier.main(["--output", out_path])
        _check(rc == 0 and buf.getvalue() == "", "--output alone is silent")
        with open(out_path, "r", encoding="utf-8") as fh:
            _check(fh.read() == pretty, "written file matches pretty JSON")

        # --output WITH --json writes file and echoes JSON
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = certifier.main(["--output", out_path, "--json"])
        _check(rc == 0 and buf.getvalue() == pretty, "--output --json echoes pretty JSON")

        # --check summary output
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = certifier.main(["--check", out_path])
        _check(
            rc == 0 and f"OK AUDIT-110 canonical_sha256={cert['canonical_sha256']} pillars=5 controls=10\n" == buf.getvalue(),
            "--check summary format",
        )

        # --check --json output
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = certifier.main(["--check", out_path, "--json"])
        _check(rc == 0 and buf.getvalue() == pretty, "--check --json echoes pretty JSON")

        # Byte drift (valid certificate JSON with non-canonical formatting) rejected
        drift_path = os.path.join(tmpdir, "drift.json")
        with open(drift_path, "w", encoding="utf-8", newline="\n") as fh:
            fh.write(json.dumps(cert, sort_keys=True) + "\n")
        _expect_err(lambda: certifier.check_certificate_file(drift_path), "ERR_CERT_DRIFT", "byte drift rejected")

        # CRLF, invalid UTF-8, missing file, and 5000-digit int rejected with typed errors and clean CLI exit 2
        crlf_path = os.path.join(tmpdir, "crlf.json")
        with open(crlf_path, "wb") as fh:
            fh.write(pretty.replace("\n", "\r\n").encode("utf-8"))
        _expect_err(lambda: certifier.check_certificate_file(crlf_path), "ERR_CERT_CRLF", "CRLF rejected")

        bad_utf8_path = os.path.join(tmpdir, "bad_utf8.json")
        with open(bad_utf8_path, "wb") as fh:
            fh.write(b"\xff\xfe\x00\x01")
        _expect_err(lambda: certifier.check_certificate_file(bad_utf8_path), "ERR_CERT_READ", "invalid UTF-8 rejected")
        _expect_err(lambda: certifier.check_certificate_file(os.path.join(tmpdir, "missing.json")), "ERR_CERT_READ", "missing file rejected")

        huge_path = os.path.join(tmpdir, "huge.json")
        with open(huge_path, "w", encoding="utf-8", newline="\n") as fh:
            fh.write('{"n": ' + ("9" * 5000) + "}\n")
        _expect_err(lambda: certifier.check_certificate_file(huge_path), "ERR_CERT_JSON", "5000-digit file rejected")

        err_buf = io.StringIO()
        orig_stderr = sys.stderr
        try:
            sys.stderr = err_buf
            rc_err = certifier.main(["--check", crlf_path])
            _check(
                rc_err == 2 and "ERR ERR_CERT_CRLF" in err_buf.getvalue() and "Traceback" not in err_buf.getvalue(),
                "CLI --check CRLF exits 2 cleanly",
            )
            err_buf2 = io.StringIO()
            sys.stderr = err_buf2
            rc_io = certifier.main(["--output", tmpdir])
            _check(
                rc_io == 2 and "ERR ERR_CERT_IO" in err_buf2.getvalue() and "Traceback" not in err_buf2.getvalue(),
                "CLI --output dir exits 2 cleanly",
            )
        finally:
            sys.stderr = orig_stderr


def main() -> int:
    tests = [
        test_primitives_and_helpers,
        test_pillar_1,
        test_pillar_2,
        test_pillar_3,
        test_pillar_4,
        test_pillar_5,
        test_certificate_validator,
        test_certifier_cli,
    ]
    for fn in tests:
        fn()
    sys.stdout.write(f"PASS AUDIT-110 R5_TESTS={len(tests)}/{len(tests)}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
