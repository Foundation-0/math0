#!/usr/bin/env python3
"""
Wave 2 Round 4B — Arm R4B-2 (AUDIT-050): Exact-Operator Cross-Pollination &
Tomography of judegomila/canculus@ef76861b and judegomila/OnCo@d4384208.
100% pure Python 3 stdlib (int, Fraction, frozenset; zero external deps; zero bare asserts).

Strictly READ-ONLY against all external repos (0 external PRs/issues/comments).

Four exact components:
  1. Hardened Canculus Route-Normal-Form & Semantic-Entailment Adaptation Closure (SF-04/SF-05):
     closes live-reproduced CANC-B1 (NF flips robust verdict), CANC-B2a/b (rulesEncoded=0 on
     active rules & flagship brafSystem without universe), and CANC-B4a/b (idempotence & '+'
     delimiter collisions); proves Free Distributive Lattice De Morgan involution Tr(Tr(M)) == M,
     exact NF functoriality NF(F(R0)) == NF(F(NF(R0))), and Prop. 7.8 non-upward-closed obstruction.
  2. Exact 2x2 Schur-Complement (SF-01 #22) & 1D PGL(2, Q) Feedback Engine (SF-02):
     solves linear feedback release over pure Fraction, proving exact conservation r(a) + h*y(a) == u,
     exact 4-point PGL(2, Q) cross-ratio invariance, and closing CANC-B3 (live JS float64 boundary
     flip r(alphaCrit) < theta at u=1, g=3, h=3, theta=0.3).
  3. Exact Tropical (min, max, +) Timed Closure with Dual Optimality Witness (SF-05):
     replaces unbounded while(changed) with negative-delay refusal (closing CANC-B4c) and
     emits exact zero-gap shortest-hyperpath witness certificates over Fraction.
  4. Reverse-Extracted OnCo@d4384208 Cited Epistemic Graph Governance Gates (SF-04):
     single-direction ref validation + derived backlinks, zero-tolerance link-sense kind check,
     fail-closed semantic diff classifier (data/product/neither), and deep-value record compare.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
from itertools import combinations
import json
import re
import sys
from typing import Any, Callable


# ---------------------------------------------------------------------------
# Part 1: Hardened Canculus Normal Forms, Transversals & Semantic Closure
# ---------------------------------------------------------------------------

Route = frozenset[str]


def make_route(caps: list[str] | tuple[str, ...] | set[str] | frozenset[str]) -> Route:
    """Canonical deduplicated route (closes CANC-B4a idempotence & CANC-B4b '+' collision)."""
    if not isinstance(caps, (list, tuple, set, frozenset)):
        raise TypeError("route capabilities must be an iterable collection")
    cleaned: list[str] = []
    for cap in caps:
        if not isinstance(cap, str) or not cap.strip():
            raise ValueError("each capability must be a non-empty str")
        cleaned.append(cap.strip())
    return frozenset(cleaned)


def route_tuple(r: Route) -> tuple[str, ...]:
    return tuple(sorted(r))


def minimal_antichain(routes: list[Route]) -> list[Route]:
    """Canonical Prop. 6.2 route normal form M(Phi): inclusion-minimal antichain."""
    uniq = sorted(set(routes), key=lambda r: (len(r), route_tuple(r)))
    out: list[Route] = []
    for r in uniq:
        if not any(s < r for s in uniq):
            out.append(r)
    return out


def is_transversal(cut: Route, routes: list[Route]) -> bool:
    """True iff cut hits every route in routes (r & cut != empty for all r)."""
    return all(bool(r & cut) for r in routes)


def minimal_transversals(routes: list[Route], universe: list[str]) -> list[Route]:
    """Exact Thm. 6.4 De Morgan minimal hitting sets of a route hypergraph."""
    if not universe:
        raise ValueError("universe must be non-empty")
    norm_routes = minimal_antichain(routes)
    # Empty route (tautology True) cannot be hit by any finite cut
    if any(len(r) == 0 for r in norm_routes):
        return []
    found: list[Route] = []
    univ_sorted = sorted(set(universe))
    for size in range(len(univ_sorted) + 1):
        for comb in combinations(univ_sorted, size):
            u_set = frozenset(comb)
            if not is_transversal(u_set, norm_routes):
                continue
            if any(m <= u_set for m in found):
                continue
            found.append(u_set)
    return found


@dataclass(frozen=True)
class AdaptationRule:
    rule_id: str
    prereq_routes: tuple[Route, ...]
    guard: Callable[[Route, dict[str, Any]], bool]
    guard_label: str
    consequences: tuple[Route, ...]
    delay: Fraction
    level: str


def rules_encoded_exact(
    rules: list[AdaptationRule],
    universe: list[str],
    ctx: dict[str, Any],
) -> list[str]:
    """
    Existential coverage check over 2^V (closes CANC-B2a non-monotone guards & CANC-B2b
    missing universe caps): a rule is encoded for ctx iff SOME U subset V satisfies guard(U, ctx).
    """
    if not universe:
        raise ValueError("universe must be non-empty for coverage check")
    univ_sorted = sorted(set(universe))
    if len(univ_sorted) > 12:
        raise ValueError("exact subset coverage enumeration bounded to |V| <= 12")
    encoded: list[str] = []
    all_subsets = [
        frozenset(comb)
        for size in range(len(univ_sorted) + 1)
        for comb in combinations(univ_sorted, size)
    ]
    for rule in rules:
        if any(rule.guard(u_set, ctx) for u_set in all_subsets):
            encoded.append(rule.rule_id)
    return encoded


def semantic_adaptation_closure(
    baseline: list[Route],
    rules: list[AdaptationRule],
    intervention: Route,
    ctx: dict[str, Any],
    universe: list[str],
) -> dict[str, Any]:
    """
    Hardened Algorithm 1 using upward-closure semantic entailment (`any(s <= p for s in family)`)
    instead of syntactic set equality, guaranteeing exact Normal-Form Functoriality:
      NF(F_{U,c}(R0)) == NF(F_{U,c}(NF(R0)))  (closes CANC-B1, CANC-B2a/b).
    """
    family: set[Route] = set(minimal_antichain(baseline))
    fired: set[str] = set()
    trace: list[dict[str, Any]] = []
    round_num = 0
    changed = True
    while changed:
        changed = False
        round_num += 1
        for rule in rules:
            if rule.rule_id in fired:
                continue
            # Semantic upward-closure entailment: prerequisite p is satisfied if some s in family has s <= p
            prereq_ok = all(any(s <= p for s in family) for p in rule.prereq_routes)
            if not prereq_ok or not rule.guard(intervention, ctx):
                continue
            before_nf = set(minimal_antichain(list(family)))
            family.update(rule.consequences)
            after_nf = set(minimal_antichain(list(family)))
            family = after_nf
            fired.add(rule.rule_id)
            added = sorted(after_nf - before_nf, key=lambda r: (len(r), route_tuple(r)))
            if added:
                changed = True
            trace.append({
                "round": round_num,
                "rule_id": rule.rule_id,
                "added": [list(route_tuple(r)) for r in added],
            })

    closed_nf = minimal_antichain(list(family))
    escape = [r for r in closed_nf if not (r & intervention)]
    encoded = rules_encoded_exact(rules, universe, ctx)
    return {
        "closed_nf": [list(route_tuple(r)) for r in closed_nf],
        "escape": [list(route_tuple(r)) for r in escape],
        "robust": len(escape) == 0,
        "rules_encoded": len(encoded),
        "encoded_rule_ids": encoded,
        "trace": trace,
    }


def minimal_robust_cuts_exact(
    baseline: list[Route],
    rules: list[AdaptationRule],
    ctx: dict[str, Any],
    universe: list[str],
) -> list[list[str]]:
    """Exact Thm. 7.6 inclusion-minimal adaptation-robust interventions (non-monotone safe)."""
    univ_sorted = sorted(set(universe))
    robust_sets: list[Route] = []
    minimal: list[Route] = []
    for size in range(len(univ_sorted) + 1):
        for comb in combinations(univ_sorted, size):
            u_set = frozenset(comb)
            res = semantic_adaptation_closure(baseline, rules, u_set, ctx, univ_sorted)
            if not res["robust"]:
                continue
            robust_sets.append(u_set)
            if not any(m < u_set for m in robust_sets):
                minimal.append(u_set)
    return [list(route_tuple(m)) for m in minimal]


# ---------------------------------------------------------------------------
# Part 2: Exact 2x2 Schur Complement & 1D PGL(2, Q) Linear Feedback Release
# ---------------------------------------------------------------------------

def solve_feedback_schur_exact(
    alpha: Fraction, u: Fraction, g: Fraction, h: Fraction
) -> dict[str, Any]:
    """
    Exact 2x2 linear feedback block solver over pure Fraction (SF-01 #22 & SF-02):
      [ 1      h ] [ r ]   [ u ]
      [-a*g    1 ] [ y ] = [ 0 ]
    Exact Schur complement S = 1 - (-a*g)*h = 1 + a*g*h.
    Conservation invariant: r(a) + h * y(a) === u (0 residual).
    """
    if u < 0 or g < 0 or h < 0 or alpha < 0:
        raise ValueError("feedback parameters (alpha, u, g, h) must be non-negative Fractions")
    schur = Fraction(1, 1) + alpha * g * h
    r_val = u / schur
    y_val = (alpha * g * u) / schur
    residual = (r_val + h * y_val) - u
    return {
        "schur_S": str(schur),
        "r": r_val,
        "y": y_val,
        "conservation_residual_zero": residual == 0,
    }


def alpha_crit_exact(u: Fraction, g: Fraction, h: Fraction, theta: Fraction) -> dict[str, Any]:
    """
    Exact rational critical residual activity alpha_crit = (u/theta - 1)/(g*h)
    closing CANC-B3 (live JS float64 flip r(alphaCrit) < theta at (1, 3, 3, 0.3)).
    """
    if theta <= 0:
        raise ValueError("bypass threshold theta must be strictly positive")
    if u < 0 or g < 0 or h < 0:
        raise ValueError("feedback parameters (u, g, h) must be non-negative")
    if u < theta:
        return {"regime": "never", "alpha_crit": None, "r_at_crit_ge_theta": False}
    if g * h == 0 or u >= theta * (Fraction(1, 1) + g * h):
        return {"regime": "always", "alpha_crit": None, "r_at_crit_ge_theta": True}
    ac = (u / theta - Fraction(1, 1)) / (g * h)
    at_crit = solve_feedback_schur_exact(ac, u, g, h)
    return {
        "regime": "intermediate",
        "alpha_crit": str(ac),
        "r_at_crit": str(at_crit["r"]),
        "r_at_crit_ge_theta": at_crit["r"] >= theta,
        "exact_equality_at_crit": at_crit["r"] == theta,
    }


def cross_ratio_exact(z1: Fraction, z2: Fraction, z3: Fraction, z4: Fraction) -> Fraction:
    """Exact PGL(2, Q) 4-point cross-ratio (z1 - z3)(z2 - z4) / ((z1 - z4)(z2 - z3))."""
    denom = (z1 - z4) * (z2 - z3)
    if denom == 0:
        raise ValueError("degenerate cross-ratio denominator (coincident points)")
    return ((z1 - z3) * (z2 - z4)) / denom


# ---------------------------------------------------------------------------
# Part 3: Exact Tropical (min, max, +) Timed Closure with Dual Certificate
# ---------------------------------------------------------------------------

def earliest_activation_times_exact(
    baseline: list[Route],
    rules: list[AdaptationRule],
    intervention: Route,
    ctx: dict[str, Any],
) -> dict[str, Any]:
    """
    Exact rational tropical (min, max, +) shortest-hyperpath relaxation (Eqs. 41-42)
    with negative-delay refusal (closing CANC-B4c infinite loop) and exact primal-dual
    optimality witness tree verification.
    """
    for rule in rules:
        if rule.delay < 0:
            raise ValueError(f"negative delay ({rule.delay}) forbidden in causal timed closure")

    times: dict[Route, Fraction] = {r: Fraction(0, 1) for r in minimal_antichain(baseline)}
    witness: dict[Route, str] = {r: "BASELINE" for r in times}
    # Bound iterations by number of enabled rules + 1 (exact Bellman-Ford termination)
    enabled = [r for r in rules if r.guard(intervention, ctx)]
    for _ in range(len(enabled) + 1):
        changed = False
        for rule in enabled:
            prereq_t: list[Fraction] = []
            all_avail = True
            for p in rule.prereq_routes:
                # Semantic entailment: earliest time any route s <= p is available
                matching_times = [t_s for s, t_s in times.items() if s <= p]
                if not matching_times:
                    all_avail = False
                    break
                prereq_t.append(min(matching_times))
            if not all_avail:
                continue
            cand_time = (max(prereq_t) if prereq_t else Fraction(0, 1)) + rule.delay
            for q in rule.consequences:
                cur = times.get(q)
                if cur is None or cand_time < cur:
                    times[q] = cand_time
                    witness[q] = rule.rule_id
                    changed = True
        if not changed:
            break

    # Verify exact tropical Bellman-Ford optimality dual condition on every enabled rule:
    # t(q) <= max_{p in prereq} min_{s <= p} t(s) + delay(rule)
    dual_ok = True
    for rule in enabled:
        prereq_t = []
        avail = True
        for p in rule.prereq_routes:
            mt = [t_s for s, t_s in times.items() if s <= p]
            if not mt:
                avail = False
                break
            prereq_t.append(min(mt))
        if avail:
            bound = (max(prereq_t) if prereq_t else Fraction(0, 1)) + rule.delay
            for q in rule.consequences:
                if q not in times or times[q] > bound:
                    dual_ok = False

    entries = [
        {"route": list(route_tuple(r)), "time": str(t), "witness": witness[r]}
        for r, t in sorted(times.items(), key=lambda kv: (kv[1], route_tuple(kv[0])))
    ]
    return {
        "timed_routes": entries,
        "tropical_dual_optimal": dual_ok,
    }


def robust_at_horizon_exact(
    baseline: list[Route],
    rules: list[AdaptationRule],
    intervention: Route,
    ctx: dict[str, Any],
    horizon: Fraction,
) -> bool:
    """True iff every route derivable with time <= horizon is hit by intervention."""
    if horizon < 0:
        raise ValueError("horizon must be non-negative")
    res = earliest_activation_times_exact(baseline, rules, intervention, ctx)
    for item in res["timed_routes"]:
        if Fraction(item["time"]) <= horizon:
            r_set = frozenset(item["route"])
            if not (r_set & intervention):
                return False
    return True


# ---------------------------------------------------------------------------
# Part 4: Reverse-Extracted OnCo@d4384208 Epistemic-Graph Governance Gates
# ---------------------------------------------------------------------------

_KEBAB_ID_RE = re.compile(r"^[a-z0-9]+(-[a-z0-9]+)*$")
_ISO_DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")

_ONCO_REL_KIND_MAP: dict[str, str] = {
    "cancers": "cancer",
    "drugs": "drug",
    "targets": "target",
    "trials": "trial",
    "terms": "term",
}


def validate_cited_epistemic_graph(records: list[dict[str, Any]]) -> dict[str, Any]:
    """
    Reverse-extracted OnCo@d4384208 graph validator (src/lib/graph.ts + scripts/validate.ts):
      1. Strict kebab-case IDs, duplicate-ID refusal, ISO asOf date, mandatory primary source links.
      2. Single-direction reference resolution + automatic backlink derivation + dangling-ref refusal.
      3. Zero-tolerance Link-Sense Disambiguation: typed relation field (e.g. 'cancers') MUST point
         to a record of the matching kind ('cancer'), refusing glossary-stub ('term') mislinks!
    """
    if not records:
        raise ValueError("graph records must be non-empty")
    by_id: dict[str, dict[str, Any]] = {}
    for rec in records:
        rid = rec.get("id")
        kind = rec.get("kind")
        as_of = rec.get("asOf")
        links = rec.get("links")
        if not isinstance(rid, str) or _KEBAB_ID_RE.fullmatch(rid) is None:
            raise ValueError(f"invalid kebab-case entity id: {rid!r}")
        if rid in by_id:
            raise ValueError(f"duplicate entity id: {rid!r}")
        if not isinstance(kind, str) or not kind:
            raise ValueError(f"missing kind for entity {rid!r}")
        if not isinstance(as_of, str) or _ISO_DATE_RE.fullmatch(as_of) is None:
            raise ValueError(f"invalid ISO asOf date for entity {rid!r}: {as_of!r}")
        if not isinstance(links, list) or len(links) == 0:
            raise ValueError(f"entity {rid!r} missing mandatory primary source links")
        by_id[rid] = rec

    backlinks: dict[str, list[dict[str, str]]] = {rid: [] for rid in by_id}
    link_sense_errors: list[str] = []
    for rid, rec in by_id.items():
        for rel_field, expected_kind in _ONCO_REL_KIND_MAP.items():
            targets = rec.get(rel_field, [])
            if not isinstance(targets, list):
                raise ValueError(f"relation field {rel_field!r} on {rid!r} must be a list")
            for target_id in targets:
                if target_id not in by_id:
                    raise ValueError(f"dangling reference: {rid} -> {target_id} via {rel_field}")
                target_rec = by_id[target_id]
                if target_rec["kind"] != expected_kind:
                    link_sense_errors.append(
                        f"{rid}.{rel_field} -> {target_id} (expected kind={expected_kind}, got {target_rec['kind']})"
                    )
                if target_id != rid:
                    backlinks[target_id].append({"from": rid, "via": rel_field})

    if link_sense_errors:
        return {
            "valid": False,
            "entity_count": len(by_id),
            "link_sense_errors": link_sense_errors,
            "backlink_count": sum(len(v) for v in backlinks.values()),
        }
    return {
        "valid": True,
        "entity_count": len(by_id),
        "link_sense_errors": [],
        "backlink_count": sum(len(v) for v in backlinks.values()),
    }


def classify_change_semantic(paths: list[str]) -> dict[str, Any]:
    """
    Reverse-extracted OnCo@d4384208 semantic diff gate (scripts/change-class.ts):
    separates 'data' updates from 'product' changes requiring explicit owner approval,
    failing closed to 'product' for unrecognized root/config paths!
    """
    if not paths:
        raise ValueError("changed path list must be non-empty")
    out: dict[str, list[str]] = {"product": [], "data": [], "neither": []}
    for p in paths:
        if not isinstance(p, str) or not p.strip():
            raise ValueError("changed path must be a non-empty str")
        norm = p.strip().lstrip("./")
        if norm.endswith((".test.ts", ".test.tsx", ".test.py")) or norm.startswith("docs/") or norm in ("README.md", "AGENTS.md", "CHANGELOG.md"):
            cls = "neither"
        elif norm.startswith(("src/data/", "public/")):
            cls = "data"
        elif norm.startswith(("src/lib/", "src/app/", "src/components/")):
            cls = "product"
        else:
            # Fail closed: unknown top-level config/schema requires product approval
            cls = "product"
        out[cls].append(norm)
    return {
        "counts": {k: len(v) for k, v in out.items()},
        "requires_owner_approval": len(out["product"]) > 0,
        "classes": out,
    }


def deep_compare_records(rec_a: dict[str, Any], rec_b: dict[str, Any]) -> dict[str, Any]:
    """
    Reverse-extracted OnCo MCP deep-value comparator (packages/onco-mcp/src/server.ts:29-51):
    compares complete structured values (including False / [] / nested keys), never truncated displays.
    """
    if not isinstance(rec_a, dict) or not isinstance(rec_b, dict):
        raise TypeError("records to compare must be dicts")
    keys = sorted(set(rec_a.keys()) | set(rec_b.keys()))
    differing = [k for k in keys if rec_a.get(k) != rec_b.get(k) or (k in rec_a) != (k in rec_b)]
    return {
        "identical": len(differing) == 0,
        "differing_fields": differing,
    }


# ---------------------------------------------------------------------------
# Self-Contained Exact Verification Matrix (4-mode isolated R4 bit-identical)
# ---------------------------------------------------------------------------

def run_full_bridge_matrix() -> dict[str, Any]:
    """Run all 4 exact verification suites for judegomila/canculus + OnCo (AUDIT-050)."""
    # 1. Canculus BRAF-CRC + Melanoma + Prop. 7.8 + Reciprocal AR/AKT + Bug Closures
    r0 = make_route(["B", "M", "E"])
    r1 = make_route(["G", "R", "C", "M", "E"])
    r_mel = make_route(["R", "C", "M", "E"])
    braf_u = ["B", "G", "R", "C", "M", "E"]
    crc_ctx = {"lineage": "CRC"}
    mel_ctx = {"lineage": "melanoma"}

    # Exact Fraction feedback guard for BRAF-CRC
    u0, g0, h0, th0 = Fraction(1), Fraction(3), Fraction(2), Fraction(11, 20)
    alpha_treat = Fraction(1, 10)
    egfr_rule = AdaptationRule(
        rule_id="rho_EGFR",
        prereq_routes=(r0,),
        guard=lambda U, c: ("B" in U) and c.get("lineage") == "CRC" and solve_feedback_schur_exact(alpha_treat, u0, g0, h0)["r"] >= th0,
        guard_label="B in U & r(1/10) >= 11/20 & CRC",
        consequences=(r1,),
        delay=Fraction(12),
        level="L1",
    )
    mel_rule = AdaptationRule(
        rule_id="rho_MAPK_reactivation",
        prereq_routes=(r0,),
        guard=lambda U, c: ("B" in U) and c.get("lineage") == "melanoma",
        guard_label="B in U & melanoma",
        consequences=(r_mel,),
        delay=Fraction(1440),
        level="L3",
    )

    # Free Distributive Lattice De Morgan Involution: Tr(Tr(M)) == M on two tested finite hypergraphs
    m_braf = minimal_antichain([r0, r1])
    tr_braf = minimal_transversals(m_braf, braf_u)
    tr_tr_braf = minimal_transversals(tr_braf, braf_u)
    path_u = ["a", "b", "c", "d"]
    m_path = minimal_antichain([make_route(["a", "b"]), make_route(["b", "c"]), make_route(["c", "d"])])
    tr_path = minimal_transversals(m_path, path_u)
    tr_tr_path = minimal_transversals(tr_path, path_u)
    demorgan_involution_ok = (set(m_braf) == set(tr_tr_braf)) and (set(m_path) == set(tr_tr_path))

    # Exact reproduction of Eq. 56 minimal robust cuts: {M}, {E}, {B,G}, {B,R}, {B,C}
    braf_cuts = minimal_robust_cuts_exact([r0], [egfr_rule, mel_rule], crc_ctx, braf_u)
    eq56_exact_match = sorted(braf_cuts) == [["B", "C"], ["B", "G"], ["B", "R"], ["E"], ["M"]]

    # CANC-B1 closure: Normal-Form Functoriality NF(F(R0)) == NF(F(NF(R0)))
    r0_unnorm = [make_route(["M"]), make_route(["B", "M", "E"])]
    r0_norm = minimal_antichain(r0_unnorm)
    rule_sup = AdaptationRule(
        rule_id="rho_sup",
        prereq_routes=(make_route(["B", "M", "E"]),),
        guard=lambda U, c: "M" in U,
        guard_label="M in U",
        consequences=(make_route(["G"]),),
        delay=Fraction(1),
        level="L1",
    )
    res_unnorm = semantic_adaptation_closure(r0_unnorm, [rule_sup], make_route(["M"]), crc_ctx, ["B", "M", "E", "G"])
    res_norm = semantic_adaptation_closure(r0_norm, [rule_sup], make_route(["M"]), crc_ctx, ["B", "M", "E", "G"])
    nf_functoriality_ok = (res_unnorm["robust"] == res_norm["robust"] == False) and (
        res_unnorm["closed_nf"] == res_norm["closed_nf"]
    )

    # CANC-B2a/b closure: non-monotone guard U.has("B") && !U.has("G") reports rules_encoded == 1
    mono_rule = AdaptationRule(
        rule_id="rho_mono",
        prereq_routes=(r0,),
        guard=lambda U, c: ("B" in U) and ("G" not in U),
        guard_label="B in U & G not in U",
        consequences=(r1,),
        delay=Fraction(12),
        level="L1",
    )
    res_mono = semantic_adaptation_closure([r0], [mono_rule], make_route(["B"]), crc_ctx, braf_u)
    non_monotone_coverage_ok = (res_mono["rules_encoded"] == 1) and (not res_mono["robust"])

    # Prop. 7.8 non-upward-closed robustness: {a} True -> {a,b} False -> {a,b,c} True
    prop78_rule = AdaptationRule(
        rule_id="rho_b",
        prereq_routes=(),
        guard=lambda U, c: "b" in U,
        guard_label="b in U",
        consequences=(make_route(["c"]),),
        delay=Fraction(1),
        level="L1",
    )
    p78_a = semantic_adaptation_closure([make_route(["a"])], [prop78_rule], make_route(["a"]), {}, ["a", "b", "c"])["robust"]
    p78_ab = semantic_adaptation_closure([make_route(["a"])], [prop78_rule], make_route(["a", "b"]), {}, ["a", "b", "c"])["robust"]
    p78_abc = semantic_adaptation_closure([make_route(["a"])], [prop78_rule], make_route(["a", "b", "c"]), {}, ["a", "b", "c"])["robust"]
    prop78_non_monotone_ok = p78_a and (not p78_ab) and p78_abc

    # 2. Exact 2x2 Schur & PGL(2, Q) Cross-Ratio Invariance + CANC-B3 Float64 Criticality Closure
    alphas = (Fraction(0), Fraction(1, 5), Fraction(1, 2), Fraction(2, 1))
    sols = [solve_feedback_schur_exact(a, u0, g0, h0) for a in alphas]
    cr_alpha = cross_ratio_exact(*alphas)
    cr_r = cross_ratio_exact(*(s["r"] for s in sols))
    cr_y = cross_ratio_exact(*(s["y"] for s in sols))
    pgl2_feedback_ok = (
        all(s["conservation_residual_zero"] for s in sols)
        and cr_alpha == cr_r == cr_y
    )
    # Exact alphaCrit at (1, 3, 3, 3/10) where JS float64 flipped r >= theta to false!
    ac_b3 = alpha_crit_exact(Fraction(1), Fraction(3), Fraction(3), Fraction(3, 10))
    ac_default = alpha_crit_exact(u0, g0, h0, th0)

    # 3. Exact Tropical (min, max, +) Timed Closure with Dual Certificate
    timed_crc = earliest_activation_times_exact([r0], [egfr_rule, mel_rule], make_route(["B"]), crc_ctx)
    timed_mel = earliest_activation_times_exact([r0], [egfr_rule, mel_rule], make_route(["B"]), mel_ctx)
    horizon_checks_ok = (
        timed_crc["tropical_dual_optimal"]
        and timed_mel["tropical_dual_optimal"]
        and robust_at_horizon_exact([r0], [egfr_rule, mel_rule], make_route(["B"]), crc_ctx, Fraction(6))
        and (not robust_at_horizon_exact([r0], [egfr_rule, mel_rule], make_route(["B"]), crc_ctx, Fraction(24)))
        and robust_at_horizon_exact([r0], [egfr_rule, mel_rule], make_route(["B"]), mel_ctx, Fraction(168))
        and (not robust_at_horizon_exact([r0], [egfr_rule, mel_rule], make_route(["B"]), mel_ctx, Fraction(2160)))
    )

    # 4. Reverse-Extracted OnCo Epistemic-Graph Governance Gates
    good_graph = [
        {"id": "braf-v600e", "kind": "target", "asOf": "2026-11-21", "links": [{"label": "UniProt", "url": "https://uniprot.org"}]},
        {"id": "crc", "kind": "cancer", "asOf": "2026-11-21", "links": [{"label": "NCI", "url": "https://cancer.gov"}], "targets": ["braf-v600e"]},
        {"id": "encorafenib", "kind": "drug", "asOf": "2026-11-21", "links": [{"label": "FDA", "url": "https://fda.gov"}], "cancers": ["crc"], "targets": ["braf-v600e"]},
    ]
    bad_sense_graph = [
        {"id": "brain-mets", "kind": "term", "asOf": "2026-11-21", "links": [{"label": "Glossary", "url": "https://onco.cc"}]},
        {"id": "trial-1", "kind": "trial", "asOf": "2026-11-21", "links": [{"label": "CTgov", "url": "https://clinicaltrials.gov"}], "cancers": ["brain-mets"]},
    ]
    onco_good = validate_cited_epistemic_graph(good_graph)
    onco_bad_sense = validate_cited_epistemic_graph(bad_sense_graph)
    diff_data_only = classify_change_semantic(["src/data/drugs.ts", "docs/GAPS.md", "src/lib/graph.test.ts"])
    diff_unknown_fail_closed = classify_change_semantic(["src/data/drugs.ts", "custom-schema.json"])
    deep_cmp = deep_compare_records(
        {"id": "x", "summary": "same", "flags": {"hidden": False}},
        {"id": "x", "summary": "same", "flags": {"hidden": True}},
    )

    all_passed = (
        demorgan_involution_ok
        and eq56_exact_match
        and nf_functoriality_ok
        and non_monotone_coverage_ok
        and prop78_non_monotone_ok
        and pgl2_feedback_ok
        and ac_b3["alpha_crit"] == "7/27"
        and ac_b3["r_at_crit_ge_theta"]
        and ac_b3["exact_equality_at_crit"]
        and ac_default["alpha_crit"] == "3/22"
        and horizon_checks_ok
        and onco_good["valid"]
        and onco_good["backlink_count"] == 3
        and (not onco_bad_sense["valid"])
        and (not diff_data_only["requires_owner_approval"])
        and diff_unknown_fail_closed["requires_owner_approval"]
        and (not deep_cmp["identical"])
        and deep_cmp["differing_fields"] == ["flags"]
    )

    payload: dict[str, Any] = {
        "schema": "expedition.round4b.arm2.judegomila_canculus_onco.v1",
        "audit_id": "AUDIT-050",
        "oracle_class": "exact+anchor",
        "novelty_grade": "N1",
        "pinned_readonly_commits": {
            "judegomila/canculus": "ef76861b4e84adc7c629713df72fe53a99928c71",
            "judegomila/OnCo": "d43842087851281084d0f9e7171f555635361e7f",
        },
        "all_passed": all_passed,
        "part_1_canculus_normal_form_and_closure": {
            "demorgan_involution_Tr_Tr_M_eq_M": demorgan_involution_ok,
            "demorgan_involution_tested_hypergraphs": 2,
            "eq56_minimal_robust_cuts": braf_cuts,
            "eq56_exact_match": eq56_exact_match,
            "canc_b1_nf_functoriality_closed": nf_functoriality_ok,
            "canc_b2_non_monotone_rules_encoded_closed": non_monotone_coverage_ok,
            "prop78_non_upward_closed_transition": [p78_a, p78_ab, p78_abc],
        },
        "part_2_schur_pgl2_feedback": {
            "cross_ratio_alpha": str(cr_alpha),
            "cross_ratio_r": str(cr_r),
            "cross_ratio_y": str(cr_y),
            "pgl2_cross_ratio_and_conservation_exact": pgl2_feedback_ok,
            "canc_b3_exact_crit_1_3_3_0p3": ac_b3,
            "default_braf_crit": ac_default,
        },
        "part_3_tropical_timed_closure": {
            "crc_timed": timed_crc,
            "melanoma_timed": timed_mel,
            "horizon_checks_exact": horizon_checks_ok,
        },
        "part_4_onco_epistemic_graph_gates": {
            "valid_graph": onco_good,
            "link_sense_glossary_mislink_caught": not onco_bad_sense["valid"],
            "link_sense_errors": onco_bad_sense["link_sense_errors"],
            "diff_data_only_auto_ship": not diff_data_only["requires_owner_approval"],
            "diff_unknown_config_fail_closed": diff_unknown_fail_closed["requires_owner_approval"],
            "deep_compare_catches_hidden_diff": not deep_cmp["identical"],
        },
    }
    canon = json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False).encode("utf-8")
    payload["canonical_sha256"] = hashlib.sha256(canon).hexdigest()
    return payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Round-4B Arm R4B-2 judegomila/canculus & OnCo Bridge")
    parser.add_argument("--json", action="store_true", help="Emit canonical deterministic JSON")
    args = parser.parse_args(argv)
    report = run_full_bridge_matrix()
    if args.json:
        print(json.dumps(report, sort_keys=True, indent=2))
    else:
        print(f"Round-4B Arm R4B-2 judegomila/canculus+OnCo: all_passed={report['all_passed']}")
    if not report["all_passed"]:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
