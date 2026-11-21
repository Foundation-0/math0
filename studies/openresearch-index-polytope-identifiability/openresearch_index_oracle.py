"""
Exact Pure-Q Mathematical Tomography & Tao Observability Oracle
for the alphaXiv OpenResearch Intelligence Index (AUDIT-069).

Zero floats on all trust paths. Zero third-party dependencies.
Zero bare `assert` statements; all trust-boundary refusals raise
`IndexOracleError(ValueError)` with deterministic machine-readable `.code`.
"""
from __future__ import annotations

from fractions import Fraction
import hashlib
import json
import re
from typing import Any, Mapping, Sequence


_EXACT_NUM_RE = re.compile(r"\A-?(?:0|[1-9][0-9]*)(?:\.[0-9]+|/[1-9][0-9]*)?\Z")
_SHA256_HEX_RE = re.compile(r"\A[0-9a-f]{64}\Z")

EXPECTED_PROCESS_KEYS = frozenset(
    {
        "frozen_contract_sha256",
        "split_leakage_count",
        "internet_contamination_audit",
        "goodhart_kl_delta_bps",
        "max_kl_delta_bps",
        "r4_isolated_parity_runs",
        "r5_mutation_killed",
        "r5_mutation_total",
    }
)

VERIFIED_INTERNET_STATUS = "OFFLINE_OR_ALLOWLIST_VERIFIED"
DEFAULT_INDEX_WEIGHTS = (Fraction(2, 5), Fraction(2, 5), Fraction(1, 5))


class IndexOracleError(ValueError):
    """Fail-closed exact-arithmetic or schema refusal error."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"[{code}] {message}")
        self.code = code


def verify_no_floats(obj: Any, path: str = "root") -> None:
    """Recursively reject any Python float anywhere in an object tree."""
    if isinstance(obj, float):
        raise IndexOracleError("FLOAT_FORBIDDEN", f"float forbidden at {path}")
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
        raise IndexOracleError("INVALID_STR", f"{field} must be str")
    if value.strip() == "":
        raise IndexOracleError("EMPTY_STR", f"{field} must be non-empty")
    return value


def require_exact_int(
    value: Any,
    field: str,
    min_value: int | None = None,
    max_value: int | None = None,
) -> int:
    """Require an exact int (rejecting bool and float) within optional closed bounds."""
    if isinstance(value, bool) or not isinstance(value, int):
        raise IndexOracleError("INVALID_INT", f"{field} must be exact int")
    if min_value is not None and value < min_value:
        raise IndexOracleError("INT_BELOW_MIN", f"{field}={value} < {min_value}")
    if max_value is not None and value > max_value:
        raise IndexOracleError("INT_ABOVE_MAX", f"{field}={value} > {max_value}")
    return value


def require_exact_fraction(
    value: Any,
    field: str,
    min_value: Fraction | None = None,
    max_value: Fraction | None = None,
) -> Fraction:
    """Require an exact Fraction, exact int (non-bool), or canonical decimal/rational string."""
    if isinstance(value, bool):
        raise IndexOracleError("BOOL_NOT_FRACTION", f"{field} cannot be bool")
    if isinstance(value, Fraction):
        out = value
    elif isinstance(value, int):
        out = Fraction(value, 1)
    elif isinstance(value, str):
        if _EXACT_NUM_RE.match(value) is None:
            raise IndexOracleError("INVALID_FRACTION_STR", f"{field}={value!r} is not canonical")
        out = Fraction(value)
    else:
        raise IndexOracleError("INVALID_FRACTION_TYPE", f"{field} must be exact rational")
    if min_value is not None and out < min_value:
        raise IndexOracleError("FRACTION_BELOW_MIN", f"{field}={out} < {min_value}")
    if max_value is not None and out > max_value:
        raise IndexOracleError("FRACTION_ABOVE_MAX", f"{field}={out} > {max_value}")
    return out


def frac_str(value: Fraction) -> str:
    """Canonical exact rational string 'p/q'."""
    f = require_exact_fraction(value, "value")
    return f"{f.numerator}/{f.denominator}"


def format_exact_decimal(value: Fraction, places: int = 6) -> str:
    """Pure-integer exact decimal rounding (half-up) with zero float usage."""
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
    """Emit canonical sorted-key UTF-8 JSON bytes after proving zero floats exist."""
    verify_no_floats(payload, "payload")
    return json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    ).encode("utf-8")


def canonical_sha256(payload: Any) -> str:
    """SHA-256 hex digest of canonical float-free JSON representation."""
    return hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def compute_composite_index_exact(
    science: Any,
    post_training: Any,
    literature: Any,
    weights: Sequence[Any] = DEFAULT_INDEX_WEIGHTS,
) -> Fraction:
    """Exact pure-Q weighted composite score over the 3 OpenResearch tracks."""
    s = require_exact_fraction(science, "science", Fraction(0), Fraction(1))
    p = require_exact_fraction(post_training, "post_training", Fraction(0), Fraction(1))
    lit = require_exact_fraction(literature, "literature", Fraction(0), Fraction(1))
    if len(weights) != 3:
        raise IndexOracleError("WEIGHT_COUNT_INVALID", "weights must have length 3")
    w_s = require_exact_fraction(weights[0], "weights[0]", Fraction(0), Fraction(1))
    w_p = require_exact_fraction(weights[1], "weights[1]", Fraction(0), Fraction(1))
    w_l = require_exact_fraction(weights[2], "weights[2]", Fraction(0), Fraction(1))
    if w_s + w_p + w_l != Fraction(1):
        raise IndexOracleError("WEIGHT_SUM_NOT_ONE", "weights must sum to 1")
    return w_s * s + w_p * p + w_l * lit


def audit_task_leverage_asymmetry(
    track_weights: Mapping[str, Any],
    track_task_counts: Mapping[str, Any],
) -> dict[str, Any]:
    """Compute exact per-task headline leverage and max/min disparity across tracks."""
    if len(track_weights) < 2:
        raise IndexOracleError("TOO_FEW_TRACKS", "need at least 2 tracks")
    if set(track_weights.keys()) != set(track_task_counts.keys()):
        raise IndexOracleError("TRACK_KEY_MISMATCH", "weight and count track keys must match")
    weights_q: dict[str, Fraction] = {}
    counts_i: dict[str, int] = {}
    total_w = Fraction(0)
    total_tasks = 0
    for key in sorted(track_weights.keys()):
        require_non_empty_str(key, "track_name")
        w = require_exact_fraction(track_weights[key], f"weight[{key}]", Fraction(0), Fraction(1))
        if w == Fraction(0):
            raise IndexOracleError("ZERO_TRACK_WEIGHT", f"track {key} weight must be positive")
        c = require_exact_int(track_task_counts[key], f"task_count[{key}]", min_value=1)
        weights_q[key] = w
        counts_i[key] = c
        total_w += w
        total_tasks += c
    if total_w != Fraction(1):
        raise IndexOracleError("TRACK_WEIGHT_SUM_NOT_ONE", "track weights must sum to 1")

    per_task: dict[str, Fraction] = {k: weights_q[k] / counts_i[k] for k in weights_q}
    proportional_w: dict[str, Fraction] = {
        k: Fraction(counts_i[k], total_tasks) for k in counts_i
    }
    max_lev = max(per_task.values())
    min_lev = min(per_task.values())
    ratio = max_lev / min_lev
    return {
        "total_tasks": total_tasks,
        "per_task_weight_exact": {k: frac_str(v) for k, v in per_task.items()},
        "per_task_weight_dec": {k: format_exact_decimal(v, 6) for k, v in per_task.items()},
        "task_proportional_weights_exact": {k: frac_str(v) for k, v in proportional_w.items()},
        "max_to_min_task_leverage_exact": frac_str(ratio),
        "max_to_min_task_leverage_dec": format_exact_decimal(ratio, 6),
    }


def _clip_polygon_halfspace(
    poly: list[tuple[Fraction, Fraction]],
    a: Fraction,
    b: Fraction,
    c: Fraction,
) -> list[tuple[Fraction, Fraction]]:
    """Exact pure-Q Sutherland-Hodgman clipping against a*x + b*y + c >= 0."""
    if len(poly) < 3:
        return []
    out: list[tuple[Fraction, Fraction]] = []
    n = len(poly)
    for i in range(n):
        p1 = poly[i]
        p2 = poly[(i + 1) % n]
        d1 = a * p1[0] + b * p1[1] + c
        d2 = a * p2[0] + b * p2[1] + c
        in1 = d1 >= 0
        in2 = d2 >= 0
        if in1 and in2:
            out.append(p2)
        elif in1 and not in2:
            t = d1 / (d1 - d2)
            out.append((p1[0] + t * (p2[0] - p1[0]), p1[1] + t * (p2[1] - p1[1])))
        elif not in1 and in2:
            t = d1 / (d1 - d2)
            out.append((p1[0] + t * (p2[0] - p1[0]), p1[1] + t * (p2[1] - p1[1])))
            out.append(p2)
    return out


def _polygon_twice_area_exact(poly: Sequence[tuple[Fraction, Fraction]]) -> Fraction:
    """Twice the unsigned exact rational area of a convex 2D polygon (Shoelace)."""
    n = len(poly)
    if n < 3:
        return Fraction(0)
    acc = Fraction(0)
    for i in range(n):
        x1, y1 = poly[i]
        x2, y2 = poly[(i + 1) % n]
        acc += x1 * y2 - x2 * y1
    return -acc if acc < 0 else acc


def exact_simplex_region_fraction(
    halfspaces: Sequence[tuple[Any, Any, Any]],
) -> Fraction:
    """
    Exact pure-Q area fraction of the 2-simplex Delta_2 = {(w_S, w_P) >= 0 : w_S + w_P <= 1}
    satisfying all linear inequalities a * w_S + b * w_P + c >= 0.
    Because area(Delta_2) = 1/2, the fraction equals 2 * area(clipped_polygon) = twice_area!
    """
    poly: list[tuple[Fraction, Fraction]] = [
        (Fraction(0), Fraction(0)),
        (Fraction(1), Fraction(0)),
        (Fraction(0), Fraction(1)),
    ]
    for idx, hs in enumerate(halfspaces):
        if len(hs) != 3:
            raise IndexOracleError("HALFSPACE_ARITY", f"halfspace[{idx}] must have 3 coeffs")
        a = require_exact_fraction(hs[0], f"halfspace[{idx}][0]")
        b = require_exact_fraction(hs[1], f"halfspace[{idx}][1]")
        c = require_exact_fraction(hs[2], f"halfspace[{idx}][2]")
        poly = _clip_polygon_halfspace(poly, a, b, c)
        if len(poly) < 3:
            return Fraction(0)
    return _polygon_twice_area_exact(poly)


def audit_weight_sensitivity_simplex(
    models: Sequence[Mapping[str, Any]],
    baseline_weights: Sequence[Any] = DEFAULT_INDEX_WEIGHTS,
) -> dict[str, Any]:
    """
    Exact pure-Q 2-simplex polytope tomography over track weights (w_S, w_P, w_L):
      - Exact Delta_2 area fraction where each model ranks #1.
      - Exact Delta_2 area fraction preserving the full baseline ordering and top-5 ordering.
      - Exact #1 flip threshold along the w_L=0 and w_P=0 edges between top-2 winners.
    """
    if len(models) < 2:
        raise IndexOracleError("TOO_FEW_MODELS", "need at least 2 models")
    parsed: list[tuple[str, Fraction, Fraction, Fraction]] = []
    seen_names: set[str] = set()
    for idx, item in enumerate(models):
        name = require_non_empty_str(item.get("name"), f"models[{idx}].name")
        if name in seen_names:
            raise IndexOracleError("DUPLICATE_MODEL", f"duplicate model {name!r}")
        seen_names.add(name)
        s = require_exact_fraction(item.get("science"), f"{name}.science", Fraction(0), Fraction(1))
        p = require_exact_fraction(
            item.get("post_training"), f"{name}.post_training", Fraction(0), Fraction(1)
        )
        lit = require_exact_fraction(
            item.get("literature"), f"{name}.literature", Fraction(0), Fraction(1)
        )
        parsed.append((name, s, p, lit))

    baseline_scored = sorted(
        [
            (compute_composite_index_exact(s, p, lit, baseline_weights), name, s, p, lit)
            for name, s, p, lit in parsed
        ],
        key=lambda row: (-row[0], row[1]),
    )

    def _pair_hs(
        hi: tuple[str, Fraction, Fraction, Fraction],
        lo: tuple[str, Fraction, Fraction, Fraction],
    ) -> tuple[Fraction, Fraction, Fraction]:
        _, s1, p1, l1 = hi
        _, s2, p2, l2 = lo
        return ((s1 - l1) - (s2 - l2), (p1 - l1) - (p2 - l2), l1 - l2)

    winner_area: dict[str, Fraction] = {}
    for row in parsed:
        hs_list = [_pair_hs(row, other) for other in parsed if other[0] != row[0]]
        winner_area[row[0]] = exact_simplex_region_fraction(hs_list)

    ordered_rows = [(name, s, p, lit) for _, name, s, p, lit in baseline_scored]
    full_order_hs = [_pair_hs(ordered_rows[i], ordered_rows[i + 1]) for i in range(len(ordered_rows) - 1)]
    full_order_area = exact_simplex_region_fraction(full_order_hs)

    top_k = min(5, len(ordered_rows))
    top_order_hs = [_pair_hs(ordered_rows[i], ordered_rows[i + 1]) for i in range(top_k - 1)]
    top_order_area = exact_simplex_region_fraction(top_order_hs)

    # Exact edge intercepts between #1 and highest-area competitor (if any)
    ranked_winners = sorted(winner_area.items(), key=lambda kv: (-kv[1], kv[0]))
    edge_flips: dict[str, Any] = {}
    if len(ranked_winners) >= 2 and ranked_winners[1][1] > 0:
        by_name = {r[0]: r for r in parsed}
        m1 = by_name[ranked_winners[0][0]]
        m2 = by_name[ranked_winners[1][0]]
        a, b, c = _pair_hs(m1, m2)
        # Edge w_L = 0 -> w_P = 1 - w_S -> (a - b) * w_S + (b + c) = 0
        if a != b:
            ws_wl0 = -(b + c) / (a - b)
            if Fraction(0) <= ws_wl0 <= Fraction(1):
                edge_flips["edge_wL_eq_0_flip_wS_exact"] = frac_str(ws_wl0)
                edge_flips["edge_wL_eq_0_flip_wS_dec"] = format_exact_decimal(ws_wl0, 6)
        # Edge w_P = 0 -> a * w_S + c = 0
        if a != 0:
            ws_wp0 = -c / a
            if Fraction(0) <= ws_wp0 <= Fraction(1):
                edge_flips["edge_wP_eq_0_flip_wS_exact"] = frac_str(ws_wp0)
                edge_flips["edge_wP_eq_0_flip_wS_dec"] = format_exact_decimal(ws_wp0, 6)
        edge_flips["primary_winner"] = m1[0]
        edge_flips["challenger_winner"] = m2[0]

    area_sum = sum(winner_area.values(), Fraction(0))
    return {
        "baseline_ranking": [r[0] for r in ordered_rows],
        "winner_simplex_fractions_exact": {k: frac_str(v) for k, v in winner_area.items()},
        "winner_simplex_fractions_dec": {
            k: format_exact_decimal(v, 6) for k, v in winner_area.items()
        },
        "winner_fraction_sum_exact": frac_str(area_sum),
        "positive_winner_models": [k for k, v in ranked_winners if v > 0],
        "full_baseline_order_fraction_exact": frac_str(full_order_area),
        "full_baseline_order_fraction_dec": format_exact_decimal(full_order_area, 6),
        "top_k_count": top_k,
        "top_k_baseline_order_fraction_exact": frac_str(top_order_area),
        "top_k_baseline_order_fraction_dec": format_exact_decimal(top_order_area, 6),
        "winner_boundary_intercepts": edge_flips,
    }


def compute_pareto_frontier_exact(entries: Sequence[Mapping[str, Any]]) -> list[dict[str, str]]:
    """
    Exact cost-minimizing, score-maximizing Pareto frontier.
    Rejects non-positive cost, out-of-range score, empty list, or duplicate names.
    """
    if len(entries) == 0:
        raise IndexOracleError("EMPTY_ENTRIES", "entries must be non-empty")
    seen: set[str] = set()
    normalized: list[tuple[Fraction, Fraction, str]] = []
    for idx, item in enumerate(entries):
        name = require_non_empty_str(item.get("name"), f"entries[{idx}].name")
        if name in seen:
            raise IndexOracleError("DUPLICATE_ENTRY", f"duplicate entry {name!r}")
        seen.add(name)
        cost = require_exact_fraction(item.get("cost"), f"{name}.cost", Fraction(0))
        if cost == Fraction(0):
            raise IndexOracleError("NON_POSITIVE_COST", f"{name}.cost must be > 0")
        score = require_exact_fraction(item.get("score"), f"{name}.score", Fraction(0), Fraction(1))
        normalized.append((cost, score, name))

    # Sort by ascending cost, then descending score (handles tied cost cleanly)
    normalized.sort(key=lambda row: (row[0], -row[1], row[2]))
    frontier: list[dict[str, str]] = []
    best_score = Fraction(-1)
    for cost, score, name in normalized:
        if score > best_score:
            frontier.append(
                {
                    "name": name,
                    "cost_exact": frac_str(cost),
                    "cost_dec": format_exact_decimal(cost, 2),
                    "score_exact": frac_str(score),
                    "score_dec": format_exact_decimal(score, 4),
                }
            )
            best_score = score
    return frontier


def audit_ci_separability_and_pareto_stability(
    entries: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    """
    Audit exact 95% CI pairwise overlap graph, overlap cliques, minimum clean separation gap,
    and CI-perturbed Pareto frontier stability (whether a cheaper model's CI upper bound
    reaches or exceeds a pricier frontier model's CI lower bound).
    """
    if len(entries) < 2:
        raise IndexOracleError("TOO_FEW_CI_ENTRIES", "need at least 2 entries for CI audit")
    parsed: list[tuple[str, Fraction, Fraction, Fraction, Fraction]] = []
    seen: set[str] = set()
    for idx, item in enumerate(entries):
        name = require_non_empty_str(item.get("name"), f"entries[{idx}].name")
        if name in seen:
            raise IndexOracleError("DUPLICATE_CI_ENTRY", f"duplicate entry {name!r}")
        seen.add(name)
        cost = require_exact_fraction(item.get("cost"), f"{name}.cost", Fraction(0))
        if cost == Fraction(0):
            raise IndexOracleError("NON_POSITIVE_CI_COST", f"{name}.cost must be > 0")
        score = require_exact_fraction(item.get("score"), f"{name}.score", Fraction(0), Fraction(1))
        ci_lo = require_exact_fraction(item.get("ci_lo"), f"{name}.ci_lo", Fraction(0), Fraction(1))
        ci_hi = require_exact_fraction(item.get("ci_hi"), f"{name}.ci_hi", Fraction(0), Fraction(1))
        if ci_lo > score:
            raise IndexOracleError("CI_LO_GT_SCORE", f"{name}: ci_lo > score")
        if ci_hi < score:
            raise IndexOracleError("CI_HI_LT_SCORE", f"{name}: ci_hi < score")
        parsed.append((name, cost, score, ci_lo, ci_hi))

    ranked = sorted(parsed, key=lambda r: (-r[2], r[0]))
    overlaps: list[dict[str, str]] = []
    separated: list[dict[str, str]] = []
    n = len(ranked)
    for i in range(n):
        for j in range(i + 1, n):
            n1, _, _, lo1, hi1 = ranked[i]
            n2, _, _, lo2, hi2 = ranked[j]
            ov_lo = max(lo1, lo2)
            ov_hi = min(hi1, hi2)
            if ov_lo <= ov_hi:
                width = ov_hi - ov_lo
                overlaps.append(
                    {
                        "pair": f"{n1} <-> {n2}",
                        "overlap_width_exact": frac_str(width),
                        "overlap_width_dec": format_exact_decimal(width, 4),
                    }
                )
            else:
                gap = ov_lo - ov_hi
                separated.append(
                    {
                        "pair": f"{n1} > {n2}",
                        "gap_exact": frac_str(gap),
                        "gap_dec": format_exact_decimal(gap, 4),
                    }
                )

    # Check consecutive-rank maximal CI cliques (indices a..b where all pairs overlap)
    overlap_set = {
        (ranked[i][0], ranked[j][0])
        for i in range(n)
        for j in range(i + 1, n)
        if max(ranked[i][3], ranked[j][3]) <= min(ranked[i][4], ranked[j][4])
    }
    largest_rank_clique: list[str] = []
    for i in range(n):
        for j in range(i + 1, n):
            is_clique = True
            for a in range(i, j + 1):
                for b in range(a + 1, j + 1):
                    if (ranked[a][0], ranked[b][0]) not in overlap_set:
                        is_clique = False
                        break
                if not is_clique:
                    break
            if is_clique and (j - i + 1) > len(largest_rank_clique):
                largest_rank_clique = [ranked[k][0] for k in range(i, j + 1)]

    frontier = compute_pareto_frontier_exact(entries)
    by_name = {r[0]: r for r in parsed}
    pareto_ci_fragilities: list[dict[str, str]] = []
    for k in range(len(frontier) - 1):
        cheaper = by_name[frontier[k]["name"]]
        pricier = by_name[frontier[k + 1]["name"]]
        if cheaper[4] >= pricier[3]:
            cost_ratio = pricier[1] / cheaper[1]
            margin = cheaper[4] - pricier[3]
            pareto_ci_fragilities.append(
                {
                    "cheaper_model": cheaper[0],
                    "pricier_model": pricier[0],
                    "cheaper_ci_hi_minus_pricier_ci_lo_exact": frac_str(margin),
                    "cheaper_ci_hi_minus_pricier_ci_lo_dec": format_exact_decimal(margin, 4),
                    "cost_ratio_exact": frac_str(cost_ratio),
                    "cost_ratio_dec": format_exact_decimal(cost_ratio, 4),
                }
            )

    min_sep = min(separated, key=lambda x: Fraction(x["gap_exact"])) if separated else None
    return {
        "total_pairs": n * (n - 1) // 2,
        "overlapping_pair_count": len(overlaps),
        "separated_pair_count": len(separated),
        "overlapping_pairs": overlaps,
        "smallest_clean_separation": min_sep,
        "largest_contiguous_rank_ci_clique": largest_rank_clique,
        "headline_pareto_frontier": [f["name"] for f in frontier],
        "pareto_ci_fragilities": pareto_ci_fragilities,
    }


def _rref_and_nullspace_exact(
    matrix: list[list[Fraction]],
    num_cols: int,
) -> tuple[int, list[list[Fraction]]]:
    """Exact pure-Q Gaussian elimination (RREF) and explicit rational basis for ker(X)."""
    rows = [list(r) for r in matrix]
    m = len(rows)
    pivots: list[int] = []
    r = 0
    for c in range(num_cols):
        piv = None
        for i in range(r, m):
            if rows[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        pv = rows[r][c]
        rows[r] = [v / pv for v in rows[r]]
        for i in range(m):
            if i != r and rows[i][c] != 0:
                fac = rows[i][c]
                rows[i] = [rows[i][j] - fac * rows[r][j] for j in range(num_cols)]
        pivots.append(c)
        r += 1
    pivot_set = set(pivots)
    free_cols = [c for c in range(num_cols) if c not in pivot_set]
    basis: list[list[Fraction]] = []
    for fc in free_cols:
        vec = [Fraction(0)] * num_cols
        vec[fc] = Fraction(1)
        for row_idx, pc in enumerate(pivots):
            vec[pc] = -rows[row_idx][fc]
        basis.append(vec)
    return len(pivots), basis


def audit_bipartite_confounding_exact(
    observations: Sequence[tuple[str, str]],
) -> dict[str, Any]:
    """
    Exact pure-Q linear-algebra identifiability proof for two-way additive model
    y_{m,h} = mu_m + gamma_h over observed (model, harness) pairs.

    A contrast c^T theta is identifiable iff c is orthogonal to every basis vector of ker(X).
    When the bipartite Model-Harness graph has K connected components, dim ker(X) = K,
    leaving K - 1 non-trivial confounding directions that prevent cross-harness model comparison.
    """
    if len(observations) == 0:
        raise IndexOracleError("EMPTY_OBSERVATIONS", "observations must be non-empty")
    seen_pairs: set[tuple[str, str]] = set()
    models_sorted_set: set[str] = set()
    harnesses_sorted_set: set[str] = set()
    cleaned: list[tuple[str, str]] = []
    for idx, pair in enumerate(observations):
        if len(pair) != 2:
            raise IndexOracleError("INVALID_OBS_PAIR", f"observations[{idx}] must be (model, harness)")
        m_name = require_non_empty_str(pair[0], f"observations[{idx}][0]")
        h_name = require_non_empty_str(pair[1], f"observations[{idx}][1]")
        key = (m_name, h_name)
        if key in seen_pairs:
            raise IndexOracleError("DUPLICATE_OBSERVATION", f"duplicate cell {key!r}")
        seen_pairs.add(key)
        models_sorted_set.add(m_name)
        harnesses_sorted_set.add(h_name)
        cleaned.append(key)

    models = sorted(models_sorted_set)
    harnesses = sorted(harnesses_sorted_set)
    m_idx = {m: i for i, m in enumerate(models)}
    h_idx = {h: len(models) + i for i, h in enumerate(harnesses)}
    num_cols = len(models) + len(harnesses)

    design_x: list[list[Fraction]] = []
    for m_name, h_name in cleaned:
        row = [Fraction(0)] * num_cols
        row[m_idx[m_name]] = Fraction(1)
        row[h_idx[h_name]] = Fraction(1)
        design_x.append(row)

    rank, null_basis = _rref_and_nullspace_exact(design_x, num_cols)
    nullity = len(null_basis)

    def _is_identifiable(c_idx1: int, c_idx2: int) -> bool:
        for v in null_basis:
            if v[c_idx1] - v[c_idx2] != 0:
                return False
        return True

    ident_model_pairs: list[str] = []
    unident_model_pairs: list[str] = []
    for i in range(len(models)):
        for j in range(i + 1, len(models)):
            label = f"{models[i]} vs {models[j]}"
            if _is_identifiable(m_idx[models[i]], m_idx[models[j]]):
                ident_model_pairs.append(label)
            else:
                unident_model_pairs.append(label)

    ident_harness_pairs: list[str] = []
    unident_harness_pairs: list[str] = []
    for i in range(len(harnesses)):
        for j in range(i + 1, len(harnesses)):
            label = f"{harnesses[i]} vs {harnesses[j]}"
            if _is_identifiable(h_idx[harnesses[i]], h_idx[harnesses[j]]):
                ident_harness_pairs.append(label)
            else:
                unident_harness_pairs.append(label)

    total_m_pairs = len(models) * (len(models) - 1) // 2
    ident_ratio = (
        Fraction(len(ident_model_pairs), total_m_pairs) if total_m_pairs > 0 else Fraction(1)
    )
    return {
        "observation_count": len(cleaned),
        "model_count": len(models),
        "harness_count": len(harnesses),
        "parameter_count": num_cols,
        "design_rank": rank,
        "nullspace_dim": nullity,
        "connected_components": nullity,
        "min_bridge_cells_needed": nullity - 1,
        "fully_identifiable_cross_harness": nullity == 1,
        "identifiable_model_pair_count": len(ident_model_pairs),
        "unidentifiable_model_pair_count": len(unident_model_pairs),
        "identifiable_model_pair_fraction_exact": frac_str(ident_ratio),
        "identifiable_harness_pair_count": len(ident_harness_pairs),
        "unidentifiable_harness_pair_count": len(unident_harness_pairs),
        "identifiable_model_pairs": ident_model_pairs,
        "unidentifiable_model_pairs": unident_model_pairs,
        "identifiable_harness_pairs": ident_harness_pairs,
        "unidentifiable_harness_pairs": unident_harness_pairs,
        "nullspace_basis_columns": models + [f"harness:{h}" for h in harnesses],
        "nullspace_basis_exact": [[frac_str(x) for x in v] for v in null_basis],
    }


def audit_missing_attempts_and_cost_extrapolation(
    completed_attempts: int,
    full_attempts: int,
    observed_index_score: Any,
    reported_full_cost: Any,
    reported_per_attempt_cost: Any,
    track_attempt_counts: Sequence[int],
    track_per_attempt_costs: Sequence[Any],
    track_weights: Sequence[Any] = DEFAULT_INDEX_WEIGHTS,
) -> dict[str, Any]:
    """
    Exact audit of incomplete-attempt models (e.g., Fable 5.1* with 74/87 attempts):
      - Reconstructs full-pass cost sum(n_t * c_t) vs reported headline cost vs actual spend.
      - Computes exact MNAR (Missing Not At Random) lower/upper bounds on the headline index
        if all missing attempts came from a single track (worst-case 0-imputation vs 1-imputation).
    """
    full_n = require_exact_int(full_attempts, "full_attempts", min_value=1)
    comp_n = require_exact_int(completed_attempts, "completed_attempts", min_value=1, max_value=full_n)
    obs_idx = require_exact_fraction(observed_index_score, "observed_index_score", Fraction(0), Fraction(1))
    rep_full = require_exact_fraction(reported_full_cost, "reported_full_cost", Fraction(0))
    rep_per = require_exact_fraction(reported_per_attempt_cost, "reported_per_attempt_cost", Fraction(0))
    if len(track_attempt_counts) != 3 or len(track_per_attempt_costs) != 3 or len(track_weights) != 3:
        raise IndexOracleError("TRACK_LENGTH_INVALID", "track counts, costs, and weights must have length 3")

    counts = [require_exact_int(c, f"track_attempt_counts[{i}]", min_value=1) for i, c in enumerate(track_attempt_counts)]
    if sum(counts) != full_n:
        raise IndexOracleError("TRACK_COUNT_SUM_MISMATCH", "sum(track_attempt_counts) != full_attempts")
    costs = [require_exact_fraction(c, f"track_per_attempt_costs[{i}]", Fraction(0)) for i, c in enumerate(track_per_attempt_costs)]
    weights = [require_exact_fraction(w, f"track_weights[{i}]", Fraction(0), Fraction(1)) for i, w in enumerate(track_weights)]
    if sum(weights, Fraction(0)) != Fraction(1):
        raise IndexOracleError("MISSING_AUDIT_WEIGHT_SUM", "track_weights must sum to 1")

    missing = full_n - comp_n
    reconstructed_full = sum((counts[i] * costs[i] for i in range(3)), Fraction(0))
    actual_spend_est = comp_n * rep_per
    extrap_gap = rep_full - actual_spend_est
    missing_frac = Fraction(missing, full_n)

    # Exact MNAR worst-case shift bounds if all `missing` attempts belong to track t (capped at counts[t])
    track_names = ("science", "post_training", "literature")
    mnar_track_max_delta: dict[str, str] = {}
    mnar_track_max_delta_dec: dict[str, str] = {}
    for i, tname in enumerate(track_names):
        m_in_track = min(missing, counts[i])
        max_delta = weights[i] * Fraction(m_in_track, counts[i])
        mnar_track_max_delta[tname] = frac_str(max_delta)
        mnar_track_max_delta_dec[tname] = format_exact_decimal(max_delta, 4)

    # Exact global-proportional MNAR interval if missing rate is uniform across tracks
    global_lo = obs_idx * Fraction(comp_n, full_n)
    global_hi = global_lo + missing_frac
    return {
        "completed_attempts": comp_n,
        "full_attempts": full_n,
        "missing_attempts": missing,
        "missing_fraction_exact": frac_str(missing_frac),
        "missing_fraction_dec": format_exact_decimal(missing_frac, 4),
        "reconstructed_full_pass_cost_exact": frac_str(reconstructed_full),
        "reconstructed_full_pass_cost_dec": format_exact_decimal(reconstructed_full, 2),
        "reported_full_cost_exact": frac_str(rep_full),
        "actual_completed_spend_estimate_exact": frac_str(actual_spend_est),
        "actual_completed_spend_estimate_dec": format_exact_decimal(actual_spend_est, 2),
        "cost_extrapolation_gap_exact": frac_str(extrap_gap),
        "cost_extrapolation_gap_dec": format_exact_decimal(extrap_gap, 2),
        "uniform_mnar_score_lower_exact": frac_str(global_lo),
        "uniform_mnar_score_lower_dec": format_exact_decimal(global_lo, 4),
        "uniform_mnar_score_upper_exact": frac_str(global_hi),
        "uniform_mnar_score_upper_dec": format_exact_decimal(global_hi, 4),
        "single_track_worst_case_delta_exact": mnar_track_max_delta,
        "single_track_worst_case_delta_dec": mnar_track_max_delta_dec,
    }


def evaluate_tao_observability_gate(
    outcome_score: Any,
    process_receipt: Mapping[str, Any],
) -> dict[str, Any]:
    """
    Formalize Terence Tao's black-box observability critique into a fail-closed 5-gate
    process audit uniting Foundation-0/aletheia v1.4.0 (R1-R5) and Moissanite-Labs/warp-drive#13/#15:
      G1. Ring-0 frozen contract & run-command SHA-256 (64 lowercase hex).
      G2. Zero train/eval split leakage (split_leakage_count == 0).
      G3. Internet contamination audit verified (OFFLINE_OR_ALLOWLIST_VERIFIED).
      G4. Fisher-Schur Goodhart KL latch pass (0 <= goodhart_kl_delta_bps <= max_kl_delta_bps).
      G5. R4 isolated parity (>= 3 runs) and 100% R5 AST mutation kill (killed == total > 0).
    """
    score = require_exact_fraction(outcome_score, "outcome_score", Fraction(0), Fraction(1))
    if not isinstance(process_receipt, Mapping):
        raise IndexOracleError("INVALID_RECEIPT_TYPE", "process_receipt must be a mapping")
    verify_no_floats(process_receipt, "process_receipt")
    keys = frozenset(process_receipt.keys())
    if keys != EXPECTED_PROCESS_KEYS:
        raise IndexOracleError("RECEIPT_KEY_MISMATCH", "process_receipt keys must match exact schema")

    contract_sha = process_receipt["frozen_contract_sha256"]
    leakage = require_exact_int(process_receipt["split_leakage_count"], "split_leakage_count", min_value=0)
    net_status = process_receipt["internet_contamination_audit"]
    kl_delta = require_exact_int(process_receipt["goodhart_kl_delta_bps"], "goodhart_kl_delta_bps", min_value=0)
    max_kl = require_exact_int(process_receipt["max_kl_delta_bps"], "max_kl_delta_bps", min_value=1)
    r4_runs = require_exact_int(process_receipt["r4_isolated_parity_runs"], "r4_isolated_parity_runs", min_value=0)
    r5_total = require_exact_int(process_receipt["r5_mutation_total"], "r5_mutation_total", min_value=0)
    r5_killed = require_exact_int(
        process_receipt["r5_mutation_killed"], "r5_mutation_killed", min_value=0, max_value=r5_total
    )

    failure_reasons: list[str] = []
    if not isinstance(contract_sha, str) or _SHA256_HEX_RE.match(contract_sha) is None:
        failure_reasons.append("G1_FROZEN_CONTRACT_MISSING")
    if leakage != 0:
        failure_reasons.append("G2_SPLIT_LEAKAGE_DETECTED")
    if not isinstance(net_status, str) or net_status != VERIFIED_INTERNET_STATUS:
        failure_reasons.append("G3_UNAUDITED_INTERNET_ACCESS")
    if kl_delta > max_kl:
        failure_reasons.append("G4_GOODHART_KL_EXCEEDED")
    if r4_runs < 3:
        failure_reasons.append("G5A_R4_PARITY_BELOW_3")
    if r5_total == 0:
        failure_reasons.append("G5B_R5_MUTATION_TOTAL_ZERO")
    if r5_killed != r5_total:
        failure_reasons.append("G5C_R5_MUTATION_INCOMPLETE")

    g5_failed = int(r4_runs < 3 or r5_total == 0 or r5_killed != r5_total)
    g1_to_g4_failed = sum(
        1 for code in failure_reasons if not code.startswith("G5")
    )
    passed_count = 5 - (g1_to_g4_failed + g5_failed)
    admissible = len(failure_reasons) == 0
    adjusted = score if admissible else Fraction(0)
    return {
        "verdict": "PROMOTED" if admissible else "REJECTED_BLACK_BOX",
        "admissible": admissible,
        "outcome_score_exact": frac_str(score),
        "outcome_score_dec": format_exact_decimal(score, 4),
        "observable_adjusted_score_exact": frac_str(adjusted),
        "observable_adjusted_score_dec": format_exact_decimal(adjusted, 4),
        "process_gates_passed": passed_count,
        "process_gates_total": 5,
        "failed_gates": failure_reasons,
    }
