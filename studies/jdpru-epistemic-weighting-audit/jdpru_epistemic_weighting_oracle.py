"""Pure-stdlib, zero-float exact rational oracle for AUDIT-078 (jdpru).

Bridges two empirical & governance domains in exact rational arithmetic (Q):
  Pillar 1 (cover-your-ais <-> Aletheia v1.4.0 / AUDIT-076R):
    - Deterministic hidden/Trojan-Source Unicode scanner (zero-width, BiDi, Tags)
    - Deterministic agent safety surface scanner (CYA-GAP-01..06)
    - Exact prompt-vs-mechanical-oracle coverage accounting
  Pillar 2 (CES-Accuracy-Analysis <-> AUDIT-069R & weft-loom#42):
    - Exact Kish effective sample size n_eff & design effect DEFF (vector + summary stats)
    - Exact Bhatia-Davis extremal DEFF upper bound from released weight caps
    - Exact Meng (2018) Law-of-Large-Populations data-defect effective sample size
    - Exact Horvitz-Thompson / Hajek bias-variance weighting MSE inflation oracle
    - Exact national-raking vs. state-level Simpson worsening witness oracle
    - Exact CES |error| > 20 tail-flow conservation & README-vs-CSV drift audit

Strict Aletheia v1.4.0 invariants:
  - Zero IEEE-754 floats on all trust paths and serialized certificates
  - Zero bare assert statements
  - Deterministic canonical JSON + SHA-256 receipts
"""

from __future__ import annotations

from fractions import Fraction
import hashlib
import json
import re
from typing import Any


_STRICT_NUMBER_RE = re.compile(r"\A[+-]?(?:\d+(?:\.\d+)?|\d+/\d+)\Z")
_VALID_ARTIFACT_KINDS = frozenset({"prompt_rule", "shell_script", "ci_workflow", "mcp_config"})
_VALID_ALETHEIA_STATUSES = frozenset({"COVERED", "PARTIAL", "GAP_V15"})
_CRITICAL_GAP_IDS = frozenset({"CYA-GAP-01", "CYA-GAP-02", "CYA-GAP-03", "CYA-GAP-04"})

_UNPINNED_MCP_RE = re.compile(
    r"(?:@latest\b|npx\b[^\n]*\s(?:(?<!-)-[a-z]*y[a-z]*|--yes)\b|--dangerously-skip-permissions\b|--yolo\b|\bSessionStart\b)",
    re.IGNORECASE,
)
_RM_RF_VAR_RE = re.compile(
    r"\brm(?=\s[^\n]*(?:(?<=\s)-[a-z]*r[a-z]*\b|(?<=\s)--recursive\b))(?=\s[^\n]*(?:(?<=\s)-[a-z]*f[a-z]*\b|(?<=\s)--force\b))\s[^\n]*\$",
    re.IGNORECASE,
)
_SHELL_COMMENT_RE = re.compile(r"(?:^|\s)#.*$")
_SHELL_SEG_SPLIT_RE = re.compile(r"(?:;|&&|\|\|)")
_SET_U_ON_RE = re.compile(r"\bset\s+(?:-[a-z]*u[a-z]*\b|-o\s+nounset\b)", re.IGNORECASE)
_SET_U_OFF_RE = re.compile(r"\bset\s+(?:\+[a-z]*u[a-z]*\b|\+o\s+nounset\b)", re.IGNORECASE)
_INLINE_VAR_GUARD_RE = re.compile(r"\$\{[A-Za-z_][A-Za-z0-9_]*:\?[^}]*\}")
_CI_PRT_RE = re.compile(r"\bpull_request_target\b", re.IGNORECASE)
_CI_PRIV_RE = re.compile(
    r"(?:\bsecrets(?:\.|\[)|\btoJSON\s*\(\s*secrets\s*\)|\bwrite-all\b|\b[a-z-]+\s*:\s*write\b)",
    re.IGNORECASE,
)
_PROSE_RULE_RE = re.compile(
    r"(?:commit\s+only\s+when\s+asked|no\s+prs\b|code\s+freeze|never\s+push|ask\s+before|git\s+add\s+-a\b)",
    re.IGNORECASE,
)
_HOST_TILDE_PATH_RE = re.compile(r"(?:^|[\s`\"'(])~/[A-Za-z0-9._-]+")
_ALIAS_OR_CLOUD_RE = re.compile(
    r"(?:\balias\s+rm\s*=|\biCloud\b|\bDropbox\b|\bOneDrive\b)",
    re.IGNORECASE,
)


class JdpruOracleError(ValueError):
    """Fail-closed validation or invariant refusal with machine-readable code."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"[{code}] {message}")
        self.code = code


def verify_no_floats(obj: Any, path: str = "root") -> None:
    """Recursively refuse any float in keys or values."""
    if isinstance(obj, float):
        raise JdpruOracleError("FLOAT_FORBIDDEN", f"float forbidden at {path}")
    if isinstance(obj, dict):
        for k, v in obj.items():
            verify_no_floats(k, f"{path}.<key>")
            verify_no_floats(v, f"{path}.{k}")
    elif isinstance(obj, (list, tuple, set)):
        for idx, item in enumerate(obj):
            verify_no_floats(item, f"{path}[{idx}]")


def require_non_empty_str(value: Any, field: str) -> str:
    """Require a non-empty string and return stripped canonical text."""
    if not isinstance(value, str):
        raise JdpruOracleError("TYPE_ERROR", f"{field} must be str")
    stripped = value.strip()
    if not stripped:
        raise JdpruOracleError("EMPTY_STRING", f"{field} must be non-empty")
    return stripped


def require_exact_bool(value: Any, field: str) -> bool:
    """Require an exact bool."""
    if not isinstance(value, bool):
        raise JdpruOracleError("TYPE_ERROR", f"{field} must be bool")
    return value


def require_exact_int(value: Any, field: str) -> int:
    """Require an exact int, rejecting bools and floats."""
    if isinstance(value, bool) or not isinstance(value, int):
        raise JdpruOracleError("TYPE_ERROR", f"{field} must be exact int")
    return value


def require_exact_fraction(value: Any, field: str) -> Fraction:
    """Parse exact Fraction from Fraction, int (not bool), or strict numeric str."""
    if isinstance(value, Fraction):
        return value
    if isinstance(value, bool):
        raise JdpruOracleError("TYPE_ERROR", f"{field} cannot be bool")
    if isinstance(value, int):
        return Fraction(value, 1)
    if isinstance(value, float):
        raise JdpruOracleError("FLOAT_FORBIDDEN", f"{field} cannot be float")
    if isinstance(value, str):
        if _STRICT_NUMBER_RE.match(value) is None:
            raise JdpruOracleError("INVALID_RATIONAL", f"{field} has invalid numeric format: {value!r}")
        try:
            return Fraction(value)
        except ZeroDivisionError as exc:
            raise JdpruOracleError("ZERO_DENOMINATOR", f"{field} has zero denominator") from exc
    raise JdpruOracleError("TYPE_ERROR", f"{field} must be Fraction, int, or numeric str")


def require_list_or_tuple(value: Any, field: str) -> tuple[Any, ...]:
    """Require a non-empty list or tuple (rejecting str/bytes/iterators)."""
    if not isinstance(value, (list, tuple)):
        raise JdpruOracleError("TYPE_ERROR", f"{field} must be list or tuple")
    if len(value) == 0:
        raise JdpruOracleError("EMPTY_SEQUENCE", f"{field} must be non-empty")
    return tuple(value)


def frac_str(val: Fraction) -> str:
    """Canonical exact reduced rational string 'num/den'."""
    if not isinstance(val, Fraction):
        raise JdpruOracleError("TYPE_ERROR", "frac_str requires Fraction")
    return f"{val.numerator}/{val.denominator}"


def format_exact_decimal(val: Fraction, places: int) -> str:
    """Format Fraction to exact fixed decimal places using pure-integer half-up rounding."""
    if not isinstance(val, Fraction):
        raise JdpruOracleError("TYPE_ERROR", "val must be Fraction")
    places_i = require_exact_int(places, "places")
    if places_i < 0:
        raise JdpruOracleError("INVALID_RANGE", "places must be >= 0")
    neg = val < 0
    mag = -val if neg else val
    scale = 10 ** places_i
    scaled_num = mag.numerator * scale
    den = mag.denominator
    quot, rem = divmod(scaled_num, den)
    if 2 * rem >= den:
        quot += 1
    sign = "-" if neg and quot > 0 else ""
    if places_i == 0:
        return f"{sign}{quot}"
    int_part, frac_part = divmod(quot, scale)
    return f"{sign}{int_part}.{frac_part:0{places_i}d}"


def canonical_json_bytes(obj: Any) -> bytes:
    """Serialize float-free canonical ASCII JSON bytes."""
    verify_no_floats(obj)
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def canonical_sha256(obj: Any) -> str:
    """Return lowercase SHA-256 hex digest of canonical JSON serialization."""
    return hashlib.sha256(canonical_json_bytes(obj)).hexdigest()


# ---------------------------------------------------------------------------
# Pillar 1: cover-your-ais <-> Aletheia v1.4.0 / v1.5 Deterministic Scanners
# ---------------------------------------------------------------------------


def _classify_hidden_codepoint(cp: int) -> str | None:
    if (0x200B <= cp <= 0x200F) or cp == 0x2060 or cp == 0xFEFF:
        return "ZERO_WIDTH_OR_BOM"
    if cp == 0x061C or (0x202A <= cp <= 0x202E) or (0x2066 <= cp <= 0x2069):
        return "BIDI_OVERRIDE_OR_ISOLATE"
    if 0xE0000 <= cp <= 0xE007F:
        return "UNICODE_TAG_SMUGGLING"
    return None


def scan_hidden_unicode_exact(text: Any) -> dict[str, Any]:
    """Deterministically detect zero-width, BiDi trojan-source, and Tag Unicode chars."""
    if not isinstance(text, str):
        raise JdpruOracleError("TYPE_ERROR", "text must be str")
    findings: list[dict[str, Any]] = []
    line_no = 1
    col_no = 0
    for ch in text:
        if ch == "\n":
            line_no += 1
            col_no = 0
            continue
        col_no += 1
        cp = ord(ch)
        cat = _classify_hidden_codepoint(cp)
        if cat is not None:
            findings.append(
                {
                    "line": line_no,
                    "col": col_no,
                    "codepoint": f"U+{cp:04X}",
                    "category": cat,
                }
            )
    return {
        "clean": len(findings) == 0,
        "finding_count": len(findings),
        "findings": findings,
    }


def audit_agent_safety_surface(artifact_text: Any, artifact_kind: Any) -> dict[str, Any]:
    """Run deterministic CYA-GAP-01..06 safety audit on a rule/script/workflow/MCP artifact."""
    if not isinstance(artifact_text, str) or not artifact_text.strip():
        raise JdpruOracleError("EMPTY_STRING", "artifact_text must be non-empty str")
    kind = require_non_empty_str(artifact_kind, "artifact_kind").lower()
    if kind not in _VALID_ARTIFACT_KINDS:
        raise JdpruOracleError("INVALID_ARTIFACT_KIND", f"unsupported artifact_kind: {kind!r}")

    findings: list[dict[str, Any]] = []
    uni_res = scan_hidden_unicode_exact(artifact_text)
    for hit in uni_res["findings"]:
        findings.append(
            {
                "gap_id": "CYA-GAP-01",
                "cya_check": 8,
                "line": hit["line"],
                "detail": f"{hit['category']}:{hit['codepoint']}",
            }
        )

    lines = artifact_text.splitlines()
    nounset_active = False
    has_ci_prt = _CI_PRT_RE.search(artifact_text) is not None
    has_ci_priv = _CI_PRIV_RE.search(artifact_text) is not None

    for idx, line in enumerate(lines, start=1):
        for m_mcp in _UNPINNED_MCP_RE.finditer(line):
            findings.append(
                {
                    "gap_id": "CYA-GAP-02",
                    "cya_check": 8,
                    "line": idx,
                    "detail": m_mcp.group(0).strip(),
                }
            )
        code_part = _SHELL_COMMENT_RE.sub("", line)
        for seg in _SHELL_SEG_SPLIT_RE.split(code_part):
            if _SET_U_ON_RE.search(seg) is not None:
                nounset_active = True
            if _SET_U_OFF_RE.search(seg) is not None:
                nounset_active = False
            unguarded_seg = _INLINE_VAR_GUARD_RE.sub("", seg)
            if not nounset_active and _RM_RF_VAR_RE.search(unguarded_seg) is not None:
                findings.append(
                    {
                        "gap_id": "CYA-GAP-03",
                        "cya_check": 3,
                        "line": idx,
                        "detail": "unguarded_rm_rf_variable",
                    }
                )
        if has_ci_prt and has_ci_priv and _CI_PRT_RE.search(line) is not None:
            findings.append(
                {
                    "gap_id": "CYA-GAP-04",
                    "cya_check": 9,
                    "line": idx,
                    "detail": "pull_request_target_with_write_or_secrets",
                }
            )
        for m_prose in _PROSE_RULE_RE.finditer(line):
            findings.append(
                {
                    "gap_id": "CYA-GAP-05",
                    "cya_check": 5,
                    "line": idx,
                    "detail": m_prose.group(0).strip(),
                }
            )
        if _HOST_TILDE_PATH_RE.search(line) is not None:
            findings.append(
                {
                    "gap_id": "CYA-GAP-05",
                    "cya_check": 2,
                    "line": idx,
                    "detail": "host_home_tilde_dependency",
                }
            )
        for m_alias in _ALIAS_OR_CLOUD_RE.finditer(line):
            findings.append(
                {
                    "gap_id": "CYA-GAP-06",
                    "cya_check": 10,
                    "line": idx,
                    "detail": m_alias.group(0).strip(),
                }
            )

    gap_ids_present = sorted({f["gap_id"] for f in findings})
    if len(findings) == 0:
        risk_level = "CLEAN"
    elif any(g in _CRITICAL_GAP_IDS for g in gap_ids_present):
        risk_level = "CRITICAL"
    else:
        risk_level = "ELEVATED"

    return {
        "artifact_kind": kind,
        "risk_level": risk_level,
        "finding_count": len(findings),
        "gap_ids_present": gap_ids_present,
        "findings": findings,
    }


def evaluate_prompt_vs_oracle_coverage(checks: Any) -> dict[str, Any]:
    """Compute exact pure-Q coverage accounting between cover-your-ais and Aletheia v1.4.0."""
    items = require_list_or_tuple(checks, "checks")
    expected_keys = {"check_id", "cya_line", "aletheia_v140_status", "cya_gap_id", "prompt_blind_spot"}
    seen_ids: set[str] = set()
    covered = 0
    partial = 0
    gap_v15 = 0
    prompt_blind = 0

    for idx, entry in enumerate(items):
        if not isinstance(entry, dict) or set(entry.keys()) != expected_keys:
            raise JdpruOracleError("SCHEMA_ERROR", f"checks[{idx}] has invalid keys")
        cid = require_non_empty_str(entry["check_id"], f"checks[{idx}].check_id")
        if cid in seen_ids:
            raise JdpruOracleError("DUPLICATE_ID", f"duplicate check_id: {cid}")
        seen_ids.add(cid)
        cya_line = require_exact_int(entry["cya_line"], f"checks[{idx}].cya_line")
        if cya_line < 1:
            raise JdpruOracleError("INVALID_RANGE", f"checks[{idx}].cya_line must be >= 1")
        status = require_non_empty_str(entry["aletheia_v140_status"], f"checks[{idx}].aletheia_v140_status")
        if status not in _VALID_ALETHEIA_STATUSES:
            raise JdpruOracleError("INVALID_STATUS", f"unsupported status: {status!r}")
        gap_id = require_non_empty_str(entry["cya_gap_id"], f"checks[{idx}].cya_gap_id")
        blind = require_exact_bool(entry["prompt_blind_spot"], f"checks[{idx}].prompt_blind_spot")

        if status == "COVERED":
            if gap_id != "NONE":
                raise JdpruOracleError("INCONSISTENT_GAP", f"{cid}: COVERED check cannot carry gap {gap_id}")
            covered += 1
        else:
            if gap_id == "NONE":
                raise JdpruOracleError("INCONSISTENT_GAP", f"{cid}: {status} check requires non-NONE cya_gap_id")
            if status == "PARTIAL":
                partial += 1
            else:
                gap_v15 += 1
        if blind:
            prompt_blind += 1

    total = len(items)
    covered_ratio = Fraction(covered, total)
    mech_or_partial_ratio = Fraction(covered + partial, total)
    gap_ratio = Fraction(gap_v15, total)
    blind_ratio = Fraction(prompt_blind, total)
    return {
        "total_checks": total,
        "covered_count": covered,
        "partial_count": partial,
        "gap_v15_count": gap_v15,
        "prompt_blind_count": prompt_blind,
        "covered_ratio": frac_str(covered_ratio),
        "covered_pct": format_exact_decimal(covered_ratio * 100, 2),
        "covered_or_partial_ratio": frac_str(mech_or_partial_ratio),
        "covered_or_partial_pct": format_exact_decimal(mech_or_partial_ratio * 100, 2),
        "v15_gap_ratio": frac_str(gap_ratio),
        "v15_gap_pct": format_exact_decimal(gap_ratio * 100, 2),
        "prompt_blind_ratio": frac_str(blind_ratio),
        "prompt_blind_pct": format_exact_decimal(blind_ratio * 100, 2),
    }


# ---------------------------------------------------------------------------
# Pillar 2: CES-Accuracy-Analysis Exact Pure-Q Survey-Weighting Oracles
# ---------------------------------------------------------------------------


def compute_kish_neff_and_deff_exact(weights: Any, weight_cap: Any = None) -> dict[str, Any]:
    """Compute exact Kish effective sample size n_eff, DEFF, and Bhatia-Davis check in Q."""
    raw = require_list_or_tuple(weights, "weights")
    parsed: list[Fraction] = []
    for idx, w in enumerate(raw):
        wf = require_exact_fraction(w, f"weights[{idx}]")
        if wf <= 0:
            raise JdpruOracleError("INVALID_WEIGHT", f"weights[{idx}] must be > 0")
        parsed.append(wf)

    cap_f: Fraction | None = None
    if weight_cap is not None:
        cap_f = require_exact_fraction(weight_cap, "weight_cap")
        if cap_f <= 0:
            raise JdpruOracleError("INVALID_RANGE", "weight_cap must be > 0")

    n = len(parsed)
    sum_w = sum(parsed, Fraction(0, 1))
    sum_w2 = sum((w * w for w in parsed), Fraction(0, 1))
    mean_w = sum_w / n
    var_w = (sum_w2 / n) - (mean_w * mean_w)
    cv_sq = var_w / (mean_w * mean_w)
    deff = Fraction(n, 1) * sum_w2 / (sum_w * sum_w)
    n_eff = (sum_w * sum_w) / sum_w2
    retention = n_eff / n
    loss = Fraction(1, 1) - retention

    min_norm = min(parsed) / mean_w
    max_norm = max(parsed) / mean_w
    bd_upper = min_norm + max_norm - (min_norm * max_norm)
    bd_slack = bd_upper - deff

    exceeded_count = 0
    cap_exceeded = False
    if cap_f is not None:
        exceeded_count = sum(1 for w in parsed if w > cap_f)
        cap_exceeded = exceeded_count > 0

    return {
        "n": n,
        "mean_weight": frac_str(mean_w),
        "weight_variance": frac_str(var_w),
        "cv_squared": frac_str(cv_sq),
        "deff": frac_str(deff),
        "deff_decimal": format_exact_decimal(deff, 4),
        "n_eff": frac_str(n_eff),
        "n_eff_decimal": format_exact_decimal(n_eff, 4),
        "retention_ratio": frac_str(retention),
        "sample_loss_pct": format_exact_decimal(loss * 100, 2),
        "bhatia_davis_upper_deff": frac_str(bd_upper),
        "bhatia_davis_slack": frac_str(bd_slack),
        "bhatia_davis_satisfied": deff <= bd_upper,
        "weight_cap": frac_str(cap_f) if cap_f is not None else "NONE",
        "cap_exceeded": cap_exceeded,
        "cap_exceeded_count": exceeded_count,
    }


def compute_kish_from_summary_stats_exact(
    n: Any,
    mean_w: Any,
    sd_w: Any,
    sd_is_sample: Any = True,
) -> dict[str, Any]:
    """Compute exact Kish DEFF and n_eff from published codebook summary (N, mean, SD)."""
    n_i = require_exact_int(n, "n")
    is_sample = require_exact_bool(sd_is_sample, "sd_is_sample")
    min_n = 2 if is_sample else 1
    if n_i < min_n:
        raise JdpruOracleError("INVALID_RANGE", f"n must be >= {min_n}")
    mean_f = require_exact_fraction(mean_w, "mean_w")
    if mean_f <= 0:
        raise JdpruOracleError("INVALID_RANGE", "mean_w must be > 0")
    sd_f = require_exact_fraction(sd_w, "sd_w")
    if sd_f < 0:
        raise JdpruOracleError("INVALID_RANGE", "sd_w must be >= 0")

    sd_sq = sd_f * sd_f
    pop_var = sd_sq * Fraction(n_i - 1, n_i) if is_sample else sd_sq
    deff = Fraction(1, 1) + (pop_var / (mean_f * mean_f))
    n_eff = Fraction(n_i, 1) / deff
    loss = Fraction(1, 1) - (Fraction(1, 1) / deff)
    return {
        "n": n_i,
        "sd_is_sample": is_sample,
        "mean_w": frac_str(mean_f),
        "sd_w": frac_str(sd_f),
        "population_weight_variance": frac_str(pop_var),
        "deff": frac_str(deff),
        "deff_decimal": format_exact_decimal(deff, 6),
        "n_eff": frac_str(n_eff),
        "n_eff_decimal": format_exact_decimal(n_eff, 2),
        "sample_loss_pct": format_exact_decimal(loss * 100, 2),
    }


def compute_extremal_deff_bound_exact(w_min: Any, w_max: Any) -> dict[str, Any]:
    """Exact Bhatia-Davis extremal DEFF bound for mean-1 weights in [w_min, w_max]."""
    wmin_f = require_exact_fraction(w_min, "w_min")
    wmax_f = require_exact_fraction(w_max, "w_max")
    if wmin_f < 0 or wmin_f > 1:
        raise JdpruOracleError("INVALID_RANGE", "w_min must satisfy 0 <= w_min <= 1")
    if wmax_f < 1:
        raise JdpruOracleError("INVALID_RANGE", "w_max must satisfy w_max >= 1")

    max_var = (Fraction(1, 1) - wmin_f) * (wmax_f - Fraction(1, 1))
    deff_max = Fraction(1, 1) + max_var
    min_retention = Fraction(1, 1) / deff_max
    max_loss = Fraction(1, 1) - min_retention
    if wmax_f == wmin_f:
        p_max = Fraction(0, 1)
    else:
        p_max = (Fraction(1, 1) - wmin_f) / (wmax_f - wmin_f)
    return {
        "w_min": frac_str(wmin_f),
        "w_max": frac_str(wmax_f),
        "max_weight_variance": frac_str(max_var),
        "deff_max": frac_str(deff_max),
        "deff_max_decimal": format_exact_decimal(deff_max, 4),
        "min_neff_fraction": frac_str(min_retention),
        "min_neff_pct": format_exact_decimal(min_retention * 100, 2),
        "max_sample_loss_pct": format_exact_decimal(max_loss * 100, 2),
        "extremal_mass_at_wmax": frac_str(p_max),
    }


def compute_meng_effective_n_exact(
    sample_fraction: Any,
    data_defect_corr: Any,
    n_sample: Any = None,
) -> dict[str, Any]:
    """Exact Meng (2018) Law-of-Large-Populations effective sample size n_eff = (f/(1-f))/rho^2."""
    f = require_exact_fraction(sample_fraction, "sample_fraction")
    if f <= 0 or f >= 1:
        raise JdpruOracleError("INVALID_RANGE", "sample_fraction must satisfy 0 < f < 1")
    rho = require_exact_fraction(data_defect_corr, "data_defect_corr")
    if rho == 0 or rho < -1 or rho > 1:
        raise JdpruOracleError("INVALID_RANGE", "data_defect_corr must satisfy 0 < |rho| <= 1")

    data_quantity = (Fraction(1, 1) - f) / f
    data_defect_index = rho * rho
    n_eff_meng = Fraction(1, 1) / (data_quantity * data_defect_index)

    out: dict[str, Any] = {
        "sample_fraction": frac_str(f),
        "data_defect_corr": frac_str(rho),
        "data_quantity_factor": frac_str(data_quantity),
        "data_defect_index": frac_str(data_defect_index),
        "n_eff_meng": frac_str(n_eff_meng),
        "n_eff_meng_decimal": format_exact_decimal(n_eff_meng, 2),
    }
    if n_sample is not None:
        n_s = require_exact_int(n_sample, "n_sample")
        if n_s <= 0:
            raise JdpruOracleError("INVALID_RANGE", "n_sample must be > 0")
        eff_ratio = n_eff_meng / n_s
        out["n_sample"] = n_s
        out["efficiency_ratio"] = frac_str(eff_ratio)
        out["efficiency_pct"] = format_exact_decimal(eff_ratio * 100, 4)
        out["effective_loss_pct"] = format_exact_decimal((Fraction(1, 1) - eff_ratio) * 100, 4)
    return out


def audit_bias_variance_weighting_mse_exact(
    bias_unwt: Any,
    bias_wt: Any,
    outcome_var: Any,
    weights: Any,
) -> dict[str, Any]:
    """Exact Horvitz-Thompson / Hajek bias-variance MSE decomposition under weighting."""
    b0 = require_exact_fraction(bias_unwt, "bias_unwt")
    b1 = require_exact_fraction(bias_wt, "bias_wt")
    var_y = require_exact_fraction(outcome_var, "outcome_var")
    if var_y < 0:
        raise JdpruOracleError("INVALID_RANGE", "outcome_var must be >= 0")

    kish = compute_kish_neff_and_deff_exact(weights)
    n = kish["n"]
    deff = Fraction(kish["deff"])

    var_unwt = var_y / n
    var_wt = var_unwt * deff
    mse_unwt = (b0 * b0) + var_unwt
    mse_wt = (b1 * b1) + var_wt
    delta_mse = mse_wt - mse_unwt
    bias_sq_gain = (b0 * b0) - (b1 * b1)
    variance_penalty = var_wt - var_unwt

    return {
        "n": n,
        "deff": kish["deff"],
        "n_eff": kish["n_eff"],
        "mse_unweighted": frac_str(mse_unwt),
        "mse_weighted": frac_str(mse_wt),
        "delta_mse": frac_str(delta_mse),
        "bias_sq_reduction": frac_str(bias_sq_gain),
        "variance_penalty": frac_str(variance_penalty),
        "worsened_by_weighting": mse_wt > mse_unwt,
    }


def audit_national_raking_state_simpson_exact(
    states: Any,
    national_target_a_share: Any,
) -> dict[str, Any]:
    """Prove exact national-raking bias elimination alongside uniform state-level worsening."""
    items = require_list_or_tuple(states, "states")
    tau_a = require_exact_fraction(national_target_a_share, "national_target_a_share")
    if tau_a <= 0 or tau_a >= 1:
        raise JdpruOracleError("INVALID_RANGE", "national_target_a_share must be in (0, 1)")

    expected_keys = {"state_id", "n_a", "n_b", "mean_y_a", "mean_y_b", "true_y"}
    seen_ids: set[str] = set()
    parsed_states: list[dict[str, Any]] = []
    tot_a = 0
    tot_b = 0

    for idx, st in enumerate(items):
        if not isinstance(st, dict) or set(st.keys()) != expected_keys:
            raise JdpruOracleError("SCHEMA_ERROR", f"states[{idx}] has invalid keys")
        sid = require_non_empty_str(st["state_id"], f"states[{idx}].state_id")
        if sid in seen_ids:
            raise JdpruOracleError("DUPLICATE_ID", f"duplicate state_id: {sid}")
        seen_ids.add(sid)
        n_a = require_exact_int(st["n_a"], f"states[{idx}].n_a")
        n_b = require_exact_int(st["n_b"], f"states[{idx}].n_b")
        if n_a <= 0 or n_b <= 0:
            raise JdpruOracleError("INVALID_RANGE", f"states[{idx}] n_a and n_b must be > 0")
        y_a = require_exact_fraction(st["mean_y_a"], f"states[{idx}].mean_y_a")
        y_b = require_exact_fraction(st["mean_y_b"], f"states[{idx}].mean_y_b")
        y_true = require_exact_fraction(st["true_y"], f"states[{idx}].true_y")
        tot_a += n_a
        tot_b += n_b
        parsed_states.append(
            {
                "state_id": sid,
                "n_a": n_a,
                "n_b": n_b,
                "mean_y_a": y_a,
                "mean_y_b": y_b,
                "true_y": y_true,
            }
        )

    tot_n = tot_a + tot_b
    p_a = Fraction(tot_a, tot_n)
    p_b = Fraction(tot_b, tot_n)
    tau_b = Fraction(1, 1) - tau_a

    w_a = tau_a / p_a
    w_b = tau_b / p_b
    nat_bias_before = p_a - tau_a
    nat_a_after = (w_a * tot_a) / ((w_a * tot_a) + (w_b * tot_b))
    nat_bias_after = nat_a_after - tau_a
    deff = (p_a * w_a * w_a) + (p_b * w_b * w_b)
    n_eff = Fraction(tot_n, 1) / deff

    state_reports: list[dict[str, Any]] = []
    all_worsened = True
    sum_abs_before = Fraction(0, 1)
    sum_abs_after = Fraction(0, 1)
    for st in parsed_states:
        na, nb = st["n_a"], st["n_b"]
        est_unwt = ((na * st["mean_y_a"]) + (nb * st["mean_y_b"])) / (na + nb)
        est_rake = ((w_a * na * st["mean_y_a"]) + (w_b * nb * st["mean_y_b"])) / ((w_a * na) + (w_b * nb))
        err_unwt = est_unwt - st["true_y"]
        err_rake = est_rake - st["true_y"]
        worsened = abs(err_rake) > abs(err_unwt)
        if not worsened:
            all_worsened = False
        sum_abs_before += abs(err_unwt)
        sum_abs_after += abs(err_rake)
        state_reports.append(
            {
                "state_id": st["state_id"],
                "est_unweighted": frac_str(est_unwt),
                "est_raked": frac_str(est_rake),
                "err_unweighted": frac_str(err_unwt),
                "err_raked": frac_str(err_rake),
                "worsened": worsened,
            }
        )

    n_states = len(parsed_states)
    mae_before = sum_abs_before / n_states
    mae_after = sum_abs_after / n_states
    simpson_triggered = (abs(nat_bias_after) < abs(nat_bias_before)) and all_worsened

    return {
        "total_n": tot_n,
        "w_a": frac_str(w_a),
        "w_b": frac_str(w_b),
        "national_a_share_before": frac_str(p_a),
        "national_a_share_after": frac_str(nat_a_after),
        "national_bias_before": frac_str(nat_bias_before),
        "national_bias_after": frac_str(nat_bias_after),
        "national_deff": frac_str(deff),
        "national_n_eff": frac_str(n_eff),
        "state_mae_before": frac_str(mae_before),
        "state_mae_after": frac_str(mae_after),
        "all_states_worsened": all_worsened,
        "simpson_worsening_triggered": simpson_triggered,
        "states": state_reports,
    }


def audit_ces_tail_conservation_and_drift(
    n_obs: Any,
    matching_gt20: Any,
    moved_below20: Any,
    stayed_gt20: Any,
    crossed_above20: Any,
    weighted_gt20: Any,
    readme_metrics: Any,
    csv_metrics: Any,
) -> dict[str, Any]:
    """Verify exact |error| > 20 tail-flow conservation and README-vs-CSV numeric drift."""
    n_i = require_exact_int(n_obs, "n_obs")
    if n_i <= 0:
        raise JdpruOracleError("INVALID_RANGE", "n_obs must be > 0")
    counts = {
        "matching_gt20": require_exact_int(matching_gt20, "matching_gt20"),
        "moved_below20": require_exact_int(moved_below20, "moved_below20"),
        "stayed_gt20": require_exact_int(stayed_gt20, "stayed_gt20"),
        "crossed_above20": require_exact_int(crossed_above20, "crossed_above20"),
        "weighted_gt20": require_exact_int(weighted_gt20, "weighted_gt20"),
    }
    for name, val in counts.items():
        if val < 0 or val > n_i:
            raise JdpruOracleError("INVALID_RANGE", f"{name} must satisfy 0 <= {val} <= {n_i}")

    if counts["matching_gt20"] - counts["moved_below20"] != counts["stayed_gt20"]:
        raise JdpruOracleError("TAIL_CONSERVATION_VIOLATION", "matching_gt20 - moved_below20 != stayed_gt20")
    if counts["stayed_gt20"] + counts["crossed_above20"] != counts["weighted_gt20"]:
        raise JdpruOracleError("TAIL_CONSERVATION_VIOLATION", "stayed_gt20 + crossed_above20 != weighted_gt20")
    if counts["matching_gt20"] + counts["crossed_above20"] > n_i:
        raise JdpruOracleError("TAIL_CONSERVATION_VIOLATION", "matching_gt20 + crossed_above20 exceeds n_obs")

    if not isinstance(readme_metrics, dict) or not isinstance(csv_metrics, dict):
        raise JdpruOracleError("TYPE_ERROR", "readme_metrics and csv_metrics must be dicts")
    if len(readme_metrics) == 0 or set(readme_metrics.keys()) != set(csv_metrics.keys()):
        raise JdpruOracleError("SCHEMA_ERROR", "readme_metrics and csv_metrics must have identical non-empty keys")
    validated_keys = sorted(require_non_empty_str(k, "metric_key") for k in readme_metrics.keys())
    if len(set(validated_keys)) != len(readme_metrics):
        raise JdpruOracleError("DUPLICATE_ID", "metric keys collide after whitespace normalization")

    readme_norm = {require_non_empty_str(k, "metric_key"): v for k, v in readme_metrics.items()}
    csv_norm = {require_non_empty_str(k, "metric_key"): v for k, v in csv_metrics.items()}

    drift_rows: list[dict[str, Any]] = []
    drift_count = 0
    for k_str in validated_keys:
        r_val = require_exact_fraction(readme_norm[k_str], f"readme_metrics[{k_str}]")
        c_val = require_exact_fraction(csv_norm[k_str], f"csv_metrics[{k_str}]")
        delta = c_val - r_val
        drifted = delta != 0
        if drifted:
            drift_count += 1
        drift_rows.append(
            {
                "metric": k_str,
                "readme_value": frac_str(r_val),
                "csv_value": frac_str(c_val),
                "delta_csv_minus_readme": frac_str(delta),
                "drifted": drifted,
            }
        )

    match_share = Fraction(counts["matching_gt20"], n_i)
    stayed_share = Fraction(counts["stayed_gt20"], n_i)
    wtd_share = Fraction(counts["weighted_gt20"], n_i)
    net_delta = counts["weighted_gt20"] - counts["matching_gt20"]

    return {
        "n_obs": n_i,
        "stayed_le20": n_i - counts["matching_gt20"] - counts["crossed_above20"],
        "tail_conservation_verified": True,
        "matching_gt20_share": frac_str(match_share),
        "matching_gt20_pct": format_exact_decimal(match_share * 100, 2),
        "stayed_gt20_share": frac_str(stayed_share),
        "stayed_gt20_pct": format_exact_decimal(stayed_share * 100, 2),
        "weighted_gt20_share": frac_str(wtd_share),
        "weighted_gt20_pct": format_exact_decimal(wtd_share * 100, 2),
        "net_tail_delta": net_delta,
        "tail_worsened": net_delta > 0,
        "drift_checked_count": len(drift_rows),
        "drift_count": drift_count,
        "all_metrics_aligned": drift_count == 0,
        "drift_rows": drift_rows,
    }
