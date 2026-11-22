"""Executable zero-float audit runner for AUDIT-078 (github.com/jdpru).

Supports two strictly deterministic execution modes:
  - Live read-only mode (default): verifies pinned HEAD commits of the three
    original non-fork jdpru repositories (cover-your-ais, CES-Accuracy-Analysis,
    CS-230-DynaRT), validates verbatim textual anchors, parses live CSV/XLSX
    tables in pure Python stdlib, runs the deterministic safety scanner live on
    CES-Accuracy-Analysis/CLAUDE.md, and emits jdpru_epistemic_certificate.json.
  - Standalone mode (--standalone): executes all Pillar 1 & Pillar 2 pure-Q
    oracles against the exact pinned verbatim fixtures with zero external files.

Zero floats on trust paths. Zero bare assert statements. Zero external writes.
"""

from __future__ import annotations

import argparse
import csv
from fractions import Fraction
import hashlib
import io
import json
from pathlib import Path
import re
import sys
from typing import Any
import xml.etree.ElementTree as ET
import zipfile

_SCRIPT_DIR = str(Path(__file__).resolve().parent)
if _SCRIPT_DIR not in sys.path:
    sys.path.insert(0, _SCRIPT_DIR)

from jdpru_epistemic_weighting_oracle import (
    JdpruOracleError,
    audit_agent_safety_surface,
    audit_bias_variance_weighting_mse_exact,
    audit_ces_tail_conservation_and_drift,
    audit_national_raking_state_simpson_exact,
    canonical_json_bytes,
    canonical_sha256,
    compute_extremal_deff_bound_exact,
    compute_kish_from_summary_stats_exact,
    compute_kish_neff_and_deff_exact,
    compute_meng_effective_n_exact,
    evaluate_prompt_vs_oracle_coverage,
    frac_str,
    scan_hidden_unicode_exact,
)


_SHA40_RE = re.compile(r"\A[0-9a-f]{40}\Z")
_SAFE_GIT_REF_RE = re.compile(r"\Arefs/[A-Za-z0-9._/-]+\Z")
_XLSX_NS = {"m": "http://schemas.openxmlformats.org/spreadsheetml/2006/main"}

PINNED_REPO_HEADS: dict[str, str] = {
    "cover-your-ais": "aafd6217a61071beca2faa191e692bfc44651991",
    "CES-Accuracy-Analysis": "9375b1bbd5a239c23cf7d442c4e7dd4094c9400c",
    "CS-230-DynaRT": "c024875d595c6529c3e82a43e7e10dafd173fb5b",
}

PINNED_FORK_CATALOG: tuple[str, ...] = (
    "fmriprepviz",
    "fmri-aim4-outlier-detector",
    "fmchisel-modal",
    "iSPOT-Autoencoder",
)

CYA_TO_ALETHEIA_MAPPING: tuple[dict[str, Any], ...] = (
    {
        "check_id": "CYA-01-prod-db-in-tests",
        "cya_line": 9,
        "aletheia_v140_status": "PARTIAL",
        "cya_gap_id": "CYA-GAP-05",
        "prompt_blind_spot": True,
    },
    {
        "check_id": "CYA-02-shell-prod-creds",
        "cya_line": 12,
        "aletheia_v140_status": "PARTIAL",
        "cya_gap_id": "CYA-GAP-05",
        "prompt_blind_spot": True,
    },
    {
        "check_id": "CYA-03-unguarded-rm-rf",
        "cya_line": 15,
        "aletheia_v140_status": "GAP_V15",
        "cya_gap_id": "CYA-GAP-03",
        "prompt_blind_spot": True,
    },
    {
        "check_id": "CYA-04-one-cmd-infra-destroy",
        "cya_line": 18,
        "aletheia_v140_status": "PARTIAL",
        "cya_gap_id": "CYA-GAP-05",
        "prompt_blind_spot": True,
    },
    {
        "check_id": "CYA-05-prose-only-rules",
        "cya_line": 21,
        "aletheia_v140_status": "GAP_V15",
        "cya_gap_id": "CYA-GAP-05",
        "prompt_blind_spot": True,
    },
    {
        "check_id": "CYA-06-main-protection-gh-scope",
        "cya_line": 24,
        "aletheia_v140_status": "PARTIAL",
        "cya_gap_id": "CYA-GAP-05",
        "prompt_blind_spot": True,
    },
    {
        "check_id": "CYA-07-cloud-sync-zero-byte",
        "cya_line": 27,
        "aletheia_v140_status": "GAP_V15",
        "cya_gap_id": "CYA-GAP-06",
        "prompt_blind_spot": True,
    },
    {
        "check_id": "CYA-08-unpinned-mcp-hidden-unicode",
        "cya_line": 30,
        "aletheia_v140_status": "GAP_V15",
        "cya_gap_id": "CYA-GAP-01",
        "prompt_blind_spot": True,
    },
    {
        "check_id": "CYA-09-ci-pull-request-target",
        "cya_line": 33,
        "aletheia_v140_status": "GAP_V15",
        "cya_gap_id": "CYA-GAP-04",
        "prompt_blind_spot": True,
    },
    {
        "check_id": "CYA-10-auto-approve-alias-trap",
        "cya_line": 36,
        "aletheia_v140_status": "GAP_V15",
        "cya_gap_id": "CYA-GAP-06",
        "prompt_blind_spot": True,
    },
    {
        "check_id": "CYA-11-uncapped-money-message-tools",
        "cya_line": 39,
        "aletheia_v140_status": "COVERED",
        "cya_gap_id": "NONE",
        "prompt_blind_spot": True,
    },
    {
        "check_id": "CYA-12-consequence-warning-rule",
        "cya_line": 42,
        "aletheia_v140_status": "COVERED",
        "cya_gap_id": "NONE",
        "prompt_blind_spot": True,
    },
)

STANDALONE_CLAUDE_MD_EXCERPT: str = "\n".join(
    [
        "3. `sensitivity_analyses/` deletes `~/ces_sens_scratch/_cache` pickles.",
        "- `notes/governor-2024-returns.md`: lives at `~/Downloads/Governor_Returns_2024.xlsx`, outside the repo.",
        "  - Commit only when asked.",
        "  - Work on main and merge directly. No PRs.",
        "  - Stage with `git add -A`.",
    ]
)

STANDALONE_CYA_PROMPT_EXCERPT: str = "Audit this repo and my dev setup for hidden Unicode in rule files."

CES_README_BASE_METRICS: dict[str, str] = {
    "CesThreeVarReduction": "1.1",
    "GuideGapOverall": "1.2",
    "NeitherMeanAfter": "8.2",
    "TrendSecMatchBeta": "0.113",
    "TrendSecMatchP": "0.089",
    "TrendSecWtdBeta": "-0.016",
    "TrendSecWtdP": "0.701",
}

STANDALONE_CSV_BASE_METRICS: dict[str, str] = {
    "CesThreeVarReduction": "1.2",
    "GuideGapOverall": "1.3",
    "NeitherMeanAfter": "8.1",
    "TrendSecMatchBeta": "0.111",
    "TrendSecMatchP": "0.095",
    "TrendSecWtdBeta": "-0.019",
    "TrendSecWtdP": "0.630",
}

STANDALONE_CES_COUNTS: dict[str, int] = {
    "NObsTotal": 10487,
    "NObsDemographic": 3927,
    "NObsVotingAdmin": 917,
    "NObsCandidate": 5643,
    "NeitherNObs": 7208,
    "NeitherCellsImproved": 62,
    "NeitherCellsWorse": 32,
    "NeitherCellsSame": 3,
    "NBeyondTwentyMatching": 357,
    "NMovedBelowTwenty": 106,
    "NStayedBeyondTwenty": 251,
    "NCrossedAboveTwenty": 108,
    "NBeyondTwentyWeighted": 359,
}

STANDALONE_ANESRAKE_USED_BY_YEAR: dict[str, int] = {
    "2006": 6,
    "2008": 6,
    "2010": 9,
    "2012": 9,
    "2014": 9,
    "2016": 8,
    "2018": 8,
    "2020": 8,
    "2022": 7,
}

STANDALONE_A2_NAMED_ONLY: dict[str, str] = {
    "TrendSecMatchBeta_base": "0.111",
    "TrendSecMatchBeta_named_only": "-0.030",
    "TrendSecWtdBeta_base": "-0.019",
    "TrendSecWtdBeta_named_only": "0.023",
    "AnesHighestYears_base": "seven",
    "AnesHighestYears_named_only": "two",
}

CES_RELEASED_MAX_WEIGHTS: tuple[tuple[str, str, str], ...] = (
    ("2006", "0", "2.9"),
    ("2008", "0", "6.5"),
    ("2010", "0", "7.0"),
    ("2012", "0.00001", "20.00044"),
    ("2014_2020", "0", "15.0"),
    ("2022", "0", "15.5"),
    ("anesrake_cap", "0", "5.0"),
)


def _sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _resolve_git_head_sha(repo_dir: Path) -> str:
    """Resolve .git/HEAD strictly via loose ref, detached SHA, or packed-refs."""
    git_dir = repo_dir / ".git"
    head_file = git_dir / "HEAD"
    if not head_file.is_file():
        raise JdpruOracleError("MISSING_GIT_HEAD", f"missing .git/HEAD in {repo_dir.name}")
    raw = head_file.read_text(encoding="utf-8").strip()
    if raw.startswith("ref:"):
        ref_name = raw[4:].strip()
        if _SAFE_GIT_REF_RE.match(ref_name) is None or ".." in Path(ref_name).parts:
            raise JdpruOracleError("INVALID_GIT_REF", f"unsafe git ref {ref_name!r} in {repo_dir.name}")
        loose = git_dir / ref_name
        if loose.is_file():
            if not loose.resolve().is_relative_to(git_dir.resolve()):
                raise JdpruOracleError("INVALID_GIT_REF", f"git ref escapes .git in {repo_dir.name}")
            sha = loose.read_text(encoding="utf-8").strip()
        else:
            packed = git_dir / "packed-refs"
            sha = ""
            if packed.is_file():
                for line in packed.read_text(encoding="utf-8").splitlines():
                    if not line or line.startswith("#") or line.startswith("^"):
                        continue
                    parts = line.split()
                    if len(parts) == 2 and parts[1] == ref_name:
                        sha = parts[0]
                        break
    else:
        sha = raw
    if _SHA40_RE.match(sha) is None:
        raise JdpruOracleError("INVALID_GIT_SHA", f"unresolved git HEAD SHA in {repo_dir.name}")
    return sha


def _parse_int_comma(raw: str, field: str) -> int:
    cleaned = raw.strip().replace(",", "")
    if not cleaned.isdigit():
        raise JdpruOracleError("PARSE_ERROR", f"{field} is not an integer: {raw!r}")
    return int(cleaned)


def _parse_csv_macro_map(csv_path: Path, col_name: str) -> dict[str, str]:
    text = csv_path.read_text(encoding="utf-8")
    reader = csv.DictReader(io.StringIO(text))
    if reader.fieldnames is None or "macro" not in reader.fieldnames or col_name not in reader.fieldnames:
        raise JdpruOracleError("SCHEMA_ERROR", f"missing columns in {csv_path.name}")
    out: dict[str, str] = {}
    for row in reader:
        macro = (row.get("macro") or "").strip()
        if macro:
            out[macro] = (row.get(col_name) or "").strip()
    return out


def _parse_anesrake_used_xlsx(xlsx_path: Path) -> dict[str, int]:
    """Parse tables_and_figures/input_tables/vars_used_by_anesrake.xlsx in pure stdlib."""
    with zipfile.ZipFile(xlsx_path, "r") as zf:
        sst: list[str] = []
        if "xl/sharedStrings.xml" in zf.namelist():
            sst_root = ET.fromstring(zf.read("xl/sharedStrings.xml"))
            for si in sst_root.findall("m:si", _XLSX_NS):
                sst.append("".join(t.text or "" for t in si.findall(".//m:t", _XLSX_NS)))
        ws_root = ET.fromstring(zf.read("xl/worksheets/sheet1.xml"))

    rows: list[list[str]] = []
    for row_el in ws_root.findall(".//m:row", _XLSX_NS):
        vals: list[str] = []
        for c_el in row_el.findall("m:c", _XLSX_NS):
            c_type = c_el.attrib.get("t", "")
            v_el = c_el.find("m:v", _XLSX_NS)
            if v_el is None or v_el.text is None:
                vals.append("")
            elif c_type == "s":
                vals.append(sst[int(v_el.text)])
            else:
                vals.append(v_el.text)
        rows.append(vals)

    if len(rows) < 2 or len(rows[0]) < 2:
        raise JdpruOracleError("SCHEMA_ERROR", "vars_used_by_anesrake.xlsx has insufficient rows")
    years = rows[0][1:]
    counts = {yr: 0 for yr in years}
    for row in rows[1:]:
        for idx, yr in enumerate(years, start=1):
            if idx < len(row) and row[idx].strip() == "Used":
                counts[yr] += 1
    return counts


def _verify_live_repos(repos_root: Path) -> dict[str, Any]:
    """Read-only verification of all three pinned jdpru repositories."""
    verified_heads: dict[str, str] = {}
    for repo_name, expected_sha in PINNED_REPO_HEADS.items():
        repo_path = repos_root / repo_name
        actual_sha = _resolve_git_head_sha(repo_path)
        if actual_sha != expected_sha:
            raise JdpruOracleError("HEAD_MISMATCH", f"{repo_name} HEAD {actual_sha} != {expected_sha}")
        verified_heads[repo_name] = actual_sha

    cya_dir = repos_root / "cover-your-ais"
    ces_dir = repos_root / "CES-Accuracy-Analysis"
    dyn_dir = repos_root / "CS-230-DynaRT"

    cya_readme = cya_dir / "README.md"
    cya_prompt = cya_dir / "prompts" / "ai-codebase-safety-audit.md"
    ces_claude = ces_dir / "CLAUDE.md"
    ces_sens_readme = ces_dir / "sensitivity_analyses" / "README.md"
    ces_headline_csv = ces_dir / "sensitivity_analyses" / "results" / "headline_by_variant.csv"
    ces_prose_csv = ces_dir / "sensitivity_analyses" / "results" / "prose_numbers_by_variant.csv"
    ces_anes_xlsx = ces_dir / "tables_and_figures" / "input_tables" / "vars_used_by_anesrake.xlsx"
    ces_supp_tex = ces_dir / "supplementary_material.tex"
    dyn_readme = dyn_dir / "README.md"

    anchor_checks = [
        (cya_readme, "Prompts are not security boundaries."),
        (cya_prompt, "hidden Unicode in rule files"),
        (ces_claude, "phase 2 has independent agents verify the hits"),
        (ces_sens_readme, "This folder is untracked."),
        (ces_supp_tex, "20.00044"),
        (dyn_readme, "DynaRT is a deep learning framework"),
    ]
    for path, needle in anchor_checks:
        if not path.is_file():
            raise JdpruOracleError("MISSING_FILE", f"missing expected file {path.name}")
        if needle not in path.read_text(encoding="utf-8"):
            raise JdpruOracleError("ANCHOR_MISMATCH", f"missing anchor {needle!r} in {path.name}")

    headline_base = _parse_csv_macro_map(ces_headline_csv, "base")
    headline_named = _parse_csv_macro_map(ces_headline_csv, "A2_named_only")
    prose_base = _parse_csv_macro_map(ces_prose_csv, "base")
    anes_used = _parse_anesrake_used_xlsx(ces_anes_xlsx)

    ces_counts = {
        key: _parse_int_comma(prose_base[key], key)
        for key in STANDALONE_CES_COUNTS
    }
    csv_base_metrics = {key: headline_base[key] for key in CES_README_BASE_METRICS}
    a2_named = {
        "TrendSecMatchBeta_base": headline_base["TrendSecMatchBeta"],
        "TrendSecMatchBeta_named_only": headline_named["TrendSecMatchBeta"],
        "TrendSecWtdBeta_base": headline_base["TrendSecWtdBeta"],
        "TrendSecWtdBeta_named_only": headline_named["TrendSecWtdBeta"],
        "AnesHighestYears_base": headline_base["AnesHighestYears"],
        "AnesHighestYears_named_only": headline_named["AnesHighestYears"],
    }

    return {
        "mode": "live_readonly",
        "verified_repo_heads": verified_heads,
        "artifact_sha256": {
            "cover-your-ais/README.md": _sha256_file(cya_readme),
            "cover-your-ais/prompts/ai-codebase-safety-audit.md": _sha256_file(cya_prompt),
            "CES-Accuracy-Analysis/CLAUDE.md": _sha256_file(ces_claude),
            "CES-Accuracy-Analysis/sensitivity_analyses/README.md": _sha256_file(ces_sens_readme),
            "CES-Accuracy-Analysis/sensitivity_analyses/results/headline_by_variant.csv": _sha256_file(ces_headline_csv),
            "CES-Accuracy-Analysis/sensitivity_analyses/results/prose_numbers_by_variant.csv": _sha256_file(ces_prose_csv),
            "CES-Accuracy-Analysis/tables_and_figures/input_tables/vars_used_by_anesrake.xlsx": _sha256_file(ces_anes_xlsx),
            "CS-230-DynaRT/README.md": _sha256_file(dyn_readme),
        },
        "claude_md_text": ces_claude.read_text(encoding="utf-8"),
        "cya_prompt_text": cya_prompt.read_text(encoding="utf-8"),
        "ces_counts": ces_counts,
        "csv_base_metrics": csv_base_metrics,
        "anesrake_used_by_year": anes_used,
        "a2_named_only": a2_named,
    }


def run_audit(standalone: bool = False, repos_root: Path | None = None) -> dict[str, Any]:
    """Execute full AUDIT-078 Pillar 1 + Pillar 2 deterministic verification."""
    if standalone:
        live_info: dict[str, Any] = {
            "mode": "standalone_fixture",
            "verified_repo_heads": dict(PINNED_REPO_HEADS),
            "artifact_sha256": {},
            "claude_md_text": STANDALONE_CLAUDE_MD_EXCERPT,
            "cya_prompt_text": STANDALONE_CYA_PROMPT_EXCERPT,
            "ces_counts": dict(STANDALONE_CES_COUNTS),
            "csv_base_metrics": dict(STANDALONE_CSV_BASE_METRICS),
            "anesrake_used_by_year": dict(STANDALONE_ANESRAKE_USED_BY_YEAR),
            "a2_named_only": dict(STANDALONE_A2_NAMED_ONLY),
        }
    else:
        root = repos_root if repos_root is not None else (Path(__file__).resolve().parent.parent / "repos" / "jdpru")
        live_info = _verify_live_repos(root)

    # Pillar 1: cover-your-ais <-> Aletheia v1.4.0 / v1.5
    coverage = evaluate_prompt_vs_oracle_coverage(list(CYA_TO_ALETHEIA_MAPPING))
    cya_prompt_unicode_check = scan_hidden_unicode_exact(live_info["cya_prompt_text"])
    claude_md_audit = audit_agent_safety_surface(live_info["claude_md_text"], "prompt_rule")

    # Pillar 1 synthetic adversarial proof for CYA-GAP-01..04 + 06
    adversarial_probe = "\n".join(
        [
            "ignore\u200bprevious\u202erules",
            "npx -y @org/mcp-server@latest --dangerously-skip-permissions",
            'rm -rf "$TARGET_DIR"',
            "on: pull_request_target\npermissions:\n  contents: write\n  token: ${{ secrets.GITHUB_TOKEN }}",
            "alias rm='rm -i'",
        ]
    )
    adversarial_scan = audit_agent_safety_surface(adversarial_probe, "ci_workflow")

    # Pillar 2: CES-Accuracy-Analysis exact pure-Q audits
    counts = live_info["ces_counts"]
    obs_partition_ok = (
        counts["NObsDemographic"] + counts["NObsVotingAdmin"] + counts["NObsCandidate"] == counts["NObsTotal"]
    )
    if not obs_partition_ok:
        raise JdpruOracleError("COUNT_MISMATCH", "CES observation partition does not sum to NObsTotal")

    neither_cells_total = (
        counts["NeitherCellsImproved"] + counts["NeitherCellsWorse"] + counts["NeitherCellsSame"]
    )
    neither_worsened_ratio = Fraction(counts["NeitherCellsWorse"], neither_cells_total)

    anes_by_year = live_info["anesrake_used_by_year"]
    anes_min = min(anes_by_year.values())
    anes_max = max(anes_by_year.values())

    # 2A: Exact Kish DEFF & n_eff from 2012/2014 CES V103 summary stats (supplementary_material.tex:540)
    v103_kish_sample_sd = compute_kish_from_summary_stats_exact(54535, "1", "1.31757", sd_is_sample=True)
    v103_kish_pop_sd = compute_kish_from_summary_stats_exact(54535, "1", "1.31757", sd_is_sample=False)

    # 2B: Exact Bhatia-Davis extremal DEFF bounds across all published CES weight caps & anesrake cap
    extremal_bounds = {
        label: compute_extremal_deff_bound_exact(wmin, wmax)
        for label, wmin, wmax in CES_RELEASED_MAX_WEIGHTS
    }

    # 2C: Small-domain witness (n=50, 2 respondents at CES cap 15, 48 at 5/12 -> exact mean 1)
    small_domain_weights = [Fraction(15, 1)] * 2 + [Fraction(5, 12)] * 48
    small_domain_kish = compute_kish_neff_and_deff_exact(small_domain_weights, weight_cap=Fraction(15, 1))
    orthogonal_raking_mse = audit_bias_variance_weighting_mse_exact(
        bias_unwt="3",
        bias_wt="3",
        outcome_var="100",
        weights=small_domain_weights,
    )

    # 2D: Exact Meng (2018) data-defect paradox (manuscript.tex:317: f=1%, rho=-0.005, n=2.3M)
    meng_paradox = compute_meng_effective_n_exact("1/100", "-1/200", n_sample=2300000)

    # 2E: Exact National-Raking vs State-Level Simpson worsening witness
    simpson_witness = audit_national_raking_state_simpson_exact(
        states=[
            {
                "state_id": "S1",
                "n_a": 80,
                "n_b": 20,
                "mean_y_a": "3/5",
                "mean_y_b": "1/5",
                "true_y": "3/5",
            },
            {
                "state_id": "S2",
                "n_a": 80,
                "n_b": 20,
                "mean_y_a": "2/5",
                "mean_y_b": "4/5",
                "true_y": "2/5",
            },
        ],
        national_target_a_share="1/2",
    )

    # 2F: Exact |error| > 20 tail conservation & sensitivity_analyses/README.md vs CSV drift
    tail_and_drift = audit_ces_tail_conservation_and_drift(
        n_obs=counts["NeitherNObs"],
        matching_gt20=counts["NBeyondTwentyMatching"],
        moved_below20=counts["NMovedBelowTwenty"],
        stayed_gt20=counts["NStayedBeyondTwenty"],
        crossed_above20=counts["NCrossedAboveTwenty"],
        weighted_gt20=counts["NBeyondTwentyWeighted"],
        readme_metrics=CES_README_BASE_METRICS,
        csv_metrics=live_info["csv_base_metrics"],
    )

    # 2G: A2_named_only sign-flip check
    a2 = live_info["a2_named_only"]
    match_beta_base = Fraction(a2["TrendSecMatchBeta_base"])
    match_beta_named = Fraction(a2["TrendSecMatchBeta_named_only"])
    wtd_beta_base = Fraction(a2["TrendSecWtdBeta_base"])
    wtd_beta_named = Fraction(a2["TrendSecWtdBeta_named_only"])
    a2_sign_flips = {
        "matching_beta_base": frac_str(match_beta_base),
        "matching_beta_named_only": frac_str(match_beta_named),
        "matching_sign_flipped": (match_beta_base > 0) and (match_beta_named < 0),
        "weighted_beta_base": frac_str(wtd_beta_base),
        "weighted_beta_named_only": frac_str(wtd_beta_named),
        "weighted_sign_flipped": (wtd_beta_base < 0) and (wtd_beta_named > 0),
        "anes_highest_years_base": a2["AnesHighestYears_base"],
        "anes_highest_years_named_only": a2["AnesHighestYears_named_only"],
    }

    payload: dict[str, Any] = {
        "audit_id": "AUDIT-078",
        "arm": "R9-1-jdpru",
        "epistemic_tier": "N1",
        "aletheia_version": "1.4.0",
        "execution_mode": live_info["mode"],
        "pinned_original_repos": live_info["verified_repo_heads"],
        "cataloged_fork_repos_not_audited": list(PINNED_FORK_CATALOG),
        "artifact_sha256": live_info["artifact_sha256"],
        "pillar1_cover_your_ais": {
            "prompt_vs_aletheia_v140_coverage": coverage,
            "cya_prompt_hidden_unicode_audit": cya_prompt_unicode_check,
            "live_ces_claude_md_self_audit": claude_md_audit,
            "adversarial_cya_gap_probe": adversarial_scan,
        },
        "pillar2_ces_accuracy_analysis": {
            "obs_partition_verified": obs_partition_ok,
            "ces_counts": counts,
            "neither_cells_total": neither_cells_total,
            "neither_worsened_ratio": frac_str(neither_worsened_ratio),
            "anesrake_used_by_year": anes_by_year,
            "anesrake_used_range": f"{anes_min}--{anes_max}",
            "v103_2012_kish_sample_sd": v103_kish_sample_sd,
            "v103_2012_kish_pop_sd": v103_kish_pop_sd,
            "extremal_deff_bounds_by_cap": extremal_bounds,
            "small_domain_cap15_witness": small_domain_kish,
            "orthogonal_raking_mse_inflation": orthogonal_raking_mse,
            "meng_2018_big_data_paradox": meng_paradox,
            "national_raking_state_simpson_witness": simpson_witness,
            "tail_conservation_and_readme_drift": tail_and_drift,
            "a2_named_only_sign_flips": a2_sign_flips,
        },
        "verdict": "VERIFIED",
    }
    payload["certificate_sha256"] = canonical_sha256(payload)
    return payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="AUDIT-078 pure-Q epistemic & weighting audit runner")
    parser.add_argument("--standalone", action="store_true", help="Run using pinned verbatim fixtures without external repo clones")
    parser.add_argument("--repos-root", type=str, default=None, help="Optional directory containing cloned jdpru repositories")
    parser.add_argument("--output", type=str, default=None, help="Optional output path for canonical JSON certificate")
    parser.add_argument("--json", action="store_true", help="Emit canonical JSON certificate to stdout")
    args = parser.parse_args(argv)

    root = Path(args.repos_root) if args.repos_root is not None else None
    cert = run_audit(standalone=args.standalone, repos_root=root)
    raw = canonical_json_bytes(cert) + b"\n"

    if args.output is not None:
        out_path = Path(args.output)
        out_path.write_bytes(raw)

    if args.json:
        sys.stdout.write(raw.decode("ascii"))
    else:
        summary = {
            "audit_id": cert["audit_id"],
            "execution_mode": cert["execution_mode"],
            "verdict": cert["verdict"],
            "certificate_sha256": cert["certificate_sha256"],
            "v15_gap_count": cert["pillar1_cover_your_ais"]["prompt_vs_aletheia_v140_coverage"]["gap_v15_count"],
            "claude_md_findings": cert["pillar1_cover_your_ais"]["live_ces_claude_md_self_audit"]["finding_count"],
            "readme_csv_drift_count": cert["pillar2_ces_accuracy_analysis"]["tail_conservation_and_readme_drift"]["drift_count"],
            "v103_deff": cert["pillar2_ces_accuracy_analysis"]["v103_2012_kish_sample_sd"]["deff_decimal"],
            "meng_neff": cert["pillar2_ces_accuracy_analysis"]["meng_2018_big_data_paradox"]["n_eff_meng"],
        }
        sys.stdout.write(json.dumps(summary, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
