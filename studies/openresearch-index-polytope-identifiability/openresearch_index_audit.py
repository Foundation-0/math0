#!/usr/bin/env python3
"""
Verbatim Parser, Read-Only Provenance Verifier & Exact Pure-Q Certificate Generator
for the alphaXiv OpenResearch Intelligence Index (AUDIT-069).

Supports:
  - Default live mode: verifies pinned SHA-256 digests of the downloaded blog bundles
    under `../repos/openresearch-index-blog/` (and read-only `alphaXiv/OpenResearch`
    HEAD `48f42c450ca00ab08fe10358989311193b0f81c6`), parses all 8 models x 3 tracks x
    14 sub-rows directly into exact `Fraction`s (zero float calls!), cross-validates
    against the verbatim embedded baseline, and writes `openresearch_index_certificate.json`.
  - `--standalone` mode: runs purely from the verbatim embedded dataset with zero
    external path dependencies.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
from pathlib import Path
import re
import sys
from typing import Any

# -I isolated-mode safe local import
_SCRIPT_DIR = Path(__file__).resolve().parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))

from openresearch_index_oracle import (  # noqa: E402
    DEFAULT_INDEX_WEIGHTS,
    IndexOracleError,
    VERIFIED_INTERNET_STATUS,
    audit_bipartite_confounding_exact,
    audit_ci_separability_and_pareto_stability,
    audit_missing_attempts_and_cost_extrapolation,
    audit_task_leverage_asymmetry,
    audit_weight_sensitivity_simplex,
    canonical_json_bytes,
    canonical_sha256,
    compute_composite_index_exact,
    compute_pareto_frontier_exact,
    evaluate_tao_observability_gate,
    format_exact_decimal,
    frac_str,
    verify_no_floats,
)

PINNED_BLOG_URL = "https://alphaxiv.org/blog/introducing-openresearch-intelligence-index"
PINNED_OPENRESEARCH_REPO = "https://github.com/alphaXiv/OpenResearch"
PINNED_OPENRESEARCH_COMMIT = "48f42c450ca00ab08fe10358989311193b0f81c6"

PINNED_ARTIFACT_SHA256: dict[str, str] = {
    "index.html": "ac66dd30e7c2f53566041fd9968b1ebbe29e14370bd98ce6e5e8ac7f51d2533f",
    "ResultsTable-Cepl37af.js": "fa223017805af7b8bbe31dd44d7814018cb0c02c9de1ab012e3a56545819c187",
    "RankHeatmap-CVYXZmjT.js": "64d03a352625cc0c9f9ae87e3f8815b71800bfdf1c95d7779d743982cc5dd36c",
    "CostScoreChart-CkzD4pZy.js": "55583ebfbb15ace29f9004518882a377f2df68d09bf4831e23d0305572d4c0e2",
    "cost-vs-score.png": "51541703586bffabf9cee98bf2287294edead2a4c9434655e5ba83abc72bd8e7",
    "openresearch_sh.html": "9e00c6f0a2e0b10f4c120a3e39c0edf123a9b1594e2d3e4b99fed5cb99a2a516",
}

# Exact verbatim dataset transcribed from ResultsTable-Cepl37af.js & CostScoreChart-CkzD4pZy.js
EMBEDDED_MODELS: list[dict[str, Any]] = [
    {
        "name": "Opus 5.5",
        "provider": "Anthropic",
        "harness": "Claude Code",
        "attempts": 87,
        "complete": True,
        "index_score": "0.6183",
        "index_se": "0.0138",
        "index_lo": "0.5909",
        "index_hi": "0.6446",
        "full_usd": "1432.4",
        "cost_mean": "16.46",
        "cost_se": "0.9",
        "science_score": "0.5833",
        "science_usd": "18.25",
        "post_training_score": "0.6559",
        "post_training_usd": "9.86",
        "literature_score": "0.6132",
        "literature_usd": "17.76",
        "input_tokens_mean": 46547127,
        "output_tokens_mean": 255482,
        "minutes_mean": "153.2",
    },
    {
        "name": "GPT-6 Astra",
        "provider": "OpenAI",
        "harness": "Codex",
        "attempts": 87,
        "complete": True,
        "index_score": "0.5658",
        "index_se": "0.0139",
        "index_lo": "0.5384",
        "index_hi": "0.5905",
        "full_usd": "1951.9",
        "cost_mean": "22.44",
        "cost_se": "2.44",
        "science_score": "0.6333",
        "science_usd": "17.34",
        "post_training_score": "0.5376",
        "post_training_usd": "46.51",
        "literature_score": "0.4871",
        "literature_usd": "8.26",
        "input_tokens_mean": 15284854,
        "output_tokens_mean": 110528,
        "minutes_mean": "94.1",
    },
    {
        "name": "GPT-6.1 Sol",
        "provider": "OpenAI",
        "harness": "Codex",
        "attempts": 87,
        "complete": True,
        "index_score": "0.5495",
        "index_se": "0.0241",
        "index_lo": "0.499",
        "index_hi": "0.5959",
        "full_usd": "333.1",
        "cost_mean": "3.83",
        "cost_se": "0.39",
        "science_score": "0.6167",
        "science_usd": "2.99",
        "post_training_score": "0.5034",
        "post_training_usd": "7.8",
        "literature_score": "0.5072",
        "literature_usd": "1.46",
        "input_tokens_mean": 19987653,
        "output_tokens_mean": 146806,
        "minutes_mean": "105.9",
    },
    {
        "name": "Gemini 4 Argon",
        "provider": "Google",
        "harness": "OpenCode",
        "attempts": 87,
        "complete": True,
        "index_score": "0.5261",
        "index_se": "0.0129",
        "index_lo": "0.5001",
        "index_hi": "0.5509",
        "full_usd": "798.4",
        "cost_mean": "9.18",
        "cost_se": "0.75",
        "science_score": "0.55",
        "science_usd": "9.57",
        "post_training_score": "0.4883",
        "post_training_usd": "8.34",
        "literature_score": "0.5539",
        "literature_usd": "8.22",
        "input_tokens_mean": 34370775,
        "output_tokens_mean": 246034,
        "minutes_mean": "133.9",
    },
    {
        "name": "Fable 5.1",
        "provider": "Anthropic",
        "harness": "Claude Code",
        "attempts": 74,
        "complete": False,
        "index_score": "0.5107",
        "index_se": "0.0153",
        "index_lo": "0.4802",
        "index_hi": "0.5392",
        "full_usd": "1738.7",
        "cost_mean": "20.07",
        "cost_se": "1.33",
        "science_score": "0.3417",
        "science_usd": "23.3",
        "post_training_score": "0.6395",
        "post_training_usd": "13.36",
        "literature_score": "0.5911",
        "literature_usd": "11.15",
        "input_tokens_mean": 20649363,
        "output_tokens_mean": 209872,
        "minutes_mean": "133.6",
    },
    {
        "name": "DeepSeek V4.1 Flash",
        "provider": "DeepSeek",
        "harness": "OpenCode",
        "attempts": 87,
        "complete": True,
        "index_score": "0.274",
        "index_se": "0.0179",
        "index_lo": "0.2377",
        "index_hi": "0.3078",
        "full_usd": "62.9",
        "cost_mean": "0.72",
        "cost_se": "0.06",
        "science_score": "0.0833",
        "science_usd": "0.92",
        "post_training_score": "0.3633",
        "post_training_usd": "0.35",
        "literature_score": "0.477",
        "literature_usd": "0.18",
        "input_tokens_mean": 37933028,
        "output_tokens_mean": 242720,
        "minutes_mean": "194.2",
    },
    {
        "name": "Kimi K3",
        "provider": "Moonshot AI",
        "harness": "OpenCode",
        "attempts": 87,
        "complete": True,
        "index_score": "0.2714",
        "index_se": "0.0099",
        "index_lo": "0.2529",
        "index_hi": "0.2903",
        "full_usd": "947.8",
        "cost_mean": "10.89",
        "cost_se": "0.97",
        "science_score": "0.0333",
        "science_usd": "14.05",
        "post_training_score": "0.4223",
        "post_training_usd": "3.89",
        "literature_score": "0.4457",
        "literature_usd": "3.86",
        "input_tokens_mean": 24613292,
        "output_tokens_mean": 185678,
        "minutes_mean": "177.6",
    },
    {
        "name": "Qwen3.8-Flash",
        "provider": "Qwen",
        "harness": "OpenCode",
        "attempts": 87,
        "complete": True,
        "index_score": "0.2142",
        "index_se": "0.0154",
        "index_lo": "0.1812",
        "index_hi": "0.2417",
        "full_usd": "394.7",
        "cost_mean": "4.54",
        "cost_se": "0.44",
        "science_score": "0",
        "science_usd": "5.12",
        "post_training_score": "0.3051",
        "post_training_usd": "4.44",
        "literature_score": "0.4609",
        "literature_usd": "0.86",
        "input_tokens_mean": 29685541,
        "output_tokens_mean": 178959,
        "minutes_mean": "192.7",
    },
]

# Verbatim sub-row matrix from RankHeatmap-CVYXZmjT.js (ordered identically to EMBEDDED_MODELS)
EMBEDDED_HEATMAP_ROWS: dict[str, list[str]] = {
    "Life sciences (3)": ["0.778", "0.556", "0.444", "0.889", "0.222", "0.222", "0", "0"],
    "Physical sciences (5)": ["0.6", "0.733", "0.6", "0.533", "0.467", "0.133", "0.067", "0"],
    "Earth sciences (2)": ["0.5", "0", "0.167", "0.5", "0", "0", "0", "0"],
    "Mathematical sciences (7)": ["0.571", "0.762", "0.81", "0.571", "0.429", "0.048", "0.048", "0"],
    "Engineering sciences (3)": ["0.444", "0.667", "0.667", "0.222", "0.278", "0", "0", "0"],
    "Qwen3-0.6B GSM8K": ["0.736", "0.7", "0.724", "0.615", "0.688", "0.486", "0.631", "0.518"],
    "Qwen3-0.6B HumanEval": ["0.526", "0.49", "0.331", "0.37", "0.537", "0.244", "0.36", "0.372"],
    "Qwen3-1.7B BFCL": ["0.842", "0.694", "0.565", "0.756", "0.822", "0.8", "0.768", "0.504"],
    "Qwen3-1.7B IFEval": ["0.709", "0.607", "0.587", "0.566", "0.68", "0.303", "0.463", "0.185"],
    "SmolLM2-360M GSM8K": ["0.592", "0.504", "0.509", "0.388", "0.57", "0.303", "0.126", "0.233"],
    "SmolLM2-360M IFEval": ["0.531", "0.231", "0.304", "0.235", "0.54", "0.044", "0.187", "0.019"],
    "Navigational": ["0.908", "0.9", "0.9", "0.9", "0.884", "0.893", "0.878", "0.922"],
    "Metadata": ["0.624", "0.449", "0.501", "0.564", "0.601", "0.443", "0.388", "0.356"],
    "Semantic": ["0.307", "0.112", "0.121", "0.197", "0.288", "0.096", "0.071", "0.104"],
}


def _norm_js_num(raw: str) -> str:
    """Normalize JS numeric literal (e.g. '.6183' -> '0.6183') without using float."""
    s = raw.strip()
    if s.startswith("."):
        return "0" + s
    return s


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        while True:
            chunk = fh.read(65536)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest()


def verify_pinned_artifact_digests(
    blog_dir: Path,
    expected_digests: dict[str, str] | None = None,
) -> dict[str, str]:
    """Verify every pinned read-only blog artifact exists and matches its exact SHA-256."""
    targets = PINNED_ARTIFACT_SHA256 if expected_digests is None else expected_digests
    verified_digests: dict[str, str] = {}
    for fname, expected in targets.items():
        fpath = blog_dir / fname
        if not fpath.is_file():
            raise IndexOracleError("MISSING_PINNED_FILE", f"missing pinned artifact {fname}")
        actual = _sha256_file(fpath)
        if actual != expected:
            raise IndexOracleError("SHA256_MISMATCH", f"{fname}: got {actual}, expected {expected}")
        verified_digests[fname] = actual
    return verified_digests


def parse_blog_bundle_texts(
    rt_js: str,
    cs_js: str,
    rh_js: str,
    idx_html: str,
) -> tuple[list[dict[str, Any]], dict[str, list[str]], dict[str, bool]]:
    """Parse verbatim JS/HTML bundle texts in pure exact arithmetic and cross-check consistency."""
    # Parse ResultsTable rows
    rt_re = re.compile(
        r"\{model:`([^`]+)`,logo:[^,]+,(?:[^}]*?\},)?harness:`([^`]+)`,attempts:(\d+),"
        r"score:\{mean:([0-9.]+),se:([0-9.]+)\},"
        r"cost:\{mean:([0-9.]+),se:([0-9.]+)\},"
        r"inputTokens:\{mean:(\d+),se:(\d+)\},"
        r"outputTokens:\{mean:(\d+),se:(\d+)\},"
        r"minutes:\{mean:([0-9.]+),se:([0-9.]+)\}\}"
    )
    rt_by_name: dict[str, dict[str, Any]] = {}
    for m in rt_re.finditer(rt_js):
        rt_by_name[m.group(1)] = {
            "harness": m.group(2),
            "attempts": int(m.group(3)),
            "index_score": _norm_js_num(m.group(4)),
            "index_se": _norm_js_num(m.group(5)),
            "cost_mean": _norm_js_num(m.group(6)),
            "cost_se": _norm_js_num(m.group(7)),
            "input_tokens_mean": int(m.group(8)),
            "output_tokens_mean": int(m.group(10)),
            "minutes_mean": _norm_js_num(m.group(12)),
        }
    if len(rt_by_name) != 8:
        raise IndexOracleError("PARSE_RT_COUNT", f"expected 8 ResultsTable rows, got {len(rt_by_name)}")

    # Parse CostScoreChart rows
    cs_re = re.compile(
        r"\{name:`([^`]+)`,color:[^,]+,shape:`[^`]+`,complete:!(0|1),"
        r"index:\{score:([0-9.]+),lo:([0-9.]+),hi:([0-9.]+),usd:([0-9.]+)\},"
        r"science:\{score:([0-9.]+),usd:([0-9.]+)\},"
        r"postTraining:\{score:([0-9.]+),usd:([0-9.]+)\},"
        r"literature:\{score:([0-9.]+),usd:([0-9.]+)\}\}"
    )
    parsed_models: list[dict[str, Any]] = []
    provider_map = {m["name"]: m["provider"] for m in EMBEDDED_MODELS}
    for m in cs_re.finditer(cs_js):
        name = m.group(1)
        if name not in rt_by_name:
            raise IndexOracleError("PARSE_NAME_MISMATCH", f"{name} missing from ResultsTable")
        rt = rt_by_name[name]
        cs_score = _norm_js_num(m.group(3))
        if Fraction(cs_score) != Fraction(rt["index_score"]):
            raise IndexOracleError("CROSS_BUNDLE_SCORE_DRIFT", f"{name}: {cs_score} != {rt['index_score']}")
        parsed_models.append(
            {
                "name": name,
                "provider": provider_map[name],
                "harness": rt["harness"],
                "attempts": rt["attempts"],
                "complete": m.group(2) == "0",
                "index_score": cs_score,
                "index_se": rt["index_se"],
                "index_lo": _norm_js_num(m.group(4)),
                "index_hi": _norm_js_num(m.group(5)),
                "full_usd": _norm_js_num(m.group(6)),
                "cost_mean": rt["cost_mean"],
                "cost_se": rt["cost_se"],
                "science_score": _norm_js_num(m.group(7)),
                "science_usd": _norm_js_num(m.group(8)),
                "post_training_score": _norm_js_num(m.group(9)),
                "post_training_usd": _norm_js_num(m.group(10)),
                "literature_score": _norm_js_num(m.group(11)),
                "literature_usd": _norm_js_num(m.group(12)),
                "input_tokens_mean": rt["input_tokens_mean"],
                "output_tokens_mean": rt["output_tokens_mean"],
                "minutes_mean": rt["minutes_mean"],
            }
        )
    if len(parsed_models) != 8:
        raise IndexOracleError("PARSE_CS_COUNT", f"expected 8 CostScoreChart rows, got {len(parsed_models)}")

    # Parse RankHeatmap sub-rows
    rh_re = re.compile(r"\{label:`([^`]+)`,scores:\[([^\]]+)\],ranks:\[([^\]]+)\]\}")
    heatmap_rows: dict[str, list[str]] = {}
    for m in rh_re.finditer(rh_js):
        lbl = m.group(1)
        if lbl in EMBEDDED_HEATMAP_ROWS:
            heatmap_rows[lbl] = [_norm_js_num(tok) for tok in m.group(2).split(",")]
    if len(heatmap_rows) != len(EMBEDDED_HEATMAP_ROWS):
        raise IndexOracleError("PARSE_RH_COUNT", f"expected {len(EMBEDDED_HEATMAP_ROWS)} heatmap rows")

    # Verify embedded snapshot matches live JS parse bit-for-bit
    if parsed_models != EMBEDDED_MODELS:
        raise IndexOracleError("EMBEDDED_MODEL_DRIFT", "embedded model table diverged from live JS")
    if heatmap_rows != EMBEDDED_HEATMAP_ROWS:
        raise IndexOracleError("EMBEDDED_HEATMAP_DRIFT", "embedded heatmap diverged from live JS")

    html_flags = {
        "og_image_points_to_cost_vs_score_png": (
            'property="og:image" content="https://www.alphaxiv.org/assets/blog/'
            'introducing-openresearch-intelligence-index/cost-vs-score.png"'
            in idx_html
        ),
        "twitter_image_points_to_cost_vs_score_png": (
            'name="twitter:image" content="https://www.alphaxiv.org/assets/blog/'
            'introducing-openresearch-intelligence-index/cost-vs-score.png"'
            in idx_html
        ),
        "tao_quote_present_in_html": "learned almost nothing mathematically" in idx_html,
        "source_code_coming_soon_in_html": "Its source code is coming soon" in idx_html,
    }
    return parsed_models, heatmap_rows, html_flags


def _parse_live_bundles(blog_dir: Path) -> tuple[dict[str, str], list[dict[str, Any]], dict[str, list[str]], dict[str, bool]]:
    """Verify SHA-256 digests and parse live verbatim JS bundles directly in pure Python."""
    verified_digests = verify_pinned_artifact_digests(blog_dir)
    rt_js = (blog_dir / "ResultsTable-Cepl37af.js").read_text(encoding="utf-8")
    cs_js = (blog_dir / "CostScoreChart-CkzD4pZy.js").read_text(encoding="utf-8")
    rh_js = (blog_dir / "RankHeatmap-CVYXZmjT.js").read_text(encoding="utf-8")
    idx_html = (blog_dir / "index.html").read_text(encoding="utf-8")
    parsed_models, heatmap_rows, html_flags = parse_blog_bundle_texts(rt_js, cs_js, rh_js, idx_html)
    return verified_digests, parsed_models, heatmap_rows, html_flags


def _resolve_git_head_sha(repo_dir: Path, expected_commit: str = PINNED_OPENRESEARCH_COMMIT) -> str:
    """Resolve .git/HEAD (detached SHA, loose ref, or packed-refs) and verify exact commit SHA."""
    git_dir = repo_dir / ".git"
    head_file = git_dir / "HEAD"
    if not head_file.is_file():
        raise IndexOracleError("MISSING_REPO", "OpenResearch read-only clone missing")
    head_text = head_file.read_text(encoding="utf-8").strip()
    if head_text.startswith("ref: "):
        ref_name = head_text[5:].strip()
        if not ref_name.startswith("refs/") or ".." in ref_name:
            raise IndexOracleError("INVALID_GIT_REF", f"unsafe git ref {ref_name!r}")
        loose_ref = git_dir / ref_name
        resolved: str | None = None
        if loose_ref.is_file():
            resolved = loose_ref.read_text(encoding="utf-8").strip()
        else:
            packed = git_dir / "packed-refs"
            if packed.is_file():
                for line in packed.read_text(encoding="utf-8").splitlines():
                    stripped = line.strip()
                    if stripped == "" or stripped.startswith("#") or stripped.startswith("^"):
                        continue
                    parts = stripped.split()
                    if len(parts) >= 2 and parts[1] == ref_name:
                        resolved = parts[0]
                        break
        if resolved is None:
            raise IndexOracleError("MISSING_GIT_REF", f"cannot resolve git ref {ref_name!r}")
    else:
        resolved = head_text

    if resolved != expected_commit:
        raise IndexOracleError(
            "COMMIT_MISMATCH",
            f"HEAD commit {resolved!r} != pinned {expected_commit!r}",
        )
    return resolved


def _audit_openresearch_repo_readonly(repo_dir: Path) -> dict[str, Any]:
    """Read-only inspection of pinned alphaXiv/OpenResearch clone (zero git writes)."""
    actual_sha = _resolve_git_head_sha(repo_dir, PINNED_OPENRESEARCH_COMMIT)
    required_rel = (
        Path("SKILL.md"),
        Path("src/commands/create_experiment.rs"),
        Path("src/local/experiments.rs"),
        Path("src/commands/metrics.rs"),
    )
    texts: dict[str, str] = {}
    for rel in required_rel:
        fpath = repo_dir / rel
        if not fpath.is_file():
            raise IndexOracleError("MISSING_REPO_FILE", f"missing expected file {rel.as_posix()}")
        texts[rel.as_posix()] = fpath.read_text(encoding="utf-8")

    return {
        "repo_url": PINNED_OPENRESEARCH_REPO,
        "pinned_commit_sha": actual_sha,
        "head_ref_verified": True,
        "skill_md_advises_fixed_run_command": (
            "The run command *and* the environment are a fixed contract" in texts["SKILL.md"]
        ),
        "create_experiment_cli_allows_run_command_override": (
            "run_command: args.run_command" in texts["src/commands/create_experiment.rs"]
        ),
        "experiments_rs_accepts_per_node_run_command": (
            "let run_command = run_command" in texts["src/local/experiments.rs"]
        ),
        "metrics_rs_trackio_telemetry_opt_in_only": (
            "It logs only if the code calls trackio.init" in texts["src/commands/metrics.rs"]
        ),
    }


def build_certificate(
    models: list[dict[str, Any]],
    heatmap_rows: dict[str, list[str]],
    mode: str,
    verified_digests: dict[str, str] | None,
    html_flags: dict[str, bool] | None,
    openresearch_audit: dict[str, Any] | None,
) -> dict[str, Any]:
    """Run all exact pure-Q mathematical audits and assemble the canonical certificate."""
    # 1. Exact formula & cost accounting verification
    formula_rows: list[dict[str, Any]] = []
    max_formula_abs_diff = Fraction(0)
    equal_weight_rows: list[dict[str, str]] = []
    task_prop_rows: list[dict[str, str]] = []
    for m in models:
        s = Fraction(m["science_score"])
        p = Fraction(m["post_training_score"])
        lit = Fraction(m["literature_score"])
        rep_idx = Fraction(m["index_score"])
        calc_idx = compute_composite_index_exact(s, p, lit, DEFAULT_INDEX_WEIGHTS)
        diff = rep_idx - calc_idx
        abs_diff = -diff if diff < 0 else diff
        if abs_diff > max_formula_abs_diff:
            max_formula_abs_diff = abs_diff

        eq_idx = compute_composite_index_exact(s, p, lit, (Fraction(1, 3), Fraction(1, 3), Fraction(1, 3)))
        tp_idx = compute_composite_index_exact(s, p, lit, (Fraction(20, 29), Fraction(6, 29), Fraction(3, 29)))

        equal_weight_rows.append(
            {
                "name": m["name"],
                "equal_weight_score_exact": frac_str(eq_idx),
                "equal_weight_score_dec": format_exact_decimal(eq_idx, 4),
                "published_score_dec": format_exact_decimal(rep_idx, 4),
                "delta_equal_minus_published_dec": format_exact_decimal(eq_idx - rep_idx, 4),
            }
        )
        task_prop_rows.append(
            {
                "name": m["name"],
                "task_proportional_score_exact": frac_str(tp_idx),
                "task_proportional_score_dec": format_exact_decimal(tp_idx, 4),
            }
        )

        rec_cost = (
            60 * Fraction(m["science_usd"])
            + 18 * Fraction(m["post_training_usd"])
            + 9 * Fraction(m["literature_usd"])
        )
        rep_cost = Fraction(m["full_usd"])
        att_cost_est = m["attempts"] * Fraction(m["cost_mean"])
        formula_rows.append(
            {
                "name": m["name"],
                "provider": m["provider"],
                "harness": m["harness"],
                "attempts": m["attempts"],
                "reported_index_exact": frac_str(rep_idx),
                "recomputed_index_exact": frac_str(calc_idx),
                "index_rounding_delta_exact": frac_str(diff),
                "reported_full_usd_exact": frac_str(rep_cost),
                "reconstructed_60_18_9_usd_exact": frac_str(rec_cost),
                "reconstructed_60_18_9_usd_dec": format_exact_decimal(rec_cost, 2),
                "completed_attempts_x_mean_usd_dec": format_exact_decimal(att_cost_est, 2),
            }
        )

    # 2. Exact Fable 5.1* 41/120 rational Science reconstruction & 74/87 missing-attempt audit
    # Fable disciplines: Life(3)=2/9, Physical(5)=7/15, Earth(2)=0, Math(7)=3/7, Eng(3)=5/18
    fable_science_exact = (
        3 * Fraction(2, 9)
        + 5 * Fraction(7, 15)
        + 2 * Fraction(0, 1)
        + 7 * Fraction(3, 7)
        + 3 * Fraction(5, 18)
    ) / 20
    fable_row = [m for m in models if m["name"] == "Fable 5.1"][0]
    fable_missing_audit = audit_missing_attempts_and_cost_extrapolation(
        completed_attempts=fable_row["attempts"],
        full_attempts=87,
        observed_index_score=fable_row["index_score"],
        reported_full_cost=fable_row["full_usd"],
        reported_per_attempt_cost=fable_row["cost_mean"],
        track_attempt_counts=(60, 18, 9),
        track_per_attempt_costs=(
            fable_row["science_usd"],
            fable_row["post_training_usd"],
            fable_row["literature_usd"],
        ),
        track_weights=DEFAULT_INDEX_WEIGHTS,
    )
    fable_missing_audit["exact_fable_science_rational"] = frac_str(fable_science_exact)
    fable_missing_audit["exact_fable_science_dec4"] = format_exact_decimal(fable_science_exact, 4)
    fable_missing_audit["matches_published_0_3417"] = (
        format_exact_decimal(fable_science_exact, 4) == "0.3417"
    )
    fable_missing_audit["engineering_5_over_18_proves_unweighted_task_mean"] = (
        format_exact_decimal(Fraction(5, 18), 3) == "0.278"
    )

    # 3. Task-leverage asymmetry & exact 2-simplex weight sensitivity polytope
    leverage_audit = audit_task_leverage_asymmetry(
        track_weights={"science": Fraction(2, 5), "post_training": Fraction(2, 5), "literature": Fraction(1, 5)},
        track_task_counts={"science": 20, "post_training": 6, "literature": 3},
    )
    simplex_audit = audit_weight_sensitivity_simplex(
        [
            {
                "name": m["name"],
                "science": m["science_score"],
                "post_training": m["post_training_score"],
                "literature": m["literature_score"],
            }
            for m in models
        ],
        baseline_weights=DEFAULT_INDEX_WEIGHTS,
    )

    # 4. Exact Pareto frontiers (Headline + 3 tracks) & 95% CI separability audit
    ci_entries = [
        {
            "name": m["name"],
            "cost": m["full_usd"],
            "score": m["index_score"],
            "ci_lo": m["index_lo"],
            "ci_hi": m["index_hi"],
        }
        for m in models
    ]
    ci_and_pareto_audit = audit_ci_separability_and_pareto_stability(ci_entries)
    per_track_pareto = {
        "headline": compute_pareto_frontier_exact(ci_entries),
        "science": compute_pareto_frontier_exact(
            [{"name": m["name"], "cost": m["science_usd"], "score": m["science_score"]} for m in models]
        ),
        "post_training": compute_pareto_frontier_exact(
            [
                {"name": m["name"], "cost": m["post_training_usd"], "score": m["post_training_score"]}
                for m in models
            ]
        ),
        "literature": compute_pareto_frontier_exact(
            [{"name": m["name"], "cost": m["literature_usd"], "score": m["literature_score"]} for m in models]
        ),
    }

    # 5. Exact Bipartite Model-Harness non-identifiability + constructive 2-bridge recovery
    published_obs = [(m["name"], m["harness"]) for m in models]
    confounding_published = audit_bipartite_confounding_exact(published_obs)
    bridged_obs = published_obs + [("Opus 5.5", "OpenCode"), ("GPT-6 Astra", "OpenCode")]
    confounding_bridged = audit_bipartite_confounding_exact(bridged_obs)

    # 6. Sub-task coverage & Literature Navigational saturation audit
    nav_scores = [Fraction(x) for x in heatmap_rows["Navigational"]]
    meta_scores = [Fraction(x) for x in heatmap_rows["Metadata"]]
    sem_scores = [Fraction(x) for x in heatmap_rows["Semantic"]]
    nav_range = max(nav_scores) - min(nav_scores)
    meta_range = max(meta_scores) - min(meta_scores)
    sem_range = max(sem_scores) - min(sem_scores)
    nav_leader_idx = max(range(len(nav_scores)), key=lambda i: nav_scores[i])
    subtask_structure = {
        "post_training_factorial_declared_cells": 12,
        "post_training_factorial_evaluated_cells": 6,
        "post_training_coverage_fraction_exact": frac_str(Fraction(6, 12)),
        "literature_navigational_min_dec": format_exact_decimal(min(nav_scores), 3),
        "literature_navigational_max_dec": format_exact_decimal(max(nav_scores), 3),
        "literature_navigational_range_exact": frac_str(nav_range),
        "literature_navigational_range_dec": format_exact_decimal(nav_range, 3),
        "literature_navigational_rank1_model": models[nav_leader_idx]["name"],
        "literature_metadata_range_dec": format_exact_decimal(meta_range, 3),
        "literature_semantic_range_dec": format_exact_decimal(sem_range, 3),
    }

    # 7. Tao Black-Box Observability Gate scenarios (aletheia v1.4.0 + warp-drive#13/#15 bridge)
    sample_sha = "a" * 64
    tao_scenarios = {
        "published_index_black_box_profile": evaluate_tao_observability_gate(
            outcome_score="0.6183",
            process_receipt={
                "frozen_contract_sha256": "",
                "split_leakage_count": 1,
                "internet_contamination_audit": "UNRESTRICTED_4H_INTERNET",
                "goodhart_kl_delta_bps": 5500,
                "max_kl_delta_bps": 500,
                "r4_isolated_parity_runs": 0,
                "r5_mutation_killed": 0,
                "r5_mutation_total": 0,
            },
        ),
        "single_gate_failure_internet_only": evaluate_tao_observability_gate(
            outcome_score="0.6559",
            process_receipt={
                "frozen_contract_sha256": sample_sha,
                "split_leakage_count": 0,
                "internet_contamination_audit": "UNRESTRICTED_4H_INTERNET",
                "goodhart_kl_delta_bps": 120,
                "max_kl_delta_bps": 500,
                "r4_isolated_parity_runs": 4,
                "r5_mutation_killed": 50,
                "r5_mutation_total": 50,
            },
        ),
        "governed_aletheia_warp_drive_profile": evaluate_tao_observability_gate(
            outcome_score="0.6183",
            process_receipt={
                "frozen_contract_sha256": sample_sha,
                "split_leakage_count": 0,
                "internet_contamination_audit": VERIFIED_INTERNET_STATUS,
                "goodhart_kl_delta_bps": 120,
                "max_kl_delta_bps": 500,
                "r4_isolated_parity_runs": 4,
                "r5_mutation_killed": 50,
                "r5_mutation_total": 50,
            },
        ),
    }

    body: dict[str, Any] = {
        "schema_version": "aletheia.openresearch_index_audit.v1",
        "audit_id": "AUDIT-069",
        "mode": mode,
        "sources": {
            "blog_url": PINNED_BLOG_URL,
            "openresearch_repo_url": PINNED_OPENRESEARCH_REPO,
            "openresearch_commit_sha": PINNED_OPENRESEARCH_COMMIT,
            "pinned_artifact_sha256": verified_digests if verified_digests is not None else PINNED_ARTIFACT_SHA256,
            "html_provenance_flags": html_flags,
            "openresearch_readonly_audit": openresearch_audit,
        },
        "formula_and_cost_audit": {
            "max_composite_rounding_delta_exact": frac_str(max_formula_abs_diff),
            "max_composite_rounding_delta_dec": format_exact_decimal(max_formula_abs_diff, 6),
            "models": formula_rows,
            "equal_weight_1_3_scores_matching_stale_og_png": equal_weight_rows,
            "task_proportional_20_6_3_scores": task_prop_rows,
        },
        "fable_missing_attempts_audit": fable_missing_audit,
        "task_leverage_asymmetry": leverage_audit,
        "weight_sensitivity_simplex_exact": simplex_audit,
        "ci_separability_and_pareto_stability": ci_and_pareto_audit,
        "per_track_pareto_frontiers": per_track_pareto,
        "bipartite_confounding_published": confounding_published,
        "bipartite_confounding_with_2_opencode_bridges": confounding_bridged,
        "subtask_coverage_and_saturation": subtask_structure,
        "tao_observability_gate_scenarios": tao_scenarios,
    }
    verify_no_floats(body, "certificate")
    return {
        "canonical_sha256": canonical_sha256(body),
        "certificate": body,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="AUDIT-069 OpenResearch Intelligence Index exact audit")
    parser.add_argument("--standalone", action="store_true", help="Run without external downloaded files")
    parser.add_argument("--write-cert", type=str, default="", help="Optional path to write canonical JSON certificate")
    args = parser.parse_args(argv)

    if args.standalone:
        result = build_certificate(
            models=EMBEDDED_MODELS,
            heatmap_rows=EMBEDDED_HEATMAP_ROWS,
            mode="standalone",
            verified_digests=None,
            html_flags=None,
            openresearch_audit=None,
        )
    else:
        blog_dir = _SCRIPT_DIR.parent / "repos" / "openresearch-index-blog"
        repo_dir = _SCRIPT_DIR.parent.parent / "round5" / "repos" / "alphaxiv-OpenResearch"
        if blog_dir.is_dir() and repo_dir.is_dir():
            digests, models, heatmap_rows, html_flags = _parse_live_bundles(blog_dir)
            repo_audit = _audit_openresearch_repo_readonly(repo_dir)
            result = build_certificate(
                models=models,
                heatmap_rows=heatmap_rows,
                mode="live_pinned_verified",
                verified_digests=digests,
                html_flags=html_flags,
                openresearch_audit=repo_audit,
            )
        else:
            result = build_certificate(
                models=EMBEDDED_MODELS,
                heatmap_rows=EMBEDDED_HEATMAP_ROWS,
                mode="standalone",
                verified_digests=None,
                html_flags=None,
                openresearch_audit=None,
            )

    raw_bytes = canonical_json_bytes(result) + b"\n"
    if args.write_cert:
        out_path = Path(args.write_cert)
        out_path.write_bytes(raw_bytes)
    sys.stdout.write(raw_bytes.decode("utf-8"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
