"""Comprehensive R5 mutation-killing & adversarial red-team test suite for AUDIT-078.

Covers BOTH jdpru_epistemic_weighting_oracle.py AND jdpru_epistemic_audit.py
under -I -O -B -W error with zero bare assert statements and zero floats on
trust paths.
"""

from __future__ import annotations

import contextlib
from fractions import Fraction
import io
import json
from pathlib import Path
import sys
import tempfile
import zipfile
from typing import Any, Callable

_SCRIPT_DIR = str(Path(__file__).resolve().parent)
if _SCRIPT_DIR not in sys.path:
    sys.path.insert(0, _SCRIPT_DIR)

import jdpru_epistemic_audit as audit_mod
import jdpru_epistemic_weighting_oracle as oracle


class TestFailure(RuntimeError):
    """Explicit assertion-free test failure."""


def check_eq(actual: Any, expected: Any, label: str) -> None:
    if actual != expected or type(actual) is not type(expected):
        raise TestFailure(f"{label}: expected {expected!r} ({type(expected).__name__}), got {actual!r} ({type(actual).__name__})")


def check_true(cond: Any, label: str) -> None:
    if cond is not True:
        raise TestFailure(f"{label}: expected True, got {cond!r}")


def check_raises(fn: Callable[[], Any], expected_code: str, label: str) -> None:
    try:
        fn()
    except oracle.JdpruOracleError as exc:
        if exc.code != expected_code:
            raise TestFailure(f"{label}: expected code {expected_code!r}, got {exc.code!r} ({exc})") from exc
        return
    raise TestFailure(f"{label}: expected JdpruOracleError({expected_code!r}) but succeeded")


def _make_minimal_xlsx(path: Path, rows: list[list[str]], use_shared_strings: bool = True) -> None:
    sst: list[str] = []
    sst_idx: dict[str, int] = {}
    sheet_rows: list[str] = []
    for r_i, row in enumerate(rows, start=1):
        cells: list[str] = []
        for c_i, val in enumerate(row):
            col_chr = chr(ord("A") + c_i)
            ref = f"{col_chr}{r_i}"
            if val == "":
                cells.append(f'<c r="{ref}"/>')
            elif use_shared_strings:
                if val not in sst_idx:
                    sst_idx[val] = len(sst)
                    sst.append(val)
                cells.append(f'<c r="{ref}" t="s"><v>{sst_idx[val]}</v></c>')
            else:
                cells.append(f'<c r="{ref}" t="str"><v>{val}</v></c>')
        sheet_rows.append(f'<row r="{r_i}">{"".join(cells)}</row>')

    ns = "http://schemas.openxmlformats.org/spreadsheetml/2006/main"
    sheet_xml = f'<?xml version="1.0" encoding="UTF-8"?><worksheet xmlns="{ns}"><sheetData>{"".join(sheet_rows)}</sheetData></worksheet>'
    with zipfile.ZipFile(path, "w") as zf:
        zf.writestr("xl/worksheets/sheet1.xml", sheet_xml)
        if use_shared_strings:
            si_items = "".join(f"<si><t>{s}</t></si>" for s in sst)
            sst_xml = f'<?xml version="1.0" encoding="UTF-8"?><sst xmlns="{ns}">{si_items}</sst>'
            zf.writestr("xl/sharedStrings.xml", sst_xml)


def _create_synthetic_jdpru_workspace(
    root: Path,
    *,
    head_mode: str = "loose",
    tamper_head: bool = False,
    tamper_anchor: bool = False,
    omit_file: bool = False,
    tamper_total: bool = False,
) -> None:
    for name, sha in audit_mod.PINNED_REPO_HEADS.items():
        repo = root / name
        git_dir = repo / ".git"
        git_dir.mkdir(parents=True, exist_ok=True)
        use_sha = ("0" * 40) if (tamper_head and name == "cover-your-ais") else sha
        if head_mode == "detached":
            (git_dir / "HEAD").write_text(f"{use_sha}\n", encoding="utf-8")
        elif head_mode == "packed":
            (git_dir / "HEAD").write_text("ref: refs/heads/main\n", encoding="utf-8")
            (git_dir / "packed-refs").write_text(
                f"# pack-refs\n^deadbeef\n\n{use_sha} refs/heads/main\n",
                encoding="utf-8",
            )
        else:
            (git_dir / "HEAD").write_text("ref: refs/heads/main\n", encoding="utf-8")
            ref_file = git_dir / "refs" / "heads" / "main"
            ref_file.parent.mkdir(parents=True, exist_ok=True)
            ref_file.write_text(f"{use_sha}\n", encoding="utf-8")

    # cover-your-ais
    cya = root / "cover-your-ais"
    (cya / "prompts").mkdir(parents=True, exist_ok=True)
    if not omit_file:
        (cya / "README.md").write_text(
            "Prompts are not security boundaries.\n" if not tamper_anchor else "Different text.\n",
            encoding="utf-8",
        )
    (cya / "prompts" / "ai-codebase-safety-audit.md").write_text(
        "8. Check: hidden Unicode in rule files.\n",
        encoding="utf-8",
    )

    # CES-Accuracy-Analysis
    ces = root / "CES-Accuracy-Analysis"
    (ces / "sensitivity_analyses" / "results").mkdir(parents=True, exist_ok=True)
    (ces / "tables_and_figures" / "input_tables").mkdir(parents=True, exist_ok=True)
    (ces / "CLAUDE.md").write_text(
        audit_mod.STANDALONE_CLAUDE_MD_EXCERPT + "\nphase 2 has independent agents verify the hits\n",
        encoding="utf-8",
    )
    (ces / "sensitivity_analyses" / "README.md").write_text(
        "This folder is untracked.\n",
        encoding="utf-8",
    )
    (ces / "supplementary_material.tex").write_text(
        "Maximum & 20.00044 & 20.00044\n",
        encoding="utf-8",
    )

    hl_lines = ["macro,base,A2_named_only"]
    for k, v in audit_mod.STANDALONE_CSV_BASE_METRICS.items():
        alt = v
        if k == "TrendSecMatchBeta":
            alt = "-0.030"
        elif k == "TrendSecWtdBeta":
            alt = "0.023"
        hl_lines.append(f"{k},{v},{alt}")
    hl_lines.append("AnesHighestYears,seven,two")
    hl_lines.append(",ignored,ignored")
    (ces / "sensitivity_analyses" / "results" / "headline_by_variant.csv").write_text(
        "\n".join(hl_lines) + "\n",
        encoding="utf-8",
    )

    pr_lines = ["macro,base"]
    for k, v in audit_mod.STANDALONE_CES_COUNTS.items():
        val = (v + 1) if (tamper_total and k == "NObsTotal") else v
        pr_lines.append(f'{k},"{val:,}"')
    (ces / "sensitivity_analyses" / "results" / "prose_numbers_by_variant.csv").write_text(
        "\n".join(pr_lines) + "\n",
        encoding="utf-8",
    )

    years = list(audit_mod.STANDALONE_ANESRAKE_USED_BY_YEAR.keys())
    rows: list[list[str]] = [["Variable"] + years]
    for r_idx in range(9):
        row = [f"Var{r_idx}"]
        for yr in years:
            row.append("Used" if r_idx < audit_mod.STANDALONE_ANESRAKE_USED_BY_YEAR[yr] else "Not provided")
        rows.append(row)
    _make_minimal_xlsx(
        ces / "tables_and_figures" / "input_tables" / "vars_used_by_anesrake.xlsx",
        rows,
        use_shared_strings=True,
    )

    # CS-230-DynaRT
    dyn = root / "CS-230-DynaRT"
    (dyn / "README.md").write_text("DynaRT is a deep learning framework.\n", encoding="utf-8")


def test_primitives_and_refusals() -> None:
    # verify_no_floats
    oracle.verify_no_floats({"a": [1, (2, "x"), {3}]})
    check_raises(lambda: oracle.verify_no_floats(1.5), "FLOAT_FORBIDDEN", "scalar float")
    check_raises(lambda: oracle.verify_no_floats({1.0: "x"}), "FLOAT_FORBIDDEN", "dict float key")
    check_raises(lambda: oracle.verify_no_floats({"a": [1, 2.0]}), "FLOAT_FORBIDDEN", "nested list float")
    check_raises(lambda: oracle.verify_no_floats((1, {2.5})), "FLOAT_FORBIDDEN", "nested set float")

    # require_non_empty_str
    check_eq(oracle.require_non_empty_str("  abc  ", "f"), "abc", "strip str")
    check_raises(lambda: oracle.require_non_empty_str(123, "f"), "TYPE_ERROR", "non-str")
    check_raises(lambda: oracle.require_non_empty_str("   ", "f"), "EMPTY_STRING", "blank str")

    # require_exact_bool
    check_eq(oracle.require_exact_bool(True, "b"), True, "bool True")
    check_eq(oracle.require_exact_bool(False, "b"), False, "bool False")
    check_raises(lambda: oracle.require_exact_bool(1, "b"), "TYPE_ERROR", "int not bool")

    # require_exact_int
    check_eq(oracle.require_exact_int(7, "i"), 7, "int 7")
    check_raises(lambda: oracle.require_exact_int(True, "i"), "TYPE_ERROR", "bool not int")
    check_raises(lambda: oracle.require_exact_int(1.0, "i"), "TYPE_ERROR", "float not int")
    check_raises(lambda: oracle.require_exact_int("7", "i"), "TYPE_ERROR", "str not int")

    # require_exact_fraction
    check_eq(oracle.require_exact_fraction(Fraction(3, 4), "x"), Fraction(3, 4), "Fraction passthrough")
    check_eq(oracle.require_exact_fraction(-5, "x"), Fraction(-5, 1), "int to Fraction")
    check_eq(oracle.require_exact_fraction("+1.25", "x"), Fraction(5, 4), "decimal str")
    check_eq(oracle.require_exact_fraction("-3/8", "x"), Fraction(-3, 8), "ratio str")
    check_raises(lambda: oracle.require_exact_fraction(True, "x"), "TYPE_ERROR", "bool fraction")
    check_raises(lambda: oracle.require_exact_fraction(0.5, "x"), "FLOAT_FORBIDDEN", "float fraction")
    check_raises(lambda: oracle.require_exact_fraction("1/0", "x"), "ZERO_DENOMINATOR", "zero den")
    check_raises(lambda: oracle.require_exact_fraction("1.5\n", "x"), "INVALID_RATIONAL", "newline smuggling")
    check_raises(lambda: oracle.require_exact_fraction(" 1.5 ", "x"), "INVALID_RATIONAL", "space padded")
    check_raises(lambda: oracle.require_exact_fraction("nan", "x"), "INVALID_RATIONAL", "nan str")
    check_raises(lambda: oracle.require_exact_fraction([], "x"), "TYPE_ERROR", "list fraction")

    # require_list_or_tuple
    check_eq(oracle.require_list_or_tuple([1, 2], "s"), (1, 2), "list seq")
    check_eq(oracle.require_list_or_tuple((3,), "s"), (3,), "tuple seq")
    check_raises(lambda: oracle.require_list_or_tuple("abc", "s"), "TYPE_ERROR", "str not seq")
    check_raises(lambda: oracle.require_list_or_tuple([], "s"), "EMPTY_SEQUENCE", "empty list")

    # frac_str & format_exact_decimal
    check_eq(oracle.frac_str(Fraction(6, 4)), "3/2", "frac_str reduced")
    check_raises(lambda: oracle.frac_str(1), "TYPE_ERROR", "frac_str non-Fraction")
    check_eq(oracle.format_exact_decimal(Fraction(1, 2), 0), "1", "half-up 0dp")
    check_eq(oracle.format_exact_decimal(Fraction(49, 100), 0), "0", "below-half 0dp")
    check_eq(oracle.format_exact_decimal(Fraction(-1, 200), 2), "-0.01", "neg half-up 2dp")
    check_eq(oracle.format_exact_decimal(Fraction(-1, 1000), 2), "0.00", "neg rounds to zero no minus")
    check_eq(oracle.format_exact_decimal(Fraction(12345, 1000), 2), "12.35", "pos 2dp half-up")
    check_raises(lambda: oracle.format_exact_decimal(1, 2), "TYPE_ERROR", "format non-Fraction")
    check_raises(lambda: oracle.format_exact_decimal(Fraction(1, 2), -1), "INVALID_RANGE", "neg places")

    # canonical_json_bytes & canonical_sha256
    b = oracle.canonical_json_bytes({"b": 2, "a": 1})
    check_eq(b, b'{"a":1,"b":2}', "canonical json")
    h1 = oracle.canonical_sha256({"b": 2, "a": 1})
    h2 = oracle.canonical_sha256({"a": 1, "b": 2})
    check_eq(h1, h2, "canonical sha order invariant")
    check_eq(len(h1), 64, "sha length")
    check_raises(lambda: oracle.canonical_json_bytes({"a": 1.2}), "FLOAT_FORBIDDEN", "json float refusal")


def test_pillar1_scanners_and_coverage() -> None:
    # scan_hidden_unicode_exact boundary codepoints (low, mid, high, and adjacent clean)
    check_raises(lambda: oracle.scan_hidden_unicode_exact(123), "TYPE_ERROR", "unicode non-str")
    clean_edges = "\u200A\u2010\u2029\u202F\u205F\u2061\u2065\u206A\uFEFE\U000DFFFF\U000E0080abc"
    res_clean = oracle.scan_hidden_unicode_exact(clean_edges)
    check_eq(res_clean["clean"], True, "adjacent clean edges")
    check_eq(res_clean["finding_count"], 0, "clean count 0")

    dirty = "a\u200Bb\u200F\u2060\uFEFF\n\u061C\u202A\u202E\u2066\u2069\U000E0000\U000E007F"
    res_dirty = oracle.scan_hidden_unicode_exact(dirty)
    check_eq(res_dirty["clean"], False, "dirty unicode detected")
    check_eq(res_dirty["finding_count"], 11, "all 11 boundary codepoints detected")
    check_eq(res_dirty["findings"][0], {"line": 1, "col": 2, "codepoint": "U+200B", "category": "ZERO_WIDTH_OR_BOM"}, "zwsp pos")
    check_eq(res_dirty["findings"][4], {"line": 2, "col": 1, "codepoint": "U+061C", "category": "BIDI_OVERRIDE_OR_ISOLATE"}, "alm line2 col1")
    check_eq(res_dirty["findings"][5], {"line": 2, "col": 2, "codepoint": "U+202A", "category": "BIDI_OVERRIDE_OR_ISOLATE"}, "bidi line2 col2")
    check_eq(res_dirty["findings"][9], {"line": 2, "col": 6, "codepoint": "U+E0000", "category": "UNICODE_TAG_SMUGGLING"}, "tag low")
    check_eq(res_dirty["findings"][10], {"line": 2, "col": 7, "codepoint": "U+E007F", "category": "UNICODE_TAG_SMUGGLING"}, "tag high")

    # audit_agent_safety_surface refusals & clean & elevated & critical & bypass checks
    check_raises(lambda: oracle.audit_agent_safety_surface("", "prompt_rule"), "EMPTY_STRING", "empty artifact")
    check_raises(lambda: oracle.audit_agent_safety_surface(123, "prompt_rule"), "EMPTY_STRING", "non-str artifact")
    check_raises(lambda: oracle.audit_agent_safety_surface("ok", "unknown"), "INVALID_ARTIFACT_KIND", "bad kind")

    clean_script = "set -euo pipefail\nrm -rf \"$TARGET\"\necho done\n"
    res_safe_setu = oracle.audit_agent_safety_surface(clean_script, "SHELL_SCRIPT")
    check_eq(res_safe_setu["risk_level"], "CLEAN", "set -u protects rm -rf")
    check_eq(res_safe_setu["finding_count"], 0, "clean script 0 findings")

    inline_guarded = 'rm -rf "${TARGET:?}"\n'
    res_inline = oracle.audit_agent_safety_surface(inline_guarded, "shell_script")
    check_eq(res_inline["risk_level"], "CLEAN", "inline :? guard protects line")

    # Red-team bypass test (JDPRU-BYPASS-01):
    # - commented # set -u MUST NOT exempt rm -rf
    # - set -u AFTER rm -rf MUST NOT exempt rm -rf
    # - set +u / set +o nounset disables nounset before rm -rf
    # - mixed short/long flags (rm --recursive -f, rm -f --recursive, rm -r --force) MUST trigger
    comment_spoof = '# set -u\nrm -r -f "$DIR"\n'
    res_spoof = oracle.audit_agent_safety_surface(comment_spoof, "shell_script")
    check_eq(res_spoof["risk_level"], "CRITICAL", "comment spoof caught")
    check_eq(res_spoof["gap_ids_present"], ["CYA-GAP-03"], "CYA-GAP-03 triggered")

    after_setu = 'rm -rf "$UNSET_DIR"\nset -u\n'
    check_eq(oracle.audit_agent_safety_surface(after_setu, "shell_script")["gap_ids_present"], ["CYA-GAP-03"], "set -u after rm caught")

    re_disabled = 'set -u\nset +u\nrm -rf "$UNSET_DIR"\n'
    check_eq(oracle.audit_agent_safety_surface(re_disabled, "shell_script")["gap_ids_present"], ["CYA-GAP-03"], "set +u disables nounset")

    re_disabled_long = 'set -o nounset\nset +o nounset\nrm -rf "$UNSET_DIR"\n'
    check_eq(oracle.audit_agent_safety_surface(re_disabled_long, "shell_script")["gap_ids_present"], ["CYA-GAP-03"], "set +o nounset disables")

    inline_disabled = 'set -u; set +u; rm -rf "$UNSET_DIR"\n'
    check_eq(oracle.audit_agent_safety_surface(inline_disabled, "shell_script")["gap_ids_present"], ["CYA-GAP-03"], "semicolon set +u disables")

    for mixed_cmd in (
        'rm --recursive -f "$UNSET_DIR"\n',
        'rm -f --recursive "$UNSET_DIR"\n',
        'rm -r --force "$UNSET_DIR"\n',
    ):
        check_eq(oracle.audit_agent_safety_surface(mixed_cmd, "shell_script")["gap_ids_present"], ["CYA-GAP-03"], f"mixed flag caught: {mixed_cmd.strip()}")

    # Red-team: inline guard on one arg MUST NOT exempt an unguarded arg on the SAME line!
    same_line_mix = 'rm -rf "${SAFE:?}" "$UNSAFE"\n'
    res_mix = oracle.audit_agent_safety_surface(same_line_mix, "shell_script")
    check_eq(res_mix["finding_count"], 1, "same-line mixed guarded/unguarded caught")

    # Red-team: inline guard on line 1 MUST NOT exempt unguarded rm -rf on line 2!
    cross_line = 'echo "${SAFE:?}"\nrm -rf "$UNSAFE"\n'
    res_cross = oracle.audit_agent_safety_surface(cross_line, "shell_script")
    check_eq(res_cross["finding_count"], 1, "cross-line inline guard cannot exempt line 2")

    # Red-team (JDPRU-BYPASS-02): pull_request_target + bracket secrets / toJSON(secrets) / id-token: write
    prt_ro = "on: pull_request_target\npermissions:\n  contents: read\n"
    check_eq(oracle.audit_agent_safety_surface(prt_ro, "ci_workflow")["finding_count"], 0, "prt read-only clean")
    for priv_yaml in (
        "on: pull_request_target\npermissions:\n  id-token: write\n",
        "on: pull_request_target\nenv:\n  TOK: ${{ secrets['GITHUB_TOKEN'] }}\n",
        "on: pull_request_target\nenv:\n  DUMP: ${{ toJSON(secrets) }}\n",
    ):
        res_prt = oracle.audit_agent_safety_surface(priv_yaml, "ci_workflow")
        check_eq(res_prt["gap_ids_present"], ["CYA-GAP-04"], "prt+priv caught")
        check_eq(res_prt["risk_level"], "CRITICAL", "prt+priv critical")

    # Red-team: same line carrying prose rule + tilde path reports BOTH (no elif masking!)
    both_line = "Commit only when asked; read ~/secret.xlsx\n"
    res_both = oracle.audit_agent_safety_surface(both_line, "prompt_rule")
    check_eq(res_both["finding_count"], 2, "both prose and tilde reported on same line")
    check_eq(res_both["risk_level"], "ELEVATED", "CYA-GAP-05 alone is ELEVATED")

    # Red-team (JDPRU-BYPASS-02): multiple MCP bypass tokens + npx -q -y / -qy, pinned npx clean
    mcp_line = "npx -y pkg@latest --yolo --dangerously-skip-permissions SessionStart\n"
    res_mcp = oracle.audit_agent_safety_surface(mcp_line, "mcp_config")
    check_eq(res_mcp["finding_count"], 5, "all 5 MCP/bypass tokens caught")
    check_eq(res_mcp["risk_level"], "CRITICAL", "CYA-GAP-02 critical")
    check_eq(oracle.audit_agent_safety_surface("npx -q -y @org/mcp-server\n", "mcp_config")["gap_ids_present"], ["CYA-GAP-02"], "npx -q -y caught")
    check_eq(oracle.audit_agent_safety_surface("npx -qy @org/mcp-server\n", "mcp_config")["gap_ids_present"], ["CYA-GAP-02"], "npx -qy caught")
    check_eq(oracle.audit_agent_safety_surface("npx --registry=https://registry.npmjs.org @org/mcp@1.2.3\n", "mcp_config")["risk_level"], "CLEAN", "pinned npx clean")

    # Cloud sync / alias trap alone -> ELEVATED
    res_cloud = oracle.audit_agent_safety_surface("Repo lives in Dropbox and alias rm='rm -i'", "prompt_rule")
    check_eq(res_cloud["finding_count"], 2, "cloud + alias caught")
    check_eq(res_cloud["gap_ids_present"], ["CYA-GAP-06"], "CYA-GAP-06 only")
    check_eq(res_cloud["risk_level"], "ELEVATED", "CYA-GAP-06 alone is ELEVATED")

    # evaluate_prompt_vs_oracle_coverage
    cov = oracle.evaluate_prompt_vs_oracle_coverage(list(audit_mod.CYA_TO_ALETHEIA_MAPPING))
    check_eq(cov["total_checks"], 12, "12 checks")
    check_eq(cov["covered_count"], 2, "2 covered")
    check_eq(cov["partial_count"], 4, "4 partial")
    check_eq(cov["gap_v15_count"], 6, "6 v15 gaps")
    check_eq(cov["prompt_blind_count"], 12, "12 prompt blind")
    check_eq(cov["covered_ratio"], "1/6", "covered ratio")
    check_eq(cov["covered_pct"], "16.67", "covered pct")
    check_eq(cov["covered_or_partial_ratio"], "1/2", "covered+partial ratio")
    check_eq(cov["v15_gap_ratio"], "1/2", "gap ratio")
    check_eq(cov["prompt_blind_ratio"], "1/1", "blind ratio")

    # Non-blind check branch
    cov_mix = oracle.evaluate_prompt_vs_oracle_coverage(
        [
            {"check_id": "C1", "cya_line": 1, "aletheia_v140_status": "COVERED", "cya_gap_id": "NONE", "prompt_blind_spot": False},
        ]
    )
    check_eq(cov_mix["prompt_blind_count"], 0, "prompt_blind False counted")
    check_eq(cov_mix["prompt_blind_pct"], "0.00", "0 pct")

    # Coverage refusals
    check_raises(lambda: oracle.evaluate_prompt_vs_oracle_coverage([{"bad": 1}]), "SCHEMA_ERROR", "bad schema")
    check_raises(lambda: oracle.evaluate_prompt_vs_oracle_coverage(["not_dict"]), "SCHEMA_ERROR", "non-dict item")
    dup_item = {"check_id": "C1", "cya_line": 1, "aletheia_v140_status": "COVERED", "cya_gap_id": "NONE", "prompt_blind_spot": True}
    check_raises(lambda: oracle.evaluate_prompt_vs_oracle_coverage([dup_item, dup_item]), "DUPLICATE_ID", "dup check_id")
    bad_line = dict(dup_item, cya_line=0)
    check_raises(lambda: oracle.evaluate_prompt_vs_oracle_coverage([bad_line]), "INVALID_RANGE", "line 0")
    bad_status = dict(dup_item, aletheia_v140_status="UNKNOWN")
    check_raises(lambda: oracle.evaluate_prompt_vs_oracle_coverage([bad_status]), "INVALID_STATUS", "bad status")
    bad_cov_gap = dict(dup_item, cya_gap_id="CYA-GAP-01")
    check_raises(lambda: oracle.evaluate_prompt_vs_oracle_coverage([bad_cov_gap]), "INCONSISTENT_GAP", "covered with gap")
    bad_partial_none = dict(dup_item, aletheia_v140_status="PARTIAL", cya_gap_id="NONE")
    check_raises(lambda: oracle.evaluate_prompt_vs_oracle_coverage([bad_partial_none]), "INCONSISTENT_GAP", "partial with NONE (JDPRU-BYPASS-05)")
    bad_gap_none = dict(dup_item, aletheia_v140_status="GAP_V15", cya_gap_id="NONE")
    check_raises(lambda: oracle.evaluate_prompt_vs_oracle_coverage([bad_gap_none]), "INCONSISTENT_GAP", "gap with NONE")


def test_pillar2_oracles_and_refusals() -> None:
    # compute_kish_neff_and_deff_exact: uniform (slack 0), 3-point (slack > 0), small-domain cap15 (slack 0), cap exceeded
    u = oracle.compute_kish_neff_and_deff_exact([2, 2, 2, 2])
    check_eq(u["deff"], "1/1", "uniform DEFF 1")
    check_eq(u["n_eff"], "4/1", "uniform n_eff 4")
    check_eq(u["bhatia_davis_slack"], "0/1", "uniform slack 0")
    check_eq(u["weight_cap"], "NONE", "no cap")
    check_eq(u["cap_exceeded"], False, "no cap exceeded")

    three_pt = oracle.compute_kish_neff_and_deff_exact(["1/2", "1", "3/2"], weight_cap="1")
    check_eq(three_pt["deff"], "7/6", "3-pt DEFF")
    check_eq(three_pt["n_eff"], "18/7", "3-pt n_eff")
    check_eq(three_pt["bhatia_davis_upper_deff"], "5/4", "3-pt BD upper")
    check_eq(three_pt["bhatia_davis_slack"], "1/12", "3-pt positive slack")
    check_eq(three_pt["bhatia_davis_satisfied"], True, "BD satisfied")
    check_eq(three_pt["cap_exceeded"], True, "cap exceeded True")
    check_eq(three_pt["cap_exceeded_count"], 1, "1 weight > cap 1")

    # Boundary: w == weight_cap is NOT exceeded
    eq_cap = oracle.compute_kish_neff_and_deff_exact([1, 5], weight_cap=5)
    check_eq(eq_cap["cap_exceeded"], False, "w == cap not exceeded")
    check_eq(eq_cap["cap_exceeded_count"], 0, "0 exceeded at boundary")

    check_raises(lambda: oracle.compute_kish_neff_and_deff_exact([0, 1]), "INVALID_WEIGHT", "zero weight")
    check_raises(lambda: oracle.compute_kish_neff_and_deff_exact([-1, 2]), "INVALID_WEIGHT", "neg weight")
    check_raises(lambda: oracle.compute_kish_neff_and_deff_exact([1, 2], weight_cap=0), "INVALID_RANGE", "zero cap")
    check_raises(lambda: oracle.compute_kish_neff_and_deff_exact([1, 2], weight_cap=-1), "INVALID_RANGE", "neg cap")

    # compute_kish_from_summary_stats_exact
    v_s = oracle.compute_kish_from_summary_stats_exact(54535, "1", "1.31757", sd_is_sample=True)
    v_p = oracle.compute_kish_from_summary_stats_exact(54535, "1", "1.31757", sd_is_sample=False)
    check_eq(v_s["deff_decimal"], "2.735959", "V103 sample DEFF")
    check_eq(v_s["n_eff_decimal"], "19932.68", "V103 sample n_eff")
    check_eq(v_s["sample_loss_pct"], "63.45", "V103 sample loss pct")
    check_eq(v_p["deff_decimal"], "2.735991", "V103 pop DEFF")
    check_eq(v_p["n_eff_decimal"], "19932.45", "V103 pop n_eff")
    v_zero_sd = oracle.compute_kish_from_summary_stats_exact(1, "2", "0", sd_is_sample=False)
    check_eq(v_zero_sd["deff"], "1/1", "n=1 pop zero sd")
    check_eq(v_zero_sd["n_eff"], "1/1", "n=1 pop n_eff")
    v_n2 = oracle.compute_kish_from_summary_stats_exact(2, "1", "1", sd_is_sample=True)
    check_eq(v_n2["deff"], "3/2", "n=2 sample boundary")
    check_raises(lambda: oracle.compute_kish_from_summary_stats_exact(1, "1", "0", sd_is_sample=True), "INVALID_RANGE", "n<2 sample")
    check_raises(lambda: oracle.compute_kish_from_summary_stats_exact(0, "1", "0", sd_is_sample=False), "INVALID_RANGE", "n<1 pop")
    check_raises(lambda: oracle.compute_kish_from_summary_stats_exact(10, "0", "1", sd_is_sample=True), "INVALID_RANGE", "mean<=0")
    check_raises(lambda: oracle.compute_kish_from_summary_stats_exact(10, "1", "-1", sd_is_sample=True), "INVALID_RANGE", "sd<0")

    # compute_extremal_deff_bound_exact
    bd_deg = oracle.compute_extremal_deff_bound_exact("1", "1")
    check_eq(bd_deg["deff_max"], "1/1", "degenerate [1,1] DEFF 1")
    check_eq(bd_deg["extremal_mass_at_wmax"], "0/1", "degenerate p_max 0")
    bd_cap5 = oracle.compute_extremal_deff_bound_exact("0", "5")
    check_eq(bd_cap5["deff_max"], "5/1", "cap 5 DEFF 5")
    check_eq(bd_cap5["min_neff_fraction"], "1/5", "cap 5 retention 1/5")
    check_eq(bd_cap5["max_sample_loss_pct"], "80.00", "cap 5 loss 80%")
    check_eq(bd_cap5["extremal_mass_at_wmax"], "1/5", "cap 5 p_max 1/5")
    bd_pos = oracle.compute_extremal_deff_bound_exact("1/2", "3")
    check_eq(bd_pos["deff_max"], "2/1", "wmin=1/2, wmax=3 DEFF 2")
    check_eq(bd_pos["extremal_mass_at_wmax"], "1/5", "p_max 1/5")
    check_raises(lambda: oracle.compute_extremal_deff_bound_exact("-1/10", "5"), "INVALID_RANGE", "w_min < 0")
    check_raises(lambda: oracle.compute_extremal_deff_bound_exact("3/2", "5"), "INVALID_RANGE", "w_min > 1")
    check_raises(lambda: oracle.compute_extremal_deff_bound_exact("0", "1/2"), "INVALID_RANGE", "w_max < 1")

    # compute_meng_effective_n_exact
    m_bare = oracle.compute_meng_effective_n_exact("1/100", "-1/200")
    check_eq(m_bare["n_eff_meng"], "40000/99", "Meng exact 40000/99")
    check_eq(m_bare["n_eff_meng_decimal"], "404.04", "Meng 404.04")
    check_true("n_sample" not in m_bare, "no n_sample key when omitted")
    m_edge = oracle.compute_meng_effective_n_exact("1/2", "1", n_sample=1)
    check_eq(m_edge["n_eff_meng"], "1/1", "f=1/2 rho=1 edge")
    check_eq(m_edge["efficiency_ratio"], "1/1", "eff ratio 1")
    m_neg1 = oracle.compute_meng_effective_n_exact("1/2", "-1")
    check_eq(m_neg1["n_eff_meng"], "1/1", "rho=-1 boundary")
    check_raises(lambda: oracle.compute_meng_effective_n_exact("0", "1/2"), "INVALID_RANGE", "f=0")
    check_raises(lambda: oracle.compute_meng_effective_n_exact("1", "1/2"), "INVALID_RANGE", "f=1")
    check_raises(lambda: oracle.compute_meng_effective_n_exact("1/2", "0"), "INVALID_RANGE", "rho=0")
    check_raises(lambda: oracle.compute_meng_effective_n_exact("1/2", "-3/2"), "INVALID_RANGE", "rho<-1")
    check_raises(lambda: oracle.compute_meng_effective_n_exact("1/2", "3/2"), "INVALID_RANGE", "rho>1")
    check_raises(lambda: oracle.compute_meng_effective_n_exact("1/2", "1/2", n_sample=0), "INVALID_RANGE", "n_sample<=0")

    # audit_bias_variance_weighting_mse_exact
    mse_worse = oracle.audit_bias_variance_weighting_mse_exact("3", "3", "100", [1, 3])
    check_eq(mse_worse["deff"], "5/4", "weights [1,3] DEFF 5/4")
    check_eq(mse_worse["mse_unweighted"], "59/1", "unwt MSE 9 + 50")
    check_eq(mse_worse["mse_weighted"], "143/2", "wt MSE 9 + 62.5")
    check_eq(mse_worse["delta_mse"], "25/2", "delta MSE +12.5")
    check_eq(mse_worse["bias_sq_reduction"], "0/1", "0 bias gain")
    check_eq(mse_worse["variance_penalty"], "25/2", "var penalty 12.5")
    check_eq(mse_worse["worsened_by_weighting"], True, "worsened True")

    mse_better = oracle.audit_bias_variance_weighting_mse_exact("10", "0", "0", [1, 3])
    check_eq(mse_better["worsened_by_weighting"], False, "bias reduction wins, var=0 boundary")
    check_eq(mse_better["delta_mse"], "-100/1", "delta -100")
    check_raises(lambda: oracle.audit_bias_variance_weighting_mse_exact("0", "0", "-1", [1, 1]), "INVALID_RANGE", "neg var")

    # audit_national_raking_state_simpson_exact
    s_win = oracle.audit_national_raking_state_simpson_exact(
        [
            {"state_id": "S1", "n_a": 80, "n_b": 20, "mean_y_a": "3/5", "mean_y_b": "1/5", "true_y": "3/5"},
            {"state_id": "S2", "n_a": 80, "n_b": 20, "mean_y_a": "2/5", "mean_y_b": "4/5", "true_y": "2/5"},
        ],
        "1/2",
    )
    check_eq(s_win["national_bias_before"], "3/10", "nat bias before")
    check_eq(s_win["national_bias_after"], "0/1", "nat bias after 0")
    check_eq(s_win["national_deff"], "25/16", "nat DEFF 25/16")
    check_eq(s_win["national_n_eff"], "128/1", "nat n_eff 128")
    check_eq(s_win["state_mae_before"], "2/25", "state MAE before")
    check_eq(s_win["state_mae_after"], "1/5", "state MAE after")
    check_eq(s_win["all_states_worsened"], True, "all worsened")
    check_eq(s_win["simpson_worsening_triggered"], True, "simpson triggered")

    s_noworse = oracle.audit_national_raking_state_simpson_exact(
        [{"state_id": "S1", "n_a": 50, "n_b": 50, "mean_y_a": "1", "mean_y_b": "0", "true_y": "1/2"}],
        "1/2",
    )
    check_eq(s_noworse["all_states_worsened"], False, "exact target not worsened")
    check_eq(s_noworse["simpson_worsening_triggered"], False, "simpson False")

    valid_st = {"state_id": "S1", "n_a": 10, "n_b": 10, "mean_y_a": "1", "mean_y_b": "0", "true_y": "1/2"}
    check_raises(lambda: oracle.audit_national_raking_state_simpson_exact([valid_st], "0"), "INVALID_RANGE", "tau=0")
    check_raises(lambda: oracle.audit_national_raking_state_simpson_exact([valid_st], "1"), "INVALID_RANGE", "tau=1")
    check_raises(lambda: oracle.audit_national_raking_state_simpson_exact([{"bad": 1}], "1/2"), "SCHEMA_ERROR", "bad state schema")
    check_raises(lambda: oracle.audit_national_raking_state_simpson_exact(["bad"], "1/2"), "SCHEMA_ERROR", "non-dict state")
    check_raises(lambda: oracle.audit_national_raking_state_simpson_exact([valid_st, valid_st], "1/2"), "DUPLICATE_ID", "dup state_id")
    check_raises(lambda: oracle.audit_national_raking_state_simpson_exact([dict(valid_st, n_a=0)], "1/2"), "INVALID_RANGE", "n_a=0")
    check_raises(lambda: oracle.audit_national_raking_state_simpson_exact([dict(valid_st, n_b=0)], "1/2"), "INVALID_RANGE", "n_b=0")

    # audit_ces_tail_conservation_and_drift
    td = oracle.audit_ces_tail_conservation_and_drift(
        7208, 357, 106, 251, 108, 359,
        {"A": "1.0", "B": "2.0"},
        {"A": "1.0", "B": "2.5"},
    )
    check_eq(td["net_tail_delta"], 2, "net +2")
    check_eq(td["tail_worsened"], True, "tail worsened")
    check_eq(td["matching_gt20_pct"], "4.95", "4.95%")
    check_eq(td["stayed_gt20_pct"], "3.48", "3.48%")
    check_eq(td["weighted_gt20_pct"], "4.98", "4.98%")
    check_eq(td["drift_count"], 1, "1 drifted")
    check_eq(td["all_metrics_aligned"], False, "not aligned")

    td_ok = oracle.audit_ces_tail_conservation_and_drift(
        10, 5, 5, 0, 0, 0, {"A": "1"}, {"A": "1"}
    )
    check_eq(td_ok["tail_worsened"], False, "tail improved")
    check_eq(td_ok["all_metrics_aligned"], True, "all aligned")
    check_eq(td_ok["stayed_le20"], 5, "stayed_le20 exact")

    # Boundary: matching_gt20 + crossed_above20 == n_obs (stayed_le20 == 0) MUST succeed
    td_exact_full = oracle.audit_ces_tail_conservation_and_drift(
        150, 100, 50, 50, 50, 100, {"A": "1"}, {"A": "1"}
    )
    check_eq(td_exact_full["stayed_le20"], 0, "exact full contingency boundary allowed")

    check_raises(lambda: oracle.audit_ces_tail_conservation_and_drift(0, 0, 0, 0, 0, 0, {"A": "1"}, {"A": "1"}), "INVALID_RANGE", "n_obs=0")
    check_raises(lambda: oracle.audit_ces_tail_conservation_and_drift(10, -1, 0, 0, 0, 0, {"A": "1"}, {"A": "1"}), "INVALID_RANGE", "neg count")
    check_raises(lambda: oracle.audit_ces_tail_conservation_and_drift(10, 11, 0, 11, 0, 11, {"A": "1"}, {"A": "1"}), "INVALID_RANGE", "count > n_obs")
    check_raises(lambda: oracle.audit_ces_tail_conservation_and_drift(10, 5, 1, 3, 1, 4, {"A": "1"}, {"A": "1"}), "TAIL_CONSERVATION_VIOLATION", "first flow bad")
    check_raises(lambda: oracle.audit_ces_tail_conservation_and_drift(10, 5, 2, 3, 1, 5, {"A": "1"}, {"A": "1"}), "TAIL_CONSERVATION_VIOLATION", "second flow bad")
    check_raises(
        lambda: oracle.audit_ces_tail_conservation_and_drift(150, 100, 50, 50, 100, 150, {"A": "1"}, {"A": "1"}),
        "TAIL_CONSERVATION_VIOLATION",
        "impossible contingency table (JDPRU-BYPASS-04)",
    )
    check_raises(lambda: oracle.audit_ces_tail_conservation_and_drift(10, 5, 2, 3, 1, 4, [], {"A": "1"}), "TYPE_ERROR", "readme not dict")
    check_raises(lambda: oracle.audit_ces_tail_conservation_and_drift(10, 5, 2, 3, 1, 4, {"A": "1"}, []), "TYPE_ERROR", "csv not dict")
    check_raises(lambda: oracle.audit_ces_tail_conservation_and_drift(10, 5, 2, 3, 1, 4, {}, {}), "SCHEMA_ERROR", "empty metric dicts")
    check_raises(lambda: oracle.audit_ces_tail_conservation_and_drift(10, 5, 2, 3, 1, 4, {"A": "1"}, {"B": "1"}), "SCHEMA_ERROR", "mismatched keys")
    check_raises(lambda: oracle.audit_ces_tail_conservation_and_drift(10, 5, 2, 3, 1, 4, {1: "1", "A": "1"}, {1: "1", "A": "1"}), "TYPE_ERROR", "non-str metric key")
    check_raises(lambda: oracle.audit_ces_tail_conservation_and_drift(10, 5, 2, 3, 1, 4, {"A": "1", " A ": "1"}, {"A": "1", " A ": "1"}), "DUPLICATE_ID", "colliding trimmed metric keys")


def test_audit_runner_standalone_and_synthetic_live() -> None:
    # Standalone mode + CLI (--json, summary, --output)
    cert_s = audit_mod.run_audit(standalone=True)
    check_eq(cert_s["execution_mode"], "standalone_fixture", "standalone mode")
    check_eq(cert_s["verdict"], "VERIFIED", "standalone verified")
    check_eq(cert_s["pillar1_cover_your_ais"]["cya_prompt_hidden_unicode_audit"]["clean"], True, "cya clean")
    check_eq(cert_s["pillar1_cover_your_ais"]["live_ces_claude_md_self_audit"]["finding_count"], 5, "5 claude findings")
    check_eq(cert_s["pillar2_ces_accuracy_analysis"]["anesrake_used_range"], "6--9", "anesrake 6--9")
    check_eq(cert_s["pillar2_ces_accuracy_analysis"]["a2_named_only_sign_flips"]["matching_sign_flipped"], True, "match flipped")
    check_eq(cert_s["pillar2_ces_accuracy_analysis"]["a2_named_only_sign_flips"]["weighted_sign_flipped"], True, "wtd flipped")

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        out_json = tmp_path / "cert.json"

        # CLI --standalone --json --output
        buf_json = io.StringIO()
        with contextlib.redirect_stdout(buf_json):
            rc = audit_mod.main(["--standalone", "--json", "--output", str(out_json)])
        check_eq(rc, 0, "cli json exit 0")
        check_eq(out_json.read_text(encoding="ascii"), buf_json.getvalue(), "file matches stdout json")

        # CLI --standalone summary mode
        buf_sum = io.StringIO()
        with contextlib.redirect_stdout(buf_sum):
            rc2 = audit_mod.main(["--standalone"])
        check_eq(rc2, 0, "cli summary exit 0")
        sum_obj = json.loads(buf_sum.getvalue())
        check_eq(sum_obj["verdict"], "VERIFIED", "summary verdict")
        check_eq(sum_obj["certificate_sha256"], cert_s["certificate_sha256"], "summary sha matches")

        # Synthetic live workspace: loose ref, detached HEAD, packed-refs
        for mode in ("loose", "detached", "packed"):
            ws = tmp_path / f"ws_{mode}"
            _create_synthetic_jdpru_workspace(ws, head_mode=mode)
            cert_live = audit_mod.run_audit(standalone=False, repos_root=ws)
            check_eq(cert_live["execution_mode"], "live_readonly", f"{mode} live mode")
            check_eq(cert_live["verdict"], "VERIFIED", f"{mode} verified")
            check_eq(cert_live["pillar2_ces_accuracy_analysis"]["anesrake_used_range"], "6--9", f"{mode} xlsx range")
            check_eq(len(cert_live["artifact_sha256"]), 8, f"{mode} 8 file shas")

        # CLI --repos-root path
        buf_live = io.StringIO()
        with contextlib.redirect_stdout(buf_live):
            rc3 = audit_mod.main(["--repos-root", str(tmp_path / "ws_loose")])
        check_eq(rc3, 0, "cli live exit 0")

        # Refusal tests for _resolve_git_head_sha
        empty_repo = tmp_path / "empty_repo"
        empty_repo.mkdir()
        check_raises(lambda: audit_mod._resolve_git_head_sha(empty_repo), "MISSING_GIT_HEAD", "missing .git/HEAD")

        bad_sha_repo = tmp_path / "bad_sha_repo"
        (bad_sha_repo / ".git").mkdir(parents=True)
        (bad_sha_repo / ".git" / "HEAD").write_text("not_a_sha\n", encoding="utf-8")
        check_raises(lambda: audit_mod._resolve_git_head_sha(bad_sha_repo), "INVALID_GIT_SHA", "invalid detached sha")

        dangling_ref = tmp_path / "dangling_ref"
        (dangling_ref / ".git").mkdir(parents=True)
        (dangling_ref / ".git" / "HEAD").write_text("ref: refs/heads/missing\n", encoding="utf-8")
        check_raises(lambda: audit_mod._resolve_git_head_sha(dangling_ref), "INVALID_GIT_SHA", "dangling ref without packed")

        dangling_packed = tmp_path / "dangling_packed"
        (dangling_packed / ".git").mkdir(parents=True)
        (dangling_packed / ".git" / "HEAD").write_text("ref: refs/heads/other\n", encoding="utf-8")
        (dangling_packed / ".git" / "packed-refs").write_text(
            "a" * 40 + " refs/heads/main\n", encoding="utf-8"
        )
        check_raises(lambda: audit_mod._resolve_git_head_sha(dangling_packed), "INVALID_GIT_SHA", "ref absent in packed-refs")

        # JDPRU-BYPASS-03: path traversal & symlink escape refusals in _resolve_git_head_sha
        outside_sha = tmp_path / "outside_sha.txt"
        outside_sha.write_text("b" * 40 + "\n", encoding="utf-8")
        for label, bad_ref in (
            ("parent_traversal", "ref: ../../outside_sha.txt\n"),
            ("refs_parent_traversal", "ref: refs/../../outside_sha.txt\n"),
        ):
            trav_repo = tmp_path / f"trav_{label}"
            (trav_repo / ".git").mkdir(parents=True)
            (trav_repo / ".git" / "HEAD").write_text(bad_ref, encoding="utf-8")
            check_raises(lambda r=trav_repo: audit_mod._resolve_git_head_sha(r), "INVALID_GIT_REF", label)

        sym_repo = tmp_path / "sym_repo"
        (sym_repo / ".git" / "refs" / "heads").mkdir(parents=True)
        (sym_repo / ".git" / "HEAD").write_text("ref: refs/heads/main\n", encoding="utf-8")
        (sym_repo / ".git" / "refs" / "heads" / "main").symlink_to(outside_sha)
        check_raises(lambda: audit_mod._resolve_git_head_sha(sym_repo), "INVALID_GIT_REF", "symlink ref escape")

        # Refusal tests for _parse_int_comma, _parse_csv_macro_map, _parse_anesrake_used_xlsx
        check_eq(audit_mod._parse_int_comma("10,487", "n"), 10487, "parse comma int")
        check_raises(lambda: audit_mod._parse_int_comma("12.5", "n"), "PARSE_ERROR", "non-int comma")

        bad_csv = tmp_path / "bad.csv"
        bad_csv.write_text("foo,bar\n1,2\n", encoding="utf-8")
        check_raises(lambda: audit_mod._parse_csv_macro_map(bad_csv, "base"), "SCHEMA_ERROR", "missing macro col")

        empty_csv = tmp_path / "empty.csv"
        empty_csv.write_text("", encoding="utf-8")
        check_raises(lambda: audit_mod._parse_csv_macro_map(empty_csv, "base"), "SCHEMA_ERROR", "empty csv")

        # XLSX without sharedStrings + empty cell + insufficient rows
        inline_xlsx = tmp_path / "inline.xlsx"
        _make_minimal_xlsx(inline_xlsx, [["Variable", "2020"], ["Age", "Used"], ["Sex", ""]], use_shared_strings=False)
        check_eq(audit_mod._parse_anesrake_used_xlsx(inline_xlsx), {"2020": 1}, "inline xlsx without sharedStrings")

        short_xlsx = tmp_path / "short.xlsx"
        _make_minimal_xlsx(short_xlsx, [["OnlyHeader"]], use_shared_strings=True)
        check_raises(lambda: audit_mod._parse_anesrake_used_xlsx(short_xlsx), "SCHEMA_ERROR", "short xlsx")

        narrow_xlsx = tmp_path / "narrow.xlsx"
        _make_minimal_xlsx(narrow_xlsx, [["OnlyCol"], ["Row1"]], use_shared_strings=True)
        check_raises(lambda: audit_mod._parse_anesrake_used_xlsx(narrow_xlsx), "SCHEMA_ERROR", "narrow xlsx")

        # Live workspace tampering refusals
        ws_head = tmp_path / "ws_head_bad"
        _create_synthetic_jdpru_workspace(ws_head, tamper_head=True)
        check_raises(lambda: audit_mod.run_audit(standalone=False, repos_root=ws_head), "HEAD_MISMATCH", "head mismatch")

        ws_omit = tmp_path / "ws_omit"
        _create_synthetic_jdpru_workspace(ws_omit, omit_file=True)
        check_raises(lambda: audit_mod.run_audit(standalone=False, repos_root=ws_omit), "MISSING_FILE", "missing file")

        ws_anch = tmp_path / "ws_anch"
        _create_synthetic_jdpru_workspace(ws_anch, tamper_anchor=True)
        check_raises(lambda: audit_mod.run_audit(standalone=False, repos_root=ws_anch), "ANCHOR_MISMATCH", "anchor mismatch")

        ws_tot = tmp_path / "ws_tot"
        _create_synthetic_jdpru_workspace(ws_tot, tamper_total=True)
        check_raises(lambda: audit_mod.run_audit(standalone=False, repos_root=ws_tot), "COUNT_MISMATCH", "obs partition mismatch")

    # Default live repos root (when running inside expedition workspace)
    default_root = Path(__file__).resolve().parent.parent / "repos" / "jdpru"
    if (default_root / "cover-your-ais" / ".git" / "HEAD").is_file():
        cert_real = audit_mod.run_audit(standalone=False)
        check_eq(cert_real["verdict"], "VERIFIED", "default live repos verified")
        check_eq(cert_real["pillar1_cover_your_ais"]["cya_prompt_hidden_unicode_audit"]["clean"], True, "real cya clean")
        check_eq(cert_real["pillar2_ces_accuracy_analysis"]["tail_conservation_and_readme_drift"]["drift_count"], 7, "real 7 drifts")


def main() -> int:
    tests = [
        ("primitives_and_refusals", test_primitives_and_refusals),
        ("pillar1_scanners_and_coverage", test_pillar1_scanners_and_coverage),
        ("pillar2_oracles_and_refusals", test_pillar2_oracles_and_refusals),
        ("audit_runner_standalone_and_synthetic_live", test_audit_runner_standalone_and_synthetic_live),
    ]
    for name, fn in tests:
        fn()
    sys.stdout.write(json.dumps({"suite": "test_jdpru_epistemic_r5", "passed": len(tests), "status": "PASS"}, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
