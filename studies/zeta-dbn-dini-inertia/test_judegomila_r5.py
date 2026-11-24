#!/usr/bin/env python3
"""R5 adversarial refusal & boundary test suite for hardened_dini_and_r5_mutator.py.

Designed to achieve 100.0% AST mutation kill rate under `aletheia mutate`,
testing every positive gate, every negative tamper class (exact domain bounds,
banner, sentinel, line count, leg order/primes/N-range/contiguity/patterns/counts,
ratio_ub bounds/exact worst, witness L/y box containment, cross-precision
aliasing & disagreement, C-source binding, symlink rejection), and every -O-immune
truncation boundary (closing J-01 and J-02).

Zero bare asserts. Safe under python3 -I -O -B and PYTHONHASHSEED=12345.
"""

from __future__ import annotations

from decimal import Decimal
from fractions import Fraction
import os
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
if str(Path(__file__).resolve().parent) not in sys.path:
    sys.path.insert(0, str(Path(__file__).resolve().parent))

import hardened_dini_and_r5_mutator as mod

SAMPLE_180 = "\n".join(
    [
        mod.DINI_BANNER,
        "PASS P=235711 N=690988..728999 patterns=243 rects=297490 splits=297004 h_nonpositive=93662 ratio_ub=0.99999860767275095 worst={gmask=19,r=(0,1],L=[1.0418546566960283,1.0543084951295314],y=[0.19969058624497746,0.20217430455339475],branch=1}",
        "PASS P=2357 N=729000..818999 patterns=81 rects=52239 splits=52077 h_nonpositive=15287 ratio_ub=0.99997108289971948 worst={gmask=15,r=(0,1],L=[2.5190428321629144,2.5315489667629487],y=[0.20714174117022932,0.20962545947864661],branch=1}",
        "PASS P=235 N=819000..1027999 patterns=27 rects=9290 splits=9236 h_nonpositive=4367 ratio_ub=0.99999531591311097 worst={gmask=7,r=(0,1],L=[0.71838681372645952,0.72469672201858804],y=[0.20714174117022932,0.20962545947864661],branch=1}",
        "PASS P=23 N=1028000..3840000 patterns=9 rects=237 splits=219 h_nonpositive=81 ratio_ub=0.99224051320925355 worst={gmask=3,r=(0,1],L=[3.5697049871544797,3.9806418166682707],y=[0.26675098057224422,0.34622996644159743],branch=1}",
        mod.DINI_SENTINEL,
    ]
) + "\n"

SAMPLE_256 = SAMPLE_180.replace(
    "0.99997108289971948", "0.99997108988463879"
).replace(
    "0.99999531591311097", "0.99999531405046582"
).replace(
    "0.99224051320925355", "0.99224052112549543"
)

SAMPLE_C_SOURCE = "\n".join(mod.REQUIRED_DINI_C_TOKENS) + "\n"


def _require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"TEST FAILURE: {msg}")


def _expect_reject(fn, msg: str) -> None:
    try:
        fn()
    except mod.HardenedAuditError:
        return
    raise RuntimeError(f"MUTATION ESCAPE — expected HardenedAuditError: {msg}")


def _replace_line(text: str, idx: int, new_line: str) -> str:
    lines = text.splitlines()
    lines[idx] = new_line
    return "\n".join(lines) + "\n"


def run_all_tests() -> dict[str, int]:
    passed = 0

    # 1. Exact domain check + parameterized negative tamper controls (kills M003..M009!)
    dom = mod.verify_dini_domain_exact()
    _require(dom["t0"] == "129/800", "t0 exact")
    _require(dom["y0_sq"] == "87677/2500000", "y0_sq exact")
    _require(dom["ymax_sq"] == "271/400", "ymax_sq exact")
    _require(dom["lambda_bound"] == "893927/5000000", "lambda_bound exact")
    _require(dom["expected_slack"] == "27846544981/20000000000000000", "slack exact")
    _expect_reject(
        lambda: mod.verify_dini_domain_exact(
            t0=Fraction(130, 800), lam_bound=Fraction(130, 800) + mod.Y0_SQ_EXACT / 2
        ),
        "tampered t0 with consistent lam_bound",
    )
    _expect_reject(
        lambda: mod.verify_dini_domain_exact(
            y0_sq=Fraction(87678, 2_500_000),
            lam_bound=mod.T0_EXACT + Fraction(87678, 2_500_000) / 2,
        ),
        "tampered y0_sq with consistent lam_bound",
    )
    _expect_reject(lambda: mod.verify_dini_domain_exact(lam_bound=Fraction(893928, 5_000_000)), "tampered lam_bound")
    _expect_reject(lambda: mod.verify_dini_domain_exact(ybox_lo=Fraction(1, 2)), "ybox_lo too large")
    _expect_reject(lambda: mod.verify_dini_domain_exact(ybox_hi=Fraction(1, 2)), "ybox_hi too small")
    passed += 1

    # 2. Positive log / pair / source acceptance + general (expected_worst=None) mode
    pair = mod.audit_dini_pair_texts(SAMPLE_180, SAMPLE_256, require_distinct_traces=True)
    _require(pair["status"] == "PASS", "pair status PASS")
    _require(pair["worst_ratio"] == "0.99999860767275095", "pair worst ratio")
    src_ok = mod.audit_dini_source_text(SAMPLE_C_SOURCE)
    _require(src_ok["status"] == "PASS", "source PASS")
    mod.audit_dini_log_text(SAMPLE_180, expected_worst=None)
    passed += 1

    # 3. Tight boundary acceptance (l_lo == l_hi, y_lo == YBOX_LO_DEC, y_hi == YBOX_HI_DEC, splits=0, hnp=0, hnp=rects)
    boundary_row = (
        "PASS P=23 N=1028000..3840000 patterns=9 rects=1 splits=0 h_nonpositive=0 "
        "ratio_ub=0.5 worst={gmask=3,r=(0,1],L=[1.0,1.0],"
        "y=[0.187271994702891,0.823103881657717],branch=0}"
    )
    mod.audit_dini_log_text(_replace_line(SAMPLE_180, 4, boundary_row))
    boundary_row2 = (
        "PASS P=23 N=1028000..3840000 patterns=9 rects=5 splits=4 h_nonpositive=5 "
        "ratio_ub=0.5 worst={gmask=3,r=(0,1],L=[1.0,1.0],"
        "y=[0.5,0.5],branch=1}"
    )
    mod.audit_dini_log_text(_replace_line(SAMPLE_180, 4, boundary_row2))
    passed += 1

    # 4. Line count (including middle-line smuggling before sentinel!), banner, sentinel rejections
    base_lines = SAMPLE_180.splitlines()
    smuggled_7 = "\n".join(base_lines[:5] + ["SMUGGLED EXTRA LINE", base_lines[5]]) + "\n"
    _expect_reject(lambda: mod.audit_dini_log_text(smuggled_7), "smuggled 7th line before sentinel")
    _expect_reject(lambda: mod.audit_dini_log_text("\n".join(base_lines[:-1])), "5 lines")
    _expect_reject(lambda: mod.audit_dini_log_text(_replace_line(SAMPLE_180, 0, mod.DINI_BANNER + " extra")), "bad banner")
    _expect_reject(lambda: mod.audit_dini_log_text(_replace_line(SAMPLE_180, 5, mod.DINI_SENTINEL + "!")), "bad sentinel")
    passed += 1

    # 5. Strict grammar, duplicate ratio_ub, domain/order/patterns mismatch, AND custom gapped leg_specs contiguity!
    _expect_reject(
        lambda: mod.audit_dini_log_text(
            _replace_line(SAMPLE_180, 1, SAMPLE_180.splitlines()[1] + " ratio_ub=0.1")
        ),
        "duplicate ratio_ub / trailing junk",
    )
    _expect_reject(
        lambda: mod.audit_dini_log_text(
            _replace_line(SAMPLE_180, 1, SAMPLE_180.splitlines()[1].replace("P=235711", "P=2357"))
        ),
        "swapped primes label",
    )
    _expect_reject(
        lambda: mod.audit_dini_log_text(
            _replace_line(SAMPLE_180, 4, SAMPLE_180.splitlines()[4].replace("patterns=9", "patterns=8"))
        ),
        "wrong patterns count",
    )
    # Test contiguity guard independently using a gapped custom spec matching the tampered log!
    gapped_specs = (
        ("235711", 690_988, 728_999, 243),
        ("2357", 729_001, 818_999, 81),  # gap at 729000!
        ("235", 819_000, 1_027_999, 27),
        ("23", 1_028_000, 3_840_000, 9),
    )
    gapped_log = _replace_line(
        SAMPLE_180, 2, SAMPLE_180.splitlines()[2].replace("N=729000..818999", "N=729001..818999")
    )
    _expect_reject(
        lambda: mod.audit_dini_log_text(gapped_log, leg_specs=gapped_specs),
        "non-contiguous leg_specs gap",
    )
    passed += 1

    # 6. Rects / splits / h_nonpositive boundaries
    for bad_fields, desc in (
        ("rects=0 splits=0 h_nonpositive=0", "rects==0"),
        ("rects=5 splits=5 h_nonpositive=1", "splits==rects"),
        ("rects=5 splits=2 h_nonpositive=6", "hnp>rects"),
    ):
        bad_row = (
            f"PASS P=23 N=1028000..3840000 patterns=9 {bad_fields} "
            "ratio_ub=0.5 worst={gmask=3,r=(0,1],L=[1.0,2.0],y=[0.3,0.4],branch=1}"
        )
        _expect_reject(lambda r=bad_row: mod.audit_dini_log_text(_replace_line(SAMPLE_180, 4, r)), desc)
    passed += 1

    # 7. Ratio bounds (0, 1) independently of expected_worst + exact worst gate + decimal parser
    # Non-worst leg 4 set to 0 / -0.5 keeps max == EXPECTED_WORST_DEC, isolating 0 < ratio!
    for bad_low, desc in (("0", "non-worst ratio==0"), ("-0.5", "non-worst ratio<0")):
        bad_row = SAMPLE_180.splitlines()[4].replace("0.99224051320925355", bad_low)
        _expect_reject(lambda r=bad_row: mod.audit_dini_log_text(_replace_line(SAMPLE_180, 4, r)), desc)
    # expected_worst=None isolates ratio < 1!
    for bad_high, desc in (("1", "ratio==1 under expected_worst=None"), ("1.000001", "ratio>1 under expected_worst=None")):
        bad_row = SAMPLE_180.splitlines()[1].replace("0.99999860767275095", bad_high)
        _expect_reject(
            lambda r=bad_row: mod.audit_dini_log_text(_replace_line(SAMPLE_180, 1, r), expected_worst=None),
            desc,
        )
    # Valid ratio in (0, 1) that differs from EXPECTED_WORST_DEC isolates worst != expected_worst!
    _expect_reject(
        lambda: mod.audit_dini_log_text(
            _replace_line(SAMPLE_180, 1, SAMPLE_180.splitlines()[1].replace("0.99999860767275095", "0.999998"))
        ),
        "worst != EXPECTED_WORST_DEC",
    )
    _expect_reject(lambda: mod._parse_finite_decimal("not_a_number", "x"), "malformed decimal")
    _expect_reject(lambda: mod._parse_finite_decimal("NaN", "x"), "NaN decimal")
    _expect_reject(lambda: mod._parse_finite_decimal("Infinity", "x"), "Inf decimal")
    passed += 1

    # 8. Witness box L and y containment rejections
    for bad_witness, desc in (
        ("L=[0,1.0],y=[0.3,0.4]", "L_lo==0"),
        ("L=[-1.0,1.0],y=[0.3,0.4]", "L_lo<0"),
        ("L=[2.0,1.0],y=[0.3,0.4]", "L_lo>L_hi"),
        ("L=[1.0,2.0],y=[0.187271994702890,0.4]", "y_lo<ybox_lo"),
        ("L=[1.0,2.0],y=[0.5,0.4]", "y_lo>y_hi"),
        ("L=[1.0,2.0],y=[0.3,0.823103881657718]", "y_hi>ybox_hi"),
    ):
        bad_row = (
            "PASS P=23 N=1028000..3840000 patterns=9 rects=10 splits=4 h_nonpositive=2 "
            f"ratio_ub=0.5 worst={{gmask=3,r=(0,1],{bad_witness},branch=1}}"
        )
        _expect_reject(lambda r=bad_row: mod.audit_dini_log_text(_replace_line(SAMPLE_180, 4, r)), desc)
    passed += 1

    # 9. Cross-precision aliasing and disagreement rejections + tolerance boundary acceptance
    _expect_reject(
        lambda: mod.audit_dini_pair_texts(SAMPLE_180, SAMPLE_180, require_distinct_traces=True),
        "byte-identical 180/256 aliasing",
    )
    r4_180 = Decimal("0.99224051320925355")
    r4_at_tol = str(r4_180 + mod.PAIR_AGREEMENT_TOL)
    r4_over_tol = str(r4_180 + mod.PAIR_AGREEMENT_TOL + Decimal("1e-10"))
    mod.audit_dini_pair_texts(
        SAMPLE_180,
        SAMPLE_180.replace("0.99224051320925355", r4_at_tol),
        require_distinct_traces=True,
    )
    _expect_reject(
        lambda: mod.audit_dini_pair_texts(
            SAMPLE_180,
            SAMPLE_180.replace("0.99224051320925355", r4_over_tol),
            require_distinct_traces=True,
        ),
        "180-vs-256 diff > 1e-7",
    )
    passed += 1

    # 10. C source token missing rejection & symlink/missing-file rejection
    for tok in mod.REQUIRED_DINI_C_TOKENS:
        _expect_reject(
            lambda t=tok: mod.audit_dini_source_text(SAMPLE_C_SOURCE.replace(t, "")),
            f"missing C token {tok}",
        )
    with tempfile.TemporaryDirectory() as td:
        root = Path(td)
        (root / "logs").mkdir()
        (root / "verifiers").mkdir()
        (root / "logs" / "triangle_y_dini_180.log").write_text(SAMPLE_180, encoding="utf-8")
        (root / "logs" / "triangle_y_dini_256.log").write_text(SAMPLE_256, encoding="utf-8")
        (root / "verifiers" / "verify_triangle_y_dini_arb.c").write_text(SAMPLE_C_SOURCE, encoding="utf-8")
        repo_res = mod.audit_dini_repo_files(root)
        _require(repo_res["pair"]["status"] == "PASS", "temp repo PASS")
        (root / "logs" / "triangle_y_dini_256.log").unlink()
        _expect_reject(lambda: mod.audit_dini_repo_files(root), "missing 256 log")
        os.symlink(root / "logs" / "triangle_y_dini_180.log", root / "logs" / "triangle_y_dini_256.log")
        _expect_reject(lambda: mod.audit_dini_repo_files(root), "symlink 256 log")
    passed += 1

    # 11. J-02 -O-immune safe_floor_trunc / safe_ceil_trunc exact values + negative/type/digits rejections
    _require(mod.safe_floor_trunc(Fraction(1, 3), 10) == "0.3333333333", "floor 1/3")
    _require(mod.safe_ceil_trunc(Fraction(1, 3), 10) == "0.3333333334", "ceil 1/3")
    _require(mod.safe_floor_trunc(Fraction(0), 2) == "0.00", "floor 0")
    _require(mod.safe_ceil_trunc(Fraction(0), 2) == "0.00", "ceil 0")
    _require(mod.safe_floor_trunc(Fraction(1, 4), 2) == "0.25", "floor 1/4")
    _require(mod.safe_ceil_trunc(Fraction(1, 4), 2) == "0.25", "ceil 1/4")
    _require(mod.safe_floor_trunc(Fraction(5, 2), 0) == "2", "floor 0 digits")
    _require(mod.safe_ceil_trunc(Fraction(5, 2), 0) == "3", "ceil 0 digits")
    for fn in (mod.safe_floor_trunc, mod.safe_ceil_trunc):
        _expect_reject(lambda f=fn: f(Fraction(-1, 100), 2), f"{fn.__name__} negative v")
        _expect_reject(lambda f=fn: f(0.5, 2), f"{fn.__name__} float rejection")  # type: ignore[arg-type]
        _expect_reject(lambda f=fn: f(Fraction(1, 2), -1), f"{fn.__name__} negative digits")
        _expect_reject(lambda f=fn: f(Fraction(1, 2), True), f"{fn.__name__} bool digits")
        _expect_reject(lambda f=fn: f(Fraction(1, 2), "2"), f"{fn.__name__} str digits")  # type: ignore[arg-type]
    passed += 1

    # 12. Live verification against read-only judegomila-dbn-audit clone (when available)
    real_repo = Path(__file__).resolve().parent.parent / "repos" / "judegomila-dbn-audit"
    if real_repo.is_dir():
        real_res = mod.audit_dini_repo_files(real_repo)
        _require(real_res["pair"]["status"] == "PASS", "real repo Dini PASS")
        _require(real_res["source"]["status"] == "PASS", "real repo C source PASS")
    passed += 1

    return {"groups_passed": passed}


if __name__ == "__main__":
    summary = run_all_tests()
    print(f"R5_HARDENED_DINI_SUITE PASS ({summary['groups_passed']} test groups)")
    sys.exit(0)
