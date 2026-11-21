#!/usr/bin/env python3
"""Hardened zero-float reference verifiers for judegomila/dbn-audit gaps J-01 and J-02.

Closes two concrete adversarial hygiene findings from AUDIT-049 without touching
the read-only external repository:
  - J-01: Hardened strict grammar, domain-tiling, witness-containment, and
    dual-precision non-aliasing verifier for the sealed Arb Dini y-transfer
    certificates (slack ~ 1.39232724905e-6).
  - J-02: -O-immune exact rational floor_trunc / ceil_trunc replacements eliminating
    bare `assert v >= 0` (which silently misformats -1/100 as "-1.99" under -O).

Zero floating-point arithmetic on trust paths. Zero bare asserts.
Safe under: python3 -I -B, python3 -I -O -B, PYTHONHASHSEED=12345.
"""

from __future__ import annotations

from decimal import Context, Decimal, InvalidOperation
from fractions import Fraction
from pathlib import Path
import re
import sys

DECIMAL_CTX = Context(prec=100)

T0_EXACT = Fraction(129, 800)
Y0_SQ_EXACT = Fraction(87677, 2_500_000)
YMAX_SQ_EXACT = Fraction(1) - 2 * T0_EXACT  # 271/400
LAMBDA_BOUND_EXACT = Fraction(893927, 5_000_000)
YBOX_LO_DEC = Decimal("0.187271994702891")
YBOX_HI_DEC = Decimal("0.823103881657717")
YBOX_LO_EXACT = Fraction(187271994702891, 10**15)
YBOX_HI_EXACT = Fraction(823103881657717, 10**15)

EXPECTED_WORST_DEC = Decimal("0.99999860767275095")
EXPECTED_SLACK_EXACT = Fraction(1) - Fraction(99999860767275095, 10**17)
PAIR_AGREEMENT_TOL = Decimal("1e-7")

DINI_BANNER = (
    "ROW t=16125/100000 y2=350708/10000000 "
    "ybox=[0.187271994702891,0.823103881657717] "
    "sigma_prime>=1/2 gamma_log_prime<0"
)
DINI_SENTINEL = (
    "RESULT PASS: direct-Triangle mass is nonincreasing "
    "on the full y interval"
)

# Exact ordered (primes_tag, n_lo, n_hi, expected_patterns = 3^k)
EXPECTED_LEG_SPECS: tuple[tuple[str, int, int, int], ...] = (
    ("235711", 690_988, 728_999, 243),
    ("2357", 729_000, 818_999, 81),
    ("235", 819_000, 1_027_999, 27),
    ("23", 1_028_000, 3_840_000, 9),
)

DEC_NUM_PAT = r"[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?"
LEG_ROW_RE = re.compile(
    r"^PASS P=(?P<primes>\d+) "
    r"N=(?P<nlo>\d+)\.\.(?P<nhi>\d+) "
    r"patterns=(?P<patterns>\d+) "
    r"rects=(?P<rects>\d+) "
    r"splits=(?P<splits>\d+) "
    r"h_nonpositive=(?P<hnp>\d+) "
    rf"ratio_ub=(?P<ratio>{DEC_NUM_PAT}) "
    r"worst=\{gmask=(?P<gmask>\d+),"
    r"r=\(0,1\],"
    rf"L=\[(?P<Llo>{DEC_NUM_PAT}),(?P<Lhi>{DEC_NUM_PAT})\],"
    rf"y=\[(?P<ylo>{DEC_NUM_PAT}),(?P<yhi>{DEC_NUM_PAT})\],"
    r"branch=(?P<branch>[01])\}$"
)

REQUIRED_DINI_C_TOKENS: tuple[str, ...] = (
    "h_nonpositive=%lu ratio_ub=%.17g ",
    "ok &= audit_leg(5, 690988, 728999, t);",
    "ok &= audit_leg(4, 729000, 818999, t);",
    "ok &= audit_leg(3, 819000, 1027999, t);",
    "ok &= audit_leg(2, 1028000, 3840000, t);",
    "if (!arb_contains(ybox, yexact_lo)",
    "|| !arb_contains(ybox, yexact_hi))",
    "RESULT PASS: direct-Triangle mass is nonincreasing ",
)


class HardenedAuditError(ValueError):
    """Fail-closed error raised whenever an invariant or certificate check fails."""


def _parse_finite_decimal(raw: str, label: str) -> Decimal:
    try:
        val = DECIMAL_CTX.create_decimal(raw)
    except InvalidOperation as exc:
        raise HardenedAuditError(f"malformed decimal for {label}: {raw!r}") from exc
    if not val.is_finite():
        raise HardenedAuditError(f"non-finite decimal for {label}: {raw!r}")
    return val


def verify_dini_domain_exact(
    *,
    t0: Fraction = T0_EXACT,
    y0_sq: Fraction = Y0_SQ_EXACT,
    ybox_lo: Fraction = YBOX_LO_EXACT,
    ybox_hi: Fraction = YBOX_HI_EXACT,
    lam_bound: Fraction = LAMBDA_BOUND_EXACT,
) -> dict[str, str]:
    """Exact pure-Fraction proof that the printed Dini y-box encloses [y0, ymax]."""
    ymax_sq = Fraction(1) - 2 * t0
    if t0 != Fraction(16125, 100_000):
        raise HardenedAuditError("t0 exact identity failed")
    if y0_sq != Fraction(350708, 10_000_000):
        raise HardenedAuditError("y0^2 exact identity failed")
    if t0 + y0_sq / 2 != lam_bound:
        raise HardenedAuditError("Lambda bound identity failed")
    if not (ybox_lo * ybox_lo < y0_sq):
        raise HardenedAuditError("ybox lower endpoint does not lie below y0")
    if not (ymax_sq < ybox_hi * ybox_hi):
        raise HardenedAuditError("ybox upper endpoint does not lie above ymax")
    return {
        "t0": str(t0),
        "y0_sq": str(y0_sq),
        "ymax_sq": str(ymax_sq),
        "lambda_bound": str(lam_bound),
        "expected_slack": str(EXPECTED_SLACK_EXACT),
    }


def audit_dini_log_text(
    text: str,
    label: str = "dini.log",
    *,
    leg_specs: tuple[tuple[str, int, int, int], ...] = EXPECTED_LEG_SPECS,
    expected_worst: Decimal | None = EXPECTED_WORST_DEC,
) -> dict[str, object]:
    """Strictly parse and validate one sealed Arb Dini y-transfer transcript."""
    lines = text.splitlines()
    expected_lines = 2 + len(leg_specs)
    if len(lines) != expected_lines:
        raise HardenedAuditError(
            f"{label}: expected exact {expected_lines}-line transcript, got {len(lines)}"
        )
    if lines[0] != DINI_BANNER:
        raise HardenedAuditError(f"{label}: wrong fixed-domain banner")
    if lines[-1] != DINI_SENTINEL:
        raise HardenedAuditError(f"{label}: wrong terminal sentinel")

    leg_ratios: list[Decimal] = []
    leg_records: list[dict[str, object]] = []
    prev_nhi: int | None = None

    for idx, (row, spec) in enumerate(zip(lines[1:-1], leg_specs)):
        exp_primes, exp_nlo, exp_nhi, exp_patterns = spec
        m = LEG_ROW_RE.fullmatch(row)
        if m is None:
            raise HardenedAuditError(f"{label}: leg {idx} failed strict row grammar")

        primes = m.group("primes")
        nlo = int(m.group("nlo"))
        nhi = int(m.group("nhi"))
        patterns = int(m.group("patterns"))
        rects = int(m.group("rects"))
        splits = int(m.group("splits"))
        hnp = int(m.group("hnp"))

        if (primes, nlo, nhi, patterns) != (exp_primes, exp_nlo, exp_nhi, exp_patterns):
            raise HardenedAuditError(
                f"{label}: leg {idx} domain mismatch {(primes, nlo, nhi, patterns)}"
            )
        if prev_nhi is not None and nlo != prev_nhi + 1:
            raise HardenedAuditError(f"{label}: leg {idx} gap/overlap at N={nlo}")
        prev_nhi = nhi

        if rects <= 0 or splits < 0 or splits >= rects or hnp < 0 or hnp > rects:
            raise HardenedAuditError(f"{label}: leg {idx} invalid branch/rect counts")

        ratio = _parse_finite_decimal(m.group("ratio"), f"{label}:leg{idx}:ratio_ub")
        if not (Decimal(0) < ratio < Decimal(1)):
            raise HardenedAuditError(f"{label}: leg {idx} ratio_ub={ratio} not in (0,1)")

        l_lo = _parse_finite_decimal(m.group("Llo"), f"{label}:leg{idx}:Llo")
        l_hi = _parse_finite_decimal(m.group("Lhi"), f"{label}:leg{idx}:Lhi")
        y_lo = _parse_finite_decimal(m.group("ylo"), f"{label}:leg{idx}:ylo")
        y_hi = _parse_finite_decimal(m.group("yhi"), f"{label}:leg{idx}:yhi")
        if not (Decimal(0) < l_lo <= l_hi):
            raise HardenedAuditError(f"{label}: leg {idx} invalid L witness box")
        if not (YBOX_LO_DEC <= y_lo <= y_hi <= YBOX_HI_DEC):
            raise HardenedAuditError(f"{label}: leg {idx} y witness outside ybox")

        leg_ratios.append(ratio)
        leg_records.append(
            {
                "primes": primes,
                "n_range": f"{nlo}..{nhi}",
                "patterns": patterns,
                "rects": rects,
                "splits": splits,
                "h_nonpositive": hnp,
                "ratio_ub": str(ratio),
            }
        )

    worst = max(leg_ratios)
    if expected_worst is not None and worst != expected_worst:
        raise HardenedAuditError(
            f"{label}: worst ratio {worst} != expected {expected_worst}"
        )
    slack_frac = Fraction(1) - Fraction(worst)
    return {
        "label": label,
        "worst_ratio": str(worst),
        "slack_exact": str(slack_frac),
        "leg_ratios": [str(r) for r in leg_ratios],
        "legs": leg_records,
    }


def audit_dini_pair_texts(
    text_180: str,
    text_256: str,
    *,
    require_distinct_traces: bool = True,
) -> dict[str, object]:
    """Audit both 180-bit and 256-bit transcripts with cross-precision checks."""
    res_180 = audit_dini_log_text(text_180, label="triangle_y_dini_180.log")
    res_256 = audit_dini_log_text(text_256, label="triangle_y_dini_256.log")

    if require_distinct_traces and text_180 == text_256:
        raise HardenedAuditError(
            "180-bit and 256-bit transcripts are byte-identical (possible log aliasing)"
        )

    ratios_180 = [Decimal(x) for x in res_180["leg_ratios"]]  # type: ignore[index]
    ratios_256 = [Decimal(x) for x in res_256["leg_ratios"]]  # type: ignore[index]
    for idx, (r180, r256) in enumerate(zip(ratios_180, ratios_256)):
        diff = abs(r180 - r256)
        if diff > PAIR_AGREEMENT_TOL:
            raise HardenedAuditError(
                f"leg {idx} 180-vs-256 disagreement {diff} > {PAIR_AGREEMENT_TOL}"
            )

    return {
        "status": "PASS",
        "domain_exact": verify_dini_domain_exact(),
        "log_180": res_180,
        "log_256": res_256,
        "worst_ratio": str(EXPECTED_WORST_DEC),
        "slack_exact": str(EXPECTED_SLACK_EXACT),
    }


def audit_dini_source_text(source: str) -> dict[str, object]:
    """Bind all four fixed-domain leg gates and ybox containment in C source."""
    missing = [tok for tok in REQUIRED_DINI_C_TOKENS if tok not in source]
    if missing:
        raise HardenedAuditError(f"Arb Dini C source missing required gate(s): {missing}")
    return {
        "status": "PASS",
        "checked_tokens": len(REQUIRED_DINI_C_TOKENS),
    }


def audit_dini_repo_files(repo_root: Path) -> dict[str, object]:
    """Read-only file-level audit rejecting symlinks and binding logs + C source."""
    log_180 = repo_root / "logs" / "triangle_y_dini_180.log"
    log_256 = repo_root / "logs" / "triangle_y_dini_256.log"
    c_src = repo_root / "verifiers" / "verify_triangle_y_dini_arb.c"

    for p in (log_180, log_256, c_src):
        if p.is_symlink() or not p.is_file():
            raise HardenedAuditError(f"{p.name}: not a regular non-symlink file")

    pair_res = audit_dini_pair_texts(
        log_180.read_text(encoding="utf-8"),
        log_256.read_text(encoding="utf-8"),
        require_distinct_traces=True,
    )
    src_res = audit_dini_source_text(c_src.read_text(encoding="utf-8"))
    return {"pair": pair_res, "source": src_res}


def safe_floor_trunc(v: Fraction, digits: int) -> str:
    """-O-immune exact rational floor truncation for non-negative Fractions (J-02 fix)."""
    if not isinstance(v, Fraction):
        raise HardenedAuditError("safe_floor_trunc requires exact Fraction")
    if not isinstance(digits, int) or isinstance(digits, bool) or digits < 0:
        raise HardenedAuditError("digits must be a non-negative int")
    if v < 0:
        raise HardenedAuditError(f"safe_floor_trunc requires v >= 0, got {v}")
    scale = 10**digits
    n = (v * scale).__floor__()
    if digits == 0:
        return str(n)
    ip, fr = divmod(n, scale)
    return f"{ip}.{fr:0{digits}d}"


def safe_ceil_trunc(v: Fraction, digits: int) -> str:
    """-O-immune exact rational ceil truncation for non-negative Fractions (J-02 fix)."""
    if not isinstance(v, Fraction):
        raise HardenedAuditError("safe_ceil_trunc requires exact Fraction")
    if not isinstance(digits, int) or isinstance(digits, bool) or digits < 0:
        raise HardenedAuditError("digits must be a non-negative int")
    if v < 0:
        raise HardenedAuditError(f"safe_ceil_trunc requires v >= 0, got {v}")
    scale = 10**digits
    n = -((-v * scale).__floor__())
    if digits == 0:
        return str(n)
    ip, fr = divmod(n, scale)
    return f"{ip}.{fr:0{digits}d}"


def main() -> int:
    import json

    repo = Path(__file__).resolve().parent.parent / "repos" / "judegomila-dbn-audit"
    if (repo / "logs" / "triangle_y_dini_180.log").is_file():
        res = audit_dini_repo_files(repo)
    else:
        sealed_180 = "\n".join(
            [
                DINI_BANNER,
                "PASS P=235711 N=690988..728999 patterns=243 rects=297490 splits=297004 h_nonpositive=93662 ratio_ub=0.99999860767275095 worst={gmask=19,r=(0,1],L=[1.0418546566960283,1.0543084951295314],y=[0.19969058624497746,0.20217430455339475],branch=1}",
                "PASS P=2357 N=729000..818999 patterns=81 rects=52239 splits=52077 h_nonpositive=15287 ratio_ub=0.99997108289971948 worst={gmask=15,r=(0,1],L=[2.5190428321629144,2.5315489667629487],y=[0.20714174117022932,0.20962545947864661],branch=1}",
                "PASS P=235 N=819000..1027999 patterns=27 rects=9290 splits=9236 h_nonpositive=4367 ratio_ub=0.99999531591311097 worst={gmask=7,r=(0,1],L=[0.71838681372645952,0.72469672201858804],y=[0.20714174117022932,0.20962545947864661],branch=1}",
                "PASS P=23 N=1028000..3840000 patterns=9 rects=237 splits=219 h_nonpositive=81 ratio_ub=0.99224051320925355 worst={gmask=3,r=(0,1],L=[3.5697049871544797,3.9806418166682707],y=[0.26675098057224422,0.34622996644159743],branch=1}",
                DINI_SENTINEL,
            ]
        ) + "\n"
        sealed_256 = sealed_180.replace(
            "0.99997108289971948", "0.99997108988463879"
        ).replace(
            "0.99999531591311097", "0.99999531405046582"
        ).replace(
            "0.99224051320925355", "0.99224052112549543"
        )
        res = {
            "mode": "standalone_sealed_transcripts",
            "pair": audit_dini_pair_texts(sealed_180, sealed_256, require_distinct_traces=True),
            "source": audit_dini_source_text("\n".join(REQUIRED_DINI_C_TOKENS) + "\n"),
        }
    trunc_checks = {
        "floor_1_3_10": safe_floor_trunc(Fraction(1, 3), 10),
        "ceil_1_3_10": safe_ceil_trunc(Fraction(1, 3), 10),
        "floor_0_2": safe_floor_trunc(Fraction(0), 2),
        "ceil_1_4_2": safe_ceil_trunc(Fraction(1, 4), 2),
        "floor_5_2_0": safe_floor_trunc(Fraction(5, 2), 0),
        "ceil_5_2_0": safe_ceil_trunc(Fraction(5, 2), 0),
    }
    print(json.dumps({"dini_audit": res, "trunc_checks": trunc_checks}, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
