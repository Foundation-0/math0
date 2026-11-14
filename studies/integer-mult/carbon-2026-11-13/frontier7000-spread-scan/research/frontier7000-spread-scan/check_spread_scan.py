#!/usr/bin/env python3
"""
check_spread_scan.py — Standalone Zero-Float `fractions.Fraction` Certificate Checker
for `research/frontier7000-spread-scan/` (`CrocSwap/integer-mult-bounds`).

Refuses `-O` / `-OO` / nonzero `PYTHONOPTIMIZE` fail-closed.
"""

from __future__ import annotations

import hashlib
import json
import os
import sys

if sys.flags.optimize > 0 or os.environ.get("PYTHONOPTIMIZE", "").strip() not in ("", "0"):
    sys.stderr.write("FATAL: optimized Python (-O / PYTHONOPTIMIZE) is forbidden by verification contract.\n")
    sys.exit(2)

from fractions import Fraction
from pathlib import Path
from typing import Any

RADIX_34 = 10**42


def parse_q(val: str | int) -> Fraction:
    if isinstance(val, int):
        return Fraction(val, 1)
    if not isinstance(val, str) or "." in val:
        raise ValueError(f"Expected exact integer or a/b rational string, got {val!r}")
    return Fraction(val)


def floor_radix(x: Fraction, D: int = RADIX_34) -> Fraction:
    return Fraction((x.numerator * D) // x.denominator, D)


def ceil_radix(x: Fraction, D: int = RADIX_34) -> Fraction:
    return Fraction(-((-x.numerator * D) // x.denominator), D)


def rational_ln_interval(num: int, den: int = 1, terms: int = 38) -> tuple[Fraction, Fraction]:
    """Outward-directed rational interval `[lo, hi]` for `ln(num / den)` (`num >= den >= 1`)."""
    assert num >= den >= 1 and terms >= 8
    if num == den:
        return Fraction(0), Fraction(0)
    D = 10**46

    def atanh_2_interval(z: Fraction, k_terms: int) -> tuple[Fraction, Fraction]:
        assert abs(z) <= Fraction(1, 3)
        z2 = z * z
        zp = z
        lo_acc = 0
        hi_acc = 0
        for j in range(k_terms):
            term = (2 * zp) / (2 * j + 1)
            lo_acc += (term.numerator * D) // term.denominator
            hi_acc += -((-term.numerator * D) // term.denominator)
            zp *= z2
        rem = (2 * abs(zp)) / ((2 * k_terms + 1) * (1 - z2))
        rem_up = -((-rem.numerator * D) // rem.denominator)
        return Fraction(lo_acc - rem_up, D), Fraction(hi_acc + rem_up, D)

    ln2_lo, ln2_hi = atanh_2_interval(Fraction(1, 3), terms)
    k = 0
    while Fraction(num, den * (1 << k)) > Fraction(4, 3):
        k += 1
    u = Fraction(num, den * (1 << k))
    assert Fraction(2, 3) <= u <= Fraction(4, 3)
    z = (u - 1) / (u + 1)
    u_lo, u_hi = atanh_2_interval(z, terms)
    return floor_radix(k * ln2_lo + u_lo), ceil_radix(k * ln2_hi + u_hi)


def rational_exp_neg_interval(x_lo: Fraction, x_hi: Fraction, terms: int = 30) -> tuple[Fraction, Fraction]:
    """
    Outward-directed rational interval `[lo, hi]` for `exp(-x) = 1 / exp(x)` given `0 <= x_lo <= x <= x_hi <= 1`.
    """
    assert Fraction(0) <= x_lo <= x_hi <= Fraction(1) and terms >= 8
    D = 10**46
    lo_term = D
    hi_term = D
    lo_sum = D
    hi_sum = D
    for j in range(1, terms):
        lo_term = (lo_term * x_lo.numerator) // (x_lo.denominator * j)
        hi_term = -((-hi_term * x_hi.numerator) // (x_hi.denominator * j))
        lo_sum += lo_term
        hi_sum += hi_term
    hi_next = -((-hi_term * x_hi.numerator) // (x_hi.denominator * terms))
    rem_frac = Fraction(hi_next, D) * Fraction(terms + 1, 1) / (Fraction(terms + 1, 1) - x_hi)
    rem_up = -((-rem_frac.numerator * D) // rem_frac.denominator)
    exp_pos_lo = Fraction(lo_sum, D)
    exp_pos_hi = Fraction(hi_sum + rem_up, D)
    return floor_radix(Fraction(1, 1) / exp_pos_hi), ceil_radix(Fraction(1, 1) / exp_pos_lo)


_LN_CACHE: dict[int, tuple[Fraction, Fraction]] = {}


def enclose_r_pow_1_minus_c(r: int, c: Fraction) -> tuple[Fraction, Fraction]:
    """Sound rational interval `[L, U]` containing `r^(1 - c) = r * exp(-c * ln r)` (`r >= 1`, `0 <= c < 1/10`)."""
    assert r >= 1 and Fraction(0) <= c < Fraction(1, 10)
    if r == 1 or c == 0:
        v = Fraction(r, 1) if c == 0 else Fraction(1, 1)
        return v, v
    if r not in _LN_CACHE:
        _LN_CACHE[r] = rational_ln_interval(r, 1)
    ln_lo, ln_hi = _LN_CACHE[r]
    x_lo, x_hi = c * ln_lo, c * ln_hi
    e_lo, e_hi = rational_exp_neg_interval(x_lo, x_hi)
    return floor_radix(Fraction(r, 1) * e_lo), ceil_radix(Fraction(r, 1) * e_hi)


def enclose_margin(T: dict[int, int], P: dict[int, int], c: Fraction) -> tuple[Fraction, Fraction]:
    """
    Sound rational interval `[margin_lo, margin_hi]` for `sum_r T_r r^(1-c) - sum_r P_r r^(1-c)`.
    - If `margin_lo > 0`, `c` is strictly BELOW the true root `c*` (`c < c*`).
    - If `margin_hi < 0`, `c` is strictly ABOVE the true root `c*` (`c > c*`).
    """
    t_lo = Fraction(0)
    t_hi = Fraction(0)
    for r, cnt in T.items():
        if cnt:
            lo, hi = enclose_r_pow_1_minus_c(r, c)
            t_lo += cnt * lo
            t_hi += cnt * hi
    p_lo = Fraction(0)
    p_hi = Fraction(0)
    for r, cnt in P.items():
        if cnt:
            lo, hi = enclose_r_pow_1_minus_c(r, c)
            p_lo += cnt * lo
            p_hi += cnt * hi
    return t_lo - p_hi, t_hi - p_lo


def verify_root_bracket(T: dict[int, int], P: dict[int, int], c_lo: Fraction, c_hi: Fraction, label: str) -> None:
    if not (Fraction(0) < c_lo < c_hi):
        raise ValueError(f"{label}: invalid bracket order {c_lo} >= {c_hi}")
    m_lo_at_clo, _ = enclose_margin(T, P, c_lo)
    if not (m_lo_at_clo > 0):
        raise ValueError(f"{label}: lower bracket c_lo={c_lo} failed strict positivity (margin_lo={m_lo_at_clo})")
    _, m_hi_at_chi = enclose_margin(T, P, c_hi)
    if not (m_hi_at_chi < 0):
        raise ValueError(f"{label}: upper bracket c_hi={c_hi} failed strict negativity (margin_hi={m_hi_at_chi})")


def mat_mul_int(A: list[list[int]], B: list[list[int]]) -> list[list[int]]:
    n, inner, m = len(A), len(B), len(B[0])
    return [[sum(A[i][k] * B[k][j] for k in range(inner)) for j in range(m)] for i in range(n)]


def exact_rank_q_int(M: list[list[int]]) -> int:
    A = [[Fraction(x, 1) for x in row] for row in M]
    rows, cols = len(A), len(A[0])
    rk = 0
    for c in range(cols):
        piv = next((r for r in range(rk, rows) if A[r][c] != 0), None)
        if piv is None:
            continue
        A[rk], A[piv] = A[piv], A[rk]
        pv = A[rk][c]
        for r in range(rk + 1, rows):
            if A[r][c] != 0:
                fac = A[r][c] / pv
                for j in range(c, cols):
                    A[r][j] -= fac * A[rk][j]
        rk += 1
    return rk


def verify_certificate_dict(cert: dict[str, Any]) -> dict[str, Any]:
    claimed_sha = cert.get("certificate_sha256")
    if not isinstance(claimed_sha, str) or len(claimed_sha) != 64:
        raise ValueError("Missing or malformed certificate_sha256")
    body = {k: v for k, v in cert.items() if k != "certificate_sha256"}
    actual_sha = hashlib.sha256(
        json.dumps(body, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    if actual_sha != claimed_sha:
        raise ValueError(f"SHA-256 mismatch: expected {claimed_sha}, got {actual_sha}")

    # 1. Verify Frontier #7000 baseline histograms, 3-stratum split, surplus = 1520, and 30-digit raw bracket
    base = cert["frontier7000_baseline"]
    T = {int(k): int(v) for k, v in base["productive_T"].items()}
    P = {int(k): int(v) for k, v in base["paid_P"].items()}
    nat_paid = {int(k): int(v) for k, v in base["native_paid"].items()}

    if sum(T.values()) != 23392 or sum(P.values()) != 117612:
        raise ValueError("Baseline T/P total counts do not match 23,392 / 117,612")
    mass_T = sum(r * c for r, c in T.items())
    mass_P = sum(r * c for r, c in P.items())
    if mass_T != 321364 or mass_P != 319844 or (mass_T - mass_P) != 1520:
        raise ValueError("Baseline rank masses or surplus 1,520 mismatch")
    if sum(nat_paid.values()) != 6310 or sum(r * c for r, c in nat_paid.items()) != 10962:
        raise ValueError("native.paid count/mass mismatch")

    # Check exact 3-stratum identity P == 18 * native.paid + 416@r=1 + whole_idles
    whole_idles = {int(k): int(v) for k, v in base["caller_whole_idles"].items()}
    query_r1 = int(base["caller_query_r1"])
    if query_r1 != 416 or sum(whole_idles.values()) != 3616:
        raise ValueError("Caller QUERY / whole-idle counts mismatch")
    if any(r % 8 != 0 for r in whole_idles):
        raise ValueError("Whole-idle rank violates 8Z stage-block dimension lock")
    recon_P: dict[int, int] = {}
    for r, c in nat_paid.items():
        recon_P[r] = recon_P.get(r, 0) + 18 * c
    recon_P[1] = recon_P.get(1, 0) + query_r1
    for r, c in whole_idles.items():
        recon_P[r] = recon_P.get(r, 0) + c
    if recon_P != P:
        raise ValueError("3-stratum paid-call reconstruction failed!")

    k0_lo = parse_q(base["raw_bracket_lo"])
    k0_hi = parse_q(base["raw_bracket_hi"])
    verify_root_bracket(T, P, k0_lo, k0_hi, "frontier7000_raw_bracket")

    k_premise = parse_q(base["complex_BIT_premise"])
    k_bit_adm = parse_q(base["admitted_BIT_saving"])
    if k_premise != Fraction(376669, 100000000) or k_bit_adm != Fraction(12039, 3125000):
        raise ValueError("BIT ceiling constants mismatch")
    if not (k0_hi < k_premise < k_bit_adm):
        raise ValueError("Expected k0 < complex_BIT_premise < admitted_BIT_saving")

    # 2. Verify all 12 legal symmetric pairwise spreads (r, r) -> (r-d, r+d) inside [1, 8]
    spreads = cert["symmetric_pairwise_spreads"]
    if len(spreads) != 12:
        raise ValueError(f"Expected 12 legal symmetric spreads on [1,8], got {len(spreads)}")
    seen_pairs = set()
    for entry in spreads:
        r = int(entry["r"])
        d = int(entry["d"])
        seen_pairs.add((r, d))
        if not (1 <= r - d < r < r + d <= 8):
            raise ValueError(f"Out-of-cap spread ({r}, {d})")
        max_local = int(entry["max_local_pairs"])
        if max_local != nat_paid[r] // 2:
            raise ValueError(f"max_local_pairs mismatch at r={r}")
        # Check exact integer concavity witness
        lhs_i = int(entry["integer_witness_lhs"])
        rhs_i = int(entry["integer_witness_rhs"])
        if lhs_i != r ** (2 * r) or rhs_i != ((r - d) ** (r - d)) * ((r + d) ** (r + d)) or not (lhs_i < rhs_i):
            raise ValueError(f"Integer concavity witness failed for ({r},{r})->({r-d},{r+d})")

        # Construct shifted global paid histogram at bucket saturation and verify exact rational bracket
        P_mod = dict(P)
        P_mod[r] -= 36 * max_local
        P_mod[r - d] = P_mod.get(r - d, 0) + 18 * max_local
        P_mod[r + d] = P_mod.get(r + d, 0) + 18 * max_local
        if any(v < 0 for v in P_mod.values()):
            raise ValueError("Negative paid count after spread")
        if sum(P_mod.values()) != 117612 or sum(rk * cv for rk, cv in P_mod.items()) != 319844:
            raise ValueError("Spread violated count or rank-mass conservation")
        s_lo = parse_q(entry["saturated_k_lo"])
        s_hi = parse_q(entry["saturated_k_hi"])
        if not (s_lo > k0_hi):
            raise ValueError(f"Spread ({r},{d}) did not strictly raise kappa above k0_hi")
        verify_root_bracket(T, P_mod, s_lo, s_hi, f"spread_{r}_{d}")

    if len(seen_pairs) != 12:
        raise ValueError("Duplicate (r, d) entries in symmetric_pairwise_spreads")

    # 3. Verify Global [1, 8] Bauer-Karamata Extreme-Point Balayage & Minimum BIT-Premise Crossing Witness
    bal = cert["bauer_karamata_balayage"]
    nat_bal = {int(k): int(v) for k, v in bal["balayage_native_paid"].items()}
    if sum(nat_bal.values()) != 6310 or sum(r * c for r, c in nat_bal.items()) != 10962:
        raise ValueError("Balayage native.paid violates N=6310 or M=10962 conservation")
    P_bal = {1: query_r1 + 18 * nat_bal.get(1, 0)}
    for r, c in nat_bal.items():
        if r != 1:
            P_bal[r] = P_bal.get(r, 0) + 18 * c
    for r, c in whole_idles.items():
        P_bal[r] = P_bal.get(r, 0) + c
    if sum(P_bal.values()) != 117612 or sum(r * c for r, c in P_bal.items()) != 319844:
        raise ValueError("Global P_bal violates count/mass conservation")
    bal_lo = parse_q(bal["k_balayage_lo"])
    bal_hi = parse_q(bal["k_balayage_hi"])
    verify_root_bracket(T, P_bal, bal_lo, bal_hi, "bauer_karamata_balayage")
    if not (bal_lo > k_bit_adm):
        raise ValueError("Bauer-Karamata balayage did not exceed admitted_BIT_saving")

    # Verify minimum symmetric pair recipe that strictly crosses complex_BIT_premise = 376669/100000000
    cross = cert["bit_premise_crossing_recipe"]
    P_cross = dict(P)
    total_local_pairs_used = 0
    for step in cross["local_pair_moves"]:
        r = int(step["r"])
        d = int(step["d"])
        lp = int(step["local_pairs"])
        if lp < 0 or not (1 <= r - d < r < r + d <= 8):
            raise ValueError("Invalid crossing move")
        P_cross[r] -= 36 * lp
        P_cross[r - d] = P_cross.get(r - d, 0) + 18 * lp
        P_cross[r + d] = P_cross.get(r + d, 0) + 18 * lp
        total_local_pairs_used += lp
    if any(v < 0 for v in P_cross.values()):
        raise ValueError("Crossing recipe overdrew a native.paid bucket!")
    if total_local_pairs_used != int(cross["total_local_pairs"]):
        raise ValueError("Crossing total_local_pairs mismatch")
    cr_lo = parse_q(cross["k_crossing_lo"])
    cr_hi = parse_q(cross["k_crossing_hi"])
    verify_root_bracket(T, P_cross, cr_lo, cr_hi, "bit_premise_crossing")
    if not (cr_lo > k_premise):
        raise ValueError("Crossing recipe failed to strictly exceed complex_BIT_premise!")

    # 4. Verify Explicit GL_9(Z) 2-Wire Flag Re-Pivoting & Coupled-Contact Obstruction Witness
    gl9 = cert["gl9_flag_repivoting_witness"]
    Q1 = [[int(x) for x in row] for row in gl9["Q1_18x18"]]
    Q2 = [[int(x) for x in row] for row in gl9["Q2_18x18"]]
    Q1p = [[int(x) for x in row] for row in gl9["Q1_repiv_18x18"]]
    Q2p = [[int(x) for x in row] for row in gl9["Q2_repiv_18x18"]]
    C_leg = [[int(x) for x in row] for row in gl9["C_commuting_contact_18x18"]]
    C_obs = [[int(x) for x in row] for row in gl9["C_coupled_contact_18x18"]]

    def diff_rank_top9(M18: list[list[int]]) -> int:
        diff = [[M18[i][j] - (1 if i == j else 0) for j in range(9)] for i in range(9)]
        return exact_rank_q_int(diff)

    if diff_rank_top9(Q1) != 5 or diff_rank_top9(Q2) != 5:
        raise ValueError("Original GL_9 moves do not have quotient ranks (5, 5)")
    if diff_rank_top9(Q1p) != 2 or diff_rank_top9(Q2p) != 8:
        raise ValueError("Re-pivoted GL_9 moves do not have quotient ranks (2, 8)")

    orig_leg = mat_mul_int(Q2, mat_mul_int(C_leg, Q1))
    repiv_leg = mat_mul_int(Q2p, mat_mul_int(C_leg, Q1p))
    coalesced_leg = mat_mul_int(mat_mul_int(Q2, Q1), C_leg)
    if orig_leg != repiv_leg:
        raise ValueError("Legal commuting-spectator flag re-pivoting changed 2-wire operator!")
    if orig_leg == coalesced_leg:
        raise ValueError("Intervening contact C_leg trivially allowed coalescing without step-1 move!")

    orig_obs = mat_mul_int(Q2, mat_mul_int(C_obs, Q1))
    repiv_obs = mat_mul_int(Q2p, mat_mul_int(C_obs, Q1p))
    if orig_obs == repiv_obs:
        raise ValueError("Coupled non-commuting contact C_obs failed to obstruct (5,5)->(2,8) spread!")

    return {
        "status": "OK",
        "certificate_sha256": actual_sha,
        "baseline_k_lo": str(k0_lo),
        "balayage_k_lo": str(bal_lo),
        "crossing_local_pairs": total_local_pairs_used,
    }


def main() -> int:
    cert_path = (
        Path(sys.argv[1])
        if len(sys.argv) > 1
        else Path(__file__).resolve().parent / "certificates" / "frontier7000_spread_scan_certificate.json"
    )
    cert = json.loads(cert_path.read_text(encoding="utf-8"))
    res = verify_certificate_dict(cert)
    print(f"CHECK_SPREAD_SCAN_OK sha256={res['certificate_sha256'][:16]}... min_pairs_to_BIT_premise={res['crossing_local_pairs']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
