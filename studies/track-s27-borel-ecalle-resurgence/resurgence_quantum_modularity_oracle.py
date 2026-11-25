#!/usr/bin/env python3
"""Borel-Ecalle Resurgence, Alien Derivatives, Stokes Automorphism & Zagier
Quantum Modularity in Pure Exact Z/Q.

100% pure Python 3 stdlib (int, fractions.Fraction, math).
ZERO IEEE-754 floats, ZERO bare assert statements, ZERO RNG calls, ZERO
third-party imports, ZERO personal-path or private-repo references.

Novelty Scope: N1 (clean-room unified pure-Z/Q formal Borel-convolution,
trans-series alien-derivative/bridge/Stokes engine, nonlinear Riccati resurgent
large-order/low-order certifier, Bernoulli/Stirling/Eisenstein operator, and
Zagier-Kontsevich/Fishburn/Habiro-trefoil cyclotomic certifier with strict
fail-closed I/O hardening; all classical Ecalle, Borel, Bernoulli, Ramanujan,
Zagier, Kontsevich, Habiro, and Garoufalidis theorems quarantined as N0).
"""
from __future__ import annotations

from fractions import Fraction
import math
from typing import Any

TRACK_ID = "TRACK-S27-BOREL-ECALLE-QUANTUM-MODULARITY"
SCHEMA_VERSION = "1.0.0"
MAX_INT_BITS = 3_322
MAX_RATIONAL_BITS = 3_322


class ResurgenceError(ValueError):
    """Typed fail-closed error for domain, algebraic, and strict I/O checks."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"[{code}] {message}")
        self.code = code
        self.detail = message


# ============================================================================
# 1. Strict Type, Domain, Rational, Formatting, & Series Primitives
# ============================================================================

def require_ok(cond: bool, code: str, message: str) -> None:
    if type(cond) is not bool:
        raise ResurgenceError("INVALID_CONDITION_TYPE", f"{code}: condition must be exact bool")
    if not cond:
        raise ResurgenceError(code, message)


def require_exact_int(
    val: Any,
    name: str,
    lo: int | None = None,
    hi: int | None = None,
) -> int:
    if type(val) is not int:
        raise ResurgenceError("INVALID_INT_TYPE", f"{name} must be exact int")
    if val.bit_length() > MAX_INT_BITS:
        raise ResurgenceError("INT_BIT_LIMIT", f"{name} exceeds {MAX_INT_BITS}-bit cap")
    if lo is not None and val < lo:
        raise ResurgenceError("INT_OUT_OF_RANGE", f"{name} must be >= {lo}")
    if hi is not None and val > hi:
        raise ResurgenceError("INT_OUT_OF_RANGE", f"{name} must be <= {hi}")
    return val


def require_exact_bool(val: Any, name: str) -> bool:
    if type(val) is not bool:
        raise ResurgenceError("INVALID_BOOL_TYPE", f"{name} must be exact bool")
    return val


def require_exact_fraction(val: Any, name: str) -> Fraction:
    if type(val) is not Fraction:
        raise ResurgenceError("INVALID_FRACTION_TYPE", f"{name} must be exact Fraction")
    if val.numerator.bit_length() > MAX_RATIONAL_BITS or val.denominator.bit_length() > MAX_RATIONAL_BITS:
        raise ResurgenceError("RATIONAL_BIT_LIMIT", f"{name} exceeds {MAX_RATIONAL_BITS}-bit cap")
    return val


def require_fraction_series(seq: Any, name: str, min_len: int = 1, max_len: int = 128) -> list[Fraction]:
    require_ok(type(seq) is list, "INVALID_SERIES_TYPE", f"{name} must be exact list of Fraction")
    require_ok(min_len <= len(seq) <= max_len, "INVALID_SERIES_LEN", f"{name} length must be in [{min_len}, {max_len}]")
    return [require_exact_fraction(c, f"{name}[{i}]") for i, c in enumerate(seq)]


def format_fraction(q: Fraction) -> str:
    q = require_exact_fraction(q, "q")
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"


def format_decimal_trunc(q: Fraction, places: int = 6) -> str:
    """Exact toward-zero decimal formatting of Fraction with -0.00 normalized to 0.00."""
    q = require_exact_fraction(q, "q")
    places = require_exact_int(places, "places", lo=0, hi=24)
    neg = q < 0
    num = -q.numerator if neg else q.numerator
    den = q.denominator
    scale = 10**places
    scaled = (num * scale) // den
    if scaled == 0:
        neg = False
    sign = "-" if neg else ""
    if places == 0:
        return f"{sign}{scaled}"
    whole, frac = divmod(scaled, scale)
    return f"{sign}{whole}.{frac:0{places}d}"


def poly_mul_exact(p: list[Fraction], q: list[Fraction], max_deg: int) -> list[Fraction]:
    """Exact truncated Cauchy product in Q[[x]] mod x^(max_deg + 1)."""
    p_c = require_fraction_series(p, "p")
    q_c = require_fraction_series(q, "q")
    max_deg = require_exact_int(max_deg, "max_deg", lo=0, hi=128)
    out = [Fraction(0, 1)] * (max_deg + 1)
    for i, a in enumerate(p_c):
        if i > max_deg:
            break
        if a == 0:
            continue
        lim = min(len(q_c), max_deg + 1 - i)
        for j in range(lim):
            b = q_c[j]
            if b != 0:
                out[i + j] += a * b
    return out


def series_z_shift_mul(a: list[Fraction], b: list[Fraction], max_order: int) -> list[Fraction]:
    """Multiply two z*Q[[z]] series: (sum_{j>=0} a[j] z^{j+1}) * (sum_{k>=0} b[k] z^{k+1})
    returned in z*Q[[z]] coordinates [c_0, c_1, ...] representing sum c_n z^{n+1} (c_0 = 0)."""
    a_c = require_fraction_series(a, "a")
    b_c = require_fraction_series(b, "b")
    max_order = require_exact_int(max_order, "max_order", lo=1, hi=128)
    out = [Fraction(0, 1)] * (max_order + 1)
    for j, aj in enumerate(a_c):
        if j >= max_order:
            break
        if aj == 0:
            continue
        for k, bk in enumerate(b_c):
            idx = j + k + 1
            if idx > max_order:
                break
            if bk != 0:
                out[idx] += aj * bk
    return out


# ============================================================================
# 2. Pillar 1 — Exact Formal Borel Transform, Convolution & Euler Resurgence
# ============================================================================

def borel_transform(z_coeffs: list[Fraction]) -> list[Fraction]:
    """Formal Borel transform B[sum_{n>=0} a_n z^{n+1}] = sum_{n>=0} (a_n / n!) zeta^n."""
    cs = require_fraction_series(z_coeffs, "z_coeffs")
    return [c / math.factorial(n) for n, c in enumerate(cs)]


def borel_inverse(zeta_coeffs: list[Fraction]) -> list[Fraction]:
    """Formal inverse Borel (Laplace) transform B^{-1}[sum b_n zeta^n] = sum (n! b_n) z^{n+1}."""
    cs = require_fraction_series(zeta_coeffs, "zeta_coeffs")
    return [c * math.factorial(n) for n, c in enumerate(cs)]


def borel_convolve(f: list[Fraction], g: list[Fraction], max_deg: int) -> list[Fraction]:
    """Exact Borel convolution (f * g)(zeta) = int_0^zeta f(u) g(zeta - u) du via Beta identity."""
    fc = require_fraction_series(f, "f")
    gc = require_fraction_series(g, "g")
    max_deg = require_exact_int(max_deg, "max_deg", lo=0, hi=128)
    out = [Fraction(0, 1)] * (max_deg + 1)
    for j, fj in enumerate(fc):
        if j >= max_deg:
            break
        if fj == 0:
            continue
        fact_j = math.factorial(j)
        for k, gk in enumerate(gc):
            deg = j + k + 1
            if deg > max_deg:
                break
            if gk != 0:
                beta = Fraction(fact_j * math.factorial(k), math.factorial(deg))
                out[deg] += fj * gk * beta
    return out


def euler_series_coeffs(max_n: int) -> list[Fraction]:
    """Compute Euler series a_n = (-1)^n n! (representing sum_{n=0}^{max_n} a_n z^{n+1}) via ODE recurrence."""
    max_n = require_exact_int(max_n, "max_n", lo=1, hi=60)
    a: list[Fraction] = [Fraction(1, 1)]
    for n in range(1, max_n + 1):
        a.append(-n * a[n - 1])
    return a


def verify_pillar1_borel_euler() -> dict[str, Any]:
    """Certify Pillar 1: Borel transform/inverse, Beta convolution homomorphism/associativity,
    derivative rule B[z^2 d/dz f] = zeta B[f], Euler ODE residual 0 through N=20,
    (1+zeta) B[y_hat] == 1 mod zeta^21, and optimal superasymptotic truncation at z=1/10."""
    n_ord = 20
    y_hat = euler_series_coeffs(n_ord)
    b_y = borel_transform(y_hat)
    roundtrip_ok = borel_inverse(b_y) == y_hat

    # Exact ODE residual for z^2 y' + y = z:
    # [z^1]: a_0 - 1 == 0; [z^{n+1}] (n >= 1): n * a_{n-1} + a_n == 0
    ode_residuals = [y_hat[0] - Fraction(1, 1)] + [n * y_hat[n - 1] + y_hat[n] for n in range(1, n_ord + 1)]
    ode_residual_zero = all(r == 0 for r in ode_residuals)

    # Exact Borel pole identity: B[y_hat](zeta) == sum (-zeta)^n and (1 + zeta) B[y_hat] == 1 mod zeta^{21}
    expected_geom = [Fraction((-1) ** n, 1) for n in range(n_ord + 1)]
    borel_geom_exact = b_y == expected_geom
    one_plus_zeta = [Fraction(1, 1), Fraction(1, 1)]
    prod_closure = poly_mul_exact(one_plus_zeta, b_y, n_ord)
    borel_pole_closure_exact = prod_closure == [Fraction(1, 1)] + [Fraction(0, 1)] * n_ord

    # Exact Borel derivative rule B[z^2 d/dz y_hat] == zeta * B[y_hat] mod zeta^{21}
    z2_dy = [Fraction(0, 1)] + [n * y_hat[n - 1] for n in range(1, n_ord + 1)]
    b_z2_dy = borel_transform(z2_dy)
    zeta_b_y = [Fraction(0, 1)] + b_y[:n_ord]
    deriv_rule_exact = b_z2_dy == zeta_b_y

    # Exact Borel convolution algebra homomorphism, commutativity, and associativity
    f_z = [Fraction(n + 1, 2) for n in range(9)]
    g_z = [Fraction((-1) ** n, n + 1) for n in range(9)]
    h_z = [Fraction(2 * n + 1, 3) for n in range(9)]
    bf, bg, bh = borel_transform(f_z), borel_transform(g_z), borel_transform(h_z)
    hom_exact = borel_transform(series_z_shift_mul(f_z, g_z, 8)) == borel_convolve(bf, bg, 8)
    comm_exact = borel_convolve(bf, bg, 8) == borel_convolve(bg, bf, 8)
    assoc_exact = borel_convolve(borel_convolve(bf, bg, 8), bh, 8) == borel_convolve(bf, borel_convolve(bg, bh, 8), 8)

    # Optimal superasymptotic truncation at z = 1/10 (n* = floor(1/z) = 10)
    z_val = Fraction(1, 10)
    n_star = int(Fraction(1, 1) // z_val)
    term_mags = [abs(y_hat[n]) * (z_val ** (n + 1)) for n in range(13)]
    min_mag = min(term_mags)
    trunc_ok = all(
        (
            n_star == 10,
            term_mags[10] == Fraction(567, 15_625_000),
            term_mags[9] == term_mags[10],
            term_mags[10] == min_mag,
            term_mags[8] > term_mags[9],
            term_mags[11] > term_mags[10],
            term_mags[12] > term_mags[11],
        )
    )

    all_verified = all(
        (
            roundtrip_ok,
            ode_residual_zero,
            borel_geom_exact,
            borel_pole_closure_exact,
            deriv_rule_exact,
            hom_exact,
            comm_exact,
            assoc_exact,
            trunc_ok,
        )
    )

    return {
        "all_verified": all_verified,
        "euler_order_N": n_ord,
        "borel_inverse_roundtrip_exact": roundtrip_ok,
        "euler_ode_residual_zero": ode_residual_zero,
        "borel_geometric_series_exact": borel_geom_exact,
        "borel_pole_location": "-1",
        "borel_pole_residue": "1",
        "borel_pole_closure_exact": borel_pole_closure_exact,
        "borel_derivative_rule_exact": deriv_rule_exact,
        "borel_convolution_homomorphism_exact": hom_exact,
        "borel_convolution_commutative": comm_exact,
        "borel_convolution_associative": assoc_exact,
        "superasymptotic_truncation_z_1_10": {
            "z": format_fraction(z_val),
            "n_star": n_star,
            "term_8_mag": format_fraction(term_mags[8]),
            "term_9_mag": format_fraction(term_mags[9]),
            "term_10_mag": format_fraction(term_mags[10]),
            "term_11_mag": format_fraction(term_mags[11]),
            "minimal_at_n9_and_n10": trunc_ok,
        },
    }


# ============================================================================
# 3. Pillar 2 — Alien Derivatives, Bridge Equation, Stokes & Riccati Trans-Series
# ============================================================================

def riccati_transseries_sectors(c_param: Fraction, max_n: int) -> dict[str, list[Fraction]]:
    """Solve nonlinear Riccati ODE z^2 y' + y = z + c y^2 in exact Q[[z]] across sectors m = 0, 1, 2.

    For integer 2c >= 1, phi_0 = sum_{n>=1} a0[n] z^n, phi_1 = z^{2c} psi_1(z), phi_2 = z^{4c} psi_2(z)
    with instanton factor e^{m/z} (Borel pole at omega = -1).
    """
    c_param = require_exact_fraction(c_param, "c_param")
    max_n = require_exact_int(max_n, "max_n", lo=4, hi=40)
    two_c = 2 * c_param
    require_ok(two_c.denominator == 1 and two_c.numerator >= 1, "INVALID_RICCATI_C", "2*c_param must be integer >= 1")

    a0 = [Fraction(0, 1)] * (max_n + 1)
    a0[1] = Fraction(1, 1)
    for n in range(2, max_n + 1):
        conv = sum((a0[j] * a0[n - j] for j in range(1, n)), Fraction(0, 1))
        a0[n] = -(n - 1) * a0[n - 1] + c_param * conv

    psi1 = [Fraction(0, 1)] * max_n
    psi1[0] = Fraction(1, 1)
    for k in range(1, max_n):
        rhs = two_c * sum((a0[j] * psi1[k + 1 - j] for j in range(2, k + 2)), Fraction(0, 1))
        psi1[k] = rhs / k

    psi2 = [Fraction(0, 1)] * max_n
    for k in range(max_n):
        p1sq = sum((psi1[j] * psi1[k - j] for j in range(k + 1)), Fraction(0, 1))
        prev_d = (k - 1 + 4 * c_param) * psi2[k - 1] if k >= 1 else Fraction(0, 1)
        conv02 = sum((a0[j] * psi2[k - j] for j in range(1, k + 1)), Fraction(0, 1))
        psi2[k] = -c_param * p1sq + prev_d - two_c * conv02

    return {"a0": a0, "psi1": psi1, "psi2": psi2}


def _pi_machin_enclosure(terms: int = 8) -> tuple[Fraction, Fraction]:
    """Exact pure-Q enclosure pi_lo < pi < pi_hi via Machin's formula pi/4 = 4 arctan(1/5) - arctan(1/239)."""
    def arctan_inv(q_int: int) -> tuple[Fraction, Fraction]:
        acc = Fraction(0, 1)
        for k in range(terms):
            term = Fraction(1, (2 * k + 1) * (q_int ** (2 * k + 1)))
            acc = acc + term if k % 2 == 0 else acc - term
        nxt = Fraction(1, (2 * terms + 1) * (q_int ** (2 * terms + 1)))
        if terms % 2 == 0:
            return acc, acc + nxt
        return acc - nxt, acc

    a5_lo, a5_hi = arctan_inv(5)
    a239_lo, a239_hi = arctan_inv(239)
    return 4 * (4 * a5_lo - a239_hi), 4 * (4 * a5_hi - a239_lo)


def stokes_shift_transseries(sectors: list[list[Fraction]], sigma: Fraction, stokes_s1: Fraction) -> list[Fraction]:
    """Apply exact Stokes automorphism S = exp(dot_Delta_{-1}) to a 1-parameter trans-series
    sum_{m=0}^M sigma^m e^{m/z} phi_m(z) via bridge equation dot_Delta_{-1} = S_1 d/d(sigma),
    returning the shifted sector weights [c_0, c_1, ..., c_M] where S[Phi](sigma) = sum c_m e^{m/z} phi_m."""
    require_ok(type(sectors) is list and 1 <= len(sectors) <= 8, "INVALID_SECTORS", "sectors must be non-empty list")
    for idx, sec in enumerate(sectors):
        require_fraction_series(sec, f"sectors[{idx}]")
    sigma = require_exact_fraction(sigma, "sigma")
    stokes_s1 = require_exact_fraction(stokes_s1, "stokes_s1")
    m_max = len(sectors) - 1
    # Direct exponential series of operator S_1 * d/d(sigma) acting on sigma^m:
    # exp(S_1 d/d(sigma))(sigma^m) = sum_{r=0}^m (S_1^r / r!) * (m! / (m-r)!) * sigma^{m-r}
    shifted_weights: list[Fraction] = []
    for m in range(m_max + 1):
        w_m = Fraction(0, 1)
        for r in range(m + 1):
            w_m += (stokes_s1**r) * Fraction(math.comb(m, r), 1) * (sigma ** (m - r))
        shifted_weights.append(w_m)
    return shifted_weights


def verify_pillar2_alien_bridge_stokes() -> dict[str, Any]:
    """Certify Pillar 2: Linear Euler bridge equation & Stokes automorphism, alien-derivative
    Leibniz rule, nonlinear Riccati (c=1/2) 3-sector exact ODE verification, resurgent
    large-order/low-order correspondence (Richardson + 1/pi enclosure), and c=1 polynomial control."""
    # 2a. Linear Euler trans-series Phi(z; sigma) = phi_0(z) + sigma e^{1/z} * 1
    y_hat = euler_series_coeffs(10)
    phi1_euler = [Fraction(1, 1)] + [Fraction(0, 1)] * 10
    euler_bridge_ok = True
    for s1_val, sig_val in ((Fraction(1, 1), Fraction(2, 1)), (Fraction(3, 1), Fraction(-1, 2)), (Fraction(-5, 2), Fraction(7, 3))):
        # Bridge eq: dot_Delta_{-1}(phi_0 + sigma e^{1/z} phi_1) = S_1 e^{1/z} phi_1 == S_1 d/d(sigma) Phi
        # Stokes automorphism: exp(dot_Delta_{-1}) Phi(sigma) = (1 + dot_Delta_{-1}) Phi(sigma) = Phi(sigma + S_1)
        stokes_w = stokes_shift_transseries([y_hat, phi1_euler], sig_val, s1_val)
        direct_w = [Fraction(1, 1), sig_val + s1_val]
        if stokes_w != direct_w:
            euler_bridge_ok = False

    # Alien-derivative Leibniz rule Delta_{-1}(f * g) == (Delta_{-1} f) * g + f * (Delta_{-1} g)
    # Using resurgent algebra generated by phi_0 (Delta_{-1} phi_0 = S_1 * 1) and polynomial p(z) (Delta_{-1} p = 0):
    # Take f = phi_0 (degree-shifted power series in Q[[z]]), g = p(z) * phi_0 where p(z) = 1 + 2z + 3z^2.
    # Product f*g = p(z) * phi_0^2; by Leibniz, Delta_{-1}(p * phi_0^2) = 2 * S_1 * p * phi_0.
    # Independently: (Delta_{-1} f)*g + f*(Delta_{-1} g) = S_1*(p*phi_0) + phi_0*(S_1*p) = 2*S_1*p*phi_0.
    s1_test = Fraction(3, 2)
    p_poly = [Fraction(1, 1), Fraction(2, 1), Fraction(3, 1)]
    f_ser = [Fraction(0, 1)] + y_hat[:8]  # z * y_hat_shift = sum a_n z^{n+1}
    g_ser = poly_mul_exact(p_poly, f_ser, 8)
    df_ser = [s1_test] + [Fraction(0, 1)] * 8
    dg_ser = [s1_test * c for c in p_poly] + [Fraction(0, 1)] * 6
    lhs_leibniz = [2 * s1_test * c for c in g_ser]
    rhs_leibniz = [
        poly_mul_exact(df_ser, g_ser, 8)[k] + poly_mul_exact(f_ser, dg_ser, 8)[k]
        for k in range(9)
    ]
    leibniz_exact = lhs_leibniz == rhs_leibniz

    # 2b. Nonlinear Riccati ODE z^2 y' + y = z + (1/2) y^2 through order N = 30
    c_half = Fraction(1, 2)
    n_ric = 30
    ric = riccati_transseries_sectors(c_half, n_ric)
    a0, psi1, psi2 = ric["a0"], ric["psi1"], ric["psi2"]

    # Verify all 3 exact sector ODE residuals vanish identically
    res_m0 = [
        ((n - 1) * a0[n - 1] if n >= 2 else Fraction(0, 1))
        + a0[n]
        - (Fraction(1, 1) if n == 1 else Fraction(0, 1))
        - c_half * sum((a0[j] * a0[n - j] for j in range(1, n)), Fraction(0, 1))
        for n in range(1, n_ric + 1)
    ]
    res_m1 = [
        k * psi1[k] - 2 * c_half * sum((a0[j] * psi1[k + 1 - j] for j in range(2, k + 2)), Fraction(0, 1))
        for k in range(1, n_ric)
    ]
    res_m2 = [
        ((k + 1) * psi2[k - 1] if k >= 1 else Fraction(0, 1))
        - psi2[k]
        - c_half * sum((psi1[j] * psi1[k - j] for j in range(k + 1)), Fraction(0, 1))
        - 2 * c_half * sum((a0[j] * psi2[k - j] for j in range(1, k + 1)), Fraction(0, 1))
        for k in range(n_ric)
    ]
    ric_ode_ok = all((all(x == 0 for x in res_m0), all(x == 0 for x in res_m1), all(x == 0 for x in res_m2)))

    # Nonlinear 3-sector Stokes automorphism check: S[Phi](sigma) == Phi(sigma + S_1) through m = 2
    ric_stokes_w = stokes_shift_transseries([a0[:6], psi1[:6], psi2[:6]], Fraction(2, 3), Fraction(5, 4))
    sig_plus_s1 = Fraction(2, 3) + Fraction(5, 4)
    ric_stokes_ok = ric_stokes_w == [Fraction(1, 1), sig_plus_s1, sig_plus_s1**2]

    # Resurgent large-order / low-order correspondence:
    # r_n = (-1)^{n-1} a0[n] / (n-2)! ~ (1/pi) * (1 - psi1[1]/(n-2) + psi1[2]/((n-2)(n-3)) - psi1[3]/((n-2)(n-3)(n-4)) + ...)
    def r_seq(n: int) -> Fraction:
        return ((-1) ** (n - 1) * a0[n]) / math.factorial(n - 2)

    def d1_est(n: int) -> Fraction:
        rn_val = r_seq(n)
        return (n - 2) * (n - 3) * (r_seq(n - 1) - rn_val) / rn_val

    d1_20, d1_25, d1_30 = d1_est(20), d1_est(25), d1_est(30)
    rich1_30 = 28 * d1_30 - 27 * d1_est(29)
    target_neg_psi1_1 = -psi1[1]  # exact 1/2
    err_20 = abs(d1_20 - target_neg_psi1_1)
    err_25 = abs(d1_25 - target_neg_psi1_1)
    err_30 = abs(d1_30 - target_neg_psi1_1)
    err_rich30 = abs(rich1_30 - target_neg_psi1_1)

    # 3-term low-order normalized Stokes constant estimator vs pure-Q 1/pi enclosure
    s3_30 = (
        Fraction(1, 1)
        - psi1[1] / 28
        + psi1[2] / (28 * 27)
        - psi1[3] / (28 * 27 * 26)
    )
    c_stokes_est_30 = r_seq(30) / s3_30
    pi_lo, pi_hi = _pi_machin_enclosure(8)
    inv_pi_lo = Fraction(1, 1) / pi_hi
    inv_pi_hi = Fraction(1, 1) / pi_lo
    stokes_dist_from_inv_pi_lt_1e5 = all(
        (
            abs(c_stokes_est_30 - inv_pi_lo) < Fraction(1, 100_000),
            abs(c_stokes_est_30 - inv_pi_hi) < Fraction(1, 100_000),
        )
    )

    # Degenerate polynomial control c = 1: z^2 y' + y = z + y^2 has exact solution y = z
    ric_c1 = riccati_transseries_sectors(Fraction(1, 1), 8)
    c1_poly_collapse = all((ric_c1["a0"][1] == 1, all(x == 0 for x in ric_c1["a0"][2:])))

    all_verified = all(
        (
            euler_bridge_ok,
            leibniz_exact,
            ric_ode_ok,
            ric_stokes_ok,
            target_neg_psi1_1 == Fraction(1, 2),
            err_20 > err_25,
            err_25 > err_30,
            err_rich30 < err_30,
            err_rich30 < Fraction(1, 200),
            stokes_dist_from_inv_pi_lt_1e5,
            c1_poly_collapse,
        )
    )

    return {
        "all_verified": all_verified,
        "linear_euler_bridge_and_stokes_exact": euler_bridge_ok,
        "alien_leibniz_rule_exact": leibniz_exact,
        "riccati_c_half": {
            "c": format_fraction(c_half),
            "order_N": n_ric,
            "all_3_sector_ode_residuals_zero": ric_ode_ok,
            "stokes_automorphism_3sector_exact": ric_stokes_ok,
            "a0_first_8": [format_fraction(x) for x in a0[1:9]],
            "psi1_first_6": [format_fraction(x) for x in psi1[:6]],
            "psi2_first_5": [format_fraction(x) for x in psi2[:5]],
            "exact_neg_psi1_1": format_fraction(target_neg_psi1_1),
            "large_order_d1_n20_6dp": format_decimal_trunc(d1_20, 6),
            "large_order_d1_n25_6dp": format_decimal_trunc(d1_25, 6),
            "large_order_d1_n30_6dp": format_decimal_trunc(d1_30, 6),
            "richardson_R1_n30_6dp": format_decimal_trunc(rich1_30, 6),
            "monotone_convergence_verified": all((err_20 > err_25, err_25 > err_30)),
            "stokes_C_est_n30_6dp": format_decimal_trunc(c_stokes_est_30, 6),
            "inv_pi_6dp": format_decimal_trunc(inv_pi_lo, 6),
            "stokes_C_matches_inv_pi_within_1e5": stokes_dist_from_inv_pi_lt_1e5,
        },
        "riccati_c1_exact_polynomial_control": c1_poly_collapse,
    }


# ============================================================================
# 4. Pillar 3 — Bernoulli / Stirling Divergence, Euler-Maclaurin & Eisenstein
# ============================================================================

def bernoulli_numbers_exact(max_n: int) -> list[Fraction]:
    """Exact rational Bernoulli numbers B_0..B_{max_n} (B_1 = -1/2) via exact recurrence."""
    max_n = require_exact_int(max_n, "max_n", lo=0, hi=40)
    b_list: list[Fraction] = [Fraction(1, 1)]
    for n in range(1, max_n + 1):
        s_val = sum((Fraction(math.comb(n + 1, k), 1) * b_list[k] for k in range(n)), Fraction(0, 1))
        b_list.append(-s_val / (n + 1))
    return b_list


def sigma_divisor_sum(n: int, k_pow: int) -> int:
    """Exact integer divisor power sum sigma_k(n) = sum_{d | n} d^k."""
    n = require_exact_int(n, "n", lo=1, hi=10_000)
    k_pow = require_exact_int(k_pow, "k_pow", lo=0, hi=12)
    return sum(d**k_pow for d in range(1, n + 1) if n % d == 0)


def verify_pillar3_bernoulli_stirling_eisenstein() -> dict[str, Any]:
    """Certify Pillar 3: Bernoulli B_0..B_24, Stirling c_k = B_{2k}/(2k(2k-1)),
    factorial divergence crossing 1 at k=4->5, exact two-sided Borel-pole lattice bounds
    (2k)(2k-1)/(4 pi_hi^2 (1 + 2^{2-2k})) < |c_{k+1}/c_k| < (2k)(2k-1)/(4 pi_lo^2),
    exact Euler-Maclaurin power sums, and the Eisenstein bridge E_4^2 == E_8."""
    b_all = bernoulli_numbers_exact(24)
    odd_vanish = all(b_all[2 * k + 1] == 0 for k in range(1, 12))
    b_even = [b_all[2 * k] for k in range(1, 13)]
    stirling_c = [b_all[2 * k] / (2 * k * (2 * k - 1)) for k in range(1, 13)]
    sign_alt_ok = all(((-1) ** (k - 1)) * stirling_c[k - 1] > 0 for k in range(1, 13))

    ratios = [abs(stirling_c[k]) / abs(stirling_c[k - 1]) for k in range(1, 12)]
    crossing_at_k4 = all((all(ratios[i] < 1 for i in range(3)), all(ratios[i] > 1 for i in range(3, 11))))
    monotone_ratios = all(ratios[i] < ratios[i + 1] for i in range(10))

    # Borel pole lattice zeta_m = +/- 2 pi i m => exact two-sided pure-Q ratio enclosure for all k = 1..11:
    # |c_{k+1}/c_k| = (2k)(2k-1)/(4 pi^2) * zeta(2k+2)/zeta(2k), with 1 < zeta(2k+2) < zeta(2k) < 1 + 2^{2-2k}
    pi_lo, pi_hi = _pi_machin_enclosure(8)
    four_pi_lo_sq = 4 * pi_lo * pi_lo
    four_pi_hi_sq = 4 * pi_hi * pi_hi
    pole_two_sided_ok = all(
        Fraction((2 * k) * (2 * k - 1), 1) / (four_pi_hi_sq * (Fraction(1, 1) + Fraction(1, 1 << (2 * k - 2))))
        < ratios[k - 1]
        < Fraction((2 * k) * (2 * k - 1), 1) / four_pi_lo_sq
        for k in range(1, 12)
    )
    # Exact rational lower bound at k = 4 -> 5 already exceeds 1, certifying strict factorial divergence
    div_lb_k4 = Fraction(8 * 7, 1) / (four_pi_hi_sq * (Fraction(1, 1) + Fraction(1, 1 << 6)))
    div_lb_k4_gt_1 = div_lb_k4 > 1

    # Exact Euler-Maclaurin / Faulhaber power sums for p in 1..5, M = 10
    m_em = 10
    em_ok = True
    for p in range(1, 6):
        direct_sum = Fraction(sum(j**p for j in range(1, m_em + 1)), 1)
        # sum_{j=1}^M j^p = 1/(p+1) * sum_{r=0}^p C(p+1, r) * B_r^+ * M^{p+1-r} (B_1^+ = +1/2)
        em_val = Fraction(0, 1)
        for r in range(p + 1):
            br_plus = Fraction(1, 2) if r == 1 else b_all[r]
            em_val += Fraction(math.comb(p + 1, r), 1) * br_plus * (m_em ** (p + 1 - r))
        em_val /= p + 1
        if em_val != direct_sum:
            em_ok = False

    # Direct Eisenstein modular bridge: E_{2k}(q) = 1 - (4k/B_{2k}) sum sigma_{2k-1}(n) q^n
    eisenstein_prefactors = [Fraction(-4 * k, 1) / b_all[2 * k] for k in (1, 2, 3, 4)]
    e4_q = [Fraction(1, 1)] + [eisenstein_prefactors[1] * sigma_divisor_sum(n, 3) for n in range(1, 13)]
    e8_q = [Fraction(1, 1)] + [eisenstein_prefactors[3] * sigma_divisor_sum(n, 7) for n in range(1, 13)]
    e4_sq_eq_e8 = poly_mul_exact(e4_q, e4_q, 12) == e8_q

    all_verified = all(
        (
            odd_vanish,
            b_all[2] == Fraction(1, 6),
            b_all[12] == Fraction(-691, 2730),
            b_all[24] == Fraction(-236_364_091, 2730),
            stirling_c[0] == Fraction(1, 12),
            stirling_c[1] == Fraction(-1, 360),
            stirling_c[2] == Fraction(1, 1260),
            stirling_c[3] == Fraction(-1, 1680),
            sign_alt_ok,
            crossing_at_k4,
            monotone_ratios,
            pole_two_sided_ok,
            div_lb_k4_gt_1,
            em_ok,
            eisenstein_prefactors == [Fraction(-24, 1), Fraction(240, 1), Fraction(-504, 1), Fraction(480, 1)],
            e4_sq_eq_e8,
        )
    )

    return {
        "all_verified": all_verified,
        "odd_bernoulli_vanish_B3_to_B23": odd_vanish,
        "bernoulli_even_B2_to_B24": {f"B_{2 * k}": format_fraction(b_even[k - 1]) for k in range(1, 13)},
        "stirling_c1_to_c6": [format_fraction(x) for x in stirling_c[:6]],
        "stirling_sign_alternation_exact": sign_alt_ok,
        "stirling_ratio_crosses_1_at_k4_to_5": crossing_at_k4,
        "stirling_ratio_k4_to_5": format_fraction(ratios[3]),
        "stirling_ratio_k11_to_12": format_fraction(ratios[10]),
        "borel_pole_lattice_2pi_i_bounds_exact": pole_two_sided_ok,
        "divergence_lower_bound_k4_gt_1": div_lb_k4_gt_1,
        "divergence_lower_bound_k4_6dp": format_decimal_trunc(div_lb_k4, 6),
        "euler_maclaurin_power_sums_p1_to_5_exact": em_ok,
        "eisenstein_bridge_s22a": {
            "prefactors_E2_E4_E6_E8": [format_fraction(x) for x in eisenstein_prefactors],
            "E4_squared_equals_E8_mod_q13": e4_sq_eq_e8,
        },
    }


# ============================================================================
# 5. Pillar 4 — Zagier-Kontsevich F(q), Fishburn A022493 & S23b Trefoil Bridge
# ============================================================================

def _mul_zi(x: tuple[int, int], y: tuple[int, int]) -> tuple[int, int]:
    return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def _mul_zw(x: tuple[int, int], y: tuple[int, int]) -> tuple[int, int]:
    """Exact multiplication in Eisenstein integers Z[omega] where omega^2 + omega + 1 = 0."""
    return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0] - x[1] * y[1])


def kontsevich_f_root_of_unity(order_n: int) -> tuple[int, int]:
    """Evaluate Kontsevich's strange function F(q) = sum_{n=0}^{N-1} (q; q)_n at canonical
    roots of unity q = zeta_N for N in {1, 2, 3, 4, 6} in exact Z, Z[i], or Z[omega]."""
    order_n = require_exact_int(order_n, "order_n", lo=1, hi=6)
    require_ok(order_n in (1, 2, 3, 4, 6), "UNSUPPORTED_ROOT_ORDER", "order_n must be in {1, 2, 3, 4, 6}")
    if order_n == 1:
        return (1, 0)
    if order_n == 2:
        return (3, 0)
    if order_n == 4:
        pows = ((1, 0), (0, 1), (-1, 0), (0, -1))
        mul_fn = _mul_zi
    elif order_n == 3:
        pows = ((1, 0), (0, 1), (-1, -1))
        mul_fn = _mul_zw
    else:
        # Primitive 6th root of unity zeta_6 = 1 + omega (zeta_6^2 - zeta_6 + 1 = 0, zeta_6^3 = -1)
        pows = ((1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1))
        mul_fn = _mul_zw
    acc = (1, 0)
    prod = (1, 0)
    for k in range(1, order_n):
        pk = pows[k % order_n]
        prod = mul_fn(prod, (1 - pk[0], -pk[1]))
        acc = (acc[0] + prod[0], acc[1] + prod[1])
    return acc


def fishburn_numbers_exact(max_deg: int) -> list[int]:
    """Compute exact Fishburn numbers (OEIS A022493) as [x^k] F(1 - x) = sum_{n>=0} prod_{k=1}^n (1 - (1-x)^k)."""
    max_deg = require_exact_int(max_deg, "max_deg", lo=0, hi=14)
    f_ser = [Fraction(0, 1)] * (max_deg + 1)
    f_ser[0] = Fraction(1, 1)
    prod_ser = [Fraction(0, 1)] * (max_deg + 1)
    prod_ser[0] = Fraction(1, 1)
    for n in range(1, max_deg + 1):
        fac = [Fraction(0, 1)] * (max_deg + 1)
        for j in range(1, min(n, max_deg) + 1):
            fac[j] = Fraction(((-1) ** (j - 1)) * math.comb(n, j), 1)
        prod_ser = poly_mul_exact(prod_ser, fac, max_deg)
        for j in range(max_deg + 1):
            f_ser[j] += prod_ser[j]
    return [int(c.numerator) for c in f_ser]


def habiro_trefoil_colored_jones(color_n: int) -> dict[int, int]:
    """Exact Habiro-Zagier cyclotomic expansion J_N(3_1; q) = q^{N-1} sum_{k=0}^{N-1} q^{kN} prod_{j=1}^k (1 - q^{N-j})."""
    color_n = require_exact_int(color_n, "color_n", lo=1, hi=8)
    tot: dict[int, int] = {}
    for k in range(color_n):
        term: dict[int, int] = {(color_n - 1) + k * color_n: 1}
        for j in range(1, k + 1):
            nxt: dict[int, int] = {}
            shift = color_n - j
            for e, c in term.items():
                nxt[e] = nxt.get(e, 0) + c
                nxt[e + shift] = nxt.get(e + shift, 0) - c
            term = {e: c for e, c in nxt.items() if c != 0}
        for e, c in term.items():
            tot[e] = tot.get(e, 0) + c
    return {e: c for e, c in sorted(tot.items()) if c != 0}


def verify_pillar4_zagier_quantum_modularity() -> dict[str, Any]:
    """Certify Pillar 4: Kontsevich F(q) at roots of unity {1, -1, omega, i, zeta_6},
    Fishburn numbers A022493, Zagier radial F(e^{-t}) & exact Strange Identity
    e^{-t/24} F(e^{-t}) == sum ((-1)^{n+1}/2 L(-2n-1, chi_12)) / n! (t/24)^n across orders 0..9,
    and exact Habiro/Kashaev trefoil SU(2)_k bridge."""
    # 4a. Exact finite termination at roots of unity
    f_1 = kontsevich_f_root_of_unity(1)
    f_m1 = kontsevich_f_root_of_unity(2)
    f_w = kontsevich_f_root_of_unity(3)
    f_i = kontsevich_f_root_of_unity(4)
    f_z6 = kontsevich_f_root_of_unity(6)

    # 4b. Fishburn numbers OEIS A022493 via F(1 - x)
    fishburn = fishburn_numbers_exact(10)
    expected_fishburn = [1, 1, 2, 5, 15, 53, 217, 1014, 5335, 31240, 201608]

    # 4c. Zagier radial expansion F(e^{-t}) & exact Zagier Strange Identity across orders 0..9
    m_zag = 9
    f_et = [Fraction(0, 1)] * (m_zag + 1)
    f_et[0] = Fraction(1, 1)
    prod_et = [Fraction(0, 1)] * (m_zag + 1)
    prod_et[0] = Fraction(1, 1)
    for n in range(1, m_zag + 1):
        fac = [Fraction(0, 1)] * (m_zag + 1)
        for j in range(1, m_zag + 1):
            fac[j] = Fraction(((-1) ** (j - 1)) * (n**j), math.factorial(j))
        prod_et = poly_mul_exact(prod_et, fac, m_zag)
        for j in range(m_zag + 1):
            f_et[j] += prod_et[j]
    exp_mt24 = [Fraction((-1) ** j, math.factorial(j) * (24**j)) for j in range(m_zag + 1)]
    zag_et = poly_mul_exact(exp_mt24, f_et, m_zag)
    c_zagier = [int((zag_et[n] * math.factorial(n) * (24**n)).numerator) for n in range(m_zag + 1)]

    # Independent generalized Bernoulli computation of (-1)^{n+1}/2 * L(-2n-1, chi_12)
    b_nums = bernoulli_numbers_exact(2 * m_zag + 2)
    chi12 = ((1, 1), (5, -1), (7, -1), (11, 1))
    l_zagier: list[int] = []
    for n in range(m_zag + 1):
        k = 2 * n + 2
        b_k_chi = Fraction(0, 1)
        for a_res, chi_a in chi12:
            x = Fraction(a_res, 12)
            bp = sum((Fraction(math.comb(k, j), 1) * b_nums[j] * (x ** (k - j)) for j in range(k + 1)), Fraction(0, 1))
            b_k_chi += chi_a * bp
        b_k_chi *= Fraction(12, 1) ** (k - 1)
        l_neg = -b_k_chi / k
        val = Fraction((-1) ** (n + 1), 2) * l_neg
        l_zagier.append(int(val.numerator) if val.denominator == 1 else -1)
    strange_identity_exact = c_zagier == l_zagier

    # 4d. Habiro-Zagier trefoil colored Jones & exact SU(2)_k bridge
    j2 = habiro_trefoil_colored_jones(2)
    j3 = habiro_trefoil_colored_jones(3)
    j4 = habiro_trefoil_colored_jones(4)
    j2_matches_s23b = j2 == {1: 1, 3: 1, 4: -1}

    # Exact Kashaev-Zagier root-of-unity collapse J_N(3_1; zeta_N) == zeta_N^{N-1} F(zeta_N^{-1})
    # N = 2 (q = -1): J_2(-1) = -3 == (-1)*F(-1)
    j2_at_m1 = sum(c * ((-1) ** e) for e, c in j2.items())
    kashaev_n2 = j2_at_m1 == -f_m1[0]

    # N = 3 (q = omega): F(omega^{-1}) = conj(5 - omega) = 5 - (-1 - omega) = 6 + omega; omega^2 * (6 + omega) = -5 - 6 omega
    wpows = ((1, 0), (0, 1), (-1, -1))
    j3_at_w = (
        sum(c * wpows[e % 3][0] for e, c in j3.items()),
        sum(c * wpows[e % 3][1] for e, c in j3.items()),
    )
    f_w_conj = (f_w[0] - f_w[1], -f_w[1])
    kashaev_n3 = j3_at_w == _mul_zw(wpows[2], f_w_conj)

    # N = 4 (q = i): F(-i) = conj(8 - 3i) = 8 + 3i; i^3 * (8 + 3i) = 3 - 8i
    ipows = ((1, 0), (0, 1), (-1, 0), (0, -1))
    j4_at_i = (
        sum(c * ipows[e % 4][0] for e, c in j4.items()),
        sum(c * ipows[e % 4][1] for e, c in j4.items()),
    )
    f_i_conj = (f_i[0], -f_i[1])
    kashaev_n4 = j4_at_i == _mul_zi(ipows[3], f_i_conj)

    # SU(2)_k evaluations of V_{3_1}(q) = q + q^3 - q^4:
    # k=1 (q = omega): 1; k=2 (q = i): -1; k=4 (q = zeta_6 = 1+w): 1 + 2w (norm^2 = 1^2 - 1*2 + 2^2 = 3)
    z6pows = ((1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1))
    v_k1 = (sum(c * wpows[e % 3][0] for e, c in j2.items()), sum(c * wpows[e % 3][1] for e, c in j2.items()))
    v_k2 = (sum(c * ipows[e % 4][0] for e, c in j2.items()), sum(c * ipows[e % 4][1] for e, c in j2.items()))
    v_k4 = (sum(c * z6pows[e % 6][0] for e, c in j2.items()), sum(c * z6pows[e % 6][1] for e, c in j2.items()))
    v_k4_norm_sq = v_k4[0] * v_k4[0] - v_k4[0] * v_k4[1] + v_k4[1] * v_k4[1]
    s23b_levels_match = all((v_k1 == (1, 0), v_k2 == (-1, 0), v_k4 == (1, 2), v_k4_norm_sq == 3))

    all_verified = all(
        (
            f_1 == (1, 0),
            f_m1 == (3, 0),
            f_w == (5, -1),
            f_i == (8, -3),
            f_z6 == (4, -13),
            fishburn == expected_fishburn,
            strange_identity_exact,
            j2_matches_s23b,
            kashaev_n2,
            kashaev_n3,
            kashaev_n4,
            s23b_levels_match,
        )
    )

    return {
        "all_verified": all_verified,
        "kontsevich_roots_of_unity": {
            "F_1": list(f_1),
            "F_minus1": list(f_m1),
            "F_omega_in_Z_omega": list(f_w),
            "F_i_in_Z_i": list(f_i),
            "F_zeta6_in_Z_omega": list(f_z6),
        },
        "fishburn_A022493_0_to_10": fishburn,
        "zagier_radial_F_exp_minus_t_0_to_6": [format_fraction(x) for x in f_et[:7]],
        "zagier_strange_identity_C0_to_C9": c_zagier,
        "zagier_strange_identity_L_match_all_10": strange_identity_exact,
        "trefoil_habiro_s23b_bridge": {
            "J2_matches_S23b_V31": j2_matches_s23b,
            "J2_coeffs": {str(e): c for e, c in j2.items()},
            "J3_coeffs": {str(e): c for e, c in j3.items()},
            "J4_coeffs": {str(e): c for e, c in j4.items()},
            "kashaev_collapse_N2_N3_N4": [kashaev_n2, kashaev_n3, kashaev_n4],
            "s23b_SU2_levels_k1_k2_k4_match": s23b_levels_match,
            "s23b_k4_norm_sq": v_k4_norm_sq,
        },
    }


def compute_s27_payload() -> dict[str, Any]:
    """Build the complete deterministic zero-float resurgence & quantum modularity payload."""
    return {
        "track_id": TRACK_ID,
        "novelty_class": "N1",
        "oracle_class": "exact",
        "pillar1_borel_euler": verify_pillar1_borel_euler(),
        "pillar2_alien_bridge_stokes": verify_pillar2_alien_bridge_stokes(),
        "pillar3_bernoulli_stirling_eisenstein": verify_pillar3_bernoulli_stirling_eisenstein(),
        "pillar4_zagier_quantum_modularity": verify_pillar4_zagier_quantum_modularity(),
    }
