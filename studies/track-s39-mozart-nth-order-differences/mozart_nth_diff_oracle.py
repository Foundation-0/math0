#!/usr/bin/env python3
"""Track S39 (Portal 37): Exact Pure-Z/Q Certification of Wolfgang Amadeus Mozart
and n-th Order Differences Within: Frobenius Period-p Annihilation over Z_12,
Nyquist-Third Spectral Prism, Ducci 2^k Nilpotence, K.551 S_5 Counterpoint,
K.516f Rank-1 Dice-Game Invariance, and Putz (1995) CS-13 Anti-Numerology.

100% pure Python 3 stdlib (fractions.Fraction, itertools, math, typing).
ZERO floating-point arithmetic, ZERO bare assert statements, ZERO RNG calls,
ZERO third-party imports, ZERO personal-path or private-repo references.

Honest Law-4 Novelty: N1 (clean-room unified pure-Z/Q exact-operator certifier
bridging Frobenius finite-difference annihilation over Z_12 ~= Z_3 x Z_4, exact
Nyquist-third spectral prism R_n vs analytic white-noise/random-walk ratios,
Ducci cyclic absolute-difference 2^k nilpotence over F_2[S]/(1+S^L), K.551
quintuple S_5 invertible counterpoint checking, K.516f rank-1 bar-boundary
invariance, and exact Putz 1995 anti-numerology range-compression analysis;
all classical theorems and cited prior work strictly quarantined as N0).
"""
from __future__ import annotations

from fractions import Fraction
import itertools
import math
from typing import Any

TRACK_ID = "TRACK-S39-MOZART-NTH-DIFF"
SCHEMA_VERSION = "1.0.0"
MAX_RATIONAL_BITS = 4_096
MAX_JSON_INT_BITS = 4_096
MAX_STR_LEN = 512

# Authentic Mozart / control MIDI pitch sequences (C4 = 60, semitones in Z)
# K.550 (Symphony No. 40 in G minor, I): Eb5-D5-D5 x3 -> Bb5 (bars 1-3)
K550_OPENING_10: tuple[int, ...] = (75, 74, 74, 75, 74, 74, 75, 74, 74, 82)
# K.550 full opening 20-note phrase (bars 1-5)
K550_PHRASE_20: tuple[int, ...] = (
    75, 74, 74, 75, 74, 74, 75, 74, 74, 82,
    82, 81, 79, 79, 77, 75, 75, 74, 72, 72,
)
# K.545 (Sonata Facile in C major, I): Alberti bass [C4, G4, E4, G4] x4
K545_ALBERTI_16: tuple[int, ...] = (60, 67, 64, 67) * 4
# K.545 opening melody (bars 1-4)
K545_MELODY_17: tuple[int, ...] = (
    72, 76, 79, 71, 72, 74, 72, 81, 79, 84, 79, 77, 79, 77, 76, 77, 76,
)
# K.331 (Piano Sonata in A major, I, 6/8 theme, bars 1-3)
K331_THEME_18: tuple[int, ...] = (
    73, 74, 73, 76, 76, 71,
    71, 73, 71, 74, 74, 69,
    69, 71, 73, 74, 73, 71,
)
# K.525 (Eine Kleine Nachtmusik in G major, I, bars 1-4)
K525_THEME_18: tuple[int, ...] = (
    67, 62, 67, 62, 67, 62, 67, 71, 74,
    72, 69, 72, 69, 72, 69, 66, 69, 62,
)
# Control: C-major ascending scale (16 notes)
C_MAJOR_SCALE_16: tuple[int, ...] = (
    60, 62, 64, 65, 67, 69, 71, 72, 74, 76, 77, 79, 81, 83, 84, 86,
)

# Canonical Ducci phrase vectors from Mozart works
DUCCI_MOZART_CASES: tuple[tuple[str, tuple[int, ...], str, int], ...] = (
    ("K551_4note_CDFE", (60, 62, 65, 64), "ZERO", 4),
    ("K551_8note_CDFE_EDCB", (72, 74, 77, 76, 76, 74, 72, 71), "ZERO", 7),
    ("K545_Alberti_L4", (60, 67, 64, 67), "ZERO", 4),
    ("K550_8note_phrase", (75, 74, 74, 75, 74, 74, 75, 74), "ZERO", 8),
    ("K550_3note_sigh_L3", (75, 74, 74), "CYCLE", 3),
    ("K331_6_8_bar_L6", (73, 74, 73, 76, 76, 71), "CYCLE", 6),
)

# K.551 Jupiter Finale 5-voice invertible counterpoint model (pitch-class offsets in C major)
# Voice 0 is Mozart's authentic 4-note cantus firmus [C, D, F, E] = [0, 2, 5, 4]
K551_S5_VALID_VOICES: tuple[tuple[int, ...], ...] = (
    (0, 2, 5, 4),
    (4, 7, 9, 7),
    (0, 4, 0, 4),
    (4, 0, 4, 0),
    (7, 4, 2, 4),
)
# Must-fail counter-model: voice 1 moves in strict parallel 5ths (+7 semitones) with voice 0
K551_S5_PARALLEL_5TH_VOICES: tuple[tuple[int, ...], ...] = (
    (0, 2, 5, 4),
    (7, 9, 12, 11),
    (0, 4, 0, 4),
    (4, 0, 4, 0),
    (7, 4, 2, 4),
)
# Must-fail counter-model: voice 1 doubles voice 0 in parallel octaves (0 mod 12)
K551_S5_PARALLEL_8VE_VOICES: tuple[tuple[int, ...], ...] = (
    (0, 2, 5, 4),
    (0, 2, 5, 4),
    (0, 4, 0, 4),
    (4, 0, 4, 0),
    (7, 4, 2, 4),
)

# Representative Mozart piano sonata first-movement bar-count splits (exposition a, dev+recap b)
# from Putz (1995, Mathematics Magazine 68(4):275-282, N0)
PUTZ_1995_MOZART_SPLITS: tuple[tuple[str, int, int], ...] = (
    ("K.279_I", 38, 62),
    ("K.280_I", 56, 88),
    ("K.281_I", 40, 69),
    ("K.282_I", 15, 21),
    ("K.283_I", 53, 67),
    ("K.284_I", 51, 76),
    ("K.309_I", 58, 97),
    ("K.310_I", 49, 84),
    ("K.330_I", 58, 92),
    ("K.332_I", 93, 136),
    ("K.333_I", 63, 102),
    ("K.457_I", 74, 111),
    ("K.545_I", 28, 45),
    ("K.570_I", 79, 130),
    ("K.576_I", 58, 102),
)


class MozartNthDiffError(ValueError):
    """Typed fail-closed error for Track S39 domain, algebraic, and Zone-B checks."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"[{code}] {message}")
        self.code = code
        self.detail = message


# ============================================================================
# 1. Strict Type, Domain, and Exact Rational Primitives
# ============================================================================

def require_ok(cond: bool, code: str, message: str) -> None:
    if type(cond) is not bool:
        raise MozartNthDiffError("INVALID_CONDITION_TYPE", f"{code}: condition must be exact bool")
    if not cond:
        raise MozartNthDiffError(code, message)


def require_exact_int(
    val: Any,
    name: str,
    lo: int | None = None,
    hi: int | None = None,
) -> int:
    if type(val) is not int:
        raise MozartNthDiffError("INVALID_INT_TYPE", f"{name} must be exact int")
    if val.bit_length() > MAX_RATIONAL_BITS:
        raise MozartNthDiffError("INT_BIT_LIMIT", f"{name} exceeds {MAX_RATIONAL_BITS}-bit cap")
    if lo is not None:
        if type(lo) is not int:
            raise MozartNthDiffError("INVALID_BOUND_TYPE", f"{name}: lo must be exact int")
        if val < lo:
            raise MozartNthDiffError("INT_OUT_OF_RANGE", f"{name} must be >= {lo}")
    if hi is not None:
        if type(hi) is not int:
            raise MozartNthDiffError("INVALID_BOUND_TYPE", f"{name}: hi must be exact int")
        if val > hi:
            raise MozartNthDiffError("INT_OUT_OF_RANGE", f"{name} must be <= {hi}")
    return val


def require_exact_bool(val: Any, name: str) -> bool:
    if type(val) is not bool:
        raise MozartNthDiffError("INVALID_BOOL_TYPE", f"{name} must be exact bool")
    return val


def require_exact_fraction(
    val: Any,
    name: str,
    *,
    lo: Fraction | None = None,
    hi: Fraction | None = None,
) -> Fraction:
    if type(val) is not Fraction:
        raise MozartNthDiffError("INVALID_FRACTION_TYPE", f"{name} must be exact Fraction")
    if val.numerator.bit_length() > MAX_RATIONAL_BITS:
        raise MozartNthDiffError("RATIONAL_BIT_LIMIT", f"{name} numerator exceeds {MAX_RATIONAL_BITS}-bit cap")
    if val.denominator.bit_length() > MAX_RATIONAL_BITS:
        raise MozartNthDiffError("RATIONAL_BIT_LIMIT", f"{name} denominator exceeds {MAX_RATIONAL_BITS}-bit cap")
    if lo is not None:
        if type(lo) is not Fraction:
            raise MozartNthDiffError("INVALID_BOUND_TYPE", f"{name}: lo must be exact Fraction")
        if val < lo:
            raise MozartNthDiffError("FRACTION_OUT_OF_RANGE", f"{name} below lower bound")
    if hi is not None:
        if type(hi) is not Fraction:
            raise MozartNthDiffError("INVALID_BOUND_TYPE", f"{name}: hi must be exact Fraction")
        if val > hi:
            raise MozartNthDiffError("FRACTION_OUT_OF_RANGE", f"{name} above upper bound")
    return val


def format_fraction(q: Fraction) -> str:
    q = require_exact_fraction(q, "q")
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"


def format_decimal_rounded(q: Fraction, digits: int = 6) -> str:
    """Exact pure-integer half-up decimal formatter for Fraction (zero floats, no -0.00)."""
    q = require_exact_fraction(q, "q")
    digits = require_exact_int(digits, "digits", lo=1, hi=12)
    neg = q < 0
    aq = -q if neg else q
    scale = 10**digits
    scaled_x10 = (aq.numerator * scale * 10) // aq.denominator
    rounded = (scaled_x10 + 5) // 10
    if rounded == 0:
        neg = False
    whole = rounded // scale
    frac = rounded % scale
    prefix = "-" if neg else ""
    return f"{prefix}{whole}.{frac:0{digits}d}"


def _require_int_seq(seq: Any, name: str, *, min_len: int = 1, max_len: int = 256) -> list[int]:
    if type(seq) not in (list, tuple):
        raise MozartNthDiffError("INVALID_SEQ_TYPE", f"{name} must be exact list or tuple")
    require_ok(len(seq) >= min_len, "SEQ_TOO_SHORT", f"{name} length must be >= {min_len}")
    require_ok(len(seq) <= max_len, "SEQ_TOO_LONG", f"{name} length must be <= {max_len}")
    return [require_exact_int(v, f"{name}[{i}]", lo=-10_000, hi=10_000) for i, v in enumerate(seq)]


# ============================================================================
# 2. Exact Finite-Difference, Shift, & Ducci Operators
# ============================================================================

def forward_difference(seq: list[int] | tuple[int, ...], order: int) -> list[int]:
    """Exact forward difference Delta^n(seq) over Z."""
    cur = _require_int_seq(seq, "seq", min_len=2)
    n = require_exact_int(order, "order", lo=0, hi=32)
    require_ok(n < len(cur), "ORDER_TOO_HIGH", "order must be strictly less than sequence length")
    for _ in range(n):
        cur = [cur[i + 1] - cur[i] for i in range(len(cur) - 1)]
    return cur


def shift_difference(seq: list[int] | tuple[int, ...], lag: int) -> list[int]:
    """Exact lag-k shift difference (S^k - I)(seq)[i] = seq[i+k] - seq[i] over Z."""
    cur = _require_int_seq(seq, "seq", min_len=2)
    k = require_exact_int(lag, "lag", lo=1, hi=32)
    require_ok(k < len(cur), "LAG_TOO_HIGH", "lag must be strictly less than sequence length")
    return [cur[i + k] - cur[i] for i in range(len(cur) - k)]


def cyclic_forward_difference(seq: list[int] | tuple[int, ...]) -> list[int]:
    """Exact cyclic 1st forward difference Delta_cyc(seq)[i] = seq[(i+1)%L] - seq[i]."""
    cur = _require_int_seq(seq, "seq", min_len=2)
    n = len(cur)
    return [cur[(i + 1) % n] - cur[i] for i in range(n)]


def l2_energy_exact(seq: list[int] | tuple[int, ...]) -> int:
    """Exact squared L2 norm ||seq||_2^2 in Z_>=0."""
    cur = _require_int_seq(seq, "seq", min_len=1)
    return sum(x * x for x in cur)


def ducci_orbit(vec: list[int] | tuple[int, ...], max_steps: int = 512) -> dict[str, Any]:
    """Exact integer orbit of cyclic Ducci map D_cyc(v)_i = |v_{(i+1)%L} - v_i|."""
    start = tuple(_require_int_seq(vec, "vec", min_len=2, max_len=64))
    cap = require_exact_int(max_steps, "max_steps", lo=1, hi=4_096)
    cur = start
    seen: dict[tuple[int, ...], int] = {}
    step = 0
    while step <= cap:
        if all(x == 0 for x in cur):
            return {
                "length": len(start),
                "outcome": "ZERO",
                "steps_to_zero": step,
                "cycle_entry_step": -1,
                "cycle_period": 0,
                "terminal_state": list(cur),
            }
        if cur in seen:
            entry = seen[cur]
            return {
                "length": len(start),
                "outcome": "CYCLE",
                "steps_to_zero": -1,
                "cycle_entry_step": entry,
                "cycle_period": step - entry,
                "terminal_state": list(cur),
            }
        seen[cur] = step
        n = len(cur)
        cur = tuple(abs(cur[(i + 1) % n] - cur[i]) for i in range(n))
        step += 1
    raise MozartNthDiffError("DUCCI_STEP_LIMIT", "Ducci orbit exceeded max_steps without terminating or cycling")


# ============================================================================
# 3. Pillar 1 — Exact Frobenius Period-p Annihilation over Z_12 ~= Z_3 x Z_4
# ============================================================================

def _is_prime_small(p: int) -> bool:
    if p < 2:
        return False
    d = 2
    while d * d <= p:
        if p % d == 0:
            return False
        d += 1
    return True


def verify_frobenius_binomial_mod_p(prime_p: int, exponent_r: int = 1) -> dict[str, Any]:
    """Certify (S - I)^(p^r) == S^(p^r) - I (mod p) via exact binomial coefficients."""
    p = require_exact_int(prime_p, "prime_p", lo=2, hi=29)
    require_ok(_is_prime_small(p), "NOT_PRIME", "prime_p must be prime")
    r = require_exact_int(exponent_r, "exponent_r", lo=1, hi=4)
    q = p**r
    interior_all_zero = True
    for k in range(1, q):
        if math.comb(q, k) % p != 0:
            interior_all_zero = False
    # Constant term (-1)^q mod p vs -1 mod p:
    # For odd prime p, (-1)^(p^r) = -1 == p-1 (mod p); for p=2, (+1) == (-1) == 1 (mod 2).
    const_term_mod_p = ((-1) ** q) % p
    target_neg_one_mod_p = (-1) % p
    const_match = const_term_mod_p == target_neg_one_mod_p
    lead_match = (math.comb(q, q) % p) == 1
    # Direct operator identity check on deterministic non-periodic integer probe of length q + 6
    probe = [((i * i + 3 * i + 1) % 13) for i in range(q + 6)]
    d_q_mod_p = [x % p for x in forward_difference(probe, q)]
    s_q_mod_p = [x % p for x in shift_difference(probe, q)]
    op_match = d_q_mod_p == s_q_mod_p
    return {
        "prime_p": p,
        "exponent_r": r,
        "order_q": q,
        "interior_binomials_zero_mod_p": interior_all_zero,
        "endpoints_match_Sp_minus_I_mod_p": all((const_match, lead_match)),
        "operator_probe_identity_exact": op_match,
        "verified": all((interior_all_zero, const_match, lead_match, op_match)),
    }


def verify_pillar1_frobenius_z12() -> dict[str, Any]:
    """Certify Frobenius Delta^(p^r) == S^(p^r) - I (mod p), live K.550 & K.545
    annihilation, and exact CRT Z_12 <-> Z_3 x Z_4 musical decomposition."""
    frob_primes = [verify_frobenius_binomial_mod_p(p, 1) for p in (2, 3, 5, 7)]
    frob_powers = [verify_frobenius_binomial_mod_p(p, r) for p, r in ((2, 2), (2, 3), (3, 2))]
    frob_all_ok = all(item["verified"] for item in frob_primes + frob_powers)

    # K.550 Symphony No. 40 opening: Eb5-D5-D5 x3 -> Bb5
    k550_d2_mod3 = [x % 3 for x in forward_difference(K550_OPENING_10, 2)]
    k550_d3_raw = forward_difference(K550_OPENING_10, 3)
    k550_d3_mod3 = [x % 3 for x in k550_d3_raw]
    k550_s3_mod3 = [x % 3 for x in shift_difference(K550_OPENING_10, 3)]
    k550_leap_semitones = K550_OPENING_10[-1] - K550_OPENING_10[-2]
    k550_ok = all(
        (
            k550_d2_mod3 == [1, 1, 1, 1, 1, 1, 1, 2],
            k550_d3_mod3 == [0, 0, 0, 0, 0, 0, 1],
            k550_d3_mod3 == k550_s3_mod3,
            k550_leap_semitones == 8,
            k550_leap_semitones % 3 == 2,
            (K550_OPENING_10[-1] - K550_OPENING_10[-4]) == 7,
            (K550_OPENING_10[-1] - K550_OPENING_10[-4]) % 3 == 1,
        )
    )

    # K.545 Alberti bass [C4, G4, E4, G4] x4
    k545_d4_mod2 = [x % 2 for x in forward_difference(K545_ALBERTI_16, 4)]
    k545_s4_raw = shift_difference(K545_ALBERTI_16, 4)
    k545_energies = [l2_energy_exact(forward_difference(K545_ALBERTI_16, n)) for n in range(1, 6)]
    k545_energies_growing = all(k545_energies[i] < k545_energies[i + 1] for i in range(4))
    k545_ok = all(
        (
            k545_d4_mod2 == [0] * 12,
            k545_s4_raw == [0] * 12,
            k545_energies == [415, 1432, 5248, 19584, 72384],
            k545_energies_growing,
        )
    )

    # Exact CRT bijection Z_12 <-> Z_3 x Z_4:
    #   forward: x -> (x % 3, x % 4)
    #   inverse: (r3, r4) -> (4 * r3 + 9 * r4) % 12
    #   4 fibers of constant r4 (r3 varies over Z_3) = 4 augmented triads (+4 semitones)
    #   3 fibers of constant r3 (r4 varies over Z_4) = 3 diminished-7th chords (+3 semitones)
    crt_pairs: list[list[int]] = []
    crt_inverse_ok = True
    for x in range(12):
        r3, r4 = x % 3, x % 4
        crt_pairs.append([x, r3, r4])
        if (4 * r3 + 9 * r4) % 12 != x:
            crt_inverse_ok = False
    crt_bijective = len({(p[1], p[2]) for p in crt_pairs}) == 12

    augmented_triads = [sorted(x for x in range(12) if x % 4 == r4) for r4 in range(4)]
    diminished_7ths = [sorted(x for x in range(12) if x % 3 == r3) for r3 in range(3)]
    aug_step4_ok = all(
        all((len(tri) == 3, tri[1] - tri[0] == 4, tri[2] - tri[1] == 4))
        for tri in augmented_triads
    )
    dim_step3_ok = all(
        all((len(ch) == 4, ch[1] - ch[0] == 3, ch[2] - ch[1] == 3, ch[3] - ch[2] == 3))
        for ch in diminished_7ths
    )
    crt_ok = all((crt_inverse_ok, crt_bijective, aug_step4_ok, dim_step3_ok))

    all_verified = all((frob_all_ok, k550_ok, k545_ok, crt_ok))
    return {
        "frobenius_prime_checks": frob_primes,
        "frobenius_prime_power_checks": frob_powers,
        "k550_period3_annihilation": {
            "opening_midi": list(K550_OPENING_10),
            "delta2_mod3": k550_d2_mod3,
            "delta3_raw": k550_d3_raw,
            "delta3_mod3": k550_d3_mod3,
            "s3_minus_I_mod3": k550_s3_mod3,
            "leap_semitones": k550_leap_semitones,
            "exact_annihilation_verified": k550_ok,
        },
        "k545_alberti_period4_annihilation": {
            "alberti_midi": list(K545_ALBERTI_16),
            "delta4_mod2": k545_d4_mod2,
            "s4_minus_I_exact_Z": k545_s4_raw,
            "integer_energies_E1_to_E5": k545_energies,
            "energies_strictly_growing": k545_energies_growing,
            "exact_annihilation_verified": k545_ok,
        },
        "crt_z12_decomposition": {
            "bijection_table_x_r3_r4": crt_pairs,
            "augmented_triads_by_r4": augmented_triads,
            "diminished_7ths_by_r3": diminished_7ths,
            "crt_bijection_and_chords_verified": crt_ok,
        },
        "all_verified": all_verified,
    }


# ============================================================================
# 4. Pillar 2 — Exact Nyquist-Third Spectral Prism vs White Noise & Random Walk
# ============================================================================

def verify_pillar2_spectral_prism() -> dict[str, Any]:
    """Certify exact white-noise/random-walk difference variance ratios, exact
    rational sinusoidal gain |2 sin(w/2)|^2 = 2 - 2 cos(w) in {0,1,2,3,4}, and
    strict textural ordering across all 6 Mozart/control sequences."""
    # Analytic White Noise: E[(Delta^n X)^2]/Var(X) = sum_{k=0}^n C(n,k)^2 = C(2n, n)
    wn_variances: list[int] = []
    wn_vandermonde_ok = True
    for n in range(1, 6):
        sum_sq = sum(math.comb(n, k) ** 2 for k in range(n + 1))
        central = math.comb(2 * n, n)
        if sum_sq != central:
            wn_vandermonde_ok = False
        wn_variances.append(central)

    wn_ratios: list[Fraction] = []
    wn_ratio_formula_ok = True
    for n in range(1, 6):
        prev_v = 1 if n == 1 else wn_variances[n - 2]
        r_emp = Fraction(wn_variances[n - 1], prev_v)
        r_closed = Fraction(2 * (2 * n - 1), n)
        if r_emp != r_closed:
            wn_ratio_formula_ok = False
        wn_ratios.append(r_closed)

    # Analytic Random Walk: Delta^1(RW) = WN => R_n^RW = R_{n-1}^WN for n = 2..5
    rw_ratios = [wn_ratios[n - 2] for n in range(2, 6)]
    rw_exact_ok = rw_ratios == [Fraction(2, 1), Fraction(3, 1), Fraction(10, 3), Fraction(7, 2)]

    # Exact rational sinusoidal gain |2 sin(w/2)|^2 = 2 - 2 cos(w) on exact rational-cosine wavelengths
    # Verified both algebraically and via exact cyclic Z-eigenfunctions w (zero trig, zero floats)!
    sinusoid_spec = (
        ("inf", Fraction(1, 1), 0, [1, 1, 1, 1]),
        ("6", Fraction(1, 2), 1, [2, 1, -1, -2, -1, 1]),
        ("4", Fraction(0, 1), 2, [1, 0, -1, 0]),
        ("3", Fraction(-1, 2), 3, [2, -1, -1]),
        ("2", Fraction(-1, 1), 4, [1, -1]),
    )
    sinusoid_rows: list[dict[str, Any]] = []
    sinusoid_ok = True
    for lam_lbl, cos_w, exp_gain, wave in sinusoid_spec:
        alg_gain = Fraction(2, 1) - 2 * cos_w
        e_w = l2_energy_exact(wave)
        e_dw = l2_energy_exact(cyclic_forward_difference(wave))
        eigen_gain = Fraction(e_dw, e_w)
        if not all((alg_gain == exp_gain, eigen_gain == exp_gain)):
            sinusoid_ok = False
        sinusoid_rows.append(
            {
                "wavelength_lambda": lam_lbl,
                "cos_omega_q": format_fraction(cos_w),
                "gain_exact": exp_gain,
                "eigenwave_energy": e_w,
                "eigenwave_diff_energy": e_dw,
            }
        )

    # Compute exact rational E_1..E_5 and R_2..R_5 across all 6 Mozart/control sequences
    corpus = (
        ("Scale", C_MAJOR_SCALE_16),
        ("K.550", K550_PHRASE_20),
        ("K.331", K331_THEME_18),
        ("K.525", K525_THEME_18),
        ("K.545_Mel", K545_MELODY_17),
        ("K.545_Alberti", K545_ALBERTI_16),
    )
    seq_results: list[dict[str, Any]] = []
    r2_map: dict[str, Fraction] = {}
    for name, seq in corpus:
        es = [l2_energy_exact(forward_difference(seq, n)) for n in range(1, 6)]
        rs = [Fraction(es[i], es[i - 1]) for i in range(1, 5)]
        r2_map[name] = rs[0]
        seq_results.append(
            {
                "name": name,
                "length": len(seq),
                "energies_E1_to_E5": es,
                "ratios_R2_to_R5_q": [format_fraction(r) for r in rs],
                "ratios_R2_to_R5_dec6": [format_decimal_rounded(r, 6) for r in rs],
            }
        )

    ordering_strict = all(
        (
            r2_map["Scale"] < Fraction(1, 1),
            Fraction(1, 1) < r2_map["K.550"],
            r2_map["K.550"] < Fraction(2, 1),
            Fraction(2, 1) < r2_map["K.331"],
            r2_map["K.331"] < r2_map["K.545_Mel"],
            r2_map["K.545_Mel"] < r2_map["K.525"],
            r2_map["K.525"] < r2_map["K.545_Alberti"],
            r2_map["K.545_Alberti"] < Fraction(4, 1),
        )
    )

    all_verified = all(
        (
            wn_vandermonde_ok,
            wn_variances == [2, 6, 20, 70, 252],
            wn_ratio_formula_ok,
            rw_exact_ok,
            sinusoid_ok,
            ordering_strict,
        )
    )
    return {
        "white_noise_variances_n1_to_n5": wn_variances,
        "white_noise_ratios_R1_to_R5_q": [format_fraction(r) for r in wn_ratios],
        "random_walk_ratios_R2_to_R5_q": [format_fraction(r) for r in rw_ratios],
        "sinusoidal_gain_table": sinusoid_rows,
        "unity_cutoff_lambda": 6,
        "nyquist_ceiling": 4,
        "mozart_corpus_prism": seq_results,
        "strict_textural_ordering_verified": ordering_strict,
        "all_verified": all_verified,
    }


# ============================================================================
# 5. Pillar 3 — Ducci Iterated Absolute Differences = Exact 2^k Nilpotence
# ============================================================================

def verify_pillar3_ducci_nilpotence() -> dict[str, Any]:
    """Certify live Ducci D_cyc^n nilpotence on 2^k Mozart phrases vs binary cycles
    on non-2^k lengths, plus exact F_2^L algebraic characterization for L in 2..12."""
    mozart_rows: list[dict[str, Any]] = []
    mozart_ok = True
    for name, vec, exp_outcome, exp_metric in DUCCI_MOZART_CASES:
        orb = ducci_orbit(vec)
        orb["case_id"] = name
        orb["input_midi"] = list(vec)
        if exp_outcome == "ZERO":
            if not all((orb["outcome"] == "ZERO", orb["steps_to_zero"] == exp_metric)):
                mozart_ok = False
        else:
            if not all((orb["outcome"] == "CYCLE", orb["cycle_period"] == exp_metric)):
                mozart_ok = False
        mozart_rows.append(orb)

    # Check exact cycle details specified for K.550 L=3 and K.331 L=6
    by_id = {row["case_id"]: row for row in mozart_rows}
    sigh_l3 = by_id["K550_3note_sigh_L3"]
    bar_l6 = by_id["K331_6_8_bar_L6"]
    cycles_exact = all(
        (
            sigh_l3["cycle_entry_step"] == 1,
            sigh_l3["terminal_state"] == [1, 0, 1],
            bar_l6["cycle_entry_step"] == 4,
            bar_l6["terminal_state"] == [1, 1, 0, 0, 1, 1],
        )
    )

    # Exact F_2[S]/(1 + S^L) unit-impulse characterization across ALL L in 2..12:
    # (1 + S)^n * e_0 == 0 (mod 2) eventually iff L is a power of 2 (L in {2, 4, 8}),
    # with exact first nilpotence step n == L for L = 2^k!
    f2_rows: list[dict[str, Any]] = []
    f2_char_ok = True
    for length_l in range(2, 13):
        impulse = [1] + [0] * (length_l - 1)
        orb = ducci_orbit(impulse)
        is_pow2 = (length_l & (length_l - 1)) == 0
        if is_pow2:
            if not all((orb["outcome"] == "ZERO", orb["steps_to_zero"] == length_l)):
                f2_char_ok = False
        else:
            if orb["outcome"] != "CYCLE":
                f2_char_ok = False
        f2_rows.append(
            {
                "L": length_l,
                "is_power_of_2": is_pow2,
                "outcome": orb["outcome"],
                "steps_to_zero": orb["steps_to_zero"],
                "cycle_entry_step": orb["cycle_entry_step"],
                "cycle_period": orb["cycle_period"],
            }
        )

    all_verified = all((mozart_ok, cycles_exact, f2_char_ok))
    return {
        "mozart_ducci_orbits": mozart_rows,
        "f2_impulse_characterization_L2_to_L12": f2_rows,
        "nilpotent_iff_power_of_2_L2_to_L12": f2_char_ok,
        "all_verified": all_verified,
    }


# ============================================================================
# 6. Pillar 4 — K.551 S_5 Counterpoint, K.516f Dice Game & CS-13 Anti-Numerology
# ============================================================================

def check_s5_invertible_counterpoint(voices: tuple[tuple[int, ...], ...] | list[list[int]]) -> dict[str, Any]:
    """Exhaustively check all 5! = 120 vertical register permutations of a 5-voice model
    for zero forbidden parallel-5th/8ve 1st differences (Delta^1(p_hi - p_lo) == 0 at
    p_hi - p_lo == 0 or 7 mod 12)."""
    if type(voices) not in (list, tuple):
        raise MozartNthDiffError("INVALID_VOICES_TYPE", "voices must be exact list or tuple")
    require_ok(len(voices) == 5, "INVALID_VOICE_COUNT", "quintuple counterpoint requires exactly 5 voices")
    norm: list[list[int]] = []
    n_steps: int | None = None
    for idx, v in enumerate(voices):
        nv = _require_int_seq(v, f"voices[{idx}]", min_len=2, max_len=32)
        if n_steps is None:
            n_steps = len(nv)
        else:
            require_ok(len(nv) == n_steps, "VOICE_LEN_MISMATCH", "all 5 voices must have identical length")
        norm.append(nv)

    total_perms = 0
    clean_perms = 0
    violating_perms = 0
    first_violation: dict[str, Any] | None = None
    assert_steps = n_steps if n_steps is not None else 0
    for perm in itertools.permutations(range(5)):
        total_perms += 1
        pitched = [[36 + 12 * perm[v] + norm[v][t] for t in range(assert_steps)] for v in range(5)]
        viol_info: dict[str, Any] | None = None
        for i in range(5):
            for j in range(5):
                if i == j:
                    continue
                for t in range(assert_steps - 1):
                    if pitched[i][t] >= pitched[j][t]:
                        iv_t = (pitched[i][t] - pitched[j][t]) % 12
                        d_iv = (pitched[i][t + 1] - pitched[j][t + 1]) - (pitched[i][t] - pitched[j][t])
                        if iv_t in (0, 7) and d_iv == 0:
                            viol_info = {
                                "perm": list(perm),
                                "upper_voice": i,
                                "lower_voice": j,
                                "step_t": t,
                                "interval_mod12": iv_t,
                            }
                            break
                if viol_info is not None:
                    break
            if viol_info is not None:
                break
        if viol_info is None:
            clean_perms += 1
        else:
            violating_perms += 1
            if first_violation is None:
                first_violation = viol_info
    return {
        "total_permutations": total_perms,
        "clean_permutations": clean_perms,
        "violating_permutations": violating_perms,
        "all_120_clean": clean_perms == 120,
        "first_violation": first_violation,
    }


def _k516f_bar_seam_compatible(exit_pc: int, entry_pc: int) -> bool:
    """Exact diatonic C-major seam compatibility check (excludes tritone 6 and non-diatonic leaps)."""
    c_maj = (0, 2, 4, 5, 7, 9, 11)
    if exit_pc % 12 not in c_maj or entry_pc % 12 not in c_maj:
        return False
    step_mod = (entry_pc - exit_pc) % 12
    return step_mod != 6


def verify_pillar4_combinatorial_invariance_and_cs13() -> dict[str, Any]:
    """Certify K.551 S_5 120-permutation invertible counterpoint (+ must-fail counter-models),
    K.516f Dice Game combinatorics & rank-1 bar-boundary voice-leading invariance, and
    Putz (1995) CS-13 exact pure-Q anti-numerology audit."""
    # 4a. K.551 S_5 Quintuple Counterpoint
    s5_valid = check_s5_invertible_counterpoint(K551_S5_VALID_VOICES)
    s5_bad_p5 = check_s5_invertible_counterpoint(K551_S5_PARALLEL_5TH_VOICES)
    s5_bad_p8 = check_s5_invertible_counterpoint(K551_S5_PARALLEL_8VE_VOICES)
    s5_ok = all(
        (
            s5_valid["total_permutations"] == 120,
            s5_valid["clean_permutations"] == 120,
            s5_valid["violating_permutations"] == 0,
            s5_valid["all_120_clean"] is True,
            s5_bad_p5["clean_permutations"] == 60,
            s5_bad_p5["violating_permutations"] == 60,
            s5_bad_p5["all_120_clean"] is False,
            s5_bad_p8["clean_permutations"] == 0,
            s5_bad_p8["violating_permutations"] == 120,
        )
    )

    # 4b. K.516f Musikalisches Wuerfelspiel combinatorics & exact rank-1 bar-boundary theorem
    minuets_fixed_bar8 = 11**14
    minuets_two_bar8 = 2 * (11**14)
    # Explicit 11-variant C-major tonic-grid exit & entry pitch classes (C=0, E=4, G=7)
    # All exits & entries lie in C-major triad {0, 4, 7} -> zero tritone (6) seams across all 11x11 = 121 pairs!
    bar_exits_11 = [0, 4, 7, 0, 4, 7, 0, 4, 7, 0, 7]
    bar_entries_11 = [0, 4, 7, 4, 0, 7, 0, 7, 4, 7, 0]
    compat_matrix = [
        [1 if _k516f_bar_seam_compatible(u, v) else 0 for v in bar_entries_11]
        for u in bar_exits_11
    ]
    all_ones_121 = sum(sum(row) for row in compat_matrix)
    rank1_exact = all(row == [1] * 11 for row in compat_matrix)

    # Counter-model: inject chromatic F# (6) into 1 variant exit -> breaks rank-1 compatibility
    broken_exits_11 = list(bar_exits_11)
    broken_exits_11[10] = 6
    broken_compat = sum(
        1 if _k516f_bar_seam_compatible(u, v) else 0
        for u in broken_exits_11
        for v in bar_entries_11
    )

    # Exact path count via repeated matrix-vector multiplication across 14 free bars:
    # vec_0 = [1]*11; apply A 13 times => sum(vec_13) == 11**14!
    path_vec = [1] * 11
    for _ in range(13):
        path_vec = [sum(compat_matrix[u][v] * path_vec[u] for u in range(11)) for v in range(11)]
    matrix_path_count = sum(path_vec)

    k516f_ok = all(
        (
            minuets_fixed_bar8 == 379_749_833_583_241,
            minuets_two_bar8 == 759_499_667_166_482,
            all_ones_121 == 121,
            rank1_exact,
            broken_compat == 110,
            matrix_path_count == minuets_fixed_bar8,
        )
    )

    # 4c. Putz (1995) CS-13 Anti-Numerology Audit over exact Q
    phi_inv_lo = Fraction(618_033, 1_000_000)
    phi_inv_hi = Fraction(618_034, 1_000_000)
    phi_bracket_ok = all(
        (
            phi_inv_lo * phi_inv_lo + phi_inv_lo < Fraction(1, 1),
            phi_inv_hi * phi_inv_hi + phi_inv_hi > Fraction(1, 1),
        )
    )
    tol_2pct = Fraction(1, 50)
    putz_rows: list[dict[str, Any]] = []
    nonzero_defect_count = 0
    fail_2pct_ab_count = 0
    max_err_ab = Fraction(0, 1)
    neg_defects = 0
    pos_defects = 0
    for sonata_id, a_bars, b_bars in PUTZ_1995_MOZART_SPLITS:
        total_bars = a_bars + b_bars
        r_ba = Fraction(b_bars, total_bars)
        r_ab = Fraction(a_bars, b_bars)
        defect = b_bars * b_bars - a_bars * total_bars
        if defect != 0:
            nonzero_defect_count += 1
        if defect < 0:
            neg_defects += 1
        else:
            pos_defects += 1
        # Proven lower bound on |r_ab - phi^-1|
        if r_ab > phi_inv_hi:
            err_ab_lo = r_ab - phi_inv_hi
        elif r_ab < phi_inv_lo:
            err_ab_lo = phi_inv_lo - r_ab
        else:
            err_ab_lo = Fraction(0, 1)
        if err_ab_lo > max_err_ab:
            max_err_ab = err_ab_lo
        if err_ab_lo > tol_2pct:
            fail_2pct_ab_count += 1
        putz_rows.append(
            {
                "sonata": sonata_id,
                "a_exposition_bars": a_bars,
                "b_dev_recap_bars": b_bars,
                "total_bars": total_bars,
                "b_over_total_q": format_fraction(r_ba),
                "b_over_total_dec6": format_decimal_rounded(r_ba, 6),
                "a_over_b_q": format_fraction(r_ab),
                "a_over_b_dec6": format_decimal_rounded(r_ab, 6),
                "exact_golden_defect_Z": defect,
                "fails_2pct_ab_ratio_test": err_ab_lo > tol_2pct,
            }
        )

    # Exact Putz Range-Compression Lemma on Classical exposition window r = a/(a+b) in [7/20, 9/20]:
    # b/(a+b) = 1 - r spans [11/20, 13/20] (width 1/10 = 0.10), whereas a/b = r/(1-r) spans [7/13, 9/11] (width 40/143)
    r_lo = Fraction(7, 20)
    r_hi = Fraction(9, 20)
    ba_width = (1 - r_lo) - (1 - r_hi)
    ab_width = r_hi / (1 - r_hi) - r_lo / (1 - r_lo)
    compression_ratio = ab_width / ba_width
    putz_ok = all(
        (
            phi_bracket_ok,
            nonzero_defect_count == 15,
            neg_defects > 0,
            pos_defects > 0,
            fail_2pct_ab_count >= 9,
            max_err_ab > Fraction(17, 100),
            ba_width == Fraction(1, 10),
            ab_width == Fraction(40, 143),
            compression_ratio == Fraction(400, 143),
        )
    )

    all_verified = all((s5_ok, k516f_ok, putz_ok))
    return {
        "k551_s5_quintuple_counterpoint": {
            "cantus_firmus_v0_pc": list(K551_S5_VALID_VOICES[0]),
            "valid_model": s5_valid,
            "parallel_5th_counter_model": s5_bad_p5,
            "parallel_8ve_counter_model": s5_bad_p8,
            "verified": s5_ok,
        },
        "k516f_dice_game_invariance": {
            "minuets_fixed_bar8": minuets_fixed_bar8,
            "minuets_two_bar8_endings": minuets_two_bar8,
            "seam_compatibility_11x11_sum": all_ones_121,
            "seam_matrix_exact_rank_1": rank1_exact,
            "matrix_product_14bar_paths": matrix_path_count,
            "broken_chromatic_seam_sum": broken_compat,
            "verified": k516f_ok,
        },
        "putz_1995_cs13_anti_numerology": {
            "phi_inv_bracket_lo_q": format_fraction(phi_inv_lo),
            "phi_inv_bracket_hi_q": format_fraction(phi_inv_hi),
            "phi_inv_bracket_verified": phi_bracket_ok,
            "sonatas_checked": len(putz_rows),
            "nonzero_exact_defect_count": nonzero_defect_count,
            "negative_defect_count": neg_defects,
            "positive_defect_count": pos_defects,
            "fail_2pct_ab_count": fail_2pct_ab_count,
            "max_ab_deviation_lo_q": format_fraction(max_err_ab),
            "max_ab_deviation_lo_dec6": format_decimal_rounded(max_err_ab, 6),
            "range_compression_ba_width_q": format_fraction(ba_width),
            "range_compression_ab_width_q": format_fraction(ab_width),
            "range_compression_factor_q": format_fraction(compression_ratio),
            "sonata_splits": putz_rows,
            "verified": putz_ok,
        },
        "all_verified": all_verified,
    }


# ============================================================================
# 7. Unified Four-Pillar Mathematical Payload Assembly
# ============================================================================

def compute_s39_payload() -> dict[str, Any]:
    """Compute the complete zero-float pure-Z/Q Track S39 four-pillar payload."""
    p1 = verify_pillar1_frobenius_z12()
    p2 = verify_pillar2_spectral_prism()
    p3 = verify_pillar3_ducci_nilpotence()
    p4 = verify_pillar4_combinatorial_invariance_and_cs13()
    all_ok = all((p1["all_verified"], p2["all_verified"], p3["all_verified"], p4["all_verified"]))
    return {
        "track_id": TRACK_ID,
        "schema_version": SCHEMA_VERSION,
        "oracle_class": "exact",
        "novelty_class": "N1",
        "pillar1_frobenius_z12": p1,
        "pillar2_spectral_prism": p2,
        "pillar3_ducci_nilpotence": p3,
        "pillar4_combinatorial_invariance_cs13": p4,
        "all_pillars_verified": all_ok,
    }
