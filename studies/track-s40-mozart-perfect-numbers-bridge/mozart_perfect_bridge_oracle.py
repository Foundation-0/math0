"""Track S40 (Portal 38): Exact Pure-Z/Q/F2[x] Operator Bridge from Mozart n-th Order
Patterns to Perfect Numbers & F_2[x] Perfect Polynomials.

Law-5 beyond-language exact-operator unification connecting:
  - Pillar 1: Frobenius-Ducci 2^n nilpotence === Canaday (1941) splitting perfect
    polynomials A_n(x) = x^(2^n-1)(x+1)^(2^n-1) --(x=2)--> Euclid-Euler even perfect numbers
  - Pillar 2: Cyclotomic period factorization S^L - 1 = prod_{d|L} Phi_d(S) vs.
    F_2[x] Odd Perfect Polynomial Square Theorem & honest Z carry-propagation obstruction
  - Pillar 3: Nyquist-4 sigma(n) difference spectrum -> Euler pentagonal annihilator
    (Delta^2 p_k == 3, Alberti period-4 sign kernel (S^2+I)|(S^4-I)) & Ramanujan E2<->E4
  - Pillar 4: Adversarial Law-5 anti-numerology control (Stage A gauge/radix/transposition
    breakage vs. Stage B exact ring/operator invariance)

100% pure Python 3 stdlib (int, fractions.Fraction, math).
Zero IEEE-754 floats, zero float() calls, zero bare asserts, zero .isdigit(), zero RNG.
"""
from __future__ import annotations

from fractions import Fraction
import math
from typing import Any, Sequence

TRACK_ID = "TRACK-S40-MOZART-PERFECT-BRIDGE"
SCHEMA_VERSION = "aletheia.track_s40.mozart_perfect_bridge.v1"
MAX_INT_DIGITS = 1_000
MAX_INT_BITS = 3_321
MAX_RATIONAL_BITS = 3_321
MAX_PRIME_CHECK = 10_000_000
_TEN_POW_INT_DIGITS = 10**MAX_INT_DIGITS

# Authentic Mozart pitch sequences (MIDI semitones, C4 = 60)
K551_4NOTE: tuple[int, ...] = (60, 62, 65, 64)
K551_8NOTE: tuple[int, ...] = (72, 74, 77, 76, 76, 74, 72, 71)
K545_ALBERTI_4: tuple[int, ...] = (60, 67, 64, 67)
K545_ALBERTI_16: tuple[int, ...] = K545_ALBERTI_4 * 4
K550_3NOTE_SIGH: tuple[int, ...] = (75, 74, 74)
K550_8NOTE: tuple[int, ...] = (75, 74, 74, 75, 74, 74, 75, 74)
K550_PHRASE_20: tuple[int, ...] = (
    75, 74, 74, 75, 74, 74, 75, 74, 74, 82,
    82, 81, 79, 79, 77, 75, 75, 74, 72, 72,
)
K331_6_8_BAR: tuple[int, ...] = (73, 74, 73, 76, 76, 71)


class MozartPerfectBridgeError(ValueError):
    """Typed fail-closed error for all Track S40 oracle, algebra, and Zone-B checks."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"[{code}] {message}")
        self.code = code
        self.detail = message


# ============================================================================
# 1. Strict Fail-Closed Primitives (Aligned 3,321-bit / 1,000-digit Caps)
# ============================================================================

def require_ok(cond: bool, code: str, message: str) -> None:
    if type(cond) is not bool:
        raise MozartPerfectBridgeError("INVALID_CONDITION_TYPE", f"{code}: condition must be exact bool")
    if not cond:
        raise MozartPerfectBridgeError(code, message)


def require_exact_bool(val: Any, label: str = "bool") -> bool:
    if type(val) is not bool:
        raise MozartPerfectBridgeError("INVALID_BOOL_TYPE", f"{label} must be exact bool")
    return val


def require_exact_int(
    val: Any,
    label: str = "int",
    *,
    lo: int | None = None,
    hi: int | None = None,
) -> int:
    if type(val) is not int:
        raise MozartPerfectBridgeError("INVALID_INT_TYPE", f"{label} must be exact int")
    if val.bit_length() > MAX_INT_BITS:
        raise MozartPerfectBridgeError("INT_BIT_LIMIT", f"{label} exceeds {MAX_INT_BITS}-bit cap")
    if lo is not None:
        if type(lo) is not int:
            raise MozartPerfectBridgeError("INVALID_BOUND_TYPE", f"{label}.lo must be exact int")
        if val < lo:
            raise MozartPerfectBridgeError("INT_OUT_OF_RANGE", f"{label} must be >= {lo}")
    if hi is not None:
        if type(hi) is not int:
            raise MozartPerfectBridgeError("INVALID_BOUND_TYPE", f"{label}.hi must be exact int")
        if val > hi:
            raise MozartPerfectBridgeError("INT_OUT_OF_RANGE", f"{label} must be <= {hi}")
    return val


def require_exact_fraction(val: Any, label: str = "rational") -> Fraction:
    if type(val) is not Fraction:
        raise MozartPerfectBridgeError("INVALID_FRACTION_TYPE", f"{label} must be exact Fraction")
    if val.numerator.bit_length() > MAX_RATIONAL_BITS:
        raise MozartPerfectBridgeError("RATIONAL_BIT_LIMIT", f"{label} numerator exceeds {MAX_RATIONAL_BITS}-bit cap")
    if val.denominator.bit_length() > MAX_RATIONAL_BITS:
        raise MozartPerfectBridgeError("RATIONAL_BIT_LIMIT", f"{label} denominator exceeds {MAX_RATIONAL_BITS}-bit cap")
    return val


def format_rational(q: Fraction, label: str = "rational") -> str:
    val = require_exact_fraction(q, label)
    if val.denominator == 1:
        return str(val.numerator)
    return f"{val.numerator}/{val.denominator}"


def format_decimal(q: Fraction, places: int = 6) -> str:
    """Exact pure-integer half-up decimal rounding (zero floats, suppresses '-0.00...')."""
    val = require_exact_fraction(q, "decimal_val")
    p = require_exact_int(places, "places", lo=0, hi=12)
    neg = val < 0
    aq = -val if neg else val
    scale = 10**p
    scaled = aq * scale
    quot, rem = divmod(scaled.numerator, scaled.denominator)
    if rem * 2 >= scaled.denominator:
        quot += 1
    if quot == 0:
        neg = False
    sign = "-" if neg else ""
    if p == 0:
        return f"{sign}{quot}"
    whole, frac = divmod(quot, scale)
    return f"{sign}{whole}.{str(frac).rjust(p, '0')}"


def _require_int_seq(seq: Any, label: str, *, min_len: int = 1, max_len: int = 256) -> list[int]:
    if type(seq) not in (list, tuple):
        raise MozartPerfectBridgeError("INVALID_SEQ_TYPE", f"{label} must be exact list or tuple")
    require_ok(len(seq) >= min_len, "SEQ_TOO_SHORT", f"{label} length must be >= {min_len}")
    require_ok(len(seq) <= max_len, "SEQ_TOO_LONG", f"{label} length must be <= {max_len}")
    return [require_exact_int(v, f"{label}[{i}]", lo=-1_000_000, hi=1_000_000) for i, v in enumerate(seq)]


# ============================================================================
# 2. Exact Bit-Packed F_2[x] Polynomial Algebra & Z[x] Polynomial Algebra
# ============================================================================

def f2_deg(p: int) -> int:
    val = require_exact_int(p, "f2_poly", lo=0)
    return val.bit_length() - 1


def f2_mul(a: int, b: int) -> int:
    pa = require_exact_int(a, "f2_a", lo=0)
    pb = require_exact_int(b, "f2_b", lo=0)
    acc = 0
    while pb:
        if pb & 1:
            acc ^= pa
        pa <<= 1
        pb >>= 1
    return require_exact_int(acc, "f2_prod", lo=0)


def f2_divmod(a: int, b: int) -> tuple[int, int]:
    rem = require_exact_int(a, "f2_num", lo=0)
    den = require_exact_int(b, "f2_den", lo=1)
    db = den.bit_length() - 1
    q = 0
    while rem.bit_length() - 1 >= db:
        shift = (rem.bit_length() - 1) - db
        q ^= 1 << shift
        rem ^= den << shift
    return q, rem


def f2_gcd(a: int, b: int) -> int:
    x = require_exact_int(a, "f2_ga", lo=0)
    y = require_exact_int(b, "f2_gb", lo=0)
    while y:
        _, r = f2_divmod(x, y)
        x, y = y, r
    return x


def f2_pow(base: int, exp: int) -> int:
    b = require_exact_int(base, "f2_base", lo=0)
    e = require_exact_int(exp, "f2_exp", lo=0, hi=256)
    res = 1
    cur = b
    while e:
        if e & 1:
            res = f2_mul(res, cur)
        e >>= 1
        if e:
            cur = f2_mul(cur, cur)
    return res


def f2_is_irreducible(p: int) -> bool:
    poly = require_exact_int(p, "f2_irred", lo=0)
    d = f2_deg(poly)
    if d < 1:
        return False
    if d == 1:
        return True
    # Must have constant term 1 and even/odd check: P(0)=1 and P(1)=1 for deg >= 2
    if (poly & 1) == 0:
        return False
    if (poly.bit_count() & 1) == 0:
        return False
    max_div_deg = d // 2
    for cand in range(3, 1 << (max_div_deg + 1), 2):
        if f2_deg(cand) >= 2:
            if f2_divmod(poly, cand)[1] == 0:
                return False
    return True


def f2_sigma_prime_power(p: int, exp: int) -> int:
    """Exact sum of divisors sigma(P^exp) = sum_{k=0}^{exp} P^k in F_2[x]."""
    poly = require_exact_int(p, "f2_prime", lo=2)
    e = require_exact_int(exp, "f2_exp", lo=0, hi=128)
    total = 0
    cur = 1
    for _ in range(e + 1):
        total ^= cur
        cur = f2_mul(cur, poly)
    return total


def _zpoly_trim(coeffs: list[int]) -> list[int]:
    out = list(coeffs)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def zpoly_mul(a: Sequence[int], b: Sequence[int]) -> list[int]:
    pa = _require_int_seq(a, "zpoly_a", min_len=1, max_len=64)
    pb = _require_int_seq(b, "zpoly_b", min_len=1, max_len=64)
    out = [0] * (len(pa) + len(pb) - 1)
    for i, ca in enumerate(pa):
        for j, cb in enumerate(pb):
            out[i + j] += ca * cb
    return _zpoly_trim(out)


def zpoly_divexact(a: Sequence[int], b: Sequence[int]) -> list[int]:
    """Exact monic integer polynomial division in Z[x] (fails closed if non-zero remainder)."""
    rem = _zpoly_trim(_require_int_seq(a, "zpoly_num", min_len=1, max_len=64))
    den = _zpoly_trim(_require_int_seq(b, "zpoly_den", min_len=1, max_len=64))
    require_ok(den[-1] == 1, "NON_MONIC_ZPOLY", "divisor in Z[x] must be monic")
    da = len(rem) - 1
    db = len(den) - 1
    require_ok(da >= db, "ZPOLY_DEGREE_ERROR", "dividend degree < divisor degree")
    quot = [0] * (da - db + 1)
    for shift in range(da - db, -1, -1):
        lead = rem[shift + db]
        quot[shift] = lead
        if lead != 0:
            for j in range(db + 1):
                rem[shift + j] -= lead * den[j]
    require_ok(all(c == 0 for c in rem), "ZPOLY_NOT_EXACT", "Z[x] division had non-zero remainder")
    return _zpoly_trim(quot)


def zpoly_eval(coeffs: Sequence[int], x: int) -> int:
    poly = _require_int_seq(coeffs, "zpoly_eval", min_len=1, max_len=64)
    xv = require_exact_int(x, "x_eval", lo=-10_000, hi=10_000)
    acc = 0
    for c in reversed(poly):
        acc = acc * xv + c
    return acc


def cyclotomic_zpoly(n: int) -> list[int]:
    """Compute Phi_n(x) in Z[x] from scratch via x^n - 1 = prod_{d|n} Phi_d(x)."""
    nv = require_exact_int(n, "n", lo=1, hi=24)
    cache: dict[int, list[int]] = {}
    for m in range(1, nv + 1):
        if nv % m != 0:
            continue
        poly = [-1] + [0] * (m - 1) + [1]
        for d in range(1, m):
            if m % d == 0:
                poly = zpoly_divexact(poly, cache[d])
        cache[m] = poly
    return cache[nv]


# ============================================================================
# 3. Exact Integer Number Theory, Finite Differences & Ducci Operators
# ============================================================================

def is_prime_exact(n: int) -> bool:
    val = require_exact_int(n, "prime_cand", lo=0, hi=MAX_PRIME_CHECK)
    if val < 2:
        return False
    if val == 2:
        return True
    if (val & 1) == 0:
        return False
    lim = math.isqrt(val)
    d = 3
    while d <= lim:
        if val % d == 0:
            return False
        d += 2
    return True


def sigma_k_exact(n: int, k: int = 1) -> int:
    """Exact sum of k-th powers of positive divisors sigma_k(n) over Z."""
    nv = require_exact_int(n, "n", lo=1, hi=1_000_000)
    kv = require_exact_int(k, "k", lo=0, hi=5)
    total = 0
    lim = math.isqrt(nv)
    for d in range(1, lim + 1):
        if nv % d == 0:
            total += d**kv
            other = nv // d
            if other != d:
                total += other**kv
    return total


def v2_exact(n: int) -> int:
    val = require_exact_int(n, "v2_n", lo=1)
    c = 0
    while (val & 1) == 0:
        val >>= 1
        c += 1
    return c


def forward_difference(seq: Sequence[int], order: int) -> list[int]:
    cur = _require_int_seq(seq, "seq", min_len=2, max_len=256)
    ord_v = require_exact_int(order, "order", lo=0, hi=16)
    require_ok(ord_v < len(cur), "ORDER_TOO_HIGH", "order must be strictly less than sequence length")
    for _ in range(ord_v):
        cur = [cur[i + 1] - cur[i] for i in range(len(cur) - 1)]
    return cur


def spectral_prism_exact(seq: Sequence[int]) -> dict[str, Any]:
    """Compute exact integer energies E_1..E_5, raw ratios R_n = E_n/E_{n-1}, and per-sample mean-square ratios."""
    vals = _require_int_seq(seq, "prism_seq", min_len=6, max_len=256)
    length = len(vals)
    energies: list[int] = []
    for order in range(1, 6):
        d = forward_difference(vals, order)
        energies.append(sum(x * x for x in d))
    ratios_q: list[str] = []
    ratios_dec6: list[str] = []
    ms_ratios_q: list[str] = []
    ms_ratios_dec6: list[str] = []
    for idx in range(4):
        if energies[idx] == 0:
            ratios_q.append("0")
            ratios_dec6.append("0.000000")
            ms_ratios_q.append("0")
            ms_ratios_dec6.append("0.000000")
        else:
            r = Fraction(energies[idx + 1], energies[idx])
            ratios_q.append(format_rational(r))
            ratios_dec6.append(format_decimal(r, 6))
            # Per-sample mean-square ratio: (E_{n}/(L-n)) / (E_{n-1}/(L-n+1)) where n = idx + 2
            n_ord = idx + 2
            r_ms = Fraction(energies[idx + 1] * (length - n_ord + 1), energies[idx] * (length - n_ord))
            ms_ratios_q.append(format_rational(r_ms))
            ms_ratios_dec6.append(format_decimal(r_ms, 6))
    return {
        "length": length,
        "energies_E1_to_E5": energies,
        "ratios_R2_to_R5_q": ratios_q,
        "ratios_R2_to_R5_dec6": ratios_dec6,
        "ms_ratios_R2_to_R5_q": ms_ratios_q,
        "ms_ratios_R2_to_R5_dec6": ms_ratios_dec6,
    }


def ducci_orbit_exact(seq: Sequence[int], *, max_steps: int = 64) -> dict[str, Any]:
    """Exact integer cyclic Ducci iteration D_cyc(v)_i = |v_{(i+1) mod L} - v_i|."""
    cur = tuple(_require_int_seq(seq, "ducci_seq", min_len=2, max_len=32))
    cap = require_exact_int(max_steps, "max_steps", lo=1, hi=512)
    n = len(cur)
    zeros = (0,) * n
    seen: dict[tuple[int, ...], int] = {cur: 0}
    for step in range(1, cap + 1):
        nxt = tuple(abs(cur[(i + 1) % n] - cur[i]) for i in range(n))
        if nxt == zeros:
            return {
                "length": n,
                "outcome": "ZERO",
                "steps_to_zero": step,
                "cycle_entry_step": -1,
                "cycle_period": 0,
                "terminal_state": list(zeros),
            }
        if nxt in seen:
            return {
                "length": n,
                "outcome": "CYCLE",
                "steps_to_zero": -1,
                "cycle_entry_step": seen[nxt],
                "cycle_period": step - seen[nxt],
                "terminal_state": list(nxt),
            }
        seen[nxt] = step
        cur = nxt
    raise MozartPerfectBridgeError("DUCCI_STEP_LIMIT", f"Ducci orbit exceeded {cap} steps")


def to_base_digits(n: int, base: int) -> list[int]:
    """Exact base-b representation (MSB first) for positive integers."""
    val = require_exact_int(n, "base_n", lo=1)
    b = require_exact_int(base, "base_b", lo=2, hi=36)
    digits: list[int] = []
    cur = val
    while cur > 0:
        cur, rem = divmod(cur, b)
        digits.append(rem)
    digits.reverse()
    return digits


# ============================================================================
# 4. Four Exact Mathematical Pillars (Portal 38)
# ============================================================================

def certify_pillar1_frobenius_canaday_euclid() -> dict[str, Any]:
    # A. Mozart 2^n-length Ducci nilpotence + exact F_2[x] ring verification Delta^{2^n} == 0 mod (x^{2^n}+1)
    mozart_cases = (
        ("K551_4note_CDFE", K551_4NOTE, 2),
        ("K545_Alberti_4", K545_ALBERTI_4, 2),
        ("K551_8note", K551_8NOTE, 3),
        ("K550_8note", K550_8NOTE, 3),
    )
    mozart_nilpotence: list[dict[str, Any]] = []
    for name, seq, n_exp in mozart_cases:
        length = 1 << n_exp
        orb = ducci_orbit_exact(seq, max_steps=32)
        # Binary reduction mod 2 as polynomial in F_2[x] / (x^L + 1)
        poly_mod2 = sum((v & 1) << i for i, v in enumerate(seq))
        mod_poly = (1 << length) ^ 1
        delta_pow = f2_pow(0b11, length)  # (x + 1)^{2^n}
        annih_rem = f2_divmod(f2_mul(delta_pow, poly_mod2), mod_poly)[1]
        mozart_nilpotence.append(
            {
                "case_id": name,
                "length": length,
                "exponent_n": n_exp,
                "outcome": orb["outcome"],
                "steps_to_zero": orb["steps_to_zero"],
                "f2_frobenius_exact": delta_pow == mod_poly,
                "f2_annihilation_rem": annih_rem,
                "verified": all(
                    (
                        orb["outcome"] == "ZERO",
                        0 < orb["steps_to_zero"] <= length,
                        delta_pow == mod_poly,
                        annih_rem == 0,
                    )
                ),
            }
        )

    # B. Canaday (1941) splitting perfect polynomials A_n(x) = x^{2^n-1} (x+1)^{2^n-1} for n=1..6
    canaday_rows: list[dict[str, Any]] = []
    for n in range(1, 7):
        e = (1 << n) - 1
        frob_lhs = f2_pow(0b11, 1 << n)
        frob_rhs = (1 << (1 << n)) ^ 1
        quot, rem = f2_divmod(frob_rhs, 0b11)
        x_pow = f2_pow(0b10, e)
        xp1_pow = f2_pow(0b11, e)
        sigma_x = f2_sigma_prime_power(0b10, e)
        sigma_xp1 = f2_sigma_prime_power(0b11, e)
        a_poly = f2_mul(x_pow, xp1_pow)
        sigma_a = f2_mul(sigma_x, sigma_xp1)

        # Direct all-divisor XOR verification for n <= 3 (4, 16, 64 divisors)
        direct_checked = n <= 3
        direct_ok = True
        if direct_checked:
            xor_all = 0
            for i in range(e + 1):
                for j in range(e + 1):
                    xor_all ^= f2_mul(f2_pow(0b10, i), f2_pow(0b11, j))
            direct_ok = xor_all == a_poly

        canaday_rows.append(
            {
                "n": n,
                "exponent_2n_minus_1": e,
                "degree": f2_deg(a_poly),
                "frobenius_identity_exact": frob_lhs == frob_rhs,
                "quotient_by_x_plus_1_exact": all((rem == 0, quot == xp1_pow)),
                "sigma_x_eq_xp1_pow": sigma_x == xp1_pow,
                "sigma_xp1_eq_x_pow": sigma_xp1 == x_pow,
                "sigma_An_eq_An": sigma_a == a_poly,
                "direct_divisor_sum_checked": direct_checked,
                "direct_divisor_sum_exact": direct_ok,
                "verified": all(
                    (
                        frob_lhs == frob_rhs,
                        rem == 0,
                        quot == xp1_pow,
                        sigma_x == xp1_pow,
                        sigma_xp1 == x_pow,
                        sigma_a == a_poly,
                        f2_deg(a_poly) == 2 * e,
                        direct_ok,
                    )
                ),
            }
        )

    # C. Characteristic-0 x=2 specialization -> Euclid-Euler even perfect numbers + composite m=4 contrast
    euclid_rows: list[dict[str, Any]] = []
    for p in (2, 3, 5, 7, 13, 17, 19):
        mp = (1 << p) - 1
        mp_prime = is_prime_exact(mp)
        two_pow = 1 << (p - 1)
        n_perf = two_pow * mp
        sigma_two_pow = (1 << p) - 1
        sigma_mp = mp + 1
        sigma_n = sigma_two_pow * sigma_mp
        direct_checked = p <= 7
        direct_sigma_ok = True
        if direct_checked:
            direct_sigma_ok = sigma_k_exact(n_perf, 1) == 2 * n_perf
        euclid_rows.append(
            {
                "p": p,
                "mersenne_Mp": mp,
                "Mp_is_prime": mp_prime,
                "even_perfect_N": n_perf,
                "sigma_2pm1_eq_Mp": sigma_two_pow == mp,
                "sigma_N_eq_2N": sigma_n == 2 * n_perf,
                "direct_divisor_sum_checked": direct_checked,
                "direct_divisor_sum_exact": direct_sigma_ok,
                "verified": all((mp_prime, sigma_two_pow == mp, sigma_n == 2 * n_perf, direct_sigma_ok)),
            }
        )

    # Composite exponent m=4 separation: F_2[x] stays primary vs Z splits 2^4-1 = 15 = 3*5
    m_comp = 4
    z_m4 = (1 << m_comp) - 1  # 15
    n_comp = (1 << (m_comp - 1)) * z_m4  # 120
    sigma_n_comp = sigma_k_exact(n_comp, 1)  # 360
    f2_m4_primary = f2_pow(0b11, 4) == ((1 << 4) ^ 1)
    comp_contrast = {
        "m": m_comp,
        "z_2powm_minus_1": z_m4,
        "z_factors": [3, 5],
        "z_is_prime": is_prime_exact(z_m4),
        "z_candidate_N": n_comp,
        "z_sigma_N": sigma_n_comp,
        "z_two_N": 2 * n_comp,
        "z_abundant_excess": sigma_n_comp - 2 * n_comp,
        "f2_x4_plus_1_eq_xp1_pow4": f2_m4_primary,
        "f2_A2_perfect_verified": canaday_rows[1]["sigma_An_eq_An"],
        "verified": all(
            (
                z_m4 == 15,
                not is_prime_exact(z_m4),
                n_comp == 120,
                sigma_n_comp == 360,
                sigma_n_comp != 2 * n_comp,
                f2_m4_primary,
                canaday_rows[1]["sigma_An_eq_An"],
            )
        ),
    }

    p1_ok = all(
        (
            all(r["verified"] for r in mozart_nilpotence),
            all(r["verified"] for r in canaday_rows),
            all(r["verified"] for r in euclid_rows),
            comp_contrast["verified"],
        )
    )
    return {
        "mozart_2n_nilpotence": mozart_nilpotence,
        "canaday_splitting_perfect_n1_to_n6": canaday_rows,
        "euclid_euler_even_perfect_p2_to_p19": euclid_rows,
        "composite_exponent_m4_contrast": comp_contrast,
        "all_verified": p1_ok,
    }


def certify_pillar2_cyclotomic_opn_obstruction() -> dict[str, Any]:
    # A. Exact cyclotomic factorization S^L - 1 = prod_{d|L} Phi_d(S) & non-2^k Mozart Ducci obstruction
    cyc_cases = (
        ("K550_3note_sigh", K550_3NOTE_SIGH, 3, [1, 3], 3),
        ("F2_impulse_L5", (1, 0, 0, 0, 0), 5, [1, 5], 15),
        ("K331_6_8_bar", K331_6_8_BAR, 6, [1, 2, 3, 6], 6),
    )
    cyclotomic_obstructions: list[dict[str, Any]] = []
    for name, seq, length, expected_divs, expected_period in cyc_cases:
        divs = [d for d in range(1, length + 1) if length % d == 0]
        prod_poly = [1]
        odd_cyc_coprime = True
        for d in divs:
            phi_d = cyclotomic_zpoly(d)
            prod_poly = zpoly_mul(prod_poly, phi_d)
            if d > 1 and (d & 1) == 1:
                phi_f2 = sum(((c & 1) << i) for i, c in enumerate(phi_d))
                if f2_gcd(0b11, phi_f2) != 1:
                    odd_cyc_coprime = False
        target_poly = [-1] + [0] * (length - 1) + [1]
        orb = ducci_orbit_exact(seq, max_steps=64)
        cyclotomic_obstructions.append(
            {
                "case_id": name,
                "L": length,
                "divisors": divs,
                "factorization_exact": prod_poly == target_poly,
                "odd_cyclotomic_coprime_to_delta_f2": odd_cyc_coprime,
                "ducci_outcome": orb["outcome"],
                "ducci_cycle_period": orb["cycle_period"],
                "verified": all(
                    (
                        divs == expected_divs,
                        prod_poly == target_poly,
                        odd_cyc_coprime,
                        orb["outcome"] == "CYCLE",
                        orb["cycle_period"] == expected_period,
                    )
                ),
            }
        )

    # B. Exact cyclotomic divisor factorization sigma(p^a) = prod_{d|(a+1), d>1} Phi_d(p) in Z and F_2[x]
    z_cyc_checks = 0
    z_cyc_exact = 0
    for p in (2, 3, 5, 7):
        for a in range(1, 7):
            z_cyc_checks += 1
            lhs = sum(p**k for k in range(a + 1))
            rhs = 1
            for d in range(2, a + 2):
                if (a + 1) % d == 0:
                    rhs *= zpoly_eval(cyclotomic_zpoly(d), p)
            if lhs == rhs:
                z_cyc_exact += 1

    f2_cyc_checks = 0
    f2_cyc_exact = 0
    for poly_p in (0b111, 0b1011, 0b1101):  # x^2+x+1, x^3+x+1, x^3+x^2+1
        for a in range(1, 6):
            f2_cyc_checks += 1
            lhs_f2 = f2_sigma_prime_power(poly_p, a)
            rhs_f2 = 1
            for d in range(2, a + 2):
                if (a + 1) % d == 0:
                    phi_d = cyclotomic_zpoly(d)
                    eval_f2 = 0
                    for deg_i, c in enumerate(phi_d):
                        if (c & 1) == 1:
                            eval_f2 ^= f2_pow(poly_p, deg_i)
                    rhs_f2 = f2_mul(rhs_f2, eval_f2)
            if lhs_f2 == rhs_f2:
                f2_cyc_exact += 1

    # C. F_2[x] Odd Perfect Polynomial Square Theorem:
    # Exhaustive check over ALL odd irreducibles deg 2..6 (21 polynomials) x odd a in {1,3,5} (63 cases)
    odd_irreds: list[int] = []
    for d in range(2, 7):
        for cand in range((1 << d) + 1, 1 << (d + 1), 2):
            if f2_is_irreducible(cand):
                odd_irreds.append(cand)
    odd_exp_cases = 0
    odd_exp_div_ok = 0
    for poly_p in odd_irreds:
        p_plus_1 = poly_p ^ 1
        div_x_xp1 = f2_divmod(p_plus_1, 0b110)[1] == 0
        for a in (1, 3, 5):
            odd_exp_cases += 1
            sig_pa = f2_sigma_prime_power(poly_p, a)
            div_p1 = f2_divmod(sig_pa, p_plus_1)[1] == 0
            div_xxp1_sig = f2_divmod(sig_pa, 0b110)[1] == 0
            if div_x_xp1:
                if div_p1:
                    if div_xxp1_sig:
                        odd_exp_div_ok += 1

    # Also test 6 explicit non-square odd composite products A = P^a * Q^b -> x(x+1) | sigma(A), sigma(A) != A
    composite_odd_specs = (
        ((0b111, 1), (0b1011, 1)),
        ((0b111, 1), (0b1101, 2)),
        ((0b111, 3), (0b1011, 2)),
        ((0b1011, 1), (0b1101, 1)),
        ((0b111, 2), (0b10011, 1)),
        ((0b1011, 3), (0b11001, 2)),
    )
    non_square_odd_blocked = 0
    for spec in composite_odd_specs:
        poly_a = 1
        sig_a = 1
        for p_i, e_i in spec:
            poly_a = f2_mul(poly_a, f2_pow(p_i, e_i))
            sig_a = f2_mul(sig_a, f2_sigma_prime_power(p_i, e_i))
        if f2_gcd(poly_a, 0b110) == 1:
            if f2_divmod(sig_a, 0b110)[1] == 0:
                if sig_a != poly_a:
                    non_square_odd_blocked += 1

    f2_square_theorem = {
        "odd_irreducibles_deg2_to_6_count": len(odd_irreds),
        "odd_prime_power_cases_checked": odd_exp_cases,
        "odd_prime_power_divisible_by_x_xp1": odd_exp_div_ok,
        "non_square_odd_composites_checked": len(composite_odd_specs),
        "non_square_odd_composites_blocked": non_square_odd_blocked,
        "every_f2_odd_perfect_poly_must_be_square": all(
            (
                len(odd_irreds) == 21,
                odd_exp_cases == 63,
                odd_exp_div_ok == 63,
                non_square_odd_blocked == len(composite_odd_specs),
            )
        ),
    }

    # D. Honest Law-4 / Law-5 Z Carry-Propagation Obstruction (Euler primes q == 1 mod 4 vs q == 3 mod 4)
    euler_prime_rows: list[dict[str, Any]] = []
    for q in (5, 13, 17, 29, 37, 41):
        sig_q1 = q + 1
        sig_q5 = sum(q**k for k in range(6))
        v2_q1 = v2_exact(sig_q1)
        v2_q5 = v2_exact(sig_q5)
        euler_prime_rows.append(
            {
                "q": q,
                "q_mod_4": q % 4,
                "phi2_q": sig_q1,
                "v2_sigma_q1": v2_q1,
                "v2_sigma_q5": v2_q5,
                "exact_single_factor_of_2": all((q % 4 == 1, v2_q1 == 1, v2_q5 == 1)),
            }
        )
    mod3_control_rows: list[dict[str, Any]] = []
    for q in (3, 7, 11, 19):
        v2_q1 = v2_exact(q + 1)
        mod3_control_rows.append(
            {
                "q": q,
                "q_mod_4": q % 4,
                "v2_sigma_q1": v2_q1,
                "blocked_by_4_div_q_plus_1": all((q % 4 == 3, v2_q1 >= 2)),
            }
        )

    carry_obstruction = {
        "euler_primes_1_mod_4": euler_prime_rows,
        "mod3_control_primes": mod3_control_rows,
        "f2_parity_collapse_does_not_prove_integer_opn": True,
        "integer_opn_conjecture_remains_open": True,
        "verified": all(
            (
                len(euler_prime_rows) == 6,
                all(r["exact_single_factor_of_2"] for r in euler_prime_rows),
                len(mod3_control_rows) == 4,
                all(r["blocked_by_4_div_q_plus_1"] for r in mod3_control_rows),
            )
        ),
    }

    p2_ok = all(
        (
            all(r["verified"] for r in cyclotomic_obstructions),
            z_cyc_checks == 24,
            z_cyc_exact == 24,
            f2_cyc_checks == 15,
            f2_cyc_exact == 15,
            f2_square_theorem["every_f2_odd_perfect_poly_must_be_square"],
            carry_obstruction["verified"],
        )
    )
    return {
        "cyclotomic_mozart_obstructions": cyclotomic_obstructions,
        "cyclotomic_sigma_factorization": {
            "z_prime_power_checks": z_cyc_checks,
            "z_prime_power_exact": z_cyc_exact,
            "f2_prime_power_checks": f2_cyc_checks,
            "f2_prime_power_exact": f2_cyc_exact,
            "verified": all((z_cyc_exact == 24, f2_cyc_exact == 15)),
        },
        "f2_odd_perfect_square_theorem": f2_square_theorem,
        "z_carry_propagation_obstruction": carry_obstruction,
        "all_verified": p2_ok,
    }


def certify_pillar3_nyquist_pentagonal_ramanujan() -> dict[str, Any]:
    # A. Nyquist-4 spectral prism: sigma(1..32) vs K.545 Alberti vs K.550 vs n^2 control
    sigma_32 = [sigma_k_exact(n, 1) for n in range(1, 33)]
    quad_32 = [n * n for n in range(1, 33)]
    prism_specs = (
        ("quadratic_n2_1_to_32", quad_32),
        ("K550_phrase_20", K550_PHRASE_20),
        ("K545_Alberti_16", K545_ALBERTI_16),
        ("sigma_1_to_32", sigma_32),
    )
    prism_rows: list[dict[str, Any]] = []
    r2_map: dict[str, Fraction] = {}
    sigma_raw_all_gt_3_4 = False
    sigma_ms_all_gt_3_6 = False
    for name, seq in prism_specs:
        pr = spectral_prism_exact(seq)
        pr["name"] = name
        prism_rows.append(pr)
        r2_q = Fraction(pr["energies_E1_to_E5"][1], pr["energies_E1_to_E5"][0])
        r2_map[name] = r2_q
        if name == "sigma_1_to_32":
            es = pr["energies_E1_to_E5"]
            ln = pr["length"]
            sigma_raw_all_gt_3_4 = all(Fraction(es[j + 1], es[j]) > Fraction(17, 5) for j in range(4))
            sigma_ms_all_gt_3_6 = all(
                Fraction(es[j + 1] * (ln - (j + 2) + 1), es[j] * (ln - (j + 2))) > Fraction(18, 5)
                for j in range(4)
            )

    prism_ordering_ok = (
        r2_map["quadratic_n2_1_to_32"]
        < 1
        < r2_map["K550_phrase_20"]
        < 2
        < 3
        < r2_map["K545_Alberti_16"]
        < r2_map["sigma_1_to_32"]
        < 4
    )

    # B. Euler's Pentagonal Annihilator on n=1..100 + Delta^2 p_k == 3 + Alberti period-4 sign kernel
    sig_table = [0] + [sigma_k_exact(n, 1) for n in range(1, 101)]
    pent_plus = [k * (3 * k - 1) // 2 for k in range(1, 21)]
    pent_minus = [k * (3 * k + 1) // 2 for k in range(1, 21)]
    pent_residuals_zero = 0
    for n in range(1, 101):
        acc = sig_table[n]
        for k_idx in range(20):
            sign = -1 if ((k_idx + 1) & 1) == 1 else 1
            for pk in (pent_plus[k_idx], pent_minus[k_idx]):
                if n - pk > 0:
                    acc += sign * sig_table[n - pk]
                elif n - pk == 0:
                    acc += sign * n
        if acc == 0:
            pent_residuals_zero += 1

    d2_plus = forward_difference(pent_plus, 2)
    d2_minus = forward_difference(pent_minus, 2)
    d3_plus = forward_difference(pent_plus, 3)
    d3_minus = forward_difference(pent_minus, 3)

    # Exact Alberti period-4 sign operator (S^2 + I) | (S^4 - I) on [+1, +1, -1, -1] * 4
    sign_seq_16 = [1, 1, -1, -1] * 4
    s2_plus_i = [sign_seq_16[i + 2] + sign_seq_16[i] for i in range(14)]
    s4_minus_i = [sign_seq_16[i + 4] - sign_seq_16[i] for i in range(12)]
    euler_pentagonal = {
        "n_checked": 100,
        "zero_residual_count": pent_residuals_zero,
        "delta2_pent_plus_const_3": all(v == 3 for v in d2_plus),
        "delta2_pent_minus_const_3": all(v == 3 for v in d2_minus),
        "delta3_pent_plus_zero": all(v == 0 for v in d3_plus),
        "delta3_pent_minus_zero": all(v == 0 for v in d3_minus),
        "sign_seq_period4_alberti_s2_plus_I_zero": s2_plus_i == [0] * 14,
        "sign_seq_period4_alberti_s4_minus_I_zero": s4_minus_i == [0] * 12,
        "verified": all(
            (
                pent_residuals_zero == 100,
                all(v == 3 for v in d2_plus),
                all(v == 3 for v in d2_minus),
                all(v == 0 for v in d3_plus),
                all(v == 0 for v in d3_minus),
                s2_plus_i == [0] * 14,
                s4_minus_i == [0] * 12,
            )
        ),
    }

    # C. Ramanujan E_2 <-> E_4 general convolution (n=1..64: 12 sum sigma(k)sigma(n-k) == 5*sigma_3(n) + (1-6n)*sigma(n))
    #    PLUS exact perfect-number iff specialization (2n(1-6n) holds iff sigma(n)==2n -> selects {6, 28} in 1..64 + 496!)
    ram_n_checked = 64
    ram_general_zero = 0
    ram_perfect_spec_hits: list[int] = []
    for n in range(1, ram_n_checked + 1):
        lhs = 12 * sum(sig_table[k] * sig_table[n - k] for k in range(1, n))
        s3 = sigma_k_exact(n, 3)
        rhs_gen = 5 * s3 + (1 - 6 * n) * sig_table[n]
        if lhs == rhs_gen:
            ram_general_zero += 1
        rhs_perf = 5 * s3 + 2 * n * (1 - 6 * n)
        if lhs == rhs_perf:
            ram_perfect_spec_hits.append(n)

    # Extend sigma table to 496 for exact witness at n=496
    sig_496 = [0] + [sigma_k_exact(n, 1) for n in range(1, 497)]
    perfect_witnesses: list[dict[str, Any]] = []
    for n_perf, expected_val in ((6, 840), (28, 116_208), (496, 694_330_560)):
        lhs = 12 * sum(sig_496[k] * sig_496[n_perf - k] for k in range(1, n_perf))
        sig3 = sigma_k_exact(n_perf, 3)
        sig1 = sig_496[n_perf]
        rhs_gen = 5 * sig3 + (1 - 6 * n_perf) * sig1
        rhs_perf = 5 * sig3 + 2 * n_perf * (1 - 6 * n_perf)
        perfect_witnesses.append(
            {
                "n": n_perf,
                "sigma_1": sig1,
                "sigma_3": sig3,
                "lhs_12_conv": lhs,
                "rhs_general_e2_e4": rhs_gen,
                "rhs_perfect_2n_1m6n": rhs_perf,
                "verified": all((sig1 == 2 * n_perf, lhs == expected_val, rhs_gen == expected_val, rhs_perf == expected_val)),
            }
        )

    ramanujan = {
        "n_checked_1_to_64": ram_n_checked,
        "general_e2_e4_zero_residual_count": ram_general_zero,
        "perfect_specialization_hits_1_to_64": ram_perfect_spec_hits,
        "perfect_number_witnesses": perfect_witnesses,
        "verified": all(
            (
                ram_general_zero == 64,
                ram_perfect_spec_hits == [6, 28],
                all(w["verified"] for w in perfect_witnesses),
            )
        ),
    }

    p3_ok = all(
        (
            sigma_raw_all_gt_3_4,
            sigma_ms_all_gt_3_6,
            prism_ordering_ok,
            prism_rows[0]["energies_E1_to_E5"][2:] == [0, 0, 0],
            euler_pentagonal["verified"],
            ramanujan["verified"],
        )
    )
    return {
        "spectral_prism_comparison": prism_rows,
        "sigma_raw_R2_to_R5_all_gt_17_over_5": sigma_raw_all_gt_3_4,
        "sigma_ms_R2_to_R5_all_gt_18_over_5": sigma_ms_all_gt_3_6,
        "strict_nyquist_ordering_verified": prism_ordering_ok,
        "euler_pentagonal_annihilator": euler_pentagonal,
        "ramanujan_e2_e4_convolution": ramanujan,
        "all_verified": p3_ok,
    }


def certify_pillar4_anti_numerology_control() -> dict[str, Any]:
    # 1. Transposition invariance (Stage B operators invariant vs Stage A C-class histogram broken)
    base_prism = spectral_prism_exact(K545_ALBERTI_16)
    base_c_count = sum(1 for v in K545_ALBERTI_16 if v % 12 == 0)
    transp_rows: list[dict[str, Any]] = []
    for shift in (0, 1, 5, 7, 12):
        shifted = tuple(v + shift for v in K545_ALBERTI_16)
        sh_prism = spectral_prism_exact(shifted)
        sh_c_count = sum(1 for v in shifted if v % 12 == 0)
        transp_rows.append(
            {
                "semitone_shift": shift,
                "stage_b_energies_identical": sh_prism["energies_E1_to_E5"] == base_prism["energies_E1_to_E5"],
                "stage_b_ratios_identical": sh_prism["ratios_R2_to_R5_q"] == base_prism["ratios_R2_to_R5_q"],
                "stage_a_c_pitch_class_count": sh_c_count,
                "stage_a_histogram_preserved": sh_c_count == base_c_count,
            }
        )
    transposition_control_ok = all(
        (
            all(r["stage_b_energies_identical"] for r in transp_rows),
            all(r["stage_b_ratios_identical"] for r in transp_rows),
            not transp_rows[1]["stage_a_histogram_preserved"],
            not transp_rows[2]["stage_a_histogram_preserved"],
            not transp_rows[3]["stage_a_histogram_preserved"],
        )
    )

    # 2. Radix invariance (Stage B sigma(N)==2N invariant vs Stage A base-10 last-digit/digital-root artifact)
    radix_rows: list[dict[str, Any]] = []
    for base in (2, 8, 10, 12, 16):
        endings = [to_base_digits(n, base)[-1] for n in (6, 28, 496)]
        digit_sums = [sum(to_base_digits(n, base)) for n in (6, 28, 496)]
        radix_rows.append(
            {
                "base": base,
                "last_digits_6_28_496": endings,
                "digit_sums_6_28_496": digit_sums,
                "ends_in_6_or_8_in_this_base": all(d in (6, 8) for d in endings),
                "stage_b_sigma_eq_2N_all_3": all(sigma_k_exact(n, 1) == 2 * n for n in (6, 28, 496)),
            }
        )
    radix_control_ok = all(
        (
            all(r["stage_b_sigma_eq_2N_all_3"] for r in radix_rows),
            radix_rows[2]["ends_in_6_or_8_in_this_base"],  # base 10 artifact holds
            not radix_rows[0]["ends_in_6_or_8_in_this_base"],  # base 2 breaks
            not radix_rows[1]["ends_in_6_or_8_in_this_base"],  # base 8 breaks
            not radix_rows[3]["ends_in_6_or_8_in_this_base"],  # base 12 breaks
        )
    )

    # 3. CS-13 Golden-Section bar-count refutation (exact integer defect b^2 - a(a+b) != 0 and > 2% off phi^-1)
    phi_inv_lo = Fraction(618_033, 1_000_000)
    phi_inv_hi = Fraction(618_034, 1_000_000)
    phi_bracket_ok = all((phi_inv_lo * phi_inv_lo + phi_inv_lo < 1, phi_inv_hi * phi_inv_hi + phi_inv_hi > 1))
    golden_rows: list[dict[str, Any]] = []
    for sonata, a_bars, b_bars in (("K.282_I", 15, 21), ("K.283_I", 53, 67), ("K.332_I", 93, 136), ("K.576_I", 58, 102)):
        defect = b_bars * b_bars - a_bars * (a_bars + b_bars)
        ab = Fraction(a_bars, b_bars)
        min_dev = (ab - phi_inv_hi) if ab > phi_inv_hi else (phi_inv_lo - ab)
        golden_rows.append(
            {
                "sonata": sonata,
                "a": a_bars,
                "b": b_bars,
                "exact_golden_defect_Z": defect,
                "a_over_b_q": format_rational(ab),
                "min_deviation_exceeds_2pct": min_dev > Fraction(1, 50),
                "nonzero_defect": defect != 0,
            }
        )
    golden_control_ok = all(
        (
            phi_bracket_ok,
            all(r["nonzero_defect"] for r in golden_rows),
            all(r["min_deviation_exceeds_2pct"] for r in golden_rows),
        )
    )

    return {
        "transposition_invariance_control": {
            "cases": transp_rows,
            "stage_b_invariant_stage_a_broken": transposition_control_ok,
        },
        "radix_invariance_control": {
            "cases": radix_rows,
            "stage_b_invariant_base10_artifact_broken": radix_control_ok,
        },
        "golden_ratio_bar_count_refutation": {
            "phi_inv_bracket_verified": phi_bracket_ok,
            "cases": golden_rows,
            "all_reject_golden_numerology": golden_control_ok,
        },
        "all_verified": all((transposition_control_ok, radix_control_ok, golden_control_ok)),
    }


def build_payload() -> dict[str, Any]:
    p1 = certify_pillar1_frobenius_canaday_euclid()
    p2 = certify_pillar2_cyclotomic_opn_obstruction()
    p3 = certify_pillar3_nyquist_pentagonal_ramanujan()
    p4 = certify_pillar4_anti_numerology_control()
    all_ok = all((p1["all_verified"], p2["all_verified"], p3["all_verified"], p4["all_verified"]))
    return {
        "track_id": TRACK_ID,
        "portal_id": "Portal-38",
        "novelty_class": "N1",
        "pillar1_frobenius_canaday_euclid": p1,
        "pillar2_cyclotomic_opn_obstruction": p2,
        "pillar3_nyquist_pentagonal_ramanujan": p3,
        "pillar4_anti_numerology_control": p4,
        "summary": {
            "pillar_count": 4,
            "all_four_pillars_verified": all_ok,
            "integer_opn_conjecture_remains_open": True,
            "float_count_on_trust_path": 0,
            "bare_assert_count": 0,
            "rng_calls": 0,
        },
    }
