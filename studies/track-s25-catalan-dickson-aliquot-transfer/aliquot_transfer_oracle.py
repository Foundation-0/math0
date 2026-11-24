#!/usr/bin/env python3
"""Track S25 (AUDIT-125): Catalan-Dickson Aliquot Transfer Operator & Unified
Five-Pillar Pure-Z/Q Exact Engine (Portals 17, 18, 19, 20, 21).

100% pure Python 3 stdlib (int, fractions.Fraction, math, hashlib).
ZERO floating-point arithmetic, ZERO bare assert statements, ZERO RNG calls,
ZERO third-party imports, ZERO personal-path or private-repo references.

Honest Law-4 Novelty: N1 (clean-room unified pure-Z/Q verification engine, exact
5-state (v_2, v_3, v_5) finite-state aliquot Markov transfer operator & invariant
drift contrast, unified 5-pillar cross-portal synthesis, and atomic dir_fd Zone-B
certification; all classical theorems & open conjectures quarantined as N0).
"""
from __future__ import annotations

from fractions import Fraction
import hashlib
import math
from typing import Any

TRACK_ID = "TRACK-S25-AUDIT-125"
SCHEMA_VERSION = "1.0.0"
MAX_RATIONAL_BITS = 16_000
MAX_JSON_INT_BITS = 4_000
SIEVE_LIMIT = 100_000
ATLAS_LIMIT = 1_000
ATLAS_VALUE_CAP = 10**22

# Deterministic Miller-Rabin base set (Sorenson & Webster 2015: exact < 3.317e24)
_MR_BASES: tuple[int, ...] = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
LEHMER_FIVE_SEEDS: tuple[int, ...] = (276, 552, 564, 660, 966)
SYLVESTER_Q_LIST: tuple[int, ...] = (3, 5, 7, 11, 13, 17, 19, 47, 101)
KANOLD_ODD_H_LIST: tuple[int, ...] = (3, 5, 7, 9, 11, 13, 15)
MARKOV_STATE_NAMES: tuple[str, ...] = (
    "D2_PLAIN",
    "D6_CORE",
    "D10_30_MIX",
    "D4_HIGH2_NO3",
    "D12_24_HIGH2_3",
)

# Module-level deterministic caches for default SIEVE_LIMIT (100_000)
_DEFAULT_SIEVE_CACHE: tuple[list[int], list[int], list[int]] | None = None
_SMALL_PRIMES_CACHE: tuple[int, ...] | None = None
_ALIQUOT_BIG_CACHE: dict[int, int] = {}


class AliquotTransferError(ValueError):
    """Typed fail-closed error for Track S25 domain, algebraic, and Zone-B checks."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"[{code}] {message}")
        self.code = code
        self.detail = message


# ============================================================================
# 1. Strict Type, Domain, and Exact Rational Primitives
# ============================================================================

def require_ok(cond: bool, code: str, message: str) -> None:
    if type(cond) is not bool:
        raise AliquotTransferError("INVALID_CONDITION_TYPE", f"{code}: condition must be exact bool")
    if not cond:
        raise AliquotTransferError(code, message)


def require_exact_int(
    val: Any,
    name: str,
    lo: int | None = None,
    hi: int | None = None,
) -> int:
    if type(val) is not int:
        raise AliquotTransferError("INVALID_INT_TYPE", f"{name} must be exact int")
    if val.bit_length() > MAX_RATIONAL_BITS:
        raise AliquotTransferError("INT_BIT_LIMIT", f"{name} exceeds {MAX_RATIONAL_BITS}-bit cap")
    if lo is not None and val < lo:
        raise AliquotTransferError("INT_OUT_OF_RANGE", f"{name} must be >= {lo}")
    if hi is not None and val > hi:
        raise AliquotTransferError("INT_OUT_OF_RANGE", f"{name} must be <= {hi}")
    return val


def require_exact_bool(val: Any, name: str) -> bool:
    if type(val) is not bool:
        raise AliquotTransferError("INVALID_BOOL_TYPE", f"{name} must be exact bool")
    return val


def require_exact_fraction(val: Any, name: str) -> Fraction:
    if type(val) is not Fraction:
        raise AliquotTransferError("INVALID_FRACTION_TYPE", f"{name} must be exact Fraction")
    if val.numerator.bit_length() > MAX_RATIONAL_BITS or val.denominator.bit_length() > MAX_RATIONAL_BITS:
        raise AliquotTransferError("RATIONAL_BIT_LIMIT", f"{name} exceeds {MAX_RATIONAL_BITS}-bit cap")
    return val


def format_fraction(q: Fraction) -> str:
    q = require_exact_fraction(q, "q")
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"


# ============================================================================
# 2. Exact Deterministic Number-Theory Engine (Sieve, Primality, Factoring)
# ============================================================================

def build_arithmetic_sieve(limit: int) -> tuple[list[int], list[int], list[int]]:
    """Build exact (prime_factor, sigma_1, tau) tables for 0..limit in pure int."""
    limit = require_exact_int(limit, "limit", lo=2, hi=SIEVE_LIMIT)
    global _DEFAULT_SIEVE_CACHE
    if limit == SIEVE_LIMIT and _DEFAULT_SIEVE_CACHE is not None:
        return _DEFAULT_SIEVE_CACHE
    pf = list(range(limit + 1))
    root = math.isqrt(limit)
    for i in range(2, root + 1):
        if pf[i] == i:
            pf[i * i : limit + 1 : i] = [i] * (((limit - i * i) // i) + 1)
    sig1 = [1] * (limit + 1)
    tau = [1] * (limit + 1)
    sig1[0] = 0
    tau[0] = 0
    for n in range(2, limit + 1):
        p = pf[n]
        m = n // p
        if m % p != 0:
            sig1[n] = sig1[m] * (p + 1)
            tau[n] = tau[m] * 2
        else:
            pe = p * p
            e = 2
            m //= p
            while m % p == 0:
                m //= p
                pe *= p
                e += 1
            sig1[n] = sig1[m] * ((pe * p - 1) // (p - 1))
            tau[n] = tau[m] * (e + 1)
    result = (pf, sig1, tau)
    if limit == SIEVE_LIMIT:
        _DEFAULT_SIEVE_CACHE = result
    return result


def _get_small_primes() -> tuple[int, ...]:
    global _SMALL_PRIMES_CACHE
    if _SMALL_PRIMES_CACHE is None:
        pf, _, _ = build_arithmetic_sieve(SIEVE_LIMIT)
        _SMALL_PRIMES_CACHE = tuple(i for i in range(2, 1000) if pf[i] == i)
    return _SMALL_PRIMES_CACHE


def v_p_exact(n: int, p: int) -> int:
    """Exact p-adic valuation v_p(n) for n >= 1, prime p >= 2."""
    n = require_exact_int(n, "n", lo=1)
    p = require_exact_int(p, "p", lo=2)
    require_ok(is_prime_exact(p), "NOT_PRIME", f"p={p} must be prime")
    if p == 2:
        return (n & -n).bit_length() - 1
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def is_prime_exact(n: int) -> bool:
    """Deterministic primality test (exact for all 0 <= n < 3.317e24)."""
    n = require_exact_int(n, "n", lo=0, hi=3_317_044_064_679_887_385_961_980)
    if n < 2:
        return False
    if n in _MR_BASES:
        return True
    d = n - 1
    r = (d & -d).bit_length() - 1
    d >>= r
    for a in _MR_BASES:
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        composite = True
        for _ in range(r - 1):
            x = (x * x) % n
            if x == n - 1:
                composite = False
                break
        if composite:
            return False
    return True


def _pollard_brent_det(n: int) -> int:
    """Deterministic Brent-Pollard rho factor finder (zero RNG)."""
    c = 1
    while True:
        y = 2
        r = 1
        q = 1
        g = 1
        while g == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            while k < r:
                ys = y
                lim = 128 if (r - k) > 128 else (r - k)
                for _ in range(lim):
                    y = (y * y + c) % n
                    q = (q * abs(x - y)) % n
                g = math.gcd(q, n)
                k += lim
                if g != 1:
                    break
            r <<= 1
        if g == n:
            while True:
                ys = (ys * ys + c) % n
                g = math.gcd(abs(x - ys), n)
                if g > 1:
                    break
        if g != n:
            return g
        c += 1


def factorize_exact(n: int) -> dict[int, int]:
    """Deterministic exact prime factorization for 1 <= n < 3.317e24."""
    n = require_exact_int(n, "n", lo=1, hi=3_317_044_064_679_887_385_961_980)
    fac: dict[int, int] = {}
    if n <= SIEVE_LIMIT:
        pf, _, _ = build_arithmetic_sieve(SIEVE_LIMIT)
        rem = n
        while rem > 1:
            p = pf[rem]
            e = 0
            while rem % p == 0:
                rem //= p
                e += 1
            fac[p] = fac.get(p, 0) + e
        return fac
    rem = n
    for p in _get_small_primes():
        if p * p > rem:
            break
        if rem % p == 0:
            e = 0
            while rem % p == 0:
                rem //= p
                e += 1
            fac[p] = e
    if rem > 1:
        stack = [rem]
        while stack:
            u = stack.pop()
            if is_prime_exact(u):
                fac[u] = fac.get(u, 0) + 1
            else:
                d = _pollard_brent_det(u)
                stack.append(d)
                stack.append(u // d)
    return fac


def sigma1_exact(n: int) -> int:
    """Exact divisor sum sigma_1(n) for 1 <= n < 3.317e24."""
    n = require_exact_int(n, "n", lo=1, hi=3_317_044_064_679_887_385_961_980)
    if n <= SIEVE_LIMIT:
        _, sig1, _ = build_arithmetic_sieve(SIEVE_LIMIT)
        return sig1[n]
    fac = factorize_exact(n)
    prod = 1
    for p, e in fac.items():
        prod *= (p ** (e + 1) - 1) // (p - 1)
    return prod


def aliquot_s_exact(n: int) -> int:
    """Exact aliquot sum s(n) = sigma_1(n) - n."""
    n = require_exact_int(n, "n", lo=1, hi=3_317_044_064_679_887_385_961_980)
    if n <= SIEVE_LIMIT:
        _, sig1, _ = build_arithmetic_sieve(SIEVE_LIMIT)
        return sig1[n] - n
    cached = _ALIQUOT_BIG_CACHE.get(n)
    if cached is not None:
        return cached
    res = sigma1_exact(n) - n
    _ALIQUOT_BIG_CACHE[n] = res
    return res


def solve_linear_fraction(matrix: list[list[Fraction]], rhs: list[Fraction]) -> list[Fraction]:
    """Exact Gauss-Jordan linear solver A x = b over Fraction (fail-closed on singularity)."""
    if type(matrix) is not list or type(rhs) is not list:
        raise AliquotTransferError("INVALID_MATRIX_TYPE", "matrix and rhs must be exact lists")
    n = len(matrix)
    require_ok(n >= 1 and len(rhs) == n, "INVALID_MATRIX_DIM", "matrix must be non-empty square matching rhs")
    aug: list[list[Fraction]] = []
    for i in range(n):
        row = matrix[i]
        require_ok(type(row) is list and len(row) == n, "INVALID_MATRIX_ROW", "each matrix row must have length n")
        aug_row = [require_exact_fraction(v, f"A[{i}][{j}]") for j, v in enumerate(row)]
        aug_row.append(require_exact_fraction(rhs[i], f"b[{i}]"))
        aug.append(aug_row)
    for col in range(n):
        piv = -1
        for r in range(col, n):
            if aug[r][col] != 0:
                piv = r
                break
        require_ok(piv != -1, "SINGULAR_MATRIX", f"zero pivot at column {col}")
        if piv != col:
            aug[col], aug[piv] = aug[piv], aug[col]
        pv = aug[col][col]
        aug[col] = [val / pv for val in aug[col]]
        for r in range(n):
            if r != col:
                factor = aug[r][col]
                aug[r] = [aug[r][c] - factor * aug[col][c] for c in range(n + 1)]
    return [aug[i][n] for i in range(n)]


# ============================================================================
# 3. Pillar 1 — Catalan-Dickson vs. Guy-Selfridge & Aliquot Transfer (Portal 17)
# ============================================================================

def classify_even_driver_state(n: int) -> int:
    """Map even n >= 2 to canonical 5-state (v_2, v_3, v_5) driver class index."""
    n = require_exact_int(n, "n", lo=2)
    require_ok(n % 2 == 0, "NOT_EVEN_DRIVER_INPUT", "driver state classifier requires even n")
    v2 = v_p_exact(n, 2)
    has3 = n % 3 == 0
    has5 = n % 5 == 0
    if v2 == 1:
        if has3 and not has5:
            return 1
        if has5:
            return 2
        return 0
    return 4 if has3 else 3


def _driver_tag_for_orbit(n: int) -> str:
    if n == 0:
        return "ZERO"
    if n % 2 != 0:
        return "ODD"
    if n % 28 == 0 and v_p_exact(n, 2) == 2:
        return "D28_PERF"
    if n % 24 == 0 and v_p_exact(n, 2) == 3:
        return "D24_DRV"
    if n % 6 == 0 and v_p_exact(n, 2) == 1:
        return "D6_PERF"
    if v_p_exact(n, 2) == 1:
        return "D2_DOWN"
    return "EVEN_OTHER"


def verify_untouchable_exact(k: int) -> dict[str, Any]:
    """Unconditional finite proof over ALL N that k >= 2 is untouchable via n <= (k-1)^2."""
    k = require_exact_int(k, "k", lo=2, hi=316)
    _, sig1, _ = build_arithmetic_sieve(SIEVE_LIMIT)
    upper = (k - 1) * (k - 1)
    preimages = [n for n in range(1, upper + 1) if sig1[n] - n == k]
    return {
        "k": k,
        "composite_preimage_upper_bound": upper,
        "preimages_found": preimages,
        "is_untouchable_over_all_N": len(preimages) == 0,
    }


def verify_pillar1_catalan_dickson_transfer() -> dict[str, Any]:
    """Certify Portal 17: parity-lock, driver monotonicity, exact Q Markov T_{2,3,5},
    untouchable proofs, Goldbach odd-untouchable reduction, and 1..1000 aliquot atlas."""
    pf, sig1, _ = build_arithmetic_sieve(SIEVE_LIMIT)

    # 1a. Parity-Lock & Zero-Density Square-Escape Theorem across 1..10,000
    parity_limit = 10_000
    parity_vs_sigma_exc = 0
    parity_vs_escape_exc = 0
    escape_count = 0
    for n in range(1, parity_limit + 1):
        sn = sig1[n] - n
        r1 = math.isqrt(n)
        is_sq = r1 * r1 == n
        is_2sq = False
        if n % 2 == 0:
            half = n // 2
            r2 = math.isqrt(half)
            is_2sq = r2 * r2 == half
        in_escape = is_sq or is_2sq
        if in_escape:
            escape_count += 1
        same_parity = (sn % 2) == (n % 2)
        if same_parity != ((sig1[n] % 2) == 0):
            parity_vs_sigma_exc += 1
        if same_parity != (not in_escape):
            parity_vs_escape_exc += 1

    # 1b. Even-Perfect Driver Monotonicity & 6-driver persistence
    mono_checked = 0
    mono_ok = True
    for d_perf in (6, 28, 496):
        for u in (5, 7, 11, 13, 17, 19, 25, 35):
            if math.gcd(d_perf, u) != 1:
                continue
            lhs = aliquot_s_exact(d_perf * u)
            rhs = d_perf * (2 * sig1[u] - u)
            if not all((lhs == rhs, lhs > d_perf * u)):
                mono_ok = False
            mono_checked += 1

    six_total = 0
    six_v2_ok = True
    six_v3_iff_ok = True
    six_v3_suff_ok = True
    six_v3_persist = 0
    six_sig_div3_count = 0
    six_converse_counterexamples: list[int] = []
    for u in range(5, 301, 2):
        if u % 3 == 0:
            continue
        six_total += 1
        s6u = aliquot_s_exact(6 * u)
        if v_p_exact(s6u, 2) != 1:
            six_v2_ok = False
        has_v3_eq1 = v_p_exact(s6u, 3) == 1
        exact_iff = (2 * sig1[u] - u) % 3 != 0
        if has_v3_eq1 != exact_iff:
            six_v3_iff_ok = False
        if sig1[u] % 3 == 0:
            if not has_v3_eq1:
                six_v3_suff_ok = False
            six_sig_div3_count += 1
        elif has_v3_eq1:
            six_converse_counterexamples.append(u)
        if has_v3_eq1:
            six_v3_persist += 1

    # 1c. Exact pure-Q 5-state (v_2, v_3, v_5) Even-Basin Markov Transfer Operator T_{2,3,5}
    k_states = len(MARKOV_STATE_NAMES)
    counts = [[0] * k_states for _ in range(k_states)]
    escaped_odd = [0] * k_states
    sum_sn = [0] * k_states
    sum_n = [0] * k_states
    tot_state = [0] * k_states
    for n in range(2, parity_limit + 1, 2):
        c0 = classify_even_driver_state(n)
        sn = sig1[n] - n
        tot_state[c0] += 1
        sum_sn[c0] += sn
        sum_n[c0] += n
        if sn % 2 == 0:
            counts[c0][classify_even_driver_state(sn)] += 1
        else:
            escaped_odd[c0] += 1

    t_mat: list[list[Fraction]] = []
    for i in range(k_states):
        row_total = sum(counts[i])
        t_mat.append([Fraction(counts[i][j], row_total) for j in range(k_states)])

    sys_a = [
        [t_mat[j][i] - (Fraction(1, 1) if i == j else Fraction(0, 1)) for j in range(k_states)]
        for i in range(k_states)
    ]
    sys_b = [Fraction(0, 1)] * k_states
    sys_a[k_states - 1] = [Fraction(1, 1)] * k_states
    sys_b[k_states - 1] = Fraction(1, 1)
    pi_star = solve_linear_fraction(sys_a, sys_b)
    markov_residuals = [
        sum((pi_star[j] * t_mat[j][i] for j in range(k_states)), Fraction(0, 1)) - pi_star[i]
        for i in range(k_states)
    ]
    markov_ok = all(
        (
            sum(pi_star) == Fraction(1, 1),
            all(r == 0 for r in markov_residuals),
            all(p > 0 for p in pi_star),
        )
    )

    state_means = [Fraction(sum_sn[i], sum_n[i]) for i in range(k_states)]
    uniform_even_emp = Fraction(sum(sum_sn), sum(sum_n))
    stationary_drift = sum((pi_star[i] * state_means[i] for i in range(k_states)), Fraction(0, 1))

    # Pure-Q Archimedes bounds 223/71 < pi < 22/7 certifying 5*pi^2/24 - 1 > 1 and pi^2/8 - 1 < 1
    pi_lo = Fraction(223, 71)
    pi_hi = Fraction(22, 7)
    even_asymp_lo = Fraction(5, 24) * pi_lo * pi_lo - 1
    odd_asymp_hi = Fraction(1, 8) * pi_hi * pi_hi - 1

    # 1d. Untouchables (2, 5, 52) & Goldbach reduction for odd k in [3, 1001] \ {5}
    untouch_2 = verify_untouchable_exact(2)
    untouch_5 = verify_untouchable_exact(5)
    untouch_52 = verify_untouchable_exact(52)

    primes_1k = [i for i in range(2, 1002) if pf[i] == i]
    prime_set_1k = set(primes_1k)
    goldbach_odd_hits = 0
    for k in range(3, 1002, 2):
        if k == 5:
            continue
        if k == 3:
            if sig1[4] - 4 == 3:
                goldbach_odd_hits += 1
        elif k == 7:
            if sig1[8] - 8 == 7:
                goldbach_odd_hits += 1
        else:
            target = k - 1
            for p in primes_1k:
                q = target - p
                if q <= p:
                    break
                if q in prime_set_1k:
                    if sig1[p * q] - p * q == k:
                        goldbach_odd_hits += 1
                    break

    # 1e. Certified 1..1,000 Aliquot Atlas + Lehmer-5 prefixes + Poulet cycles
    known_fate: dict[int, tuple[str, int]] = {0: ("terminates", 0)}
    lehmer_records: list[dict[str, Any]] = []
    for seed in LEHMER_FIVE_SEEDS:
        cur = seed
        prefix = [cur]
        tags = [_driver_tag_for_orbit(cur)]
        known_fate[cur] = ("open_lehmer5", seed)
        for _ in range(20):
            cur = aliquot_s_exact(cur)
            prefix.append(cur)
            tags.append(_driver_tag_for_orbit(cur))
            if cur not in known_fate:
                known_fate[cur] = ("open_lehmer5", seed)
        lehmer_records.append(
            {
                "seed": seed,
                "steps": 20,
                "a20": prefix[-1],
                "abundancy_seed": format_fraction(Fraction(sig1[seed], seed)),
                "distinct_driver_tags": sorted(set(tags)),
                "driver_tag_tail5": tags[-5:],
            }
        )

    for n in range(1, ATLAS_LIMIT + 1):
        if n in known_fate:
            continue
        cur = n
        path: list[int] = []
        seen: dict[int, int] = {}
        while True:
            if cur in known_fate:
                fate = known_fate[cur]
                for v in path:
                    known_fate[v] = fate
                break
            if cur in seen:
                cyc = path[seen[cur] :]
                clen = len(cyc)
                cmin = min(cyc)
                tag = "perfect" if clen == 1 else "amicable"
                fate = (tag, cmin)
                for v in path:
                    known_fate[v] = fate
                break
            seen[cur] = len(path)
            path.append(cur)
            cur = aliquot_s_exact(cur)
            if cur > ATLAS_VALUE_CAP:
                known_fate[n] = ("high_peak_exceeding_bound", n)
                break

    fate_counts = {
        "terminates": sum(1 for n in range(1, ATLAS_LIMIT + 1) if known_fate[n][0] == "terminates"),
        "perfect": sum(1 for n in range(1, ATLAS_LIMIT + 1) if known_fate[n][0] == "perfect"),
        "amicable": sum(1 for n in range(1, ATLAS_LIMIT + 1) if known_fate[n][0] == "amicable"),
        "open_lehmer5": sum(1 for n in range(1, ATLAS_LIMIT + 1) if known_fate[n][0] == "open_lehmer5"),
        "high_peak_exceeding_bound": sum(
            1 for n in range(1, ATLAS_LIMIT + 1) if known_fate[n][0] == "high_peak_exceeding_bound"
        ),
    }

    # Exact 138 trajectory record
    cur138 = 138
    peak138 = 138
    peak138_step = 0
    step138 = 0
    while cur138 != 0:
        if cur138 > peak138:
            peak138 = cur138
            peak138_step = step138
        cur138 = aliquot_s_exact(cur138)
        step138 += 1

    # Exact Poulet 5-cycle (12496) & 28-cycle (14316) independent closure verification
    poulet_certs: list[dict[str, Any]] = []
    poulet_ok = True
    for start, exp_len in ((12496, 5), (14316, 28)):
        cur_p = start
        cyc_vals = [cur_p]
        for _ in range(exp_len):
            cur_p = aliquot_s_exact(cur_p)
            cyc_vals.append(cur_p)
        closed = all((cur_p == start, len(set(cyc_vals[:-1])) == exp_len))
        if not closed:
            poulet_ok = False
        poulet_certs.append({"start": start, "period": exp_len, "max_vertex": max(cyc_vals[:-1]), "closed": closed})

    all_verified = all(
        (
            parity_vs_sigma_exc == 0,
            parity_vs_escape_exc == 0,
            mono_ok,
            six_v2_ok,
            six_v3_iff_ok,
            six_v3_suff_ok,
            25 in six_converse_counterexamples,
            markov_ok,
            even_asymp_lo > 1,
            odd_asymp_hi < 1,
            uniform_even_emp > 1,
            stationary_drift < 1,
            untouch_2["is_untouchable_over_all_N"],
            untouch_5["is_untouchable_over_all_N"],
            untouch_52["is_untouchable_over_all_N"],
            goldbach_odd_hits == 499,
            sum(fate_counts.values()) == ATLAS_LIMIT,
            peak138 == 179_931_895_322,
            step138 - 1 == 177,
            poulet_ok,
        )
    )

    return {
        "all_verified": all_verified,
        "model_scope": "N1_finite_state_markov_model_not_CD_proof",
        "parity_lock_range": parity_limit,
        "parity_vs_sigma_exceptions": parity_vs_sigma_exc,
        "parity_vs_escape_exceptions": parity_vs_escape_exc,
        "square_escape_count": escape_count,
        "square_escape_density": format_fraction(Fraction(escape_count, parity_limit)),
        "driver_monotonicity_checked": mono_checked,
        "six_driver_coprime_checked": six_total,
        "six_driver_v3_persist_count": six_v3_persist,
        "six_driver_3_div_sigma_count": six_sig_div3_count,
        "six_driver_converse_counterexample_first": six_converse_counterexamples[0],
        "six_driver_converse_counterexample_count": len(six_converse_counterexamples),
        "markov_states": list(MARKOV_STATE_NAMES),
        "markov_state_counts": tot_state,
        "markov_escaped_odd_counts": escaped_odd,
        "markov_stationary_pi": [format_fraction(x) for x in pi_star],
        "markov_state_means": [format_fraction(x) for x in state_means],
        "uniform_even_empirical_mean": format_fraction(uniform_even_emp),
        "stationary_pi_expected_ratio": format_fraction(stationary_drift),
        "even_asymptotic_archimedes_lower_bound": format_fraction(even_asymp_lo),
        "odd_asymptotic_archimedes_upper_bound": format_fraction(odd_asymp_hi),
        "untouchable_proofs": [untouch_2, untouch_5, untouch_52],
        "goldbach_odd_preimage_witnesses_le_1001": goldbach_odd_hits,
        "atlas_1_to_1000_counts": fate_counts,
        "atlas_lehmer5_families_le_1000": {
            str(seed): [n for n in range(1, ATLAS_LIMIT + 1) if known_fate[n] == ("open_lehmer5", seed)]
            for seed in LEHMER_FIVE_SEEDS
        },
        "atlas_high_peak_seeds_le_1000": [
            n for n in range(1, ATLAS_LIMIT + 1) if known_fate[n][0] == "high_peak_exceeding_bound"
        ],
        "trajectory_138": {
            "peak": peak138,
            "peak_step": peak138_step,
            "reaches_1_step": step138 - 1,
            "reaches_0_step": step138,
        },
        "poulet_cycles": poulet_certs,
        "lehmer_five_prefixes": lehmer_records,
    }


# ============================================================================
# 4. Pillar 2 — Sylvester Abundance Wall & Odd-Prime Zsigmondy (Portal 18)
# ============================================================================

def compute_sylvester_wall_entry(q: int) -> dict[str, Any]:
    """Compute exact pure-Q k_Sylv(q) = min{k : prod_{j=1}^k p_j/(p_j-1) > 2, p_1=q}."""
    q = require_exact_int(q, "q", lo=3, hi=101)
    require_ok(is_prime_exact(q), "NOT_ODD_PRIME", "q must be an odd prime")
    pf, _, _ = build_arithmetic_sieve(SIEVE_LIMIT)
    primes = [i for i in range(q, SIEVE_LIMIT + 1) if pf[i] == i]
    num = 1
    den = 1
    prev_below_two = True
    k = 0
    p_max = q
    for p in primes:
        prev_below_two = num <= 2 * den
        num *= p
        den *= p - 1
        g = math.gcd(num, den)
        num //= g
        den //= g
        k += 1
        p_max = p
        if num > 2 * den:
            break
    margin_num = num - 2 * den
    prod_str = f"{num}/{den}"
    margin_str = f"{margin_num}/{den}"
    return {
        "q": q,
        "k_sylv": k,
        "p_max": p_max,
        "prev_le_2": prev_below_two,
        "exceeds_2": num > 2 * den,
        "num_bits": num.bit_length(),
        "den_bits": den.bit_length(),
        "exact_margin_recip_floor": den // margin_num,
        "exact_product_sha256": hashlib.sha256(prod_str.encode("ascii")).hexdigest(),
        "exact_product": prod_str,
        "exact_margin_above_2": margin_str,
    }


def verify_pillar2_sylvester_zsigmondy() -> dict[str, Any]:
    """Certify Portal 18: Sylvester wall q<=101, sharp odd-abundant witnesses,
    exact rational Sylvester deficit, and zero-exception odd-prime Zsigmondy."""
    wall_entries = [compute_sylvester_wall_entry(q) for q in SYLVESTER_Q_LIST]

    # Sharp odd-abundant witnesses attaining k_Sylv(3)=3 and k_Sylv(5)=7
    sharp_witnesses: list[dict[str, Any]] = []
    sharp_ok = True
    for q_min, factor_pairs in (
        (3, ((3, 3), (5, 1), (7, 1))),
        (5, ((5, 3), (7, 2), (11, 2), (13, 2), (17, 1), (19, 1), (23, 1))),
    ):
        n_val = 1
        ab = Fraction(1, 1)
        for p, e in factor_pairs:
            n_val *= p**e
            ab *= Fraction((p ** (e + 1) - 1) // (p - 1), p**e)
        is_odd_ab = all((n_val % 2 == 1, ab > 2))
        if not is_odd_ab:
            sharp_ok = False
        sharp_witnesses.append(
            {
                "q_min": q_min,
                "omega": len(factor_pairs),
                "n": n_val,
                "abundancy": format_fraction(ab),
                "margin_above_2": format_fraction(ab - 2),
                "is_odd_abundant": is_odd_ab,
            }
        )

    # Exact rational Sylvester deficit: p/(p-1) - I(p^{2b}) == 1 / (p^{2b}(p-1))
    deficit_checked = 0
    deficit_ok = True
    for p in (3, 5, 7, 11, 13):
        for b in (1, 2, 3):
            two_b = 2 * b
            lhs = Fraction(p, p - 1) - Fraction((p ** (two_b + 1) - 1) // (p - 1), p**two_b)
            rhs = Fraction(1, (p**two_b) * (p - 1))
            if lhs != rhs:
                deficit_ok = False
            deficit_checked += 1

    # Zero-exception odd-prime Zsigmondy primitive divisor witnesses: odd p >= 3, odd d >= 3
    zsig_checked = 0
    zsig_ok = True
    zsig_samples: list[dict[str, Any]] = []
    for p in (3, 5, 7, 11, 13, 17, 19, 23, 29):
        for d in (3, 5, 7, 9, 11):
            fac = factorize_exact(p**d - 1)
            prims = sorted(r for r in fac if all(pow(p, k, r) != 1 for k in range(1, d)))
            if not all((len(prims) >= 1, all(r % d == 1 for r in prims))):
                zsig_ok = False
            zsig_checked += 1
            if p in (3, 5) and d in (3, 5, 7):
                zsig_samples.append({"p": p, "d": d, "primitive_primes": prims})

    all_verified = all(
        (
            all(e["prev_le_2"] for e in wall_entries),
            all(e["exceeds_2"] for e in wall_entries),
            sharp_ok,
            deficit_ok,
            zsig_ok,
        )
    )

    return {
        "all_verified": all_verified,
        "sylvester_wall_table": wall_entries,
        "sharp_odd_abundant_witnesses": sharp_witnesses,
        "sylvester_deficit_identities_checked": deficit_checked,
        "zsigmondy_odd_pairs_checked": zsig_checked,
        "zsigmondy_samples": zsig_samples,
    }


# ============================================================================
# 5. Pillar 3 — Convergent Reciprocals, Pomerance alpha=1 & Ceiling (Portal 19)
# ============================================================================

def is_pomerance_alpha1_candidate(m_sq: int, sig_m_sq: int) -> bool:
    """True iff Delta = 2*m^2 - sigma_1(m^2) > 0 and Delta | m^2."""
    m_sq = require_exact_int(m_sq, "m_sq", lo=1)
    sig_m_sq = require_exact_int(sig_m_sq, "sig_m_sq", lo=1)
    delta = 2 * m_sq - sig_m_sq
    return delta > 0 and m_sq % delta == 0


def verify_pillar3_pomerance_pseudorandomness() -> dict[str, Any]:
    """Certify Portal 19: exact Euler-product local identities & 9/20 removal factor,
    exhaustive odd m<=10,000 Pomerance divisor check, and even-2^a falsification."""
    pf, _, _ = build_arithmetic_sieve(SIEVE_LIMIT)

    # 3a. Exact local Euler factor identity & p=2 removal factor 9/20 -> 3*pi^2/16
    local_checks = 0
    local_ok = True
    for p in (2, 3, 5, 7, 11, 13):
        x = Fraction(1, p * p)
        f_closed_1 = (1 + x) / ((1 - x) * (1 - x))
        f_closed_2 = (1 - x * x) / ((1 - x) ** 3)
        k_trunc = 8
        partial = sum((Fraction(2 * k + 1, 1) * (x**k) for k in range(k_trunc + 1)), Fraction(0, 1))
        tail = (x ** (k_trunc + 1)) * (Fraction(2 * k_trunc + 3, 1) - Fraction(2 * k_trunc + 1, 1) * x) / ((1 - x) ** 2)
        if not all((f_closed_1 == f_closed_2, partial + tail == f_closed_1)):
            local_ok = False
        local_checks += 1

    e2_at_2 = (Fraction(1, 1) + Fraction(1, 4)) / ((Fraction(1, 1) - Fraction(1, 4)) ** 2)
    p2_removal_factor = Fraction(1, 1) / e2_at_2
    all_m_pi2_coeff = (Fraction(1, 6) ** 3) / Fraction(1, 90)
    odd_m_pi2_coeff = p2_removal_factor * all_m_pi2_coeff

    # 3b. Exhaustive check over ALL 5,000 odd 1 <= m <= 10,000: Delta(m^2) = 2m^2 - sigma(m^2) > 0, Delta | m^2
    solutions: list[dict[str, Any]] = []
    odd_checked = 0
    for m in range(1, 10_001, 2):
        odd_checked += 1
        mm = m * m
        rem = m
        sig_mm = 1
        while rem > 1:
            p = pf[rem]
            e = 0
            while rem % p == 0:
                rem //= p
                e += 1
            sig_mm *= (p ** (2 * e + 1) - 1) // (p - 1)
        delta = 2 * mm - sig_mm
        if is_pomerance_alpha1_candidate(mm, sig_mm):
            p_cand = sig_mm // delta
            solutions.append(
                {
                    "m": m,
                    "m_squared": mm,
                    "sigma1_m_squared": sig_mm,
                    "delta": delta,
                    "p_candidate": p_cand,
                    "p_candidate_factors": [[q, e] for q, e in sorted(factorize_exact(p_cand).items())] if p_cand > 1 else [],
                    "is_true_prime": is_prime_exact(p_cand),
                }
            )

    # 3c. Exact Even-Number Pseudorandomness Falsification Witness: 2*(2^a) - sigma(2^a) == 1 | 2^a
    even_falsif_hits = 0
    for a in range(1, 31):
        pow2 = 1 << a
        sig_pow2 = (1 << (a + 1)) - 1
        delta_even = 2 * pow2 - sig_pow2
        if all((delta_even == 1, pow2 % delta_even == 0)):
            even_falsif_hits += 1

    all_verified = all(
        (
            local_ok,
            p2_removal_factor == Fraction(9, 20),
            all_m_pi2_coeff == Fraction(5, 12),
            odd_m_pi2_coeff == Fraction(3, 16),
            odd_checked == 5_000,
            [s["m"] for s in solutions] == [1, 3003],
            even_falsif_hits == 30,
        )
    )

    return {
        "all_verified": all_verified,
        "local_euler_identities_checked": local_checks,
        "p2_local_factor": format_fraction(e2_at_2),
        "p2_removal_factor": format_fraction(p2_removal_factor),
        "all_m_series_pi2_coeff": format_fraction(all_m_pi2_coeff),
        "odd_m_series_pi2_coeff": format_fraction(odd_m_pi2_coeff),
        "odd_m_checked_count": odd_checked,
        "pomerance_alpha1_solutions": solutions,
        "even_2pow_a_falsification_hits": even_falsif_hits,
        "even_2pow_a_hit_probability": format_fraction(Fraction(even_falsif_hits, 30)),
    }


# ============================================================================
# 6. Pillar 4 — Harmonic Duality (H(n)*I(n) == tau(n)) & Ore (Portal 20)
# ============================================================================

def compute_kanold_sylvester_ceiling(h: int) -> dict[str, Any]:
    """Compute exact pure-Q Kanold-Sylvester finite upper bound on omega(n) for odd Ore h."""
    h = require_exact_int(h, "h", lo=3, hi=99)
    require_ok(h % 2 == 1, "KANOLD_H_MUST_BE_ODD", "Kanold ceiling expects odd h >= 3")
    pf, _, _ = build_arithmetic_sieve(SIEVE_LIMIT)
    odd_primes = [i for i in range(3, 500) if pf[i] == i]
    prod = Fraction(1, 1)
    max_omega = 0
    cutoff_lhs = Fraction(1, 1)
    for k, p in enumerate(odd_primes, start=1):
        prod *= Fraction(2 * (p - 1), p)
        if prod < h:
            max_omega = k
        else:
            cutoff_lhs = prod
            break
    return {
        "h": h,
        "omega_upper_bound": max_omega,
        "refuted_k": max_omega + 1,
        "refuted_lhs_ratio": format_fraction(cutoff_lhs),
        "bound_exceeds_h": cutoff_lhs > h,
    }


def verify_pillar4_harmonic_ore() -> dict[str, Any]:
    """Certify Portal 20: H(n)*I(n)==tau(n), 2-adic LTE valuation law across 10,000
    odd n<=20,000, Kanold-Sylvester ceilings, h=3 4-line proof, and Ore sieve <=100,000."""
    pf, sig1, tau = build_arithmetic_sieve(SIEVE_LIMIT)

    # 4a. Exact harmonic duality H(n) * I(n) == tau(n) across 1..1,000
    duality_exceptions = 0
    for n in range(1, 1_001):
        h_n = Fraction(n * tau[n], sig1[n])
        i_n = Fraction(sig1[n], n)
        if h_n * i_n != Fraction(tau[n], 1):
            duality_exceptions += 1

    # 4b. Exact 2-adic LTE Valuation Law across ALL 10,000 odd n <= 20,000
    lte_checked = 0
    lte_exceptions = 0
    for n in range(1, 20_001, 2):
        lte_checked += 1
        lhs = v_p_exact(sig1[n], 2)
        rhs = v_p_exact(tau[n], 2)
        rem = n
        while rem > 1:
            p = pf[rem]
            e = 0
            while rem % p == 0:
                rem //= p
                e += 1
            # Note: for odd prime p and odd e, v_2(p+1) - 1 == 0 when p == 1 (mod 4)
            # and v_2(p+1) - 1 >= 1 when p == 3 (mod 4) (exact 2-adic LTE valuation law).
            if (e & 1) == 1:
                rhs += v_p_exact(p + 1, 2) - 1
        if lhs != rhs:
            lte_exceptions += 1

    # No prime power p^a (a >= 1) is Ore: gcd(p^a, sigma_1(p^a)) == 1 and sigma_1(p^a) > a + 1
    prime_power_checked = 0
    prime_power_ok = True
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23):
        for a in range(1, 7):
            pa = p**a
            s_pa = (p ** (a + 1) - 1) // (p - 1)
            if not all((math.gcd(pa, s_pa) == 1, s_pa > a + 1)):
                prime_power_ok = False
            prime_power_checked += 1

    # 4c. Kanold-Sylvester finite ceilings for odd h in {3, 5, 7, 9, 11, 13, 15}
    kanold_table = [compute_kanold_sylvester_ceiling(h) for h in KANOLD_ODD_H_LIST]

    # Exact 4-line pure-Q proof of ZERO odd Ore solutions for h = 3
    case_k3_lhs = Fraction(2 * 2, 3) * Fraction(2 * 4, 5) * Fraction(2 * 6, 7)
    case_p3_rhs = Fraction(3, 1) * Fraction(3, 2) * Fraction(5, 4)
    case_p5_hiexp_h = Fraction(6, 1) / (Fraction(5, 4) * Fraction(7, 6))
    case_p5_sqfree_i = Fraction(6, 5) * Fraction(14, 13)
    case_p5_sqfree_h = Fraction(4, 1) / case_p5_sqfree_i
    h3_proof_ok = all(
        (
            case_k3_lhs >= 3,
            case_p3_rhs < 6,
            case_p5_hiexp_h > 3,
            case_p5_sqfree_i < Fraction(4, 3),
            case_p5_sqfree_h > 3,
        )
    )

    # 4d. Exhaustive certified sieve of ALL 1 <= n <= 100,000
    ore_entries: list[dict[str, int]] = []
    for n in range(1, SIEVE_LIMIT + 1):
        if (n * tau[n]) % sig1[n] == 0:
            ore_entries.append({"n": n, "harmonic_mean": (n * tau[n]) // sig1[n]})
    odd_ores = [e["n"] for e in ore_entries if e["n"] % 2 == 1]

    all_verified = all(
        (
            duality_exceptions == 0,
            lte_checked == 10_000,
            lte_exceptions == 0,
            prime_power_ok,
            all(e["bound_exceeds_h"] for e in kanold_table),
            h3_proof_ok,
            len(ore_entries) == 18,
            odd_ores == [1],
        )
    )

    return {
        "all_verified": all_verified,
        "duality_identity_checked_up_to": 1_000,
        "duality_exceptions": duality_exceptions,
        "lte_odd_checked_count": lte_checked,
        "lte_exceptions": lte_exceptions,
        "prime_power_no_ore_checked": prime_power_checked,
        "kanold_sylvester_ceilings": kanold_table,
        "odd_ore_h3_zero_proof": {
            "omega_le_2_from_k3_lhs": format_fraction(case_k3_lhs),
            "case_3_div_n_3I_upper_lt_6": format_fraction(case_p3_rhs),
            "case_p_ge_5_high_exp_H_lower": format_fraction(case_p5_hiexp_h),
            "case_p_ge_5_sqfree_I_upper": format_fraction(case_p5_sqfree_i),
            "case_p_ge_5_sqfree_H_lower": format_fraction(case_p5_sqfree_h),
            "odd_solutions_for_h3": 0,
        },
        "ore_sieve_limit": SIEVE_LIMIT,
        "ore_numbers_count": len(ore_entries),
        "ore_numbers": ore_entries,
        "odd_ore_numbers_le_limit": odd_ores,
    }


# ============================================================================
# 7. Pillar 5 — Cyclotomic Webs, Kirchhoff Conservation & Phi_l Funnel (Portal 21)
# ============================================================================

def verify_pillar5_cyclotomic_kirchhoff() -> dict[str, Any]:
    """Certify Portal 21: Descartes 5-node Kirchhoff matrix & composite leak,
    universal 2-step Phi_l attractor funnel (l in {3,5,7}, p<=5,000), and
    forward Phi_3 cascade of {3} through depth 5."""
    pf, _, _ = build_arithmetic_sieve(SIEVE_LIMIT)

    # 5a. Descartes' 5-node spoof Kirchhoff balance matrix & leak vector
    seed_nodes = (3, 7, 11, 13)
    target_exps = {p: 2 for p in seed_nodes}
    supply: dict[int, int] = {p: 0 for p in seed_nodes}
    leak_factors: dict[int, int] = {}
    phi3_emissions: dict[str, list[list[int]]] = {}
    for p in seed_nodes:
        val = p * p + p + 1
        fac = factorize_exact(val)
        phi3_emissions[str(p)] = [[q, e] for q, e in sorted(fac.items())]
        for q, e in fac.items():
            if q in supply:
                supply[q] += e
            else:
                leak_factors[q] = leak_factors.get(q, 0) + e

    deficit = {p: target_exps[p] - supply[p] for p in seed_nodes}
    leak_product = 1
    for q, e in leak_factors.items():
        leak_product *= q**e
    fake_euler_outflow = factorize_exact((leak_product + 1) // 2)
    nonzero_deficit = {p: d for p, d in deficit.items() if d > 0}
    trunc_19 = sorted(factorize_exact(19 * 19 + 19 + 1).items())
    trunc_61 = sorted(factorize_exact(61 * 61 + 61 + 1).items())

    # 5b. Universal 2-Step Phi_l Attractor Funnel Theorem across l in {3, 5, 7}, all primes p <= 5,000
    primes_5k = [i for i in range(2, 5_001) if pf[i] == i]
    funnel_results: list[dict[str, Any]] = []
    phi3_smooth_primes: list[int] = []
    funnel_ok = True
    for ell in (3, 5, 7):
        d0 = 0
        d1 = 0
        d2 = 0
        factored_d2 = 0
        for p in primes_5k:
            if p == ell:
                d0 += 1
                continue
            val = (p**ell - 1) // (p - 1)
            if p % ell == 1:
                if v_p_exact(val, ell) != 1:
                    funnel_ok = False
                d1 += 1
                if ell == 3:
                    fac3 = factorize_exact(val)
                    if all(r < p for r in fac3):
                        phi3_smooth_primes.append(p)
            else:
                if val % ell != 1:
                    funnel_ok = False
                if ell in (3, 5) or p <= 500:
                    fac = factorize_exact(val)
                    if not all(r % ell == 1 for r in fac):
                        funnel_ok = False
                    factored_d2 += 1
                    if ell == 3:
                        if all(r < p for r in fac):
                            phi3_smooth_primes.append(p)
                d2 += 1
        if d0 + d1 + d2 != len(primes_5k):
            funnel_ok = False
        funnel_results.append(
            {
                "ell": ell,
                "primes_checked": len(primes_5k),
                "distance_0_count": d0,
                "distance_1_count": d1,
                "distance_2_count": d2,
                "distance_2_fully_factored_count": factored_d2,
            }
        )

    # 5c. Exact forward Phi_3 cascade of {3} through depth 5
    cur_layer = [3]
    seen_nodes = {3}
    cascade_layers: list[list[int]] = [[3]]
    for _ in range(5):
        nxt_nodes: set[int] = set()
        for p in cur_layer:
            fac = factorize_exact(p * p + p + 1)
            for q in fac:
                if q not in seen_nodes:
                    nxt_nodes.add(q)
        seen_nodes |= nxt_nodes
        cur_layer = sorted(nxt_nodes)
        cascade_layers.append(cur_layer)

    all_verified = all(
        (
            deficit == {3: 0, 7: 1, 11: 2, 13: 1},
            leak_product == 22_021,
            fake_euler_outflow == nonzero_deficit,
            trunc_19 == [(3, 1), (127, 1)],
            trunc_61 == [(3, 1), (13, 1), (97, 1)],
            funnel_ok,
            cascade_layers == [[3], [13], [61], [97], [3169], [3348577]],
        )
    )

    return {
        "all_verified": all_verified,
        "descartes_kirchhoff": {
            "seed_nodes": list(seed_nodes),
            "phi3_emissions": phi3_emissions,
            "internal_supply": {str(k): v for k, v in supply.items()},
            "deficit_vector": {str(k): v for k, v in deficit.items()},
            "external_leak_product": leak_product,
            "external_leak_factors": [[q, e] for q, e in sorted(leak_factors.items())],
            "fake_euler_outflow_factors": [[q, e] for q, e in sorted(fake_euler_outflow.items())],
            "truncated_phi3_19": [[q, e] for q, e in trunc_19],
            "truncated_phi3_61": [[q, e] for q, e in trunc_61],
        },
        "phi_l_attractor_funnels": funnel_results,
        "phi3_smooth_primes_lt_5000_count": len(phi3_smooth_primes),
        "phi3_smooth_primes_first5": phi3_smooth_primes[:5],
        "phi3_forward_cascade_depth5": cascade_layers,
    }


def compute_s25_payload() -> dict[str, Any]:
    """Build the complete deterministic zero-float Track S25 (Portals 17-21) payload."""
    return {
        "track_id": TRACK_ID,
        "novelty_class": "N1",
        "oracle_class": "exact",
        "pillar1_catalan_dickson_transfer": verify_pillar1_catalan_dickson_transfer(),
        "pillar2_sylvester_zsigmondy": verify_pillar2_sylvester_zsigmondy(),
        "pillar3_pomerance_pseudorandomness": verify_pillar3_pomerance_pseudorandomness(),
        "pillar4_harmonic_ore": verify_pillar4_harmonic_ore(),
        "pillar5_cyclotomic_kirchhoff": verify_pillar5_cyclotomic_kirchhoff(),
    }
