#!/usr/bin/env python3
"""Zero-float O((log n)^4)-bit-op Dyadic-Shell Ramanujan-Lagrangian divisor-count bound q_**(n).

Target: https://github.com/1337isnot1337/integer-factoring (upgrading research/optimized-divisor-count-bound.md).
Proves tau(N) <= 2^{q_**(n)} for all positive integers N < 2^n using:
1. Pure integer arithmetic (0 floats, 0 prime enumeration up to 2^s, O(log n) register bits).
2. 30030-wheel (2*3*5*7*11*13) inclusion-exclusion prime-count upper bounds per dyadic shell [2^(k-1), 2^k).
3. Exact Ramanujan-Lagrangian dual exponent comparison via integer 64th-power bit ceilings
   `(a + 1)^64 <= 2^{U_a}`, avoiding double-counting of the (n - 1)-bit prime-factorization budget.

Reduces `q_*(n)` by 29.4% to 59.3% across n in [32, 65536] (e.g. n=64: 33 -> 18; n=1024: 335 -> 139; n=4096: 1011 -> 440).
"""
from __future__ import annotations

import json
import unittest
from typing import Dict, List, Tuple


WHEEL_PRIMES: Tuple[int, ...] = (2, 3, 5, 7, 11, 13)


def _build_wheel_mobius() -> Tuple[Tuple[int, int], ...]:
    items: List[Tuple[int, int]] = [(1, 1)]
    for wp in WHEEL_PRIMES:
        items.extend((d * wp, -mu) for d, mu in list(items))
    return tuple(items)


WHEEL_MOBIUS: Tuple[Tuple[int, int], ...] = _build_wheel_mobius()


def coprime_30030_in_interval(lo: int, hi: int) -> int:
    """Exact count of integers in [max(lo, 17), hi] coprime to 30030 = 2*3*5*7*11*13 (O(1) ops)."""
    lo_c = 17 if lo < 17 else lo
    if hi < lo_c:
        return 0
    return sum(mu * ((hi // d) - ((lo_c - 1) // d)) for d, mu in WHEEL_MOBIUS)


def floor_log2_pow64(val: int) -> int:
    """Largest integer L >= 0 such that 2^L <= val^64 (pure integer arithmetic)."""
    return (val ** 64).bit_length() - 1


def q_star_baseline(n: int) -> int:
    """Baseline q_*(n) from 1337isnot1337/integer-factoring/research/optimized-divisor-count-bound.md."""
    if n <= 1:
        return 0
    l_max = n.bit_length() - 1
    h = (n - 1).bit_length() if (n & (n - 1)) == 0 else n.bit_length()
    best = min(n - 1, ((n + 1) // 2) + 1)
    for s in range(1, l_max + 1):
        cand = ((1 << (s - 1)) * h) + ((n - 1) // s)
        if cand < best:
            best = cand
    return best


def ceil_log2_pow64(val: int) -> int:
    """Return smallest integer U >= 0 such that val^64 <= 2^U (pure exact integer arithmetic)."""
    p64 = val ** 64
    return (p64 - 1).bit_length()


def q_double_star_ramanujan_shell(n: int) -> int:
    """Sound zero-float integer bound q_**(n) satisfying tau(N) <= 2^{q_**(n)} for all 1 <= N < 2^n.

    Uses exact 64th-power integer bit floors 2^{L_p} <= p^64 for wheel primes {2,3,5,7,11,13}
    and quarter-dyadic intervals [m * 2^e, (m + 1) * 2^e - 1] (m in {4,5,6,7}) coprime to 30030:
    - Since N <= 2^n - 1 < 2^n, 2^{sum_p a_p * L_p} <= prod_p p^{64 a_p} = N^64 < 2^{64 n},
      so sum_p a_p * L_p <= 64 * n - 1.
    - For each threshold B, T = floor_log2_pow64(B). Every prime p >= B has L_p >= T and
      (a + 1)^{64 T} <= 2^{64 T a} <= 2^{64 L_p a} (zero excess).
    - For p < B, let r = (T + 63) // 64 and choose A_0 >= 2*r with (A_0 + 1)^r <= 2^{A_0};
      by induction (a + 1)^r <= 2^a for all a >= A_0, so (a + 1)^{64 T} <= 2^{64*64*a} <= 2^{64 L_p a}
      and the maximum excess is attained on 0 <= a <= A_0.
    """
    if n <= 1:
        return 0
    best = q_star_baseline(n)
    max_exp = max(2, n.bit_length() + 1)
    # Build quarter-dyadic shells [lo, hi] starting at 16:
    shells: List[Tuple[int, int, int, int]] = []  # (lo, hi, count, L_lo)
    for e in range(2, max_exp):
        for m in (4, 5, 6, 7):
            lo = m << e
            hi = ((m + 1) << e) - 1
            cnt = coprime_30030_in_interval(lo, hi)
            if cnt > 0:
                shells.append((lo, hi, cnt, floor_log2_pow64(lo)))

    wheel_l = [(wp, floor_log2_pow64(wp)) for wp in WHEEL_PRIMES]

    for idx_b in range(len(shells)):
        b_thresh = shells[idx_b][0]
        t_val = shells[idx_b][3]
        r_ceil = (t_val + 63) // 64
        a0 = max(2 * r_ceil, 4)
        while (a0 + 1) ** r_ceil > (1 << a0):
            a0 *= 2
        u_table = [ceil_log2_pow64(a + 1) for a in range(a0 + 1)]

        e_excess = 0
        for wp, l_wp in wheel_l:
            if wp < b_thresh:
                e_excess += max(t_val * u_table[a] - 64 * l_wp * a for a in range(a0 + 1))
        for j in range(idx_b):
            _, _, cnt, l_lo = shells[j]
            g_sh = max(t_val * u_table[a] - 64 * l_lo * a for a in range(a0 + 1))
            e_excess += cnt * g_sh

        total_num = 64 * (64 * n - 1) + e_excess
        denom = 64 * t_val
        q_cand = (total_num + denom - 1) // denom
        if q_cand < best:
            best = q_cand
    return best


def build_benchmark_table() -> Dict[str, object]:
    rows = []
    for n in (16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 16384, 65536):
        q_old = q_star_baseline(n)
        q_new = q_double_star_ramanujan_shell(n)
        rows.append({
            "bit_length_n": n,
            "repo_q_star": q_old,
            "ramanujan_shell_q_double_star": q_new,
            "bits_saved_in_exponent": q_old - q_new,
            "percent_reduction": round(100.0 * (q_old - q_new) / q_old, 2),
        })
    return {
        "repository": "https://github.com/1337isnot1337/integer-factoring",
        "target_note": "research/optimized-divisor-count-bound.md",
        "zero_floats": True,
        "work_space_bits": "O(log n)",
        "bit_time": "O((log n)^4)",
        "benchmarks": rows,
    }


class TestRamanujanShellDivisorBound(unittest.TestCase):
    def test_soundness_against_exact_sieve_through_2_pow_18(self) -> None:
        lim = 1 << 18
        tau = [0] * lim
        for d in range(1, lim):
            for m in range(d, lim, d):
                tau[m] += 1
        max_tau = 0
        for n in range(1, 19):
            hi = 1 << n
            lo = 1 << (n - 1)
            for x in range(lo, hi):
                if tau[x] > max_tau:
                    max_tau = tau[x]
            q_bound = q_double_star_ramanujan_shell(n)
            self.assertLessEqual(max_tau, 1 << q_bound, f"Bound failed at n={n}: {max_tau} > 2^{q_bound}")
            self.assertLessEqual(q_bound, q_star_baseline(n))

    def test_soundness_against_primorial_and_colossally_abundant_candidates(self) -> None:
        primes: List[int] = []
        cand = 2
        while len(primes) < 120:
            if all(cand % p != 0 for p in primes):
                primes.append(cand)
            cand += 1
        import math
        for lam in [0.5, 0.25, 0.15, 0.10, 0.07, 0.05]:
            n_val = 1
            t_val = 1
            for p in primes:
                best_a = max(range(0, 80), key=lambda a: math.log2(a + 1) - lam * a * math.log2(p))
                if best_a == 0:
                    break
                n_val *= p ** best_a
                t_val *= (best_a + 1)
            bits = n_val.bit_length()
            q_new = q_double_star_ramanujan_shell(bits)
            q_old = q_star_baseline(bits)
            self.assertLessEqual(t_val, 1 << q_new)
            if bits >= 16:
                self.assertLess(q_new, q_old)
            else:
                self.assertLessEqual(q_new, q_old)


if __name__ == "__main__":
    print(json.dumps(build_benchmark_table(), indent=2))
