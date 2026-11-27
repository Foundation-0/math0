#!/usr/bin/env python3
"""Track S161 (EXP-Q44a) pure-Z/Q oracle: Independent audit of guoriyue/z123,
28.04x smaller elementary Affine Gabidulin family A_{4,q} in AG(4,q), and
38.14x smaller sub-million explicit 651-spread packing witness in AG(4,25).

Standard library only (int, fractions.Fraction, hashlib, itertools, json, math, os).
Zero floating-point literals or calls, zero bare asserts, zero RNG, zero network.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
from itertools import combinations, product
import json
from math import comb
import os

TRACK_ID = "S161"
QUEUE_ID = "EXP-Q44a"
SCHEMA_VERSION = "s161.q44a.z123_affine_zpoly.v1"
ORACLE_CLASS = "exact"
NOVELTY_CLASS = "N1"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.36.0"
LEAN_MODULE = "ZPolyCounterexample"
LEAN_FILE_NAME = "ZPolyCounterexample.lean"
CERT_FILE_NAME = "s161_z123_zpoly_certificate.json"
EXPECTED_LEAN_THEOREMS = 62

PINNED_LEAN_SHA256 = "44a0891fa188d392b350006a05c0211e33cd3c301f36b946532023e33508bb26"
PINNED_TOOLCHAIN_SHA256 = "582a63f8f9c5128067b688778c1051cf1464c3ca9d57b9325025c051c29b774a"
PINNED_LAKEFILE_SHA256 = "6e26024feb14dba53e43bc1303258b134809855e80e3973270bc0355c9248446"
PINNED_MANIFEST_SHA256 = "50e534cfda6b85b96c09dd488e7178d1fbabc2bf9c56307e697a9c8012f0457c"


class ZPolyError(ValueError):
    """Fail-closed typed error for Track S161."""

    def __init__(self, code: str, message: str) -> None:
        self.code = code
        self.message = message
        super().__init__(code + ": " + message)


def require_ok(cond: object, code: str, message: str) -> None:
    if cond is not True:
        raise ZPolyError(code, message)


def frac_str(val: Fraction) -> str:
    return str(val.numerator) + "/" + str(val.denominator)


def qbin(n: int, k: int, q: int) -> int:
    """Exact Gaussian binomial [n choose k]_q over Z."""
    require_ok(q >= 2, "QBIN_Q_MIN", "q must be at least 2")
    require_ok(k >= 0 and k <= n, "QBIN_BOUNDS", "k out of [0, n]")
    num = 1
    den = 1
    for i in range(k):
        num = num * (q ** (n - i) - 1)
        den = den * (q ** (i + 1) - 1)
    return num // den


# ---------------------------------------------------------------------------
# Pillar 1: Zero-shared-code EPW Kazhdan-Lusztig & Z-polynomial poset audit
# ---------------------------------------------------------------------------

def _poly_add_int(a: list[int], b: list[int]) -> list[int]:
    n = max(len(a), len(b))
    out = []
    for i in range(n):
        va = a[i] if i < len(a) else 0
        vb = b[i] if i < len(b) else 0
        out.append(va + vb)
    return out


def _poly_mul_int(a: list[int], b: list[int]) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = out[i + j] + x * y
    return out


def build_lattice_from_hyperplanes(n_elems: int, rank: int, hyperplanes: set[frozenset[int]]) -> dict[int, set[frozenset[int]]]:
    """Construct full flat lattice downward from hyperplanes and verify Oxley Prop 2.1.24 cover-partition axioms."""
    full_e = frozenset(range(n_elems))
    by_rank: dict[int, set[frozenset[int]]] = {r: set() for r in range(rank + 1)}
    by_rank[rank].add(full_e)
    by_rank[rank - 1] = set(hyperplanes)
    hyps = list(hyperplanes)
    for rk in range(rank - 2, -1, -1):
        cands: set[frozenset[int]] = set()
        for g_flat in by_rank[rk + 1]:
            subs = {g_flat & h_flat for h_flat in hyps if not g_flat.issubset(h_flat)}
            for s_flat in subs:
                has_strict_superset = any(s_flat < t_flat for t_flat in subs)
                if not has_strict_superset:
                    cands.add(s_flat)
        by_rank[rk] = cands
    require_ok(by_rank[0] == {frozenset()}, "MATROID_LOOPLESS", "rank-0 flat must be singleton empty set")
    for rk in range(rank):
        upper = list(by_rank[rk + 1])
        for f_flat in by_rank[rk]:
            diffs = [g_flat - f_flat for g_flat in upper if f_flat.issubset(g_flat)]
            total_len = sum(len(d) for d in diffs)
            union_d = set().union(*diffs) if diffs else set()
            require_ok(total_len == n_elems - len(f_flat), "MATROID_COVER_COUNT", "upward flat covers overlap")
            require_ok(union_d == (full_e - f_flat), "MATROID_COVER_UNION", "upward flat covers miss elements")
    return by_rank


def epw_kl_and_z_from_poset(
    by_rank: dict[int, set[frozenset[int]]],
    *,
    corrupt_antisym: bool = False,
    corrupt_palindrome: bool = False,
) -> tuple[list[int], list[int], dict[tuple[int, ...], int]]:
    """Compute P_M(t), Z_M(t), and flag f-vector directly from the defining EPW recurrence."""
    rank = max(by_rank.keys())
    flats: list[frozenset[int]] = []
    rk_of: dict[frozenset[int], int] = {}
    for r in range(rank + 1):
        for f_flat in sorted(by_rank[r], key=lambda s: tuple(sorted(s))):
            rk_of[f_flat] = r
            flats.append(f_flat)
    n_flats = len(flats)
    leq = [[flats[i].issubset(flats[j]) for j in range(n_flats)] for i in range(n_flats)]
    mu = [[0] * n_flats for _ in range(n_flats)]
    for i in range(n_flats):
        mu[i][i] = 1
        for j in range(i + 1, n_flats):
            if leq[i][j]:
                s_mu = 0
                for k in range(i, j):
                    if leq[i][k]:
                        if leq[k][j]:
                            s_mu = s_mu + mu[i][k]
                mu[i][j] = -s_mu

    def chi_interval(i: int, j: int) -> list[int]:
        r_ij = rk_of[flats[j]] - rk_of[flats[i]]
        poly = [0] * (r_ij + 1)
        for k in range(i, j + 1):
            if leq[i][k]:
                if leq[k][j]:
                    deg = rk_of[flats[j]] - rk_of[flats[k]]
                    poly[deg] = poly[deg] + mu[i][k]
        return poly

    p_contr: list[list[int]] = [[] for _ in range(n_flats)]
    p_contr[n_flats - 1] = [1]
    for i in range(n_flats - 2, -1, -1):
        r_cur = rank - rk_of[flats[i]]
        deg_bound = (r_cur - 1) // 2
        rhs = [0] * (r_cur + 1)
        for k in range(i + 1, n_flats):
            if leq[i][k]:
                rhs = _poly_add_int(rhs, _poly_mul_int(chi_interval(i, k), p_contr[k]))
        p_i = [-rhs[d] for d in range(deg_bound + 1)]
        lhs = [0] * (r_cur + 1)
        for d, coeff in enumerate(p_i):
            lhs[r_cur - d] = lhs[r_cur - d] + coeff
            lhs[d] = lhs[d] - coeff
        if corrupt_antisym:
            lhs[r_cur] = lhs[r_cur] + 1
        require_ok(lhs == rhs, "EPW_ANTISYMMETRY", "EPW antisymmetric recurrence failed")
        p_contr[i] = p_i

    z_poly = [0] * (rank + 1)
    for i in range(n_flats):
        rf = rk_of[flats[i]]
        for d, coeff in enumerate(p_contr[i]):
            z_poly[rf + d] = z_poly[rf + d] + coeff
    if corrupt_palindrome:
        z_poly[0] = z_poly[0] + 1
    require_ok(z_poly == list(reversed(z_poly)), "ZPOLY_PALINDROME", "Z-polynomial not palindromic")

    proper_by_rk = {r: [i for i in range(n_flats) if rk_of[flats[i]] == r] for r in range(1, rank)}

    def alpha_set(rks: tuple[int, ...]) -> int:
        if len(rks) == 0:
            return 1
        dp = {i: 1 for i in proper_by_rk[rks[0]]}
        for r_nxt in rks[1:]:
            ndp: dict[int, int] = {}
            for j in proper_by_rk[r_nxt]:
                ndp[j] = sum(cnt for i, cnt in dp.items() if leq[i][j])
            dp = ndp
        return sum(dp.values())

    flag_vec: dict[tuple[int, ...], int] = {(): 1}
    for k_len in range(1, min(rank, 4)):
        for sub in combinations(range(1, rank), k_len):
            flag_vec[sub] = alpha_set(sub)
    return p_contr[0], z_poly, flag_vec


def _build_a42_hyperplanes() -> set[frozenset[int]]:
    f4_mul = [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]]
    f4_frob = [0, 1, 3, 2]
    planes_a2 = [
        {
            frozenset(v0 ^ ((x << 2) | (f4_mul[u][x] ^ f4_mul[a][f4_frob[x]])) for x in range(4))
            for u in range(4)
            for v0 in range(16)
        }
        for a in range(4)
    ]
    aff_planes2 = {
        frozenset([i, j, k, i ^ j ^ k])
        for i in range(16)
        for j in range(i + 1, 16)
        for k in range(j + 1, 16)
    }
    aff_lines2 = [frozenset([i, j]) for i in range(16) for j in range(i + 1, 16)]
    hyps = set(aff_planes2 - set().union(*planes_a2))
    for a in range(4):
        pa = 16 + a
        for plane in planes_a2[a]:
            hyps.add(plane | {pa})
        absorbed = {frozenset([x, y]) for plane in planes_a2[a] for x in plane for y in plane if x < y}
        for line in aff_lines2:
            if line not in absorbed:
                hyps.add(line | {pa})
    for x in range(16):
        for a in range(4):
            for b in range(a + 1, 4):
                hyps.add(frozenset([x, 16 + a, 16 + b]))
    for a in range(4):
        for b in range(a + 1, 4):
            for c in range(b + 1, 4):
                hyps.add(frozenset([16 + a, 16 + b, 16 + c]))
    return hyps


def verify_epw_kl_and_zpoly_audit(tamper: str | None = None) -> dict[str, object]:
    """Zero-shared-code EPW audit on non-uniform matroids of ranks 3, 4, 5, and 7."""
    k4_hyps = {
        frozenset([0, 1, 3]), frozenset([0, 2, 4]), frozenset([1, 2, 5]), frozenset([3, 4, 5]),
        frozenset([0, 5]), frozenset([1, 4]), frozenset([2, 3]),
    }
    lat_k4 = build_lattice_from_hyperplanes(6, 3, k4_hyps)
    p_k4, z_k4, f_k4 = epw_kl_and_z_from_poset(
        lat_k4,
        corrupt_antisym=(tamper == "antisym"),
        corrupt_palindrome=(tamper == "palindrome"),
    )
    pred_rk3 = f_k4[(2,)] - f_k4[(1,)]
    if tamper == "rk3":
        pred_rk3 = pred_rk3 + 1
    require_ok(p_k4[1] == pred_rk3, "KL_RK3_FORMULA", "rank-3 [t]P formula mismatch")

    hyps_a42 = _build_a42_hyperplanes()
    lat_a42 = build_lattice_from_hyperplanes(20, 4, hyps_a42)
    p_a42, z_a42, f_a42 = epw_kl_and_z_from_poset(lat_a42)
    pred_rk4 = f_a42[(3,)] - f_a42[(1,)]
    if tamper == "rk4":
        pred_rk4 = pred_rk4 + 1
    require_ok(p_a42[1] == pred_rk4, "KL_RK4_FORMULA", "rank-4 [t]P formula mismatch")

    flats_k4 = [(r, fl) for r, fs in lat_k4.items() for fl in fs]
    hyps_rk5 = {
        f1 | frozenset(6 + x for x in f2)
        for r1, f1 in flats_k4
        for r2, f2 in flats_k4
        if r1 + r2 == 4
    }
    lat_rk5 = build_lattice_from_hyperplanes(12, 5, hyps_rk5)
    p_rk5, z_rk5, f_rk5 = epw_kl_and_z_from_poset(lat_rk5)
    pred_rk5 = f_rk5[(3,)] - f_rk5[(2,)] + f_rk5[(2, 4)] - f_rk5[(2, 3)] - f_rk5[(1, 4)] + f_rk5[(1, 2)]
    if tamper == "rk5":
        pred_rk5 = pred_rk5 + 1
    require_ok(p_rk5[2] == pred_rk5, "KL_RK5_FORMULA", "rank-5 [t^2]P formula mismatch")

    u23_flats = [
        (0, frozenset()), (1, frozenset([0])), (1, frozenset([1])),
        (1, frozenset([2])), (2, frozenset([0, 1, 2])),
    ]
    hyps_rk7 = {
        f1 | frozenset(6 + x for x in f2) | frozenset(12 + x for x in f3)
        for r1, f1 in flats_k4
        for r2, f2 in flats_k4
        for r3, f3 in u23_flats
        if r1 + r2 + r3 == 6
    }
    lat_rk7 = build_lattice_from_hyperplanes(15, 7, hyps_rk7)
    p_rk7, z_rk7, f_rk7 = epw_kl_and_z_from_poset(lat_rk7)
    z1_f = f_rk7[(6,)]
    z2_f = f_rk7[(5,)] + f_rk7[(4, 6)] - f_rk7[(4, 5)]
    z3_f = (
        f_rk7[(4,)] + f_rk7[(3, 6)] - f_rk7[(3, 4)]
        + f_rk7[(2, 5)] - f_rk7[(2, 4)]
        + f_rk7[(2, 4, 6)] - f_rk7[(2, 4, 5)]
        - f_rk7[(2, 3, 6)] + f_rk7[(2, 3, 4)]
    )
    pred_z7 = [1, z1_f, z2_f, z3_f, z3_f, z2_f, z1_f, 1]
    if tamper == "rk7":
        pred_z7[3] = pred_z7[3] + 1
    require_ok(z_rk7 == pred_z7, "ZPOLY_RK7_FORMULA", "rank-7 Z_M flag formula mismatch")
    return {
        "k4_rk3": {"P": p_k4, "Z": z_k4},
        "a42_rk4": {"P": p_a42, "Z": z_a42},
        "tr_k4_k4_rk5": {"P": p_rk5, "Z": z_rk5},
        "tr_k4_k4_u23_rk7": {"P": p_rk7, "Z": z_rk7},
    }


# ---------------------------------------------------------------------------
# Pillar 2: Closed-form flag vectors + exhaustive finite A_{4,2} and A_{4,3}
# ---------------------------------------------------------------------------

def proj_gabidulin_alpha(q: int, m: int | None = None) -> dict[tuple[int, ...], int]:
    """Flag f-vector of rank-4 projective Gabidulin matroid in PG(5, q) with m <= q^3 cosets."""
    require_ok(q >= 2, "ALPHA_Q_MIN", "q must be at least 2")
    max_m = q ** 3
    if m is None:
        m = max_m
    require_ok(m >= 0 and m <= max_m, "FAMILY_M_BOUNDS", "m out of [0, q^3]")
    b_val = m * (q ** 6)
    n1 = qbin(6, 1, q)
    n2 = qbin(6, 2, q)
    n3 = qbin(6, 3, q)
    t_val = q * q + q + 1
    htypes = [
        (n1 * comb(m, 2) + comb(m, 3), 3, 3, 6),
        (b_val, t_val + 1, 2 * t_val, (q + 3) * t_val),
        (m * n2 - b_val * t_val, q + 2, q + 2, 3 * (q + 1)),
        (n3 - b_val, t_val, t_val, (q + 1) * t_val),
    ]
    w1 = n1 + m
    w2 = n2 + n1 * m + comb(m, 2)
    return {
        (): 1,
        (1,): w1,
        (2,): w2,
        (3,): sum(n for n, _, _, _ in htypes),
        (1, 2): (q + 1) * n2 + 2 * (n1 * m + comb(m, 2)),
        (1, 3): sum(n * pts for n, pts, _, _ in htypes),
        (2, 3): sum(n * lns for n, _, lns, _ in htypes),
        (1, 2, 3): sum(n * flg for n, _, _, flg in htypes),
    }


def affine_coalesced_alpha(q: int, m: int, s_dirs: int) -> dict[tuple[int, ...], int]:
    """Flag f-vector of rank-4 affine coalesced matroid in AG(4, q) (s_dirs = q^2 or q^2 + 1)."""
    require_ok(q >= 2, "ALPHA_Q_MIN", "q must be at least 2")
    max_m = q * q + q + 1 if s_dirs == q * q + 1 else q * q
    require_ok(m >= 0 and m <= max_m, "FAMILY_M_BOUNDS", "m out of valid family range")
    n1 = q ** 4
    n2 = (q ** 3) * qbin(4, 1, q)
    n3 = (q ** 2) * qbin(4, 2, q)
    b_val = m * (q ** 2) * s_dirs
    htypes = [
        (n1 * comb(m, 2) + comb(m, 3), 3, 3, 6),
        (b_val, q * q + 1, 2 * q * q + q, q ** 3 + 3 * q * q),
        (m * n2 - b_val * q * (q + 1), q + 1, q + 1, 3 * q),
        (n3 - b_val, q * q, q * (q + 1), q * q * (q + 1)),
    ]
    w1 = n1 + m
    w2 = n2 + n1 * m + comb(m, 2)
    return {
        (): 1,
        (1,): w1,
        (2,): w2,
        (3,): sum(n for n, _, _, _ in htypes),
        (1, 2): q * n2 + 2 * (n1 * m + comb(m, 2)),
        (1, 3): sum(n * pts for n, pts, _, _ in htypes),
        (2, 3): sum(n * lns for n, _, lns, _ in htypes),
        (1, 2, 3): sum(n * flg for n, _, _, flg in htypes),
    }


def verify_finite_a42_and_a43(tamper: str | None = None) -> dict[str, object]:
    """Exhaustive finite matroid axiom and flag-vector checks on A_{4,2} (|E|=20) and A_{4,3} (|E|=90)."""
    hyps_a42 = _build_a42_hyperplanes()
    triple_cover: dict[tuple[int, int, int], int] = {}
    for h_set in hyps_a42:
        for tri in combinations(sorted(h_set), 3):
            triple_cover[tri] = triple_cover.get(tri, 0) + 1
    if tamper == "a42_missing":
        triple_cover.pop(next(iter(triple_cover)))
    if tamper == "a42_dup":
        first_k = next(iter(triple_cover))
        triple_cover[first_k] = 2
    require_ok(len(triple_cover) == 1140, "A42_TRIPLE_COUNT", "A_{4,2} must cover all 1140 triples")
    require_ok(max(triple_cover.values()) == 1, "A42_TRIPLE_UNIQUE", "A_{4,2} triple cover not unique")
    lat_a42 = build_lattice_from_hyperplanes(20, 4, hyps_a42)
    _, _, emp_a42 = epw_kl_and_z_from_poset(lat_a42)
    sym_a42 = affine_coalesced_alpha(2, 4, 4)
    if tamper == "a42_flag":
        emp_a42[(3,)] = emp_a42[(3,)] + 1
    require_ok(emp_a42 == sym_a42, "A42_FLAG_MATCH", "A_{4,2} empirical vs closed-form flag mismatch")

    # Finite A_{4,3} (|E| = 81 + 9 = 90)
    add9 = [[((x % 3 + y % 3) % 3) + 3 * ((x // 3 + y // 3) % 3) for y in range(9)] for x in range(9)]
    mul9 = [
        [(((x % 3) * (y % 3) - (x // 3) * (y // 3)) % 3) + 3 * (((x % 3) * (y // 3) + (x // 3) * (y % 3)) % 3) for y in range(9)]
        for x in range(9)
    ]
    frob9 = [mul9[mul9[x][x]][x] for x in range(9)]

    def v_add(p_pt: int, q_pt: int) -> int:
        return 9 * add9[p_pt // 9][q_pt // 9] + add9[p_pt % 9][q_pt % 9]

    aff_lines = set()
    for p_pt in range(81):
        for q_pt in range(p_pt + 1, 81):
            s_pt = v_add(p_pt, q_pt)
            aff_lines.add(frozenset([p_pt, q_pt, v_add(s_pt, s_pt)]))
    lin_1 = sorted({frozenset([0, p_pt, v_add(p_pt, p_pt)]) for p_pt in range(1, 81)}, key=lambda s: tuple(sorted(s)))
    lin_2 = {
        frozenset(v_add(x, y) for x in lin_1[i] for y in lin_1[j])
        for i in range(40)
        for j in range(i + 1, 40)
    }
    aff_planes = {frozenset(v_add(v0, w) for w in w_sp) for w_sp in lin_2 for v0 in range(81)}
    planes_by_a = []
    for a in range(9):
        fam = set()
        for u in range(9):
            w_sp = frozenset(9 * x + add9[mul9[u][x]][mul9[a][frob9[x]]] for x in range(9))
            for v0 in range(81):
                fam.add(frozenset(v_add(v0, w) for w in w_sp))
        planes_by_a.append(fam)
    chosen_planes = set().union(*planes_by_a)

    rk2_flats = set(aff_lines)
    for x in range(81):
        for a in range(9):
            rk2_flats.add(frozenset([x, 81 + a]))
    for a in range(9):
        for b in range(a + 1, 9):
            rk2_flats.add(frozenset([81 + a, 81 + b]))

    hyps_a43 = set(aff_planes - chosen_planes)
    for a in range(9):
        pa = 81 + a
        for plane in planes_by_a[a]:
            hyps_a43.add(plane | {pa})
        absorbed = {ln for ln in aff_lines if any(ln.issubset(plane) for plane in planes_by_a[a])}
        for ln in aff_lines - absorbed:
            hyps_a43.add(ln | {pa})
    for x in range(81):
        for a in range(9):
            for b in range(a + 1, 9):
                hyps_a43.add(frozenset([x, 81 + a, 81 + b]))
    for a in range(9):
        for b in range(a + 1, 9):
            for c in range(b + 1, 9):
                hyps_a43.add(frozenset([81 + a, 81 + b, 81 + c]))

    seen_pairs: set[tuple[int, int]] = set()
    pair_sum = 0
    for ln in rk2_flats:
        s_ln = sorted(ln)
        for idx_a in range(len(s_ln)):
            for idx_b in range(idx_a + 1, len(s_ln)):
                seen_pairs.add((s_ln[idx_a], s_ln[idx_b]))
                pair_sum = pair_sum + 1
    if tamper == "a43_pair":
        seen_pairs.pop()
    if tamper == "a43_pair_dup":
        pair_sum = pair_sum + 1
    require_ok(len(seen_pairs) == 4005, "A43_PAIR_PARTITION", "A_{4,3} rank-2 flats must cover all 4005 pairs")
    require_ok(pair_sum == 4005, "A43_PAIR_UNIQUE", "A_{4,3} rank-2 pair partition has overlapping pairs")

    hyps_list = list(hyps_a43)
    by_elem: list[set[int]] = [set() for _ in range(90)]
    for idx_h, h_set in enumerate(hyps_list):
        for elem in h_set:
            by_elem[elem].add(idx_h)

    rk2_bad = 0
    a23_cnt = 0
    a123_cnt = 0
    for ln in rk2_flats:
        it = iter(ln)
        cand = set(by_elem[next(it)])
        for elem in it:
            cand &= by_elem[elem]
        diffs = [hyps_list[idx_h] - ln for idx_h in cand]
        if sum(len(d) for d in diffs) != 90 - len(ln):
            rk2_bad = rk2_bad + 1
        elif len(set().union(*diffs)) != 90 - len(ln):
            rk2_bad = rk2_bad + 1
        a23_cnt = a23_cnt + len(cand)
        a123_cnt = a123_cnt + len(ln) * len(cand)
    if tamper == "a43_rk2":
        rk2_bad = 1
    require_ok(rk2_bad == 0, "A43_RK2_PARTITION", "A_{4,3} rank-2 upward hyperplane cover partition failed")

    emp_a43 = {
        (): 1,
        (1,): 90,
        (2,): len(rk2_flats),
        (3,): len(hyps_list),
        (1, 2): sum(len(ln) for ln in rk2_flats),
        (1, 3): sum(len(h_set) for h_set in hyps_list),
        (2, 3): a23_cnt,
        (1, 2, 3): a123_cnt,
    }
    sym_a43 = affine_coalesced_alpha(3, 9, 9)
    if tamper == "a43_flag":
        emp_a43[(1, 2, 3)] = emp_a43[(1, 2, 3)] + 1
    require_ok(emp_a43 == sym_a43, "A43_FLAG_MATCH", "A_{4,3} empirical vs closed-form flag mismatch")
    z2_a43 = emp_a43[(2,)] + emp_a43[(1, 3)] - emp_a43[(1, 2)]
    z_a43 = [1, emp_a43[(3,)], z2_a43, emp_a43[(3,)], 1]
    return {
        "a42": {"ground_set": 20, "hyperplanes": len(hyps_a42), "unique_triples": 1140, "a123": emp_a42[(1, 2, 3)]},
        "a43": {
            "ground_set": 90,
            "rk2_flats": len(rk2_flats),
            "hyperplanes": len(hyps_list),
            "a123": emp_a43[(1, 2, 3)],
            "Z": z_a43,
        },
    }


# ---------------------------------------------------------------------------
# Pillar 3: Explicit algebraic 651-spread parallelism of PG(3, 25)
# ---------------------------------------------------------------------------

def verify_pg3_q25_parallelism(
    *,
    check_spreads: int = 651,
    tamper: str | None = None,
) -> dict[str, object]:
    """Explicitly construct and verify all 651 pairwise-disjoint spreads of PG(3, 25) over F_625."""
    require_ok(check_spreads >= 537, "SPREAD_MIN_537", "must verify at least 537 spreads")
    require_ok(check_spreads <= 651, "SPREAD_MAX_651", "PG(3, 25) has at most 651 disjoint spreads")

    add25 = [((x % 5 + y % 5) % 5) + 5 * ((x // 5 + y // 5) % 5) for x in range(25) for y in range(25)]
    neg25 = [((-(x % 5)) % 5) + 5 * ((-((x // 5) % 5)) % 5) for x in range(25)]
    mul25 = [
        (((x % 5) * (y % 5) + 2 * (x // 5) * (y // 5)) % 5)
        + 5 * (((x % 5) * (y // 5) + (x // 5) * (y % 5)) % 5)
        for x in range(25)
        for y in range(25)
    ]
    inv25 = [0] * 25
    for x in range(1, 25):
        for y in range(1, 25):
            if mul25[x * 25 + y] == 1:
                inv25[x] = y

    ns25 = 5
    add625 = [add25[(x % 25) * 25 + (y % 25)] + 25 * add25[(x // 25) * 25 + (y // 25)] for x in range(625) for y in range(625)]
    neg625 = [neg25[x % 25] + 25 * neg25[x // 25] for x in range(625)]
    mul625 = [0] * (625 * 625)
    for x in range(625):
        ax, bx = x % 25, x // 25
        row = x * 625
        for y in range(625):
            ay, by = y % 25, y // 25
            c0 = add25[mul25[ax * 25 + ay] * 25 + mul25[ns25 * 25 + mul25[bx * 25 + by]]]
            c1 = add25[mul25[ax * 25 + by] * 25 + mul25[bx * 25 + ay]]
            mul625[row + y] = c0 + 25 * c1
    frob625 = [(x % 25) + 25 * neg25[x // 25] for x in range(625)]
    norm625 = [mul625[x * 625 + frob625[x]] for x in range(625)]

    def pow625(base: int, exp: int) -> int:
        res = 1
        cur = base
        while exp > 0:
            if exp & 1:
                res = mul625[res * 625 + cur]
            cur = mul625[cur * 625 + cur]
            exp >>= 1
        return res

    inv625 = [0] + [pow625(x, 623) for x in range(1, 625)]
    u_circle = [x for x in range(1, 625) if norm625[x] == 1]
    root_of_u = {pow625(x, 24): x for x in range(1, 625)}

    allowed_norms_25 = (2, 4, 5, 6, 7, 8, 10, 12, 13, 16, 19, 21)
    norms_set = set(allowed_norms_25)
    norm_pair_union = norms_set | {inv25[c] for c in allowed_norms_25}
    norm_pair_bad = 0
    if len(allowed_norms_25) != 12:
        norm_pair_bad = norm_pair_bad + 1
    if neg25[1] not in norms_set:
        norm_pair_bad = norm_pair_bad + 1
    if 1 in norms_set:
        norm_pair_bad = norm_pair_bad + 1
    for c in allowed_norms_25:
        if c != neg25[1]:
            if inv25[c] in norms_set:
                norm_pair_bad = norm_pair_bad + 1
    if norm_pair_union != set(range(2, 25)):
        norm_pair_bad = norm_pair_bad + 1
    if norm625[5] not in norms_set:
        norm_pair_bad = norm_pair_bad + 1
    if tamper == "allowed_norms":
        norm_pair_bad = norm_pair_bad + 1
    require_ok(norm_pair_bad == 0, "ALLOWED_NORMS_INVALID", "allowedNorms25 failed F_25* reciprocal-pair check")

    good_p = [(5, 1, v_val) for v_val in u_circle]
    if tamper == "good_set":
        good_p[-1] = good_p[0]
    good_bad = 0
    for i in range(len(good_p)):
        a1, u1, v1 = good_p[i]
        for j in range(i + 1, len(good_p)):
            a2, u2, v2 = good_p[j]
            if mul625[u1 * 625 + v2] == mul625[v1 * 625 + u2]:
                good_bad = good_bad + 1
            lhs33 = mul625[mul625[a1 * 625 + u1] * 625 + frob625[mul625[a2 * 625 + v2]]]
            rhs33 = mul625[frob625[mul625[a1 * 625 + v1]] * 625 + mul625[a2 * 625 + u2]]
            if lhs33 == rhs33:
                good_bad = good_bad + 1
    require_ok(good_bad == 0, "GOOD_SET_INVALID", "good set P failed (3.2) or (3.3)")

    norm_pt = [-1] * 390625
    id_to_vec: list[tuple[int, int, int, int]] = []
    id_to_xy: list[tuple[int, int]] = []
    for v_idx in range(1, 390625):
        c0 = v_idx % 25
        c1 = (v_idx // 25) % 25
        c2 = (v_idx // 625) % 25
        c3 = v_idx // 15625
        first_nz = c0 if c0 != 0 else (c1 if c1 != 0 else (c2 if c2 != 0 else c3))
        if first_nz == 1:
            norm_pt[v_idx] = len(id_to_vec)
            id_to_vec.append((c0, c1, c2, c3))
            id_to_xy.append((v_idx % 625, v_idx // 625))
    for pid, (c0, c1, c2, c3) in enumerate(id_to_vec):
        for lam in range(1, 25):
            idx_v = mul25[c0 * 25 + lam] + 25 * mul25[c1 * 25 + lam] + 625 * mul25[c2 * 25 + lam] + 15625 * mul25[c3 * 25 + lam]
            norm_pt[idx_v] = pid

    def line_code(id1: int, id2: int) -> int:
        u0, u1, u2, u3 = id_to_vec[id1]
        v0, v1, v2, v3 = id_to_vec[id2]
        p01 = add25[mul25[u0 * 25 + v1] * 25 + neg25[mul25[u1 * 25 + v0]]]
        p02 = add25[mul25[u0 * 25 + v2] * 25 + neg25[mul25[u2 * 25 + v0]]]
        p03 = add25[mul25[u0 * 25 + v3] * 25 + neg25[mul25[u3 * 25 + v0]]]
        p12 = add25[mul25[u1 * 25 + v2] * 25 + neg25[mul25[u2 * 25 + v1]]]
        p13 = add25[mul25[u1 * 25 + v3] * 25 + neg25[mul25[u3 * 25 + v1]]]
        p23 = add25[mul25[u2 * 25 + v3] * 25 + neg25[mul25[u3 * 25 + v2]]]
        plk = (p01, p02, p03, p12, p13, p23)
        iv = 1
        for c in plk:
            if c != 0:
                iv = inv25[c]
                break
        return (
            mul25[p01 * 25 + iv]
            + 25 * mul25[p02 * 25 + iv]
            + 625 * mul25[p03 * 25 + iv]
            + 15625 * mul25[p12 * 25 + iv]
            + 390625 * mul25[p13 * 25 + iv]
            + 9765625 * mul25[p23 * 25 + iv]
        )

    def baer_pts_and_code(p1: int, p2: int, p3: int, p4: int) -> tuple[int, tuple[int, int]]:
        tp1, tp2 = frob625[p3], frob625[p4]
        xp = add625[p1 * 625 + tp1]
        yp = add625[p2 * 625 + tp2]
        xm = mul625[25 * 625 + add625[p1 * 625 + neg625[tp1]]]
        ym = mul625[25 * 625 + add625[p2 * 625 + neg625[tp2]]]
        id1 = norm_pt[xp + 625 * yp]
        id2 = norm_pt[xm + 625 * ym]
        return line_code(id1, id2), (id1, id2)

    d1_pts: dict[int, tuple[int, int]] = {}
    c_inf, p_inf = baer_pts_and_code(0, 1, 0, 0)
    d1_pts[c_inf] = p_inf
    for a_idx in range(625):
        ca, pa = baer_pts_and_code(1, a_idx, 0, 0)
        d1_pts[ca] = pa
    d1_set = set(d1_pts.keys())

    def opp_reg_pairs(r_lines: set[int]) -> dict[int, tuple[int, int]]:
        r_sorted = sorted(r_lines)
        u0, v0 = (id_to_vec[i] for i in d1_pts[r_sorted[0]])
        u1, v1 = (id_to_vec[i] for i in d1_pts[r_sorted[1]])
        u2, v2 = (id_to_vec[i] for i in d1_pts[r_sorted[2]])
        pts0 = [v0] + [tuple(add25[u0[k] * 25 + mul25[a_sc * 25 + v0[k]]] for k in range(4)) for a_sc in range(25)]
        opp: dict[int, tuple[int, int]] = {}
        for x_pt in pts0:
            id_x = norm_pt[x_pt[0] + 25 * x_pt[1] + 625 * x_pt[2] + 15625 * x_pt[3]]
            mat = [list(x_pt), list(u2), list(v2)]
            pivs: list[int] = []
            row_i = 0
            for col in range(4):
                piv = -1
                for rr in range(row_i, 3):
                    if mat[rr][col] != 0:
                        piv = rr
                        break
                if piv < 0:
                    continue
                mat[row_i], mat[piv] = mat[piv], mat[row_i]
                iv = inv25[mat[row_i][col]]
                for cc in range(4):
                    mat[row_i][cc] = mul25[mat[row_i][cc] * 25 + iv]
                for rr in range(3):
                    if rr != row_i:
                        if mat[rr][col] != 0:
                            fac = mat[rr][col]
                            for cc in range(4):
                                mat[rr][cc] = add25[mat[rr][cc] * 25 + neg25[mul25[fac * 25 + mat[row_i][cc]]]]
                pivs.append(col)
                row_i = row_i + 1
            free_c = next(cc for cc in range(4) if cc not in pivs)
            n2 = [0, 0, 0, 0]
            n2[free_c] = 1
            for rr, pc in enumerate(pivs):
                n2[pc] = neg25[mat[rr][free_c]]
            du = 0
            dv = 0
            for k in range(4):
                du = add25[du * 25 + mul25[n2[k] * 25 + u1[k]]]
                dv = add25[dv * 25 + mul25[n2[k] * 25 + v1[k]]]
            if du == 0:
                y_pt = u1
            else:
                lam = neg25[mul25[dv * 25 + inv25[du]]]
                y_pt = tuple(add25[v1[k] * 25 + mul25[lam * 25 + u1[k]]] for k in range(4))
            id_y = norm_pt[y_pt[0] + 25 * y_pt[1] + 625 * y_pt[2] + 15625 * y_pt[3]]
            opp[line_code(id_x, id_y)] = (id_x, id_y)
        return opp

    sc_mul = [mul625[a_sc * 625 : (a_sc + 1) * 625] for a_sc in range(25)]

    def check_point_partition(pairs_list: list[tuple[int, int]]) -> bool:
        seen = bytearray(16276)
        _id_xy = id_to_xy
        _add = add625
        _npt = norm_pt
        _sc = sc_mul
        for id1, id2 in pairs_list:
            seen[id2] = 1
            x1, y1 = _id_xy[id1]
            x2, y2 = _id_xy[id2]
            x1_off = x1 * 625
            y1_off = y1 * 625
            for row in _sc:
                seen[_npt[_add[x1_off + row[x2]] + 625 * _add[y1_off + row[y2]]]] = 1
        return seen.count(1) == 16276

    union_lines = set(d1_set)
    spread_count = 1
    bad_size = 0
    overlap_cnt = 0
    pt_part_bad = 0 if check_point_partition(list(d1_pts.values())) else 1
    pt_part_checked = 1
    lines_at_537 = 0
    lines_at_510 = 0

    al = 5
    xi = root_of_u[1]
    x_prime = root_of_u[u_circle[1]]
    a1_c, a3_c = xi, mul625[al * 625 + frob625[xi]]

    for v_val in u_circle:
        if spread_count >= check_spreads:
            break
        yi = root_of_u[v_val]
        b2_c, b4_c = yi, mul625[al * 625 + frob625[yi]]
        sl_pairs: dict[int, tuple[int, int]] = {}
        c0, p0 = baer_pts_and_code(a1_c, 0, a3_c, 0)
        sl_pairs[c0] = p0
        for t_sc in range(625):
            ct, pt = baer_pts_and_code(mul625[t_sc * 625 + a1_c], b2_c, mul625[t_sc * 625 + a3_c], b4_c)
            sl_pairs[ct] = pt
        r_l = d1_set & sl_pairs.keys()
        opp_p = opp_reg_pairs(r_l)
        h0_pairs = [pt for cd, pt in sl_pairs.items() if cd not in r_l] + list(opp_p.values())
        h0_codes = {line_code(i1, i2) for i1, i2 in h0_pairs}
        pt_part_checked = pt_part_checked + 1
        if not check_point_partition(h0_pairs):
            pt_part_bad = pt_part_bad + 1
        if len(h0_codes) != 626:
            bad_size = bad_size + 1
        if not union_lines.isdisjoint(h0_codes):
            overlap_cnt = overlap_cnt + 1
        union_lines.update(h0_codes)
        spread_count = spread_count + 1
        if spread_count == 510:
            lines_at_510 = len(union_lines)
        if spread_count == 537:
            lines_at_537 = len(union_lines)

        step_b = mul625[x_prime * 625 + inv625[yi]]
        for lam in range(1, 25):
            if spread_count >= check_spreads:
                break
            b_shift = mul625[lam * 625 + step_b]
            h_lam = set()
            h_lam_pairs: list[tuple[int, int]] = []
            for id1, id2 in h0_pairs:
                x1, y1 = id_to_xy[id1]
                x2, y2 = id_to_xy[id2]
                nid1 = norm_pt[add625[x1 * 625 + mul625[b_shift * 625 + y1]] + 625 * y1]
                nid2 = norm_pt[add625[x2 * 625 + mul625[b_shift * 625 + y2]] + 625 * y2]
                h_lam.add(line_code(nid1, nid2))
                h_lam_pairs.append((nid1, nid2))
            pt_part_checked = pt_part_checked + 1
            if not check_point_partition(h_lam_pairs):
                pt_part_bad = pt_part_bad + 1
            if len(h_lam) != 626:
                bad_size = bad_size + 1
            if not union_lines.isdisjoint(h_lam):
                overlap_cnt = overlap_cnt + 1
            union_lines.update(h_lam)
            spread_count = spread_count + 1
            if spread_count == 510:
                lines_at_510 = len(union_lines)
            if spread_count == 537:
                lines_at_537 = len(union_lines)

    if tamper == "size":
        bad_size = 1
    if tamper == "overlap":
        overlap_cnt = 1
    if tamper == "pt_partition":
        pt_part_bad = 1
    require_ok(bad_size == 0, "SPREAD_SIZE_MISMATCH", "spread does not have 626 lines")
    require_ok(overlap_cnt == 0, "SPREAD_OVERLAP", "two spreads share at least one line")
    require_ok(pt_part_bad == 0, "SPREAD_POINT_PARTITION", "spread failed 16276-point partition check")
    return {
        "field_order": 25,
        "good_set_size": len(good_p),
        "spreads_verified": spread_count,
        "point_partitions_verified": pt_part_checked,
        "lines_per_spread": 626,
        "points_in_pg3_25": 16276,
        "distinct_lines_at_m510": lines_at_510,
        "distinct_lines_at_m537": lines_at_537,
        "total_distinct_lines": len(union_lines),
        "pairwise_overlaps": overlap_cnt,
    }


# ---------------------------------------------------------------------------
# Pillars 1-5: Symbolic pure-Q Taylor shifts, parallel connection, & witnesses
# ---------------------------------------------------------------------------

def _p_add_q(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    n = max(len(a), len(b))
    out = [(a[i] if i < len(a) else Fraction(0)) + (b[i] if i < len(b) else Fraction(0)) for i in range(n)]
    while len(out) > 1:
        if out[-1] == 0:
            out.pop()
        else:
            break
    return out


def _p_sub_q(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    return _p_add_q(a, [-x for x in b])


def _p_mul_q(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = out[i + j] + x * y
    while len(out) > 1:
        if out[-1] == 0:
            out.pop()
        else:
            break
    return out


def _p_shift_q(poly: list[Fraction], x0: int) -> list[Fraction]:
    res = [Fraction(0)]
    for coeff in reversed(poly):
        res = _p_add_q([coeff], _p_mul_q([Fraction(x0), Fraction(1)], res))
    return res


def _q_gauss_poly(n: int, k: int) -> list[Fraction]:
    if k == 0:
        return [Fraction(1)]
    if k == n:
        return [Fraction(1)]
    q_pow = [Fraction(0)] * k + [Fraction(1)]
    return _p_add_q(_q_gauss_poly(n - 1, k - 1), _p_mul_q(q_pow, _q_gauss_poly(n - 1, k)))


def _multichain_pair_weights(terms: list[tuple[int, tuple[int, ...]]]) -> list[tuple[tuple[int, ...], tuple[int, ...], int]]:
    acc: dict[tuple[tuple[int, ...], tuple[int, ...]], int] = {}
    for sgn, ranks in terms:
        for left in product(range(5), repeat=len(ranks)):
            if list(left) != sorted(left):
                continue
            right = tuple(s - i for s, i in zip(ranks, left))
            if any(not (0 <= j <= 4) for j in right):
                continue
            if list(right) != sorted(right):
                continue
            pl = tuple(sorted({r for r in left if 0 < r < 4}))
            pr = tuple(sorted({r for r in right if 0 < r < 4}))
            acc[(pl, pr)] = acc.get((pl, pr), 0) + sgn
    return [(pl, pr, c) for (pl, pr), c in sorted(acc.items()) if c != 0]


_RK7_Z1_W = _multichain_pair_weights([(1, (6,))])
_RK7_Z2_W = _multichain_pair_weights([(1, (5,)), (1, (4, 6)), (-1, (4, 5))])
_RK7_Z3_W = _multichain_pair_weights([
    (1, (4,)), (1, (3, 6)), (-1, (3, 4)), (1, (2, 5)), (-1, (2, 4)),
    (1, (2, 4, 6)), (-1, (2, 4, 5)), (-1, (2, 3, 6)), (1, (2, 3, 4)),
])
_RK6_Z1_W = _multichain_pair_weights([(1, (5,))])
_RK6_Z2_W = _multichain_pair_weights([(1, (4,)), (1, (3, 5)), (-1, (3, 4))])
_RK6_Z3_W = _multichain_pair_weights([
    (1, (3,)), (1, (2, 5)), (-1, (2, 3)), (1, (1, 4)), (-1, (1, 3)),
    (1, (1, 3, 5)), (-1, (1, 3, 4)), (-1, (1, 2, 5)), (1, (1, 2, 3)),
])


def z123_from_pair(ag1: dict[tuple[int, ...], int], ag2: dict[tuple[int, ...], int]) -> tuple[int, int, int]:
    """Exact rank-7 Z-polynomial coefficients z1, z2, z3 of M = T(G1 + G2)."""
    z1 = sum(c * ag1[pl] * ag2[pr] for pl, pr, c in _RK7_Z1_W)
    z2 = sum(c * ag1[pl] * ag2[pr] for pl, pr, c in _RK7_Z2_W)
    z3 = sum(c * ag1[pl] * ag2[pr] for pl, pr, c in _RK7_Z3_W)
    return z1, z2, z3


def _build_pconn_orbit_dag(q: int, m: int) -> tuple[list[tuple[str, int, int, int]], list[list[int]]]:
    n1 = q ** 4
    n2 = (q ** 3) * (q ** 3 + q ** 2 + q + 1)
    n3 = (q ** 2) * (q ** 2 + 1) * (q ** 2 + q + 1)
    b1 = (q ** 2) * (q ** 2 + 1)
    m1 = m - 1
    orbs = [
        ("O0", 0, 0, 1), ("O1_p1", 1, 1, 1), ("O1_V", 1, 0, n1), ("O1_ax", 1, 0, m1),
        ("O2_af", 2, 0, n2), ("O2_V1", 2, 1, n1), ("O2_Vp", 2, 0, n1 * m1),
        ("O2_1p", 2, 1, m1), ("O2_pp", 2, 0, comb(m1, 2)),
        ("O3_N", 3, 0, n3 - m * b1), ("O3_B1", 3, 1, b1), ("O3_Bp", 3, 0, m1 * b1),
        ("O3_1V", 3, 1, n1 * m1), ("O3_HV", 3, 0, n1 * comb(m1, 2)),
        ("O3_1A", 3, 1, comb(m1, 2)), ("O3_HA", 3, 0, comb(m1, 3)), ("O4", 4, 1, 1),
    ]
    idx = {o[0]: i for i, o in enumerate(orbs)}
    k_len = len(orbs)
    up = [[0] * k_len for _ in range(k_len)]
    for j in range(1, k_len):
        up[0][j] = orbs[j][3]
    for i in range(k_len - 1):
        up[i][idx["O4"]] = 1
    up[idx["O1_p1"]][idx["O2_V1"]] = n1
    up[idx["O1_p1"]][idx["O2_1p"]] = m1
    up[idx["O1_V"]][idx["O2_af"]] = q ** 3 + q ** 2 + q + 1
    up[idx["O1_V"]][idx["O2_V1"]] = 1
    up[idx["O1_V"]][idx["O2_Vp"]] = m1
    up[idx["O1_ax"]][idx["O2_Vp"]] = n1
    up[idx["O1_ax"]][idx["O2_1p"]] = 1
    up[idx["O1_ax"]][idx["O2_pp"]] = max(0, m1 - 1)
    up[idx["O2_af"]][idx["O3_B1"]] = 1
    up[idx["O2_af"]][idx["O3_Bp"]] = m1
    up[idx["O2_af"]][idx["O3_N"]] = (q ** 2 + q + 1) - m
    up[idx["O2_V1"]][idx["O3_B1"]] = q ** 2 + 1
    up[idx["O2_V1"]][idx["O3_1V"]] = m1
    up[idx["O2_Vp"]][idx["O3_Bp"]] = q ** 2 + 1
    up[idx["O2_Vp"]][idx["O3_1V"]] = 1
    up[idx["O2_Vp"]][idx["O3_HV"]] = max(0, m1 - 1)
    up[idx["O2_1p"]][idx["O3_1V"]] = n1
    up[idx["O2_1p"]][idx["O3_1A"]] = max(0, m1 - 1)
    up[idx["O2_pp"]][idx["O3_HV"]] = n1
    up[idx["O2_pp"]][idx["O3_1A"]] = 1
    up[idx["O2_pp"]][idx["O3_HA"]] = max(0, m1 - 2)
    up[idx["O1_p1"]][idx["O3_B1"]] = b1
    up[idx["O1_p1"]][idx["O3_1V"]] = n1 * m1
    up[idx["O1_p1"]][idx["O3_1A"]] = comb(m1, 2)
    up[idx["O1_V"]][idx["O3_B1"]] = q ** 2 + 1
    up[idx["O1_V"]][idx["O3_Bp"]] = m1 * (q ** 2 + 1)
    up[idx["O1_V"]][idx["O3_N"]] = (q ** 2 + 1) * (q ** 2 + q + 1 - m)
    up[idx["O1_V"]][idx["O3_1V"]] = m1
    up[idx["O1_V"]][idx["O3_HV"]] = comb(m1, 2)
    up[idx["O1_ax"]][idx["O3_Bp"]] = b1
    up[idx["O1_ax"]][idx["O3_1V"]] = n1
    up[idx["O1_ax"]][idx["O3_HV"]] = n1 * max(0, m1 - 1)
    up[idx["O1_ax"]][idx["O3_1A"]] = max(0, m1 - 1)
    up[idx["O1_ax"]][idx["O3_HA"]] = comb(max(0, m1 - 1), 2)
    return orbs, up


def _alpha_pconn_pair(o1, u1, o2, u2, *ranks: int) -> int:
    k_len = len(o1)
    ue1 = [[(1 if i == j else u1[i][j]) for j in range(k_len)] for i in range(k_len)]
    ue2 = [[(1 if i == j else u2[i][j]) for j in range(k_len)] for i in range(k_len)]
    by_prk: dict[int, list[tuple[int, int]]] = {s: [] for s in range(1, 7)}
    for i in range(k_len):
        for j in range(k_len):
            if o1[i][2] == o2[j][2]:
                if o1[i][3] > 0:
                    if o2[j][3] > 0:
                        prk = o1[i][1] + o2[j][1] - o1[i][2]
                        if 1 <= prk <= 6:
                            by_prk[prk].append((i, j))
    dp = {(i, j): o1[i][3] * o2[j][3] for (i, j) in by_prk[ranks[0]]}
    for rn in ranks[1:]:
        ndp: dict[tuple[int, int], int] = {}
        for i2, j2 in by_prk[rn]:
            s_val = 0
            for (i1, j1), cnt in dp.items():
                if ue1[i1][i2]:
                    if ue2[j1][j2]:
                        s_val = s_val + cnt * ue1[i1][i2] * ue2[j1][j2]
            if s_val:
                ndp[(i2, j2)] = s_val
        dp = ndp
    return sum(dp.values())


def _scale_neg1296_exact(coeffs: list[Fraction]) -> list[int]:
    out: list[int] = []
    for coeff in coeffs:
        scaled = -1296 * coeff
        require_ok(scaled.denominator == 1, "NON_INTEGRAL_DEFECT", "scaled defect coefficient not integral")
        out.append(scaled.numerator)
    return out


def _z123_3conn(g1: dict[tuple[int, ...], int], g2: dict[tuple[int, ...], int]) -> tuple[int, int, int]:
    """Exact rank-7 Z-polynomial coefficients z1, z2, z3 of 3-connected T^7(G1 + G2 + U_{1,1})."""
    def alpha(*ranks: int) -> int:
        tot = 0
        for l1 in product(range(5), repeat=len(ranks)):
            if list(l1) != sorted(l1):
                continue
            for l2 in product(range(5), repeat=len(ranks)):
                if list(l2) != sorted(l2):
                    continue
                l3 = tuple(s - i - j for s, i, j in zip(ranks, l1, l2))
                if any(not (0 <= k <= 1) for k in l3):
                    continue
                if list(l3) != sorted(l3):
                    continue
                pl1 = tuple(sorted({r for r in l1 if 0 < r < 4}))
                pl2 = tuple(sorted({r for r in l2 if 0 < r < 4}))
                tot = tot + g1[pl1] * g2[pl2]
        return tot

    z1 = alpha(6)
    z2 = alpha(5) + alpha(4, 6) - alpha(4, 5)
    z3 = (
        alpha(4) + alpha(3, 6) - alpha(3, 4)
        + alpha(2, 5) - alpha(2, 4)
        + alpha(2, 4, 6) - alpha(2, 4, 5)
        - alpha(2, 3, 6) + alpha(2, 3, 4)
    )
    return z1, z2, z3


def _z123_rk6(g1: dict[tuple[int, ...], int], g2: dict[tuple[int, ...], int]) -> tuple[int, int, int]:
    """Exact rank-6 Z-polynomial coefficients z1, z2, z3 of T^6(G1 + G2)."""
    z1 = sum(c * g1[pl] * g2[pr] for pl, pr, c in _RK6_Z1_W)
    z2 = sum(c * g1[pl] * g2[pr] for pl, pr, c in _RK6_Z2_W)
    z3 = sum(c * g1[pl] * g2[pr] for pl, pr, c in _RK6_Z3_W)
    return z1, z2, z3


def _build_pconn_hyperplanes_bitmask(
    hyps1: set[frozenset[int]],
    n1: int,
    hyps2: set[frozenset[int]],
    n2: int,
) -> tuple[int, set[int]]:
    """Construct exact bitmask hyperplanes of parallel connection P(M1, M2) at basepoint 16."""
    def _map1(fl: frozenset[int]) -> int:
        mask = 0
        for elem in fl:
            mask = mask | (1 << elem)
        return mask

    def _map2(fl: frozenset[int]) -> int:
        mask = 0
        for elem in fl:
            if elem == 16:
                mask = mask | (1 << 16)
            elif elem < 16:
                mask = mask | (1 << (n1 + elem))
            else:
                mask = mask | (1 << (n1 + elem - 1))
        return mask

    e1_mask = (1 << n1) - 1
    e2_mask = (((1 << (n2 - 1)) - 1) << n1) | (1 << 16)
    h1_0 = [_map1(h) for h in hyps1 if 16 not in h]
    h1_1 = [_map1(h) for h in hyps1 if 16 in h]
    h2_0 = [_map2(h) for h in hyps2 if 16 not in h]
    h2_1 = [_map2(h) for h in hyps2 if 16 in h]
    hyps = {a | b for a in h1_0 for b in h2_0}
    hyps.update(e1_mask | b for b in h2_1)
    hyps.update(a | e2_mask for a in h1_1)
    return n1 + n2 - 1, hyps


def _verify_bitmask_lattice_and_41_tuples(
    n_elems: int,
    rank: int,
    hyps_set: set[int],
    o1: list[tuple[str, int, int, int]],
    u1: list[list[int]],
    o2: list[tuple[str, int, int, int]],
    u2: list[list[int]],
    all_41_rks: list[tuple[int, ...]],
) -> tuple[int, list[int]]:
    """Build explicit bitmask flat lattice from hyperplanes, check Oxley Prop 2.1.24 covers, and verify all 41 rank tuples."""
    full_e = (1 << n_elems) - 1
    hyps = list(hyps_set)
    n_hyps = len(hyps)
    n_bytes = (n_hyps + 7) // 8
    h_chunks = [bytearray(n_bytes) for _ in range(n_elems)]
    for idx_h, h_mask in enumerate(hyps):
        bi = idx_h >> 3
        bbit = 1 << (idx_h & 7)
        rem_h = h_mask
        while rem_h:
            lsb = rem_h & -rem_h
            elem_i = lsb.bit_length() - 1
            h_chunks[elem_i][bi] = h_chunks[elem_i][bi] | bbit
            rem_h = rem_h ^ lsb
    h_bits = [int.from_bytes(c, "little") for c in h_chunks]
    all_h_mask = (1 << n_hyps) - 1

    r0 = full_e
    for h_mask in hyps:
        r0 = r0 & h_mask
    oxley_bad = 0
    if r0 != 0:
        oxley_bad = oxley_bad + 1

    by_rank: list[set[int]] = [set() for _ in range(rank + 1)]
    by_rank[0] = {0}
    by_rank[rank - 1] = hyps_set
    by_rank[rank] = {full_e}
    cur_layer: dict[int, int] = {0: all_h_mask}
    hmask_of: list[dict[int, int]] = [{} for _ in range(rank + 1)]
    hmask_of[0] = {0: all_h_mask}
    covers_up: list[dict[int, list[int]]] = [{} for _ in range(rank)]

    for rk in range(rank - 2):
        nxt_layer: dict[int, int] = {}
        cup = covers_up[rk]
        for f_mask, f_hmask in cur_layer.items():
            m_rem = full_e ^ f_mask
            covs: list[int] = []
            while m_rem:
                lsb = m_rem & -m_rem
                elem = lsb.bit_length() - 1
                g_hmask = f_hmask & h_bits[elem]
                g_mask = nxt_layer.get(g_hmask)
                if g_mask is None:
                    g_mask = full_e
                    hm = g_hmask
                    while hm:
                        hl = hm & -hm
                        g_mask = g_mask & hyps[hl.bit_length() - 1]
                        hm = hm ^ hl
                    nxt_layer[g_hmask] = g_mask
                covs.append(g_mask)
                m_rem = m_rem & ~g_mask
            cup[f_mask] = covs
        by_rank[rk + 1] = set(nxt_layer.values())
        cur_layer = {g_m: hm for hm, g_m in nxt_layer.items()}
        hmask_of[rk + 1] = cur_layer

    cup_top = covers_up[rank - 2]
    for f_mask, f_hmask in cur_layer.items():
        covs = []
        hm = f_hmask
        while hm:
            hl = hm & -hm
            covs.append(hyps[hl.bit_length() - 1])
            hm = hm ^ hl
        cup_top[f_mask] = covs
    covers_up[rank - 1] = {h_mask: [full_e] for h_mask in hyps}

    for rk in range(rank):
        upper = by_rank[rk + 1]
        for f_mask in by_rank[rk]:
            covs = covers_up[rk][f_mask]
            tot_diff = 0
            u_diff = 0
            for g_mask in covs:
                if g_mask not in upper:
                    oxley_bad = oxley_bad + 1
                if (f_mask & g_mask) != f_mask:
                    oxley_bad = oxley_bad + 1
                diff = g_mask ^ f_mask
                tot_diff = tot_diff + diff.bit_count()
                u_diff = u_diff | diff
            rem_e = full_e ^ f_mask
            if tot_diff != rem_e.bit_count():
                oxley_bad = oxley_bad + 1
            if u_diff != rem_e:
                oxley_bad = oxley_bad + 1
    require_ok(oxley_bad == 0, "PCONN_RK7_OXLEY_FAIL", "explicit rank-7 lattice failed Oxley Prop 2.1.24 cover check")

    covers_down: list[dict[int, list[int]]] = [{} for _ in range(rank + 1)]
    for rk in range(rank):
        for f_mask, covs in covers_up[rk].items():
            for g_mask in covs:
                covers_down[rk + 1].setdefault(g_mask, []).append(f_mask)

    down_cnt = [{g_m: [0] * 6 for g_m in by_rank[r]} for r in range(rank)]
    up_cnt = [{f_m: [0] * 7 for f_m in by_rank[r]} for r in range(rank)]
    alpha2: dict[tuple[int, int], int] = {}
    for r1 in range(1, rank - 1):
        for f_mask, hm in hmask_of[r1].items():
            up_cnt[r1][f_mask][6] = hm.bit_count()
        alpha2[(r1, 6)] = sum(up_cnt[r1][f_m][6] for f_m in by_rank[r1])
    for r2 in range(2, rank - 1):
        cd_r2 = covers_down[r2]
        for g_mask in by_rank[r2]:
            layer = set(cd_r2[g_mask])
            for r1 in range(r2 - 1, 0, -1):
                dc = len(layer)
                down_cnt[r2][g_mask][r1] = dc
                alpha2[(r1, r2)] = alpha2.get((r1, r2), 0) + dc
                uc_r1 = up_cnt[r1]
                for f_mask in layer:
                    uc_r1[f_mask][r2] = uc_r1[f_mask][r2] + 1
                nxt: set[int] = set()
                cd_r1 = covers_down[r1]
                for f_mask in layer:
                    nxt.update(cd_r1[f_mask])
                layer = nxt

    mismatches = 0
    for rks in all_41_rks:
        if len(rks) == 1:
            cnt = len(by_rank[rks[0]])
        elif len(rks) == 2:
            cnt = alpha2[rks]
        else:
            r1, r2, r3 = rks
            cnt = sum(down_cnt[r2][f2][r1] * up_cnt[r2][f2][r3] for f2 in by_rank[r2])
        if cnt != _alpha_pconn_pair(o1, u1, o2, u2, *rks):
            mismatches = mismatches + 1

    flat_counts = [len(by_rank[r]) for r in range(rank + 1)]
    return mismatches, flat_counts


def verify_universal_shifts_and_witnesses(tamper: str | None = None) -> dict[str, object]:
    """Verify exact Q-polynomial Taylor shifts at q = 27 + s, parallel connection DAG, and all witnesses."""
    def qpow_q(k: int) -> list[Fraction]:
        return [Fraction(0)] * k + [Fraction(1)]

    def bin2_q(m_p: list[Fraction]) -> list[Fraction]:
        return _p_mul_q([Fraction(1, 2)], _p_mul_q(m_p, _p_sub_q(m_p, [Fraction(1)])))

    def bin3_q(m_p: list[Fraction]) -> list[Fraction]:
        return _p_mul_q([Fraction(1, 6)], _p_mul_q(m_p, _p_mul_q(_p_sub_q(m_p, [Fraction(1)]), _p_sub_q(m_p, [Fraction(2)]))))

    def z123_poly_q(ag_p: dict[tuple[int, ...], list[Fraction]]) -> tuple[list[Fraction], list[Fraction], list[Fraction]]:
        def alpha_p(*ranks: int) -> list[Fraction]:
            tot = [Fraction(0)]
            for left in product(range(5), repeat=len(ranks)):
                right = tuple(s - i for s, i in zip(ranks, left))
                if any(not (0 <= j <= 4) for j in right):
                    continue
                if list(left) != sorted(left):
                    continue
                if list(right) != sorted(right):
                    continue
                pl = tuple(sorted({r for r in left if 0 < r < 4}))
                pr = tuple(sorted({r for r in right if 0 < r < 4}))
                tot = _p_add_q(tot, _p_mul_q(ag_p[pl], ag_p[pr]))
            return tot

        z1 = alpha_p(6)
        z2 = _p_sub_q(_p_add_q(alpha_p(5), alpha_p(4, 6)), alpha_p(4, 5))
        z3 = alpha_p(4)
        for sgn, rks in [(1, (3, 6)), (-1, (3, 4)), (1, (2, 5)), (-1, (2, 4)), (1, (2, 4, 6)), (-1, (2, 4, 5)), (-1, (2, 3, 6)), (1, (2, 3, 4))]:
            term = alpha_p(*rks)
            z3 = _p_add_q(z3, term) if sgn == 1 else _p_sub_q(z3, term)
        return z1, z2, z3

    q_var = [Fraction(0), Fraction(1)]
    m_pg, b_pg = qpow_q(3), qpow_q(9)
    n1_pg, n2_pg, n3_pg = _q_gauss_poly(6, 1), _q_gauss_poly(6, 2), _q_gauss_poly(6, 3)
    t_pg = [Fraction(1), Fraction(1), Fraction(1)]
    ht_pg = [
        (_p_add_q(_p_mul_q(n1_pg, bin2_q(m_pg)), bin3_q(m_pg)), [Fraction(3)], [Fraction(3)], [Fraction(6)]),
        (b_pg, _p_add_q(t_pg, [Fraction(1)]), _p_mul_q([Fraction(2)], t_pg), _p_mul_q([Fraction(3), Fraction(1)], t_pg)),
        (_p_sub_q(_p_mul_q(m_pg, n2_pg), _p_mul_q(b_pg, t_pg)), [Fraction(2), Fraction(1)], [Fraction(2), Fraction(1)], [Fraction(3), Fraction(3)]),
        (_p_sub_q(n3_pg, b_pg), t_pg, t_pg, _p_mul_q([Fraction(1), Fraction(1)], t_pg)),
    ]
    ag_pg = {
        (): [Fraction(1)],
        (1,): _p_add_q(n1_pg, m_pg),
        (2,): _p_add_q(n2_pg, _p_add_q(_p_mul_q(n1_pg, m_pg), bin2_q(m_pg))),
        (3,): [Fraction(0)],
        (1, 2): _p_add_q(_p_mul_q([Fraction(1), Fraction(1)], n2_pg), _p_mul_q([Fraction(2)], _p_add_q(_p_mul_q(n1_pg, m_pg), bin2_q(m_pg)))),
        (1, 3): [Fraction(0)], (2, 3): [Fraction(0)], (1, 2, 3): [Fraction(0)],
    }
    for n_p, pt_p, ln_p, fl_p in ht_pg:
        ag_pg[(3,)] = _p_add_q(ag_pg[(3,)], n_p)
        ag_pg[(1, 3)] = _p_add_q(ag_pg[(1, 3)], _p_mul_q(n_p, pt_p))
        ag_pg[(2, 3)] = _p_add_q(ag_pg[(2, 3)], _p_mul_q(n_p, ln_p))
        ag_pg[(1, 2, 3)] = _p_add_q(ag_pg[(1, 2, 3)], _p_mul_q(n_p, fl_p))
    z1_pg, z2_pg, z3_pg = z123_poly_q(ag_pg)
    d_pg = _p_sub_q(_p_mul_q(z2_pg, z2_pg), _p_mul_q(z1_pg, z3_pg))
    sh_pg = _scale_neg1296_exact(_p_shift_q(d_pg, 27))

    m_el, b_el = qpow_q(2), qpow_q(6)
    n1_el, n2_el, n3_el = qpow_q(4), _p_mul_q(qpow_q(3), _q_gauss_poly(4, 1)), _p_mul_q(qpow_q(2), _q_gauss_poly(4, 2))
    ht_el = [
        (_p_add_q(_p_mul_q(n1_el, bin2_q(m_el)), bin3_q(m_el)), [Fraction(3)], [Fraction(3)], [Fraction(6)]),
        (b_el, [Fraction(1), Fraction(0), Fraction(1)], [Fraction(0), Fraction(1), Fraction(2)], [Fraction(0), Fraction(0), Fraction(3), Fraction(1)]),
        (_p_sub_q(_p_mul_q(m_el, n2_el), _p_mul_q(b_el, [Fraction(0), Fraction(1), Fraction(1)])), [Fraction(1), Fraction(1)], [Fraction(1), Fraction(1)], [Fraction(0), Fraction(3)]),
        (_p_sub_q(n3_el, b_el), qpow_q(2), [Fraction(0), Fraction(1), Fraction(1)], [Fraction(0), Fraction(0), Fraction(1), Fraction(1)]),
    ]
    ag_el = {
        (): [Fraction(1)],
        (1,): _p_add_q(n1_el, m_el),
        (2,): _p_add_q(n2_el, _p_add_q(_p_mul_q(n1_el, m_el), bin2_q(m_el))),
        (3,): [Fraction(0)],
        (1, 2): _p_add_q(_p_mul_q(q_var, n2_el), _p_mul_q([Fraction(2)], _p_add_q(_p_mul_q(n1_el, m_el), bin2_q(m_el)))),
        (1, 3): [Fraction(0)], (2, 3): [Fraction(0)], (1, 2, 3): [Fraction(0)],
    }
    for n_p, pt_p, ln_p, fl_p in ht_el:
        ag_el[(3,)] = _p_add_q(ag_el[(3,)], n_p)
        ag_el[(1, 3)] = _p_add_q(ag_el[(1, 3)], _p_mul_q(n_p, pt_p))
        ag_el[(2, 3)] = _p_add_q(ag_el[(2, 3)], _p_mul_q(n_p, ln_p))
        ag_el[(1, 2, 3)] = _p_add_q(ag_el[(1, 2, 3)], _p_mul_q(n_p, fl_p))
    z1_el, z2_el, z3_el = z123_poly_q(ag_el)
    d_el = _p_sub_q(_p_mul_q(z2_el, z2_el), _p_mul_q(z1_el, z3_el))
    sh_el = _scale_neg1296_exact(_p_shift_q(d_el, 27))

    min_pg = min(sh_pg)
    min_el = min(sh_el)
    if tamper == "pg_zero":
        min_pg = 0
    if tamper == "el_zero":
        min_el = 0
    require_ok(min_pg > 0, "PG_SHIFT_NONPOS", "-1296*D_pg(27+s) must have strictly positive coefficients")
    require_ok(min_el > 0, "EL_SHIFT_NONPOS", "-1296*D_el(27+s) must have strictly positive coefficients")

    # Verify 17-orbit parallel connection DAG against:
    # (a) rank-4 L(M_{2,m}) basepoint-paired flag sums across m in {1, 2, 3, 4} (all 17/17 orbits active at m=4), and
    # (b) explicit un-quotiented rank-7 bitmask flat lattices L(P(M_{2,1}, M_{2,1})) and L(P(M_{2,1}, M_{2,2}))
    # across all 41 rank tuples (k <= 3) using an explicit 7-spread parallelism of PG(3, 2).
    pts3 = list(range(1, 16))
    lines3 = sorted({tuple(sorted([a, b, a ^ b])) for a in pts3 for b in pts3 if a < b})
    spreads_q2 = [list(c) for c in combinations(lines3, 5) if len({p for ln in c for p in ln}) == 15]

    def _find_par7(used: set[tuple[int, int, int]], chosen: list[list[tuple[int, int, int]]], idx_s: int) -> list[list[tuple[int, int, int]]] | None:
        if len(chosen) == 7:
            return chosen
        for i_sp in range(idx_s, len(spreads_q2)):
            sp = spreads_q2[i_sp]
            if all(ln not in used for ln in sp):
                res = _find_par7(used | set(sp), chosen + [sp], i_sp + 1)
                if res is not None:
                    return res
        return None

    par7 = _find_par7(set(), [], 0)
    aff_p2 = {frozenset([i, j, k, i ^ j ^ k]) for i in range(16) for j in range(i + 1, 16) for k in range(j + 1, 16)}
    all_41_rks = [sub for k_len in range(1, 4) for sub in combinations(range(1, 7), k_len)]
    pconn_bad = 0
    max_active_orbs = 0
    hyps_q2_by_m: dict[int, set[frozenset[int]]] = {}
    dag_q2_by_m: dict[int, tuple[list[tuple[str, int, int, int]], list[list[int]]]] = {}
    for m_q2 in (1, 2, 3, 4):
        pl_by_c = [
            {frozenset(v0 ^ w for w in {0, ln[0], ln[1], ln[2]}) for ln in par7[c_idx] for v0 in range(16)}
            for c_idx in range(m_q2)
        ]
        chosen_pl = set().union(*pl_by_c)
        hyps_mq = set(aff_p2 - chosen_pl)
        for c_idx in range(m_q2):
            pc = 16 + c_idx
            for pl in pl_by_c[c_idx]:
                hyps_mq.add(pl | {pc})
        for x_pt in range(16):
            for a_i in range(m_q2):
                for b_i in range(a_i + 1, m_q2):
                    hyps_mq.add(frozenset([x_pt, 16 + a_i, 16 + b_i]))
        for a_i in range(m_q2):
            for b_i in range(a_i + 1, m_q2):
                for c_i in range(b_i + 1, m_q2):
                    hyps_mq.add(frozenset([16 + a_i, 16 + b_i, 16 + c_i]))
        hyps_q2_by_m[m_q2] = hyps_mq
        lat_mq = build_lattice_from_hyperplanes(16 + m_q2, 4, hyps_mq)
        by_rt: dict[tuple[int, int], list[frozenset[int]]] = {}
        for rk_f, fs_set in lat_mq.items():
            for fl_set in fs_set:
                by_rt.setdefault((rk_f, 1 if 16 in fl_set else 0), []).append(fl_set)
        memo_q2: dict[tuple[tuple[int, int], ...], int] = {}

        def _count_weak(rt_seq: tuple[tuple[int, int], ...]) -> int:
            if rt_seq in memo_q2:
                return memo_q2[rt_seq]
            cur_d = {fl_s: 1 for fl_s in by_rt.get(rt_seq[0], [])}
            for rt_nxt in rt_seq[1:]:
                cands_nxt = by_rt.get(rt_nxt, [])
                nxt_d: dict[frozenset[int], int] = {}
                for g_s in cands_nxt:
                    s_c = sum(cnt_v for f_s, cnt_v in cur_d.items() if f_s.issubset(g_s))
                    if s_c:
                        nxt_d[g_s] = s_c
                cur_d = nxt_d
            ans = sum(cur_d.values())
            memo_q2[rt_seq] = ans
            return ans

        def _alpha_ex_lp(*rks: int) -> int:
            k_r = len(rks)
            tot_c = 0
            for t_seq in product((0, 1), repeat=k_r):
                if list(t_seq) != sorted(t_seq):
                    continue
                for r1_seq in product(range(5), repeat=k_r):
                    if list(r1_seq) != sorted(r1_seq):
                        continue
                    r2_seq = tuple(rks[i_k] + t_seq[i_k] - r1_seq[i_k] for i_k in range(k_r))
                    if any(not (0 <= r_v <= 4) for r_v in r2_seq):
                        continue
                    if list(r2_seq) != sorted(r2_seq):
                        continue
                    s1_seq = tuple(zip(r1_seq, t_seq))
                    s2_seq = tuple(zip(r2_seq, t_seq))
                    bad_rt = False
                    for r_v, t_v in s1_seq:
                        if r_v == 0:
                            if t_v == 1:
                                bad_rt = True
                        if r_v == 4:
                            if t_v == 0:
                                bad_rt = True
                    for r_v, t_v in s2_seq:
                        if r_v == 0:
                            if t_v == 1:
                                bad_rt = True
                        if r_v == 4:
                            if t_v == 0:
                                bad_rt = True
                    if bad_rt:
                        continue
                    tot_c = tot_c + _count_weak(s1_seq) * _count_weak(s2_seq)
            return tot_c

        o_q2, u_q2 = _build_pconn_orbit_dag(2, m_q2)
        dag_q2_by_m[m_q2] = (o_q2, u_q2)
        active_orbs = sum(1 for orb in o_q2 if orb[3] > 0)
        if active_orbs > max_active_orbs:
            max_active_orbs = active_orbs
        for rks in all_41_rks:
            if _alpha_ex_lp(*rks) != _alpha_pconn_pair(o_q2, u_q2, o_q2, u_q2, *rks):
                pconn_bad = pconn_bad + 1
    if tamper == "pconn":
        pconn_bad = 1
    require_ok(pconn_bad == 0, "PCONN_DAG_MISMATCH", "17-orbit parallel connection DAG failed q=2 lattice check")

    # Exact full range sweeps and negative controls (pure Z/Q, zero floats)
    ag27_fails: list[int] = []
    ag27_min_r: Fraction | None = None
    ag27_min_m = -1
    for m_s in range(0, 730):
        g_s = affine_coalesced_alpha(27, m_s, 729)
        z1_s, z2_s, z3_s = z123_from_pair(g_s, g_s)
        r_s = Fraction(z2_s * z2_s, z1_s * z3_s)
        if z2_s * z2_s < z1_s * z3_s:
            ag27_fails.append(m_s)
        if ag27_min_r is None:
            ag27_min_r = r_s
            ag27_min_m = m_s
        elif r_s < ag27_min_r:
            ag27_min_r = r_s
            ag27_min_m = m_s

    ag25_sp_fails: list[int] = []
    ag25_sp_min_r: Fraction | None = None
    ag25_sp_min_m = -1
    for m_s in range(0, 652):
        g_s = affine_coalesced_alpha(25, m_s, 626)
        z1_s, z2_s, z3_s = z123_from_pair(g_s, g_s)
        r_s = Fraction(z2_s * z2_s, z1_s * z3_s)
        if z2_s * z2_s < z1_s * z3_s:
            ag25_sp_fails.append(m_s)
        if ag25_sp_min_r is None:
            ag25_sp_min_r = r_s
            ag25_sp_min_m = m_s
        elif r_s < ag25_sp_min_r:
            ag25_sp_min_r = r_s
            ag25_sp_min_m = m_s

    part25_fails = 0
    part25_min_r: Fraction | None = None
    part25_min_m = -1
    part25_m625_r = Fraction(0)
    for m_s in range(1, 626):
        g_s = affine_coalesced_alpha(25, m_s, 625)
        z1_s, z2_s, z3_s = z123_from_pair(g_s, g_s)
        r_s = Fraction(z2_s * z2_s, z1_s * z3_s)
        if m_s == 625:
            part25_m625_r = r_s
        if z2_s * z2_s < z1_s * z3_s:
            part25_fails = part25_fails + 1
        if part25_min_r is None:
            part25_min_r = r_s
            part25_min_m = m_s
        elif r_s < part25_min_r:
            part25_min_r = r_s
            part25_min_m = m_s

    q23_t_fails = 0
    q23_t_min_r: Fraction | None = None
    q23_t_min_m = -1
    for m_s in range(1, 554):
        g_s = affine_coalesced_alpha(23, m_s, 530)
        z1_s, z2_s, z3_s = z123_from_pair(g_s, g_s)
        r_s = Fraction(z2_s * z2_s, z1_s * z3_s)
        if z2_s * z2_s < z1_s * z3_s:
            q23_t_fails = q23_t_fails + 1
        if q23_t_min_r is None:
            q23_t_min_r = r_s
            q23_t_min_m = m_s
        elif r_s < q23_t_min_r:
            q23_t_min_r = r_s
            q23_t_min_m = m_s

    def pconn_ratio(q1: int, m1: int, q2: int, m2: int) -> tuple[int, int, int, Fraction]:
        o1, u1 = _build_pconn_orbit_dag(q1, m1)
        o2, u2 = _build_pconn_orbit_dag(q2, m2)
        k_len = len(o1)
        ue1 = [[(1 if i == j else u1[i][j]) for j in range(k_len)] for i in range(k_len)]
        ue2 = [[(1 if i == j else u2[i][j]) for j in range(k_len)] for i in range(k_len)]
        by_prk: dict[int, list[tuple[int, int]]] = {s: [] for s in range(1, 7)}
        for i in range(k_len):
            for j in range(k_len):
                if o1[i][2] == o2[j][2]:
                    if o1[i][3] > 0:
                        if o2[j][3] > 0:
                            prk = o1[i][1] + o2[j][1] - o1[i][2]
                            if 1 <= prk <= 6:
                                by_prk[prk].append((i, j))

        def ap(*ranks: int) -> int:
            dp = {(i, j): o1[i][3] * o2[j][3] for (i, j) in by_prk[ranks[0]]}
            for rn in ranks[1:]:
                ndp: dict[tuple[int, int], int] = {}
                for i2, j2 in by_prk[rn]:
                    s_val = 0
                    for (i1, j1), cnt in dp.items():
                        v1 = ue1[i1][i2]
                        if v1:
                            v2 = ue2[j1][j2]
                            if v2:
                                s_val = s_val + cnt * v1 * v2
                    if s_val:
                        ndp[(i2, j2)] = s_val
                dp = ndp
            return sum(dp.values())

        z1_p = ap(6)
        z2_p = ap(5) + ap(4, 6) - ap(4, 5)
        z3_p = ap(4) + ap(3, 6) - ap(3, 4) + ap(2, 5) - ap(2, 4) + ap(2, 4, 6) - ap(2, 4, 5) - ap(2, 3, 6) + ap(2, 3, 4)
        return z1_p, z2_p, z3_p, Fraction(z2_p * z2_p, z1_p * z3_p)

    q23_p_fails = 0
    q23_p_min_r: Fraction | None = None
    q23_p_min_m = -1
    for m_s in range(1, 554):
        z1_p, z2_p, z3_p, r_p = pconn_ratio(23, m_s, 23, m_s)
        if z2_p * z2_p < z1_p * z3_p:
            q23_p_fails = q23_p_fails + 1
        if q23_p_min_r is None:
            q23_p_min_r = r_p
            q23_p_min_m = m_s
        elif r_p < q23_p_min_r:
            q23_p_min_r = r_p
            q23_p_min_m = m_s

    _, _, _, mixed_p_537_461 = pconn_ratio(25, 537, 23, 461)
    _, _, _, mixed_p_538_461 = pconn_ratio(25, 538, 23, 461)

    g25_537 = affine_coalesced_alpha(25, 537, 626)
    z1_3c, z2_3c, z3_3c = _z123_3conn(g25_537, g25_537)
    r_3c = Fraction(z2_3c * z2_3c, z1_3c * z3_3c)

    rk6_fails = 0
    rk6_min_z2_r: Fraction | None = None
    rk6_min_z2_m = -1
    rk6_min_z3_r: Fraction | None = None
    rk6_m626_z2_r = Fraction(0)
    for m_s in range(1, 652):
        g_s = affine_coalesced_alpha(25, m_s, 626)
        z1_6, z2_6, z3_6 = _z123_rk6(g_s, g_s)
        r2_6 = Fraction(z2_6 * z2_6, z1_6 * z3_6)
        r3_6 = Fraction(z3_6 * z3_6, z2_6 * z2_6)
        if z2_6 * z2_6 < z1_6 * z3_6:
            rk6_fails = rk6_fails + 1
        if z3_6 * z3_6 < z2_6 * z2_6:
            rk6_fails = rk6_fails + 1
        if m_s == 626:
            rk6_m626_z2_r = r2_6
        if rk6_min_z2_r is None:
            rk6_min_z2_r = r2_6
            rk6_min_z2_m = m_s
            rk6_min_z3_r = r3_6
        else:
            if r2_6 < rk6_min_z2_r:
                rk6_min_z2_r = r2_6
                rk6_min_z2_m = m_s
            if r3_6 < rk6_min_z3_r:
                rk6_min_z3_r = r3_6

    sweep_bad = 0
    if ag27_fails != list(range(461, 730)):
        sweep_bad = sweep_bad + 1
    if ag25_sp_fails != list(range(510, 566)):
        sweep_bad = sweep_bad + 1
    if part25_fails != 0:
        sweep_bad = sweep_bad + 1
    if q23_t_fails != 0:
        sweep_bad = sweep_bad + 1
    if q23_p_fails != 0:
        sweep_bad = sweep_bad + 1
    if rk6_fails != 0:
        sweep_bad = sweep_bad + 1
    if mixed_p_538_461 <= 1:
        sweep_bad = sweep_bad + 1
    if r_3c <= 1:
        sweep_bad = sweep_bad + 1
    if tamper == "sweep":
        sweep_bad = 1
    require_ok(sweep_bad == 0, "SWEEP_CONTROL_FAIL", "exact range sweep or negative control verification failed")

    # Key witnesses
    def witness_entry(g1: dict[tuple[int, ...], int], g2: dict[tuple[int, ...], int]) -> dict[str, object]:
        z1, z2, z3 = z123_from_pair(g1, g2)
        diff = z2 * z2 - z1 * z3
        return {
            "ground_set": g1[(1,)] + g2[(1,)],
            "z1": z1,
            "z2": z2,
            "z3": z3,
            "z2_sq_minus_z1_z3": diff,
            "ratio_z2sq_over_z1z3": frac_str(Fraction(z2 * z2, z1 * z3)),
            "fails_log_concavity": diff < 0,
        }

    def pconn_witness(q1: int, m1: int, q2: int, m2: int) -> dict[str, object]:
        o1, u1 = _build_pconn_orbit_dag(q1, m1)
        o2, u2 = _build_pconn_orbit_dag(q2, m2)
        ap = lambda *r: _alpha_pconn_pair(o1, u1, o2, u2, *r)
        z1 = ap(6)
        z2 = ap(5) + ap(4, 6) - ap(4, 5)
        z3 = ap(4) + ap(3, 6) - ap(3, 4) + ap(2, 5) - ap(2, 4) + ap(2, 4, 6) - ap(2, 4, 5) - ap(2, 3, 6) + ap(2, 3, 4)
        diff = z2 * z2 - z1 * z3
        return {
            "ground_set": (q1 ** 4 + m1) + (q2 ** 4 + m2) - 1,
            "z1": z1,
            "z2": z2,
            "z3": z3,
            "z2_sq_minus_z1_z3": diff,
            "ratio_z2sq_over_z1z3": frac_str(Fraction(z2 * z2, z1 * z3)),
            "fails_log_concavity": diff < 0,
        }

    witnesses = {
        "pg5_q27_m19683_guoriyue": witness_entry(proj_gabidulin_alpha(27, 19683), proj_gabidulin_alpha(27, 19683)),
        "pg5_q25_m15625_full_control": witness_entry(proj_gabidulin_alpha(25, 15625), proj_gabidulin_alpha(25, 15625)),
        "pg5_q25_m13000_subset": witness_entry(proj_gabidulin_alpha(25, 13000), proj_gabidulin_alpha(25, 13000)),
        "ag4_elem_q27_m729": witness_entry(affine_coalesced_alpha(27, 729, 729), affine_coalesced_alpha(27, 729, 729)),
        "ag4_elem_q27_m618": witness_entry(affine_coalesced_alpha(27, 618, 729), affine_coalesced_alpha(27, 618, 729)),
        "ag4_elem_q27_m461_threshold": witness_entry(affine_coalesced_alpha(27, 461, 729), affine_coalesced_alpha(27, 461, 729)),
        "ag4_elem_asym_q27m510_q25m456": witness_entry(affine_coalesced_alpha(27, 510, 729), affine_coalesced_alpha(25, 456, 625)),
        "ag4_spread_q25_m537_submillion": witness_entry(affine_coalesced_alpha(25, 537, 626), affine_coalesced_alpha(25, 537, 626)),
        "ag4_spread_q25_m510_threshold": witness_entry(affine_coalesced_alpha(25, 510, 626), affine_coalesced_alpha(25, 510, 626)),
        "ag4_pconn_q25_m537": pconn_witness(25, 537, 25, 537),
        "ag4_pconn_asym_q25_m496_m497": pconn_witness(25, 496, 25, 497),
        "ag4_spread_q23_m461_control": witness_entry(affine_coalesced_alpha(23, 461, 530), affine_coalesced_alpha(23, 461, 530)),
    }

    expected_failures = {
        "pg5_q27_m19683_guoriyue": True,
        "pg5_q25_m15625_full_control": False,
        "pg5_q25_m13000_subset": True,
        "ag4_elem_q27_m729": True,
        "ag4_elem_q27_m618": True,
        "ag4_elem_q27_m461_threshold": True,
        "ag4_elem_asym_q27m510_q25m456": True,
        "ag4_spread_q25_m537_submillion": True,
        "ag4_spread_q25_m510_threshold": True,
        "ag4_pconn_q25_m537": True,
        "ag4_pconn_asym_q25_m496_m497": True,
        "ag4_spread_q23_m461_control": False,
    }
    wit_bad = sum(1 for k, exp_f in expected_failures.items() if witnesses[k]["fails_log_concavity"] is not exp_f)
    if tamper == "witness":
        wit_bad = 1
    require_ok(wit_bad == 0, "WITNESS_CHECK_FAIL", "witness log-concavity sign mismatch")

    # Explicit true rank-7 bitmask flat-lattice verification of L(P(M_{2,1}, M_{2,1})) and L(P(M_{2,1}, M_{2,2}))
    o_q2_1, u_q2_1 = dag_q2_by_m[1]
    o_q2_2, u_q2_2 = dag_q2_by_m[2]
    rk7_11_n, rk7_11_hyps_set = _build_pconn_hyperplanes_bitmask(hyps_q2_by_m[1], 17, hyps_q2_by_m[1], 17)
    rk7_11_bad, rk7_11_counts = _verify_bitmask_lattice_and_41_tuples(
        rk7_11_n, 7, rk7_11_hyps_set, o_q2_1, u_q2_1, o_q2_1, u_q2_1, all_41_rks
    )
    rk7_12_n, rk7_12_hyps_set = _build_pconn_hyperplanes_bitmask(hyps_q2_by_m[1], 17, hyps_q2_by_m[2], 18)
    rk7_12_bad, rk7_12_counts = _verify_bitmask_lattice_and_41_tuples(
        rk7_12_n, 7, rk7_12_hyps_set, o_q2_1, u_q2_1, o_q2_2, u_q2_2, all_41_rks
    )
    rk7_bad = rk7_11_bad + rk7_12_bad
    if tamper == "pconn_rk7":
        rk7_bad = rk7_bad + 1
    require_ok(rk7_bad == 0, "PCONN_RK7_MISMATCH", "explicit rank-7 L(P(M_{2,1},M_{2,m})) flag mismatch")

    e_z123 = 29840942
    r_elem_618 = Fraction(e_z123, 1064118)
    r_elem_asym = Fraction(e_z123, 923032)
    r_sp_537 = Fraction(e_z123, 782324)
    r_pconn_496 = Fraction(e_z123, 782242)
    return {
        "pg5_defect1296_degree": len(d_pg) - 1,
        "pg5_neg_shift27_coeffs_count": len(sh_pg),
        "pg5_neg_shift27_min_coeff": min_pg,
        "pg5_neg_shift27_lead_coeff": sh_pg[-1],
        "ag4_elem_defect1296_degree": len(d_el) - 1,
        "ag4_elem_neg_shift27_coeffs_count": len(sh_el),
        "ag4_elem_neg_shift27_min_coeff": min_el,
        "ag4_elem_neg_shift27_lead_coeff": sh_el[-1],
        "shrinkage_ratios_vs_z123": {
            "ag4_elem_q27_m618": frac_str(r_elem_618),
            "ag4_elem_asym_q27_q25": frac_str(r_elem_asym),
            "ag4_spread_q25_m537": frac_str(r_sp_537),
            "ag4_pconn_q25_m496_m497": frac_str(r_pconn_496),
        },
        "pconn_q2_verification": {
            "m_values": [1, 2, 3, 4],
            "rank_tuples_per_m": len(all_41_rks),
            "max_active_orbits": max_active_orbs,
            "mismatches": pconn_bad,
            "rank7_explicit_pairs": [[1, 1], [1, 2]],
            "rank7_explicit_ground_sets": [rk7_11_n, rk7_12_n],
            "rank7_explicit_hyperplanes": [len(rk7_11_hyps_set), len(rk7_12_hyps_set)],
            "rank7_explicit_flat_counts": [rk7_11_counts, rk7_12_counts],
            "rank7_explicit_mismatches": rk7_bad,
        },
        "range_sweeps": {
            "ag4_elem_q27_s729": {
                "m_min": 0,
                "m_max": 729,
                "fail_min_m": ag27_fails[0],
                "fail_max_m": ag27_fails[-1],
                "fail_count": len(ag27_fails),
                "min_ratio_m": ag27_min_m,
                "min_ratio": frac_str(ag27_min_r),
            },
            "ag4_spread_q25_s626": {
                "m_min": 0,
                "m_max": 651,
                "fail_min_m": ag25_sp_fails[0],
                "fail_max_m": ag25_sp_fails[-1],
                "fail_count": len(ag25_sp_fails),
                "min_ratio_m": ag25_sp_min_m,
                "min_ratio": frac_str(ag25_sp_min_r),
            },
        },
        "negative_controls": {
            "ag4_partial_q25_s625_sweep": {
                "m_min": 1,
                "m_max": 625,
                "fail_count": part25_fails,
                "min_ratio_m": part25_min_m,
                "min_ratio": frac_str(part25_min_r),
                "m625_ratio": frac_str(part25_m625_r),
            },
            "ag4_spread_q23_T_sweep": {
                "m_min": 1,
                "m_max": 553,
                "fail_count": q23_t_fails,
                "min_ratio_m": q23_t_min_m,
                "min_ratio": frac_str(q23_t_min_r),
            },
            "ag4_spread_q23_P_sweep": {
                "m_min": 1,
                "m_max": 553,
                "fail_count": q23_p_fails,
                "min_ratio_m": q23_p_min_m,
                "min_ratio": frac_str(q23_p_min_r),
            },
            "ag4_pconn_mixed_q25_q23": {
                "m537_m461_ratio": frac_str(mixed_p_537_461),
                "m538_m461_ratio": frac_str(mixed_p_538_461),
            },
            "ag4_3conn_q25_m537": {
                "ground_set": 2 * g25_537[(1,)] + 1,
                "ratio_z2sq_over_z1z3": frac_str(r_3c),
            },
            "ag4_rk6_q25_sweep": {
                "m_min": 1,
                "m_max": 651,
                "fail_count": rk6_fails,
                "min_z2_ratio_m": rk6_min_z2_m,
                "min_z2_ratio": frac_str(rk6_min_z2_r),
                "m626_z2_ratio": frac_str(rk6_m626_z2_r),
                "min_z3_ratio": frac_str(rk6_min_z3_r),
            },
        },
        "witnesses": witnesses,
    }


class _FailClosedOracleParser(argparse.ArgumentParser):
    def error(self, message: str) -> None:
        raise ZPolyError("BAD_ORACLE_ARGS", message)


def compute_oracle_sections() -> dict[str, object]:
    """Run all four pure-Z/Q mathematical audit pillars and return canonical dict."""
    return {
        "pillar1_epw_kl_zpoly_audit": verify_epw_kl_and_zpoly_audit(),
        "pillar2_finite_gabidulin_ground_truth": verify_finite_a42_and_a43(),
        "pillar3_explicit_pg3_25_spread_packing": verify_pg3_q25_parallelism(),
        "pillar4_prior_art_law4": {
            "novelty_classification": NOVELTY_CLASS,
            "n2_claims": 0,
            "bcel_arxiv_2610_17135_zpoly_mentions": 0,
            "cheng_liu_arxiv_2607_24186_zpoly_equals_full_pg": True,
            "solved_conjectures_matroid_zpoly_entries": 0,
            "portal_guoriyue_z123_commit": "0b23a1c9d4618df8af1f454e917ff4ac0b1e171f",
        },
        "pillar5_shifts_and_witnesses": verify_universal_shifts_and_witnesses(),
    }


def run_oracle_cli(argv: list[str] | None = None) -> int:
    parser = _FailClosedOracleParser(
        description="Track S161 EXP-Q44a pure-Z/Q Z-polynomial oracle",
        add_help=False,
        allow_abbrev=False,
    )
    parser.add_argument("--json", action="store_true", dest="json_out")
    args, unknown = parser.parse_known_args(argv)
    require_ok(len(unknown) == 0, "BAD_ORACLE_ARGS", "unknown oracle cli argument")
    sections = compute_oracle_sections()
    canon = json.dumps(sections, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    digest = hashlib.sha256(canon).hexdigest()
    if args.json_out:
        out = dict(sections)
        out["oracle_sha256"] = digest
        os.write(1, (json.dumps(out, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode("utf-8"))
    else:
        os.write(1, ("PASS s161.q44a.z123_affine_zpoly.oracle.v1 sha256=" + digest + "\n").encode("utf-8"))
    return 0


def main(argv: list[str] | None = None) -> int:
    try:
        return run_oracle_cli(argv)
    except ZPolyError as exc:
        err = json.dumps({"status": "FAIL", "code": exc.code, "message": str(exc)}, sort_keys=True) + "\n"
        os.write(2, err.encode("utf-8"))
        return 2
    except RecursionError:
        err = json.dumps({"status": "FAIL", "code": "RECURSION", "message": "recursion limit exceeded"}, sort_keys=True) + "\n"
        os.write(2, err.encode("utf-8"))
        return 2
    except OSError as exc:
        err = json.dumps({"status": "FAIL", "code": "OS_ERROR", "message": type(exc).__name__}, sort_keys=True) + "\n"
        os.write(2, err.encode("utf-8"))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
