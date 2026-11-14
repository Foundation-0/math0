# SPDX-License-Identifier: Apache-2.0
"""Module 1: General-k Asymmetric Bi-Annihilator Flag-Shear Bypass Solver.

Implements Theorem 1 (Exact Block-Matrix Factorization for Multi-Wire Frame Bypass):
Let A in GL_{k+m}(Z[1/30]) be the net affine-linear endomorphism of a coalesced
window at frame f_b on k co-framed candidate wires W = [w_0, ..., w_{k-1}] (entering
from f_a < f_b and departing to f_c > f_b) and m co-resident external registers E:

    [ w_out ]   [ A_WW   A_WE ] [ w_in ]
    [ E_out ] = [ A_EW   A_EE ] [ E_in ]

Wire w_0 bypasses frame f_b completely (moving f_a -> f_c directly with zero
instructions at f_b) via pre-gauge P in GL_k(Z[1/30]) at f_a, reduced carrier
endomorphism M_sub in GL_{k-1+m}(Z[1/30]) at f_b, and post-gauge D in GL_k(Z[1/30])
at f_c if and only if there exist u in ker(A_WE^T) and v in ker(A_EW) satisfying
the non-singular bi-annihilator condition:

    u^T * A_WW * v != 0

and P, M_sub, D factor into elementary ADD/SCALE gates over the (1125, 25) common grid.
Iterating s times peels s = k - r wires simultaneously when rank([A_WE, A_EW^T]) = r.
"""
from __future__ import annotations
from fractions import Fraction as F


def is_235_smooth(n: int) -> bool:
    n = abs(n)
    if n == 0:
        return False
    for p in (2, 3, 5):
        while n % p == 0:
            n //= p
    return n == 1


def is_add_safe(q: F, odd_scale: int = 1125, max_pow2: int = 16) -> bool:
    """ADD requires |q| + 1 < 2^16 and denominator dividing odd_scale * 2^max_pow2.
    Numerator may be any non-zero integer (independent.py line 44).
    """
    if q == 0 or abs(q) + 1 >= 2**16:
        return False
    d = q.denominator
    p2 = 0
    while d % 2 == 0:
        d //= 2
        p2 += 1
    if p2 > max_pow2:
        return False
    return (odd_scale % d) == 0


def is_scale_safe(q: F, odd_scale: int = 1125, max_pow2: int = 16) -> bool:
    """SCALE requires both numerator and denominator {2,3,5}-smooth."""
    return is_add_safe(q, odd_scale, max_pow2) and is_235_smooth(q.numerator)


def rref_nullspace_right(rows: list[list[F]], ncols: int) -> list[list[F]]:
    """Exact rational right nullspace basis of an m x ncols matrix over Q."""
    if not rows:
        return [[F(1 if i == j else 0) for i in range(ncols)] for j in range(ncols)]
    mat = [[F(x) for x in r] for r in rows]
    m = len(mat)
    pivots = []
    r_idx = 0
    for c in range(ncols):
        piv = next((i for i in range(r_idx, m) if mat[i][c] != 0), None)
        if piv is None:
            continue
        mat[r_idx], mat[piv] = mat[piv], mat[r_idx]
        sc = mat[r_idx][c]
        mat[r_idx] = [x / sc for x in mat[r_idx]]
        for i in range(m):
            if i != r_idx and mat[i][c] != 0:
                f = mat[i][c]
                mat[i] = [mat[i][j] - f * mat[r_idx][j] for j in range(ncols)]
        pivots.append(c)
        r_idx += 1
        if r_idx == m:
            break
    piv_set = set(pivots)
    free_cols = [c for c in range(ncols) if c not in piv_set]
    basis = []
    for fc in free_cols:
        vec = [F(0)] * ncols
        vec[fc] = F(1)
        for row_pos, pc in enumerate(pivots):
            vec[pc] = -mat[row_pos][fc]
        basis.append(vec)
    return basis


def mat_mul(A: list[list[F]], B: list[list[F]]) -> list[list[F]]:
    if not A or not B:
        return []
    m, k, n = len(A), len(B), len(B[0])
    return [[sum(A[i][t] * B[t][j] for t in range(k)) for j in range(n)] for i in range(m)]


def mat_det_and_inv(A: list[list[F]]) -> tuple[F, list[list[F]] | None]:
    n = len(A)
    aug = [[F(A[i][j]) for j in range(n)] + [F(1 if i == j else 0) for j in range(n)] for i in range(n)]
    det = F(1)
    for c in range(n):
        piv = next((i for i in range(c, n) if aug[i][c] != 0), None)
        if piv is None:
            return F(0), None
        if piv != c:
            aug[c], aug[piv] = aug[piv], aug[c]
            det = -det
        sc = aug[c][c]
        det *= sc
        aug[c] = [x / sc for x in aug[c]]
        for i in range(n):
            if i != c and aug[i][c] != 0:
                f = aug[i][c]
                aug[i] = [aug[i][j] - f * aug[c][j] for j in range(2 * n)]
    return det, [row[n:] for row in aug]


def normalize_to_slk_unit_pivots(rows: list[list[F]]) -> list[list[F]] | None:
    """Transforms rows[1:] within span(rows[1:]) so the Schur complement of rows[0][0]
    is the identity matrix I_{k-1}, eliminating unnecessary SCALE gates.
    """
    k = len(rows)
    M = [[F(x) for x in r] for r in rows]
    det, _ = mat_det_and_inv(M)
    if det == 0:
        return None
    if M[0][0] != 0 and k >= 2:
        p00 = M[0][0]
        S = [
            [M[i][j] - (M[i][0] * M[0][j]) / p00 for j in range(1, k)]
            for i in range(1, k)
        ]
        _, S_inv = mat_det_and_inv(S)
        if S_inv is not None:
            M = [M[0]] + mat_mul(S_inv, M[1:])
    return M


def factor_glk_into_ops(
    M: list[list[F]],
    wires: list[int],
    frame: int,
    odd_scale: int = 1125,
    max_pow2: int = 16,
) -> list[list] | None:
    """Factors M in GL_k(Q) into native ADD/SCALE instructions at `frame`."""
    k = len(wires)
    if k == 0:
        return []
    cur = [[F(M[i][j]) for j in range(k)] for i in range(k)]
    row_ops = []

    for col in range(k):
        if cur[col][col] == 0:
            piv = next((r for r in range(col + 1, k) if cur[r][col] != 0), None)
            if piv is None:
                return None
            q_make1 = F(1) / cur[piv][col]
            if is_add_safe(q_make1, odd_scale, max_pow2):
                cur[col] = [cur[col][j] + q_make1 * cur[piv][j] for j in range(k)]
                row_ops.append(('ADD', col, piv, q_make1))
            else:
                cur[col] = [cur[col][j] + cur[piv][j] for j in range(k)]
                row_ops.append(('ADD', col, piv, F(1)))
        elif cur[col][col] != 1:
            piv = next((r for r in range(col + 1, k) if cur[r][col] != 0), None)
            if piv is not None:
                q_fix = (F(1) - cur[col][col]) / cur[piv][col]
                if is_add_safe(q_fix, odd_scale, max_pow2):
                    cur[col] = [cur[col][j] + q_fix * cur[piv][j] for j in range(k)]
                    row_ops.append(('ADD', col, piv, q_fix))

        piv_val = cur[col][col]
        for r in range(k):
            if r != col and cur[r][col] != 0:
                factor = -cur[r][col] / piv_val
                if not is_add_safe(factor, odd_scale, max_pow2):
                    return None
                cur[r] = [cur[r][j] + factor * cur[col][j] for j in range(k)]
                row_ops.append(('ADD', r, col, factor))

    for col in range(k):
        diag = cur[col][col]
        if diag != 1:
            inv_d = F(1) / diag
            if not is_scale_safe(diag, odd_scale, max_pow2) or not is_scale_safe(inv_d, odd_scale, max_pow2):
                return None
            cur[col][col] = F(1)
            row_ops.append(('SCALE', col, inv_d))

    events = []
    for op in reversed(row_ops):
        if op[0] == 'ADD':
            _, dst_i, src_i, q = op
            neg_q = -q
            if not is_add_safe(neg_q, odd_scale, max_pow2):
                return None
            events.append(['ADD', wires[dst_i], wires[src_i], str(neg_q), frame])
        elif op[0] == 'SCALE':
            _, dst_i, inv_d = op
            d = F(1) / inv_d
            if not is_scale_safe(d, odd_scale, max_pow2):
                return None
            events.append(['SCALE', wires[dst_i], str(d), frame])

    sim = [[F(1 if i == j else 0) for j in range(k)] for i in range(k)]
    w_to_idx = {w: idx for idx, w in enumerate(wires)}
    for ev in events:
        if ev[0] == 'SCALE':
            ii = w_to_idx[ev[1]]
            qq = F(ev[2])
            sim[ii] = [qq * x for x in sim[ii]]
        else:
            ii, jj, qq = w_to_idx[ev[1]], w_to_idx[ev[2]], F(ev[3])
            sim[ii] = [sim[ii][c] + qq * sim[jj][c] for c in range(k)]
    if sim != M:
        return None
    return events


def extract_coalition_block(prog_slice: list[list], coalition: list[int], fb: int) -> dict | None:
    """Extracts the exact affine-linear transfer matrix on (W, E) for events at frame `fb`.
    Aborts cleanly if any interacting external register moves into/out of `fb` mid-window
    or uses non-invertible COPY onto coalition registers.
    """
    W_set = set(coalition)
    k = len(coalition)
    w_idx = {w: i for i, w in enumerate(coalition)}
    ext_regs = []
    ext_idx = {}

    def get_ext(r: int) -> int:
        if r not in ext_idx:
            ext_idx[r] = len(ext_regs)
            ext_regs.append(r)
        return ext_idx[r]

    fb_ops = [ev for ev in prog_slice if (ev[0] in ('ADD', 'COPY', 'SCALE') and ev[-1] == fb)]
    for ev in fb_ops:
        if ev[0] == 'COPY' and (ev[1] in W_set or ev[2] in W_set):
            return None
        if ev[0] == 'ADD':
            if ev[1] in W_set and ev[2] not in W_set:
                get_ext(ev[2])
            elif ev[2] in W_set and ev[1] not in W_set:
                get_ext(ev[1])

    changed = True
    while changed:
        changed = False
        for ev in fb_ops:
            if ev[0] in ('ADD', 'COPY'):
                r1, r2 = ev[1], ev[2]
                if r1 in ext_idx and r2 not in W_set and r2 not in ext_idx:
                    get_ext(r2); changed = True
                elif r2 in ext_idx and r1 not in W_set and r1 not in ext_idx:
                    get_ext(r1); changed = True

    # Ensure no ext_reg enters/leaves fb mid-slice via MOVE/INIT/CLEAR:
    for ev in prog_slice:
        if ev[0] in ('MOVE', 'INIT', 'CLEAR') and ev[1] in ext_idx:
            return None

    m = len(ext_regs)
    dim_tot = k + m
    state = [[F(1 if i == j else 0) for j in range(dim_tot)] for i in range(dim_tot)]

    def reg_pos(r: int) -> int | None:
        if r in w_idx:
            return w_idx[r]
        if r in ext_idx:
            return k + ext_idx[r]
        return None

    orig_touched_ops = 0
    for ev in fb_ops:
        op = ev[0]
        if op == 'SCALE':
            p = reg_pos(ev[1])
            if p is not None:
                orig_touched_ops += 1
                q = F(ev[2])
                state[p] = [q * x for x in state[p]]
        elif op == 'COPY':
            p_dst, p_src = reg_pos(ev[1]), reg_pos(ev[2])
            if p_dst is not None:
                if p_src is None:
                    return None
                orig_touched_ops += 1
                q = F(ev[3])
                state[p_dst] = [q * x for x in state[p_src]]
        elif op == 'ADD':
            p_dst, p_src = reg_pos(ev[1]), reg_pos(ev[2])
            if p_dst is not None:
                if p_src is None:
                    return None
                orig_touched_ops += 1
                q = F(ev[3])
                state[p_dst] = [state[p_dst][j] + q * state[p_src][j] for j in range(dim_tot)]

    return {
        'A_WW': [row[:k] for row in state[:k]],
        'A_WE': [row[k:] for row in state[:k]],
        'A_EW': [row[:k] for row in state[k:]],
        'A_EE': [row[k:] for row in state[k:]],
        'ext_regs': ext_regs,
        'orig_touched_ops': orig_touched_ops,
    }


def synthesize_single_bypass_on_coalition(
    coalition: list[int],
    block: dict,
    fa: int,
    fb: int,
    fc_decode: int,
    odd_scale: int = 1125,
    max_pow2: int = 16,
) -> dict | None:
    """Synthesizes exact pre-gauge P (at fa), carrier fb_events (at fb, zero w_skip touches!),
    and post-gauge D (at fc_decode) via Theorem 1's block-matrix factorization.
    """
    k = len(coalition)
    A_WW, A_WE, A_EW, A_EE = block['A_WW'], block['A_WE'], block['A_EW'], block['A_EE']
    ext_regs = block['ext_regs']
    m = len(ext_regs)

    A_WE_T = [[A_WE[i][j] for i in range(k)] for j in range(m)]
    u_basis = rref_nullspace_right(A_WE_T, k)
    if not u_basis:
        return None

    v_basis = rref_nullspace_right(A_EW, k)
    if not v_basis:
        return None

    chosen = None
    # Prefer u, v pairs where uA[0] != 0 so wire 0 needs no permutation shear:
    for u in u_basis:
        uA = [sum(u[i] * A_WW[i][j] for i in range(k)) for j in range(k)]
        for v in v_basis:
            val = sum(uA[j] * v[j] for j in range(k))
            if val != 0:
                chosen = (u, v, val, uA)
                if uA[0] != 0:
                    break
        if chosen is not None and chosen[3][0] != 0:
            break
    if chosen is None:
        return None

    u, v, alpha, uA = chosen
    scale_p0 = uA[0] if uA[0] != 0 else alpha
    p0 = [x / scale_p0 for x in uA]
    p_rest = rref_nullspace_right([v], k)
    if len(p_rest) != k - 1:
        return None

    P = normalize_to_slk_unit_pivots([p0] + p_rest)
    if P is None:
        return None
    _, P_inv = mat_det_and_inv(P)
    if P_inv is None:
        return None

    col0_Pinv = [P_inv[i][0] for i in range(k)]
    A_col0 = [sum(A_WW[i][j] * col0_Pinv[j] for j in range(k)) for i in range(k)]
    d_rest = rref_nullspace_right([A_col0], k)
    if len(d_rest) != k - 1:
        return None
    d0 = [x / scale_p0 for x in u]
    D_inv = normalize_to_slk_unit_pivots([d0] + d_rest)
    if D_inv is None:
        return None
    _, D = mat_det_and_inv(D_inv)
    if D is None:
        return None

    M_WW = mat_mul(mat_mul(D_inv, A_WW), P_inv)
    M_WE = mat_mul(D_inv, A_WE)
    M_EW = mat_mul(A_EW, P_inv)

    if M_WW[0] != [F(1)] + [F(0)] * (k - 1):
        return None
    if any(M_WW[r][0] != 0 for r in range(1, k)):
        return None
    if any(M_WE[0][c] != 0 for c in range(m)) or any(M_EW[r][0] != 0 for r in range(m)):
        return None

    enc_events = factor_glk_into_ops(P, coalition, fa, odd_scale, max_pow2)
    if enc_events is None:
        return None
    dec_events = factor_glk_into_ops(D, coalition, fc_decode, odd_scale, max_pow2)
    if dec_events is None:
        return None

    carriers = coalition[1:]
    sub_regs = carriers + ext_regs
    M_sub = [M_WW[i][1:] + M_WE[i] for i in range(1, k)] + [M_EW[i][1:] + A_EE[i] for i in range(m)]
    fb_events = factor_glk_into_ops(M_sub, sub_regs, fb, odd_scale, max_pow2)
    if fb_events is None:
        return None

    # Exact (k + m) x (k + m) symbolic equivalence check:
    all_regs = coalition + ext_regs
    reg_map = {r: idx for idx, r in enumerate(all_regs)}
    sim = [[F(1 if i == j else 0) for j in range(k + m)] for i in range(k + m)]
    for ev in enc_events + fb_events + dec_events:
        if ev[0] == 'SCALE':
            ii, qq = reg_map[ev[1]], F(ev[2])
            sim[ii] = [qq * x for x in sim[ii]]
        else:
            ii, jj, qq = reg_map[ev[1]], reg_map[ev[2]], F(ev[3])
            sim[ii] = [sim[ii][c] + qq * sim[jj][c] for c in range(k + m)]

    target_full = [A_WW[i] + A_WE[i] for i in range(k)] + [A_EW[i] + A_EE[i] for i in range(m)]
    if sim != target_full:
        return None

    return {
        'w_skip': coalition[0],
        'carriers': carriers,
        'ext_regs': ext_regs,
        'u': [str(x) for x in u],
        'v': [str(x) for x in v],
        'bi_annihilator_minor': str(alpha),
        'encode_events': enc_events,
        'fb_events': fb_events,
        'decode_events': dec_events,
        'net_scalar_op_delta': (len(enc_events) + len(fb_events) + len(dec_events)) - block['orig_touched_ops'],
    }
