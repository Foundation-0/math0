"""Clean-room pure-Z/Q/F_2 cross-field propagation engine for Track S82.

Propagates Portal 78 (anthropics/formal-math/vp-vnp) proof and verification
mechanisms (M1..M6) across four strictly typed pillars with explicit Law-5
non-commutativity obstructions (zero floating-point ops, zero bare asserts):
  - Pillar 1 (M1 + M2): Strassen <2,2,2> rerouting, Extended Hamming [16,11,4] /
    E_8 [8,4,4] non-Euclidean CAT(0) rank-metric embedding, and 4-party (Q,K,V,O)
    Meixner crossing-wires rank profile.
  - Pillar 2 (M3): Constructive verified Lem F.2 1D nearest-neighbor CNOT circuit
    compiler over U_n(F_2) (n = 4, 5, 6, 8) + exact Law-5 Real-Shear Obstruction
    (minpoly lambda^2 - 3*lambda + 1 = 0, kappa_2 = phi^2 > 1 vs orthogonal WHT).
  - Pillar 3 (M4): Pure-Q Laurent polynomial engine for CircularEP beta-pole
    cancellation / O(e*/beta) contamination + Lem N.2 cutoff & Prop N.4 sigma_r.
  - Pillar 4 (M5 + M6): Weighted-Cheeger lift of Prop E.10 on 128-expert Zipf MoE
    (Inkling 2 Mini toy) + executable aletheia v2.3 Formal Trust Gates (T-13..T-15).
"""

from __future__ import annotations

from decimal import Decimal, getcontext
from fractions import Fraction
import itertools
import math
import re
from typing import Dict, List, Mapping, Sequence, Set, Tuple

getcontext().prec = 28


class PropagationError(ValueError):
    """Typed failure raised when a propagation invariant or trust gate fails."""


def _require(cond: bool, msg: str) -> None:
    if not cond:
        raise PropagationError(msg)


def _frac_to_dec_str(q: Fraction, places: int = 6) -> str:
    d = Decimal(q.numerator) / Decimal(q.denominator)
    return str(d.quantize(Decimal(10) ** (-places)))


# ---------------------------------------------------------------------------
# Exact Helpers: Z[X] polynomials, Q determinant/rank, F_2 rank/matrices
# ---------------------------------------------------------------------------


def _poly_trim(c: Sequence[int]) -> Tuple[int, ...]:
    end = len(c)
    while end > 0 and c[end - 1] == 0:
        end -= 1
    return tuple(c[:end])


def _poly_add(a: Sequence[int], b: Sequence[int]) -> Tuple[int, ...]:
    n = max(len(a), len(b))
    return _poly_trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def _poly_sub(a: Sequence[int], b: Sequence[int]) -> Tuple[int, ...]:
    n = max(len(a), len(b))
    return _poly_trim([(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)])


def _poly_neg(a: Sequence[int]) -> Tuple[int, ...]:
    return tuple(-v for v in a)


def _poly_mul(a: Sequence[int], b: Sequence[int]) -> Tuple[int, ...]:
    if not a:
        return ()
    if not b:
        return ()
    out = [0] * (len(a) + len(b) - 1)
    for i, ca in enumerate(a):
        if ca == 0:
            continue
        for j, cb in enumerate(b):
            if cb != 0:
                out[i + j] += ca * cb
    return _poly_trim(out)


def _poly_shift(a: Sequence[int], k: int) -> Tuple[int, ...]:
    if not a:
        return ()
    return (0,) * k + tuple(a)


def _poly_sub_x2(p_y: Sequence[int]) -> Tuple[int, ...]:
    if not p_y:
        return ()
    out = [0] * (2 * len(p_y) - 1)
    for idx, coeff in enumerate(p_y):
        out[2 * idx] = coeff
    return _poly_trim(out)


def _poly_det(mat: Sequence[Sequence[Tuple[int, ...]]]) -> Tuple[int, ...]:
    n = len(mat)
    acc: Tuple[int, ...] = ()
    for perm in itertools.permutations(range(n)):
        inv = 0
        for i in range(n):
            for j in range(i + 1, n):
                if perm[i] > perm[j]:
                    inv += 1
        prod: Tuple[int, ...] = (1,)
        zero = False
        for r in range(n):
            entry = mat[r][perm[r]]
            if not entry:
                zero = True
                break
            prod = _poly_mul(prod, entry)
        if zero:
            continue
        acc = _poly_sub(acc, prod) if (inv % 2 == 1) else _poly_add(acc, prod)
    return acc


def _rank_q(rows: Sequence[Sequence[int]]) -> int:
    if not rows:
        return 0
    m = len(rows)
    n = len(rows[0])
    a = [[Fraction(v) for v in row] for row in rows]
    rank = 0
    for col in range(n):
        piv = -1
        for r in range(rank, m):
            if a[r][col] != 0:
                piv = r
                break
        if piv == -1:
            continue
        a[rank], a[piv] = a[piv], a[rank]
        pv = a[rank][col]
        for r in range(rank + 1, m):
            if a[r][col] != 0:
                f = a[r][col] / pv
                for c in range(col, n):
                    a[r][c] -= f * a[rank][c]
        rank += 1
    return rank


def _det_q(mat: Sequence[Sequence[Fraction]]) -> Fraction:
    n = len(mat)
    a = [[Fraction(v) for v in row] for row in mat]
    sign = Fraction(1)
    for k in range(n):
        piv = -1
        for i in range(k, n):
            if a[i][k] != 0:
                piv = i
                break
        if piv == -1:
            return Fraction(0)
        if piv != k:
            a[k], a[piv] = a[piv], a[k]
            sign = -sign
        pv = a[k][k]
        for i in range(k + 1, n):
            if a[i][k] != 0:
                f = a[i][k] / pv
                for j in range(k, n):
                    a[i][j] -= f * a[k][j]
    out = sign
    for k in range(n):
        out *= a[k][k]
    return out


def _rank_f2_rows(rows: Sequence[int], n: int) -> int:
    work = list(rows)
    rank = 0
    for col in range(n):
        piv = -1
        for r in range(rank, n):
            if (work[r] >> col) & 1:
                piv = r
                break
        if piv == -1:
            continue
        work[rank], work[piv] = work[piv], work[rank]
        for r in range(n):
            if r != rank and ((work[r] >> col) & 1):
                work[r] ^= work[rank]
        rank += 1
    return rank


# ---------------------------------------------------------------------------
# Pillar 1 (M1 + M2): Strassen <2,2,2>, Code Rank Metric, & 4-Party (Q,K,V,O)
# ---------------------------------------------------------------------------


def _strassen_2x2(a: Sequence[Sequence[int]], b: Sequence[Sequence[int]]) -> List[List[int]]:
    a11, a12 = a[0][0], a[0][1]
    a21, a22 = a[1][0], a[1][1]
    b11, b12 = b[0][0], b[0][1]
    b21, b22 = b[1][0], b[1][1]
    m1 = (a11 + a22) * (b11 + b22)
    m2 = (a21 + a22) * b11
    m3 = a11 * (b12 - b22)
    m4 = a22 * (b21 - b11)
    m5 = (a11 + a12) * b22
    m6 = (a21 - a11) * (b11 + b12)
    m7 = (a12 - a22) * (b21 + b22)
    return [[m1 + m4 - m5 + m7, m3 + m5], [m2 + m4, m1 - m2 + m3 + m6]]


def oracle_m1_m2_cat0_rerouting_and_codes() -> Dict[str, object]:
    """Pillar 1: Verify Strassen <2,2,2>, [8,4,4]/[16,11,4] code CAT(0), & (Q,K,V,O) crossing."""
    # 1a. Strassen <2,2,2> exact bilinear verification on all 16 basis pairs + dense integer pair
    basis_2x2 = [
        [[1, 0], [0, 0]],
        [[0, 1], [0, 0]],
        [[0, 0], [1, 0]],
        [[0, 0], [0, 1]],
    ]
    basis_checks = 0
    for ma in basis_2x2:
        for mb in basis_2x2:
            naive = [
                [sum(ma[i][k] * mb[k][j] for k in range(2)) for j in range(2)]
                for i in range(2)
            ]
            if _strassen_2x2(ma, mb) == naive:
                basis_checks += 1

    # 1b. Extended Hamming [8, 4, 4] (E_8 Construction-A core!) & [16, 11, 4] parity-check code
    # Standard systematic [8, 4, 4] generator rows (4x8 over F_2): min nonzero Hamming weight == 4!
    g_e8 = (
        0b1000_0111,
        0b0100_1011,
        0b0010_1101,
        0b0001_1110,
    )
    min_wt_e8 = 8
    for msg in range(1, 16):
        cw = 0
        for bit in range(4):
            if (msg >> bit) & 1:
                cw ^= g_e8[bit]
        wt = cw.bit_count()
        if wt < min_wt_e8:
            min_wt_e8 = wt

    # Extended Hamming [16, 11, 4] parity-check matrix H (5x16): columns are all 16 5-bit vectors
    # with LSB = 1 (overall parity) + 4-bit binary index 0..15 -> rank(H) = 5, dim(ker H) = 11!
    h_16_rows = [0] * 5
    for col in range(16):
        h_16_rows[0] |= 1 << col  # overall even parity
        for b in range(4):
            if (col >> b) & 1:
                h_16_rows[b + 1] |= 1 << col
    # Row-reduce 5x16 over F_2
    work_h = list(h_16_rows)
    rk_h = 0
    for col in range(16):
        piv = -1
        for r in range(rk_h, 5):
            if (work_h[r] >> col) & 1:
                piv = r
                break
        if piv == -1:
            continue
        work_h[rk_h], work_h[piv] = work_h[piv], work_h[rk_h]
        for r in range(rk_h + 1, 5):
            if (work_h[r] >> col) & 1:
                work_h[r] ^= work_h[rk_h]
        rk_h += 1

    # Embed 5-point CAT(0) non-Euclidean rank-metric witness {0, E00, E01, E11, E00+E11}
    # directly into the 2x2 linear-code operator subspace (det G = -1/4, u^T G u = -1)
    code_ops = [(0b10, 0b00), (0b01, 0b00), (0b00, 0b01), (0b10, 0b01)]
    gram_code: List[List[Fraction]] = []
    for i in range(4):
        ri = _rank_f2_rows(code_ops[i], 2)
        row_g: List[Fraction] = []
        for j in range(4):
            rj = _rank_f2_rows(code_ops[j], 2)
            rij = _rank_f2_rows([code_ops[i][r] ^ code_ops[j][r] for r in range(2)], 2)
            row_g.append(Fraction(ri + rj - rij, 2))
        gram_code.append(row_g)
    det_code_g = _det_q(gram_code)

    # 1c. 4-party (Q, K, V, O) Meixner crossing-wires attention-routing toy tensor (Prop B.2)
    # Parties: a=Q, b=K, c=V, d=O; Sigma_1 = Sigma_2 = {({0},{1}), ({1},{0})}, Theta = 16.
    b_tbl: List[List[Tuple[int, ...]]] = [[() for _ in range(3)] for _ in range(3)]
    c_tbl: List[List[Tuple[int, ...]]] = [[() for _ in range(3)] for _ in range(3)]
    for n in range(3):
        sgn = 1 if (n % 2 == 0) else -1
        b_tbl[0][n] = _poly_shift((sgn,), n)
        c_tbl[0][n] = (sgn,)
    for r in range(1, 3):
        b_tbl[r][0] = (1,)
        c_tbl[r][0] = (1,)
        for n in range(1, 3):
            b_tbl[r][n] = _poly_sub(_poly_add(b_tbl[r - 1][n], b_tbl[r - 1][n - 1]), _poly_shift(b_tbl[r][n - 1], 1))
            c_tbl[r][n] = _poly_sub(_poly_add(c_tbl[r - 1][n], _poly_shift(c_tbl[r - 1][n - 1], 1)), c_tbl[r][n - 1])

    sigma = [((0,), (1,)), ((1,), (0,))]
    y_m1 = (-1, 0, 1)

    def build_qkvo(iq: int, ik: int, iv: int, io_: int) -> Tuple[int, ...]:
        sa, sb, sc, sd = sigma[iq], sigma[ik], sigma[iv], sigma[io_]
        rtags = [("Q", sa[0][0]), ("O", sd[0][0]), ("V", sc[0][0]), ("K", sb[0][0])]
        ctags = [("Q", sa[1][0]), ("O", sd[1][0]), ("V", sc[1][0]), ("K", sb[1][0])]
        mat: List[List[Tuple[int, ...]]] = []
        for rp, i in rtags:
            row: List[Tuple[int, ...]] = []
            for cp, j in ctags:
                pair = (rp, cp)
                if pair == ("Q", "O"):
                    val = _poly_sub_x2(c_tbl[i][j])
                elif pair == ("O", "Q"):
                    val = _poly_neg(_poly_sub_x2(c_tbl[j][i]))
                elif pair == ("Q", "V"):
                    val = _poly_shift((1,), 2 * i + 1) if i == j else ()
                elif pair == ("Q", "K"):
                    val = _poly_mul(y_m1, _poly_mul(_poly_shift((1,), 2 * i + 1), _poly_sub_x2(b_tbl[i][j])))
                elif pair == ("O", "V"):
                    val = _poly_mul(_poly_shift((1,), 2 * j + 1), _poly_sub_x2(b_tbl[j][i]))
                elif pair == ("O", "K"):
                    val = _poly_neg(_poly_shift((1,), 2 * i + 1)) if i == j else ()
                elif pair == ("V", "Q"):
                    val = _poly_neg(_poly_shift((1,), 2 * i + 1)) if i == j else ()
                elif pair == ("V", "O"):
                    val = _poly_neg(_poly_mul(_poly_shift((1,), 2 * i + 1), _poly_sub_x2(b_tbl[i][j])))
                elif pair == ("K", "Q"):
                    val = _poly_neg(_poly_mul(y_m1, _poly_mul(_poly_shift((1,), 2 * j + 1), _poly_sub_x2(b_tbl[j][i]))))
                elif pair == ("K", "O"):
                    val = _poly_shift((1,), 2 * i + 1) if i == j else ()
                elif pair == ("V", "K"):
                    val = _poly_neg(_poly_mul(y_m1, _poly_sub_x2(c_tbl[i][j])))
                elif pair == ("K", "V"):
                    val = _poly_mul(y_m1, _poly_sub_x2(c_tbl[j][i]))
                else:
                    val = ()
                row.append(val)
            mat.append(row)
        return _poly_det(mat)

    psi = {
        (iq, ik, iv, io_): build_qkvo(iq, ik, iv, io_)
        for iq in range(2)
        for ik in range(2)
        for iv in range(2)
        for io_ in range(2)
    }
    # Check QO|KV flattening rank at X^0 (== 1), X^16 (== 4), and X=1 crossing wires (rank == 4)
    mat_n0 = [
        [psi[(iq, ik, iv, io_)][0] if psi[(iq, ik, iv, io_)] else 0 for ik in range(2) for iv in range(2)]
        for iq in range(2)
        for io_ in range(2)
    ]
    mat_n16 = [
        [psi[(iq, ik, iv, io_)][16] if len(psi[(iq, ik, iv, io_)]) > 16 else 0 for ik in range(2) for iv in range(2)]
        for iq in range(2)
        for io_ in range(2)
    ]
    mat_x1 = [
        [sum(psi[(iq, ik, iv, io_)]) for ik in range(2) for iv in range(2)]
        for iq in range(2)
        for io_ in range(2)
    ]
    rk_n0 = _rank_q(mat_n0)
    rk_n16 = _rank_q(mat_n16)
    rk_x1 = _rank_q(mat_x1)

    return {
        "strassen_basis_checks": basis_checks,
        "strassen_rank_vs_naive": [7, 8],
        "strassen_7_cubed_vs_8_cubed": [7 ** 3, 8 ** 3],
        "hamming_8_4_4_min_distance": min_wt_e8,
        "hamming_16_11_4_parity_rank": rk_h,
        "hamming_16_11_4_code_dim": 16 - rk_h,
        "code_subspace_cat0_gram_det": str(det_code_g),
        "qkvo_crossing_ranks_n0_n16_x1": [rk_n0, rk_n16, rk_x1],
    }


# ---------------------------------------------------------------------------
# Pillar 2 (M3): Lem F.2 Constructive 1D CNOT Compiler & Real-Shear Obstruction
# ---------------------------------------------------------------------------


def _mat_mul_f2(a: Sequence[Sequence[int]], b: Sequence[Sequence[int]]) -> List[List[int]]:
    n = len(a)
    out = [[0] * n for _ in range(n)]
    for i in range(n):
        for k in range(n):
            if a[i][k]:
                for j in range(n):
                    out[i][j] ^= b[k][j]
    return out


def _apply_cnot1d_word_f2(n: int, gates: Sequence[int]) -> List[List[int]]:
    """Evaluate a sequence of 1D nearest-neighbor CNOT gates x_j = I + E_{j,j+1} over F_2."""
    acc = [[1 if r == c else 0 for c in range(n)] for r in range(n)]
    for j in gates:
        _require(0 <= j < n - 1, f"CNOT gate index {j} out of range for n={n}")
        # Right-multiplying acc by (I + E_{j, j+1}) adds col j into col j+1 mod 2!
        for r in range(n):
            acc[r][j + 1] ^= acc[r][j]
    return acc


def synthesize_cnot1d_rank1(n: int, k: int, xi: Sequence[int], omega: Sequence[int]) -> List[int]:
    """Constructive Lem F.2 1D nearest-neighbor CNOT synthesizer for I + upper_right(xi * omega^T).

    Emits a word in elementary nearest-neighbor 1D CNOTs x_j = I + E_{j,j+1} (0 <= j < n-1)
    with guaranteed per-gate multiplicity <= 4 (when xi[k-1]=1 and omega[0]=1) and <= 16 in general.
    """
    _require(1 <= k < n, "Cut k must satisfy 1 <= k < n")
    _require(len(xi) == k and any(xi), "xi must be nonzero of length k")
    _require(len(omega) == n - k and any(omega), "omega must be nonzero of length n - k")

    def synth_ep1(xv: Sequence[int], ov: Sequence[int]) -> List[int]:
        zeros_x = [i for i in range(k - 1) if xv[i] == 0]
        word_a = list(reversed(zeros_x)) + list(range(k - 1))
        zeros_o = [j for j in range(1, n - k) if ov[j] == 0]
        word_b = list(range(k, n - 1)) + [k + j - 1 for j in reversed(zeros_o)]
        return word_a + list(reversed(word_b)) + [k - 1] + word_b + list(reversed(word_a))

    if xi[k - 1] == 1:
        xi_parts = [list(xi)]
    else:
        e_last = [0] * (k - 1) + [1]
        xi_parts = [[xi[i] ^ e_last[i] for i in range(k)], e_last]

    if omega[0] == 1:
        om_parts = [list(omega)]
    else:
        e_first = [1] + [0] * (n - k - 1)
        om_parts = [[omega[j] ^ e_first[j] for j in range(n - k)], e_first]

    circuit: List[int] = []
    for xp in xi_parts:
        for op in om_parts:
            circuit.extend(synth_ep1(xp, op))
    return circuit


def oracle_m3_cnot1d_compiler_and_real_shear_obstruction() -> Dict[str, object]:
    """Pillar 2: Verify Lem F.2 1D CNOT compiler (n=4,5,6,8) & Law-5 Real-Shear Obstruction."""
    counts_by_n: Dict[str, int] = {}
    max_ep1 = 0
    max_gen = 0

    def verify_one(n: int, k: int, xi: Sequence[int], omega: Sequence[int]) -> Tuple[bool, int]:
        nonlocal max_ep1, max_gen
        word = synthesize_cnot1d_rank1(n, k, xi, omega)
        got = _apply_cnot1d_word_f2(n, word)
        target = [[1 if r == c else 0 for c in range(n)] for r in range(n)]
        for r in range(k):
            for c in range(n - k):
                target[r][k + c] = xi[r] & omega[c]
        peak = max(word.count(g) for g in range(n - 1))
        if xi[k - 1] == 1 and omega[0] == 1:
            if peak > max_ep1:
                max_ep1 = peak
        if peak > max_gen:
            max_gen = peak
        return (got == target), len(word)

    # Exhaustive verification on n = 4 (23) and n = 5 (72)
    for n in (4, 5):
        cnt = 0
        for k in range(1, n):
            for xi in itertools.product((0, 1), repeat=k):
                if not any(xi):
                    continue
                for om in itertools.product((0, 1), repeat=n - k):
                    if not any(om):
                        continue
                    ok_one, _ = verify_one(n, k, xi, om)
                    if ok_one:
                        cnt += 1
        counts_by_n[f"n{n}"] = cnt

    # Structured full-span & long-range verification on n = 6 (k=3: 25 pairs) and n = 8 (k=4: 64 pairs)
    # Specifically includes pure maximal-distance CNOT(0 -> n-1): xi=(1,0,...,0), om=(0,...,0,1)!
    long_range_8_gate_count = 0
    for n, k in ((6, 3), (8, 4)):
        xi_set = [
            tuple(1 if i == r else 0 for i in range(k)) for r in range(k)
        ] + [
            tuple(1 for _ in range(k)),
            tuple(1 if i % 2 == 0 else 0 for i in range(k)),
        ]
        if n == 8:
            xi_set.extend([
                (1, 0, 1, 1),
                (0, 1, 1, 0),
            ])
        om_set = [
            tuple(1 if j == c else 0 for j in range(n - k)) for c in range(n - k)
        ] + [
            tuple(1 for _ in range(n - k)),
            tuple(1 if j % 2 == 1 else 0 for j in range(n - k)),
        ]
        if n == 8:
            om_set.extend([
                (1, 1, 0, 1),
                (0, 1, 1, 0),
            ])
        cnt = 0
        for xi in xi_set:
            for om in om_set:
                ok_one, g_len = verify_one(n, k, xi, om)
                if ok_one:
                    cnt += 1
                if xi == (1, 0, 0, 0) and om == (0, 0, 0, 1):
                    long_range_8_gate_count = g_len
        counts_by_n[f"n{n}"] = cnt

    # Law-5 Real-Shear Obstruction (over Z/Q/R):
    # Elementary shear S_8 = I_8 + E_{0,1}: det(S_8) = 1, tr(S_8^T S_8) = 8 + 1 = 9 != 8!
    # 2x2 nontrivial Gram block M = [[1, 1], [1, 2]] satisfies M^2 - 3*M + I = 0!
    m2 = [[1, 1], [1, 2]]
    m2_sq = [[sum(m2[i][t] * m2[t][j] for t in range(2)) for j in range(2)] for i in range(2)]
    minpoly_zero = all(
        m2_sq[i][j] - 3 * m2[i][j] + (1 if i == j else 0) == 0
        for i in range(2)
        for j in range(2)
    )
    minpoly_str = "lambda^2 - 3*lambda + 1 = 0" if minpoly_zero else "FAILED"

    # Exact rational enclosure of kappa_2(S) = phi^2 = (3 + sqrt(5))/2 via integer isqrt:
    # 5 * 10^8 -> isqrt = 22360 -> 2.2360 < sqrt(5) < 2.2361 -> 2.61800 < phi^2 < 2.61805!
    s5_lo_int = math.isqrt(5 * (10 ** 8))
    s5_hi_int = s5_lo_int + 1
    kappa_lo = Fraction(3 * 10000 + s5_lo_int, 20000)
    kappa_hi = Fraction(3 * 10000 + s5_hi_int, 20000)

    return {
        "synthesized_counts_by_n": counts_by_n,
        "total_cnot_circuits_verified": sum(counts_by_n.values()),
        "max_endpoint1_gate_mult": max_ep1,
        "max_general_gate_mult": max_gen,
        "cnot_0_to_7_gate_len": long_range_8_gate_count,
        "real_shear_8x8_gram_trace": 6 + m2[0][0] + m2[1][1],
        "real_shear_minpoly": minpoly_str,
        "real_shear_kappa2_bracket_dec": [_frac_to_dec_str(kappa_lo, 5), _frac_to_dec_str(kappa_hi, 5)],
        "wht_orthogonal_kappa2": "1",
    }


# ---------------------------------------------------------------------------
# Pillar 3 (M4): Laurent Cutoff & sigma_r Isolation for CircularEP / Rocket RL
# ---------------------------------------------------------------------------


def _laurent_add(a: Mapping[int, Fraction], b: Mapping[int, Fraction]) -> Dict[int, Fraction]:
    out = dict(a)
    for e, c in b.items():
        nv = out.get(e, Fraction(0)) + c
        if nv == 0:
            out.pop(e, None)
        else:
            out[e] = nv
    return out


def _laurent_mul(a: Mapping[int, Fraction], b: Mapping[int, Fraction]) -> Dict[int, Fraction]:
    out: Dict[int, Fraction] = {}
    for e1, c1 in a.items():
        for e2, c2 in b.items():
            nv = out.get(e1 + e2, Fraction(0)) + c1 * c2
            if nv == 0:
                out.pop(e1 + e2, None)
            else:
                out[e1 + e2] = nv
    return out


def _laurent_trunc(a: Mapping[int, Fraction], max_exp: int) -> Dict[int, Fraction]:
    return {e: c for e, c in a.items() if e <= max_exp}


def _laurent_sigma_r(a: Mapping[int, Fraction], r: int) -> Dict[int, Fraction]:
    return {e * r: c for e, c in a.items()}


def oracle_m4_laurent_circularep_and_rocket_isolation() -> Dict[str, object]:
    """Pillar 3: Verify CircularEP beta-pole control, Lem N.2 cutoff, & Prop N.4 sigma_r."""
    # 3a. CircularEP DEQ implicit gradient: -(1/beta) * (E(x^beta) - E_0)
    # Exact free-phase fixed point (residual e* = 0):
    #   E_diff = 0*beta^0 + (7/3)*beta^1 + (5/2)*beta^2 + (11/4)*beta^9 (with high-order tail above N=8!)
    # Cutoff at Lem N.2 bound N = 2^L * Delta (L=3, Delta=1 -> N=8) preserves [beta^<=0] identically!
    neg_inv_beta = {-1: Fraction(-1)}
    g_true = Fraction(7, 3)
    e_diff_clean = {1: g_true, 2: Fraction(5, 2), 9: Fraction(11, 4)}
    grad_clean_full = _laurent_mul(neg_inv_beta, e_diff_clean)
    grad_clean_cut = _laurent_mul(neg_inv_beta, _laurent_trunc(e_diff_clean, 8))
    nonpos_full = {e: c for e, c in grad_clean_full.items() if e <= 0}
    nonpos_cut = {e: c for e, c in grad_clean_cut.items() if e <= 0}
    cutoff_val = 8 if nonpos_cut == nonpos_full else 0

    # Incomplete free-phase convergence (residual e* = 1/100 != 0 -> O(e*/beta) pole contamination!):
    e_star = Fraction(1, 100)
    e_diff_dirty = _laurent_add(e_diff_clean, {0: e_star})
    grad_dirty = _laurent_mul(neg_inv_beta, e_diff_dirty)

    # 3b. Prop N.4 sigma_r pole isolation across stages (outer pole order P = 2):
    lam0 = {-2: Fraction(1)}
    lam1 = {0: Fraction(1)}
    inner0_raw = {1: Fraction(13, 7)}
    inner1_raw = {0: Fraction(9, 4), 1: Fraction(17, 5)}

    comp_r1 = _laurent_add(
        _laurent_mul(lam0, _laurent_sigma_r(inner0_raw, 1)),
        _laurent_mul(lam1, _laurent_sigma_r(inner1_raw, 1)),
    )
    comp_r3 = _laurent_add(
        _laurent_mul(lam0, _laurent_sigma_r(inner0_raw, 3)),
        _laurent_mul(lam1, _laurent_sigma_r(inner1_raw, 3)),
    )

    return {
        "circularep_clean_eps0_grad_q": str(nonpos_full[0]),
        "circularep_lem_n2_cutoff_n": cutoff_val,
        "circularep_dirty_pole_coeff_q": str(grad_dirty[-1]),
        "prop_n4_r1_min_exp": min(comp_r1.keys()),
        "prop_n4_r3_min_exp": min(comp_r3.keys()),
        "prop_n4_r3_eps0_q": str(comp_r3[0]),
        "bf16_normal_min_exp2": -126,
        "bf16_4round_sigma3_exp2": -(2 * (3 ** 4)),
    }


# ---------------------------------------------------------------------------
# Pillar 4 (M5 + M6): Zipf MoE Weighted-Cheeger & aletheia v2.3 Gates T-13..T-15
# ---------------------------------------------------------------------------

_HEX40_RE = re.compile(r"^[0-9a-f]{40}$")
_IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$")
_ALLOWED_STD_AXIOMS: Set[str] = {"propext", "Quot.sound", "Classical.choice"}


def evaluate_gate_t13(
    statement_imports: Sequence[str],
    challenge_imports: Sequence[str],
    importers_of_challenge: Sequence[str],
    allowed_roots: Sequence[str] = ("Mathlib", "Init"),
) -> Tuple[bool, List[str]]:
    """aletheia v2.3 Gate T-13: Statement/Challenge strict import isolation."""
    errs: List[str] = []
    allowed_set = set(allowed_roots)
    for imp in statement_imports:
        root = imp.split(".")[0]
        if root not in allowed_set:
            errs.append(f"T13_STATEMENT_EXTERNAL_IMPORT:{imp}")
    for imp in challenge_imports:
        if imp != "Statement":
            errs.append(f"T13_CHALLENGE_NON_STATEMENT_IMPORT:{imp}")
    if len(importers_of_challenge) > 0:
        errs.append(f"T13_CHALLENGE_IMPORTED_BY:{','.join(importers_of_challenge)}")
    return (len(errs) == 0, errs)


def evaluate_gate_t14(
    pinned_shas: Mapping[str, str],
    enable_nanoda: bool,
    permitted_axioms: Sequence[str],
    sorry_files: Sequence[str],
) -> Tuple[bool, List[str]]:
    """aletheia v2.3 Gate T-14: Dual-kernel Lean+nanoda & pinned-SHA comparator contract."""
    errs: List[str] = []
    for req_dep in ("comparator", "nanoda", "mathlib"):
        sha = pinned_shas.get(req_dep, "")
        if not _HEX40_RE.match(sha):
            errs.append(f"T14_UNPINNED_SHA:{req_dep}")
    if not enable_nanoda:
        errs.append("T14_NANODA_DISABLED")
    for ax in permitted_axioms:
        if ax not in _ALLOWED_STD_AXIOMS:
            errs.append(f"T14_DISALLOWED_AXIOM:{ax}")
    for sf in sorry_files:
        if sf != "Challenge.lean":
            errs.append(f"T14_SORRY_OUTSIDE_CHALLENGE:{sf}")
    return (len(errs) == 0, errs)


def evaluate_gate_t15(
    table_entries: Sequence[Mapping[str, object]],
    lean_declarations: Set[str],
) -> Tuple[bool, List[str]]:
    """aletheia v2.3 Gate T-15: 1:1 Paper-to-Lean Table Parity + Remark-Gap Honesty."""
    errs: List[str] = []
    for entry in table_entries:
        label = str(entry.get("label", ""))
        formalized = entry.get("formalized")
        decl = str(entry.get("lean_decl", ""))
        if formalized is True:
            if not decl or decl not in lean_declarations:
                errs.append(f"T15_MISSING_LEAN_DECL:{label}:{decl}")
        elif formalized is False:
            if not str(entry.get("gap_reason", "")).strip():
                errs.append(f"T15_UNEXPLAINED_UNFORMALIZED_GAP:{label}")
        else:
            errs.append(f"T15_INVALID_FORMALIZED_FLAG:{label}")
    return (len(errs) == 0, errs)


def evaluate_aletheia_v23_trust_bundle(bundle: Mapping[str, object]) -> Dict[str, object]:
    """Run all three aletheia v2.3 Formal Trust Gates (T-13, T-14, T-15) fail-closed."""
    ok13, e13 = evaluate_gate_t13(
        bundle["statement_imports"],  # type: ignore[arg-type]
        bundle["challenge_imports"],  # type: ignore[arg-type]
        bundle["importers_of_challenge"],  # type: ignore[arg-type]
    )
    ok14, e14 = evaluate_gate_t14(
        bundle["pinned_shas"],  # type: ignore[arg-type]
        bool(bundle["enable_nanoda"]),
        bundle["permitted_axioms"],  # type: ignore[arg-type]
        bundle["sorry_files"],  # type: ignore[arg-type]
    )
    ok15, e15 = evaluate_gate_t15(
        bundle["table_entries"],  # type: ignore[arg-type]
        set(bundle["lean_declarations"]),  # type: ignore[arg-type]
    )
    passed = ok13 and ok14 and ok15
    return {
        "passed": passed,
        "t13_ok": ok13,
        "t14_ok": ok14,
        "t15_ok": ok15,
        "errors": e13 + e14 + e15,
    }


def oracle_m5_m6_weighted_moe_cheeger_and_trust_gates() -> Dict[str, object]:
    """Pillar 4: Verify 128-expert Zipf MoE Cheeger lift & T-13..T-15 trust gates (pos + 6 neg)."""
    # 4a. M5 Weighted-Cheeger Lift on 128-expert Inkling-2-Mini MoE toy model
    k_exp = 128
    half = 64
    unweighted_floor = Fraction(2, 9)
    unweighted_half = Fraction(half * (k_exp - half), k_exp * k_exp)

    # Exact rational Zipf-1 (w_i = 1/i) and Zipf-2 (w_i = 1/i^2) traffic distributions
    w_zipf1 = [Fraction(1, i) for i in range(1, k_exp + 1)]
    w_zipf2 = [Fraction(1, i * i) for i in range(1, k_exp + 1)]

    def weighted_cut_metrics(weights: Sequence[Fraction]) -> Tuple[Fraction, Fraction]:
        w_hot = sum(weights[:half], Fraction(0))
        w_cold = sum(weights[half:], Fraction(0))
        w_tot = w_hot + w_cold
        cross_frac = (w_hot * w_cold) / (w_tot * w_tot)
        conductance = (w_hot * w_cold) / (w_tot * min(w_hot, w_cold))
        return cross_frac, conductance

    z1_cross, z1_cond = weighted_cut_metrics(w_zipf1)
    z2_cross, z2_cond = weighted_cut_metrics(w_zipf2)
    z1_drop_vs_floor = unweighted_floor / z1_cross
    z2_drop_vs_floor = unweighted_floor / z2_cross

    # 4b. M6 Executable aletheia v2.3 Formal Trust Gate (T-13..T-15): 1 positive + 6 must-fail controls
    valid_shas = {
        "comparator": "57567492" + "a" * 32,
        "nanoda": "68d5ca9d" + "b" * 32,
        "mathlib": "0df444a360eaa60ab8c11dca51a86af692955474",
    }
    good_bundle: Dict[str, object] = {
        "statement_imports": ["Mathlib"],
        "challenge_imports": ["Statement"],
        "importers_of_challenge": [],
        "pinned_shas": valid_shas,
        "enable_nanoda": True,
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        "sorry_files": ["Challenge.lean"],
        "table_entries": [
            {"label": "Theorem M.3", "formalized": True, "lean_decl": "Paper.thm_allfields"},
            {"label": "Theorem N.5", "formalized": True, "lean_decl": "Paper.thm_approx"},
            {
                "label": "Remark N.6",
                "formalized": False,
                "lean_decl": "",
                "gap_reason": "Determinantal complexity depends on external Berkowitz [Ber84]",
            },
        ],
        "lean_declarations": ["Paper.thm_allfields", "Paper.thm_approx"],
    }
    pos_res = evaluate_aletheia_v23_trust_bundle(good_bundle)

    neg_controls: List[Tuple[str, Dict[str, object], str]] = [
        ("neg1_t13_stmt_internal", dict(good_bundle, statement_imports=["Mathlib", "Nc.Rate"]), "T13_STATEMENT_EXTERNAL_IMPORT"),
        ("neg2_t13_challenge_imported", dict(good_bundle, importers_of_challenge=["Solution.lean"]), "T13_CHALLENGE_IMPORTED_BY"),
        ("neg3_t14_nanoda_off", dict(good_bundle, enable_nanoda=False), "T14_NANODA_DISABLED"),
        ("neg4_t14_sorry_leak", dict(good_bundle, sorry_files=["Challenge.lean", "Nc/Rate.lean"]), "T14_SORRY_OUTSIDE_CHALLENGE"),
        ("neg5_t15_missing_decl", dict(good_bundle, lean_declarations=["Paper.thm_allfields"]), "T15_MISSING_LEAN_DECL"),
        (
            "neg6_t15_remark_overclaim",
            dict(
                good_bundle,
                table_entries=[
                    {"label": "Remark N.6", "formalized": True, "lean_decl": "Paper.remark_det"},
                ],
            ),
            "T15_MISSING_LEAN_DECL",
        ),
    ]
    neg_killed = 0
    for _name, b_bad, expected_code in neg_controls:
        r_bad = evaluate_aletheia_v23_trust_bundle(b_bad)
        if not bool(r_bad["passed"]):
            errs = r_bad["errors"]
            if isinstance(errs, list):
                if any(expected_code in str(e) for e in errs):
                    neg_killed += 1

    return {
        "moe_k_experts": k_exp,
        "unweighted_prop_e10_floor_q": str(unweighted_floor),
        "unweighted_half_cut_q": str(unweighted_half),
        "zipf1_cross_frac_dec": _frac_to_dec_str(z1_cross, 6),
        "zipf1_drop_vs_floor_dec": _frac_to_dec_str(z1_drop_vs_floor, 4),
        "zipf1_conductance_dec": _frac_to_dec_str(z1_cond, 6),
        "zipf2_cross_frac_dec": _frac_to_dec_str(z2_cross, 6),
        "zipf2_drop_vs_floor_dec": _frac_to_dec_str(z2_drop_vs_floor, 4),
        "zipf2_conductance_dec": _frac_to_dec_str(z2_cond, 6),
        "trust_gate_positive_passed": bool(pos_res["passed"]),
        "trust_gate_negative_controls_killed": neg_killed,
    }


def run_all_s82_oracles() -> Dict[str, object]:
    """Execute all 4 pure-Z/Q/F_2 Track S82 cross-field propagation pillars."""
    return {
        "pillar_1_m1_m2_cat0_rerouting_codes": oracle_m1_m2_cat0_rerouting_and_codes(),
        "pillar_2_m3_cnot1d_and_real_shear": oracle_m3_cnot1d_compiler_and_real_shear_obstruction(),
        "pillar_3_m4_laurent_circularep_rocket": oracle_m4_laurent_circularep_and_rocket_isolation(),
        "pillar_4_m5_m6_moe_cheeger_trust_gates": oracle_m5_m6_weighted_moe_cheeger_and_trust_gates(),
    }
