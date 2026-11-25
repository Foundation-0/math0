#!/usr/bin/env python3
"""Pure-Z/Q Exact Oracle & Certificate Builder for Track S76 (Circular Predictive Coding).

100% pure Python 3 stdlib, zero IEEE-754 floats, zero float(), zero bare asserts,
zero .isdigit(), zero random imports.
"""
from __future__ import annotations

from fractions import Fraction
import hashlib
import json
from typing import Any

SCHEMA_VERSION = "aletheia.track_s76.circular_pc_loop_schur.v1"
TRACK_ID = "TRACK-S76-CIRCULAR-PC-LOOP-SCHUR-HOLONOMY"
ANCHOR_SCHEMA_VERSION = "aletheia.track_s76.circularep_live_anchor.v1"
EXPECTED_LEAN_TOOLCHAIN = "leanprover/lean4:v4.36.0"
MAX_JSON_DEPTH = 64
MAX_INT_DIGITS = 2000
MAX_INT_BITS = 8192
_HEX_CHARS = frozenset("0123456789abcdef")
_ASCII_DIGITS = frozenset("0123456789")

LEAN_THEOREM_NAMES: tuple[str, ...] = (
    "CircularPCLoopSchur.loop_schur_2node_metric_exact",
    "CircularPCLoopSchur.loop_schur_2node_metric_softening",
    "CircularPCLoopSchur.loop_schur_3node_metric_exact",
    "CircularPCLoopSchur.loop_hessian_2node_det_eq_monodromy_sq",
    "CircularPCLoopSchur.loop_adjoint_gloop_cancellation",
    "CircularPCLoopSchur.loop_zero_energy_deq_bijection_2node",
    "CircularPCLoopSchur.loop_zero_energy_deq_bijection_3node",
    "CircularPCLoopSchur.ep_cubic_jet_centered_cancels_order1",
    "CircularPCLoopSchur.ep_exact_linear_circular_pc_bias_law",
    "CircularPCLoopSchur.ep_truncated_phase_pole_and_centered_cancellation",
    "CircularPCLoopSchur.ep_truncated_pole_nonzero",
    "CircularPCLoopSchur.contractive_loop_spd_hessian",
    "CircularPCLoopSchur.critical_bifurcation_zero_mode_shadow",
    "CircularPCLoopSchur.krein_deq_lagrangian_indefinite_inertia",
    "CircularPCLoopSchur.non_normal_contractive_transient_amplification",
    "CircularPCLoopSchur.complex_curl_power_iter_oscillation",
    "CircularPCLoopSchur.hessian_gd_stability_cliff_despite_contraction",
    "CircularPCLoopSchur.monodromy_2x2_trace_cyclic_invariance",
    "CircularPCLoopSchur.monodromy_2x2_det_cyclic_invariance",
)


class S76Error(ValueError):
    """Typed fail-closed error for Track S76 oracle and auditor."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


def require_ok(cond: bool, code: str, detail: str) -> None:
    if not cond:
        raise S76Error(code, detail)


def require_bool(val: Any, label: str) -> bool:
    require_ok(type(val) is bool, "INVALID_BOOL", f"{label}: exact bool required")
    return val


def require_exact_int(val: Any, label: str, *, lo: int | None = None, hi: int | None = None) -> int:
    require_ok(type(val) is int, "INVALID_INT", f"{label}: exact int required")
    require_ok(val.bit_length() <= MAX_INT_BITS, "INT_TOO_LARGE", f"{label}: bit_length cap exceeded")
    if lo is not None:
        require_ok(val >= lo, "INT_OUT_OF_RANGE", f"{label}: below lower bound")
    if hi is not None:
        require_ok(val <= hi, "INT_OUT_OF_RANGE", f"{label}: above upper bound")
    return val


def require_exact_str(val: Any, label: str) -> str:
    require_ok(type(val) is str, "INVALID_STR", f"{label}: exact str required")
    try:
        val.encode("utf-8", "strict")
    except UnicodeEncodeError as exc:
        raise S76Error("INVALID_UTF8_SURROGATE", f"{label}: lone surrogate forbidden") from exc
    return val


def require_hex_len(val: Any, length: int, label: str) -> str:
    s = require_exact_str(val, label)
    require_ok(len(s) == length, "INVALID_HEX", f"{label}: expected {length} lowercase hex chars")
    for ch in s:
        require_ok(ch in _HEX_CHARS, "INVALID_HEX", f"{label}: non-hex char")
    return s


def require_hex64(val: Any, label: str) -> str:
    return require_hex_len(val, 64, label)


def is_ascii_digits(s: str) -> bool:
    if not s:
        return False
    for ch in s:
        if ch not in _ASCII_DIGITS:
            return False
    return True


def validate_strict_json_tree(obj: Any, label: str = "json", max_depth: int = MAX_JSON_DEPTH) -> None:
    """Iterative zero-float, zero-subclass, bounded-depth/int/cycle JSON tree validator."""
    active_ids: set[int] = set()
    frames: list[tuple[Any, int, bool]] = [(obj, 0, False)]
    while frames:
        cur, depth, is_exit = frames.pop()
        if is_exit:
            active_ids.discard(cur)
            continue
        require_ok(depth <= max_depth, "JSON_DEPTH_EXCEEDED", f"{label}: nesting exceeds {max_depth}")
        t = type(cur)
        if cur is None or t is bool:
            continue
        if t is int:
            require_ok(cur.bit_length() <= MAX_INT_BITS, "INT_TOO_LARGE", f"{label}: int bit_length exceeded")
            continue
        if t is str:
            require_exact_str(cur, label)
            continue
        if t is list:
            oid = id(cur)
            require_ok(oid not in active_ids, "JSON_CYCLE", f"{label}: cyclic list")
            active_ids.add(oid)
            frames.append((oid, depth, True))
            for item in cur:
                frames.append((item, depth + 1, False))
            continue
        if t is dict:
            oid = id(cur)
            require_ok(oid not in active_ids, "JSON_CYCLE", f"{label}: cyclic dict")
            active_ids.add(oid)
            frames.append((oid, depth, True))
            for k, v in cur.items():
                require_exact_str(k, f"{label} key")
                frames.append((v, depth + 1, False))
            continue
        raise S76Error("INVALID_JSON_TYPE", f"{label}: forbidden type {t.__name__}")


def canonical_json_bytes(obj: Any) -> bytes:
    """Deterministic ASCII LF-terminated canonical JSON bytes (strict zero-float/subclass)."""
    validate_strict_json_tree(obj, "canonical_json")
    text = json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False) + "\n"
    return text.encode("ascii")


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def q_str(q: Fraction) -> str:
    return f"{q.numerator}" if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def dec_from_q(q: Fraction, places: int) -> str:
    """Exact HALF_UP decimal string of Fraction `q` to `places` decimal places via pure integer arithmetic."""
    scale = 10 ** places
    num = q.numerator * scale
    den = q.denominator
    neg = num < 0
    anum = -num if neg else num
    quot, rem = divmod(anum, den)
    if 2 * rem >= den:
        quot += 1
    if quot == 0:
        neg = False
    sign = "-" if neg else ""
    if places == 0:
        return f"{sign}{quot}"
    ip, fp = divmod(quot, scale)
    return f"{sign}{ip}.{fp:0{places}d}"


def parse_decimal_or_sci_to_q(text: Any, label: str) -> Fraction:
    """Parse exact ASCII decimal or scientific string (`1.23e-04`) to exact Fraction (zero floats)."""
    s = require_exact_str(text, label)
    neg = s.startswith("-")
    body = s[1:] if neg or s.startswith("+") else s
    if "e" in body or "E" in body:
        sep = "e" if "e" in body else "E"
        parts = body.split(sep)
        require_ok(len(parts) == 2, "INVALID_DECIMAL", f"{label}: malformed exponent")
        mant, exp_s = parts[0], parts[1]
        exp_neg = exp_s.startswith("-")
        exp_body = exp_s[1:] if exp_neg or exp_s.startswith("+") else exp_s
        require_ok(is_ascii_digits(exp_body) and len(exp_body) <= 4, "INVALID_DECIMAL", f"{label}: bad exponent")
        exp_val = -int(exp_body) if exp_neg else int(exp_body)
        require_ok(-200 <= exp_val <= 200, "INVALID_DECIMAL", f"{label}: exponent out of range")
    else:
        mant = body
        exp_val = 0
    if "." in mant:
        mp = mant.split(".")
        require_ok(len(mp) == 2 and is_ascii_digits(mp[0]) and is_ascii_digits(mp[1]), "INVALID_DECIMAL", f"{label}: bad mantissa")
        digits = mp[0] + mp[1]
        exp_val -= len(mp[1])
    else:
        require_ok(is_ascii_digits(mant), "INVALID_DECIMAL", f"{label}: bad integer mantissa")
        digits = mant
    val = int(digits)
    if neg:
        val = -val
    if exp_val >= 0:
        return Fraction(val * (10 ** exp_val), 1)
    return Fraction(val, 10 ** (-exp_val))


# ---------------------------------------------------------------------------
# Pure-Q Exact Linear Algebra & Bunch-Kaufman Sylvester Inertia
# ---------------------------------------------------------------------------

QMat = list[list[Fraction]]


def q_eye(n: int) -> QMat:
    return [[Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]


def q_zeros(r: int, c: int) -> QMat:
    return [[Fraction(0) for _ in range(c)] for _ in range(r)]


def q_transpose(a: QMat) -> QMat:
    return [[a[i][j] for i in range(len(a))] for j in range(len(a[0]))]


def q_add(a: QMat, b: QMat) -> QMat:
    return [[a[i][j] + b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def q_sub(a: QMat, b: QMat) -> QMat:
    return [[a[i][j] - b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def q_mul(a: QMat, b: QMat) -> QMat:
    m, k, n = len(a), len(b), len(b[0])
    out = q_zeros(m, n)
    for i in range(m):
        for t in range(k):
            at = a[i][t]
            for j in range(n):
                out[i][j] += at * b[t][j]
    return out


def q_mat_vec(a: QMat, v: list[Fraction]) -> list[Fraction]:
    return [sum((a[i][j] * v[j] for j in range(len(v))), Fraction(0)) for i in range(len(a))]


def q_trace(a: QMat) -> Fraction:
    return sum((a[i][i] for i in range(len(a))), Fraction(0))


def q_det(a: QMat) -> Fraction:
    n = len(a)
    m = [row[:] for row in a]
    sign = Fraction(1)
    det = Fraction(1)
    for col in range(n):
        piv = None
        for r in range(col, n):
            if m[r][col] != 0:
                piv = r
                break
        if piv is None:
            return Fraction(0)
        if piv != col:
            m[col], m[piv] = m[piv], m[col]
            sign = -sign
        pv = m[col][col]
        det *= pv
        for r in range(col + 1, n):
            fac = m[r][col] / pv
            for c in range(col, n):
                m[r][c] -= fac * m[col][c]
    return sign * det


def q_solve(a: QMat, b: QMat) -> QMat:
    """Solve A X = B exactly over Q."""
    n = len(a)
    ncols = len(b[0])
    aug = [a[i][:] + b[i][:] for i in range(n)]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if aug[r][col] != 0:
                piv = r
                break
        require_ok(piv is not None, "SINGULAR_MATRIX", "exact Q linear solve encountered singular matrix")
        if piv != col:
            aug[col], aug[piv] = aug[piv], aug[col]
        pv = aug[col][col]
        for c in range(col, n + ncols):
            aug[col][c] /= pv
        for r in range(n):
            if r != col:
                fac = aug[r][col]
                for c in range(col, n + ncols):
                    aug[r][c] -= fac * aug[col][c]
    return [row[n:] for row in aug]


def q_sylvester_inertia(sym: QMat) -> list[int]:
    """Exact pure-Q Bunch-Kaufman symmetric congruence returning [n_pos, n_neg, n_zero]."""
    n = len(sym)
    m = [row[:] for row in sym]
    pos = 0
    neg = 0
    zero = 0
    k = 0
    while k < n:
        piv = None
        for i in range(k, n):
            if m[i][i] != 0:
                piv = i
                break
        if piv is not None:
            if piv != k:
                m[k], m[piv] = m[piv], m[k]
                for r in range(n):
                    m[r][k], m[r][piv] = m[r][piv], m[r][k]
            d = m[k][k]
            if d > 0:
                pos += 1
            else:
                neg += 1
            for i in range(k + 1, n):
                fac = m[i][k] / d
                for j in range(k + 1, n):
                    m[i][j] -= fac * m[k][j]
            k += 1
            continue
        # No nonzero diagonal remaining: search for 2x2 off-diagonal pivot
        pair = None
        for i in range(k, n):
            for j in range(i + 1, n):
                if m[i][j] != 0:
                    pair = (i, j)
                    break
            if pair is not None:
                break
        if pair is None:
            zero += n - k
            break
        pi, pj = pair
        if pi != k:
            m[k], m[pi] = m[pi], m[k]
            for r in range(n):
                m[r][k], m[r][pi] = m[r][pi], m[r][k]
        if pj != k + 1:
            m[k + 1], m[pj] = m[pj], m[k + 1]
            for r in range(n):
                m[r][k + 1], m[r][pj] = m[r][pj], m[r][k + 1]
        # [[0, off], [off, 0]] has eigenvalues +off and -off -> (+1, -1)
        off = m[k][k + 1]
        pos += 1
        neg += 1
        for i in range(k + 2, n):
            c0 = m[i][k + 1] / off
            c1 = m[i][k] / off
            for j in range(k + 2, n):
                m[i][j] -= c0 * m[k][j] + c1 * m[k + 1][j]
        k += 2
    return [pos, neg, zero]


def _block_cyclic_loop_cert(edges: list[QMat], gs_vec: list[Fraction]) -> dict[str, Any]:
    """Exact pure-Q verification of L-layer block-cyclic Loop-Schur, G_loop, and DEQ adjoint."""
    L = len(edges)
    d = len(edges[0])
    n_tot = L * d
    J_R = q_eye(n_tot)
    # Row i corresponds to node i+1 (0-indexed: i=0..L-1; node i predicts from node (i-1) mod L via edges[i])
    for i in range(L):
        src = (i - 1) % L
        Ai = edges[i]
        for r in range(d):
            for c in range(d):
                J_R[i * d + r][src * d + c] -= Ai[r][c]
    H_pc = q_mul(q_transpose(J_R), J_R)

    # Partition into internal nodes (0..(L-1)*d - 1) and readout node L (last d coords)
    n_int = (L - 1) * d
    H_ii = [row[:n_int] for row in H_pc[:n_int]]
    H_iL = [row[n_int:] for row in H_pc[:n_int]]
    H_Li = [row[:n_int] for row in H_pc[n_int:]]
    H_LL = [row[n_int:] for row in H_pc[n_int:]]
    S_direct = q_sub(H_LL, q_mul(H_Li, q_solve(H_ii, H_iL)))

    # Monodromy M_loop = A_L * ... * A_1 and metric G_loop = I + sum_{k=1}^{L-1} P_k P_k^T
    M_loop = q_eye(d)
    for Ai in edges:
        M_loop = q_mul(Ai, M_loop)
    G_loop = q_eye(d)
    suffix = q_eye(d)
    for k in range(L - 1, 0, -1):
        suffix = q_mul(suffix, edges[k])
        G_loop = q_add(G_loop, q_mul(suffix, q_transpose(suffix)))
    ImM = q_sub(q_eye(d), M_loop)
    S_formula = q_mul(q_transpose(ImM), q_solve(G_loop, ImM))
    S_naive = q_mul(q_transpose(ImM), ImM)

    det_h = q_det(H_pc)
    det_imm = q_det(ImM)
    det_g = q_det(G_loop)

    # Exact DEQ adjoint cancellation: solve H_pc dz = [0; -gs], check e_L == -(I - M^T)^{-1} gs
    rhs = [[Fraction(0)] for _ in range(n_int)] + [[-v] for v in gs_vec]
    dz = [row[0] for row in q_solve(H_pc, rhs)]
    e_full = q_mat_vec(J_R, dz)
    e_L_from_h = e_full[n_int:]
    e_L_deq = [row[0] for row in q_solve(q_transpose(ImM), [[-v] for v in gs_vec])]

    # Cyclic basepoint shift M_alt = A_1 * A_L * ... * A_2 (for L=2: A_1 A_2 vs A_2 A_1)
    M_shift = q_eye(d)
    for Ai in edges[1:] + edges[:1]:
        M_shift = q_mul(Ai, M_shift)

    return {
        "n_layers": L,
        "block_dim": d,
        "loop_schur_identity_exact": S_direct == S_formula,
        "naive_without_gloop_strictly_differs": S_direct != S_naive,
        "det_h_eq_det_imm_sq": det_h == det_imm * det_imm,
        "det_h_q": q_str(det_h),
        "det_imm_q": q_str(det_imm),
        "det_g_loop_q": q_str(det_g),
        "g_loop_inertia": q_sylvester_inertia(G_loop),
        "h_pc_inertia": q_sylvester_inertia(H_pc),
        "schur_inertia": q_sylvester_inertia(S_direct),
        "adjoint_gloop_cancellation_exact": e_L_from_h == e_L_deq,
        "non_commuting_holonomy": M_loop != M_shift,
        "monodromy_trace_cyclic_invariant": q_trace(M_loop) == q_trace(M_shift),
        "monodromy_det_cyclic_invariant": q_det(M_loop) == q_det(M_shift),
        "monodromy_trace_q": q_str(q_trace(M_loop)),
        "monodromy_det_q": q_str(q_det(M_loop)),
    }


def certify_pillar1_loop_schur_and_holonomy() -> dict[str, Any]:
    """Pillar 1: Non-commuting L=2 and L=3 block-cyclic Loop-Schur, G_loop, and DEQ adjoint."""
    A1 = [[Fraction(1, 2), Fraction(1, 4)], [Fraction(-1, 5), Fraction(1, 3)]]
    A2 = [[Fraction(2, 5), Fraction(-1, 3)], [Fraction(1, 4), Fraction(1, 2)]]
    A3 = [[Fraction(1, 3), Fraction(1, 5)], [Fraction(-1, 4), Fraction(2, 5)]]
    gs = [Fraction(3, 4), Fraction(-5, 6)]
    w2 = _block_cyclic_loop_cert([A1, A2], gs)
    w3 = _block_cyclic_loop_cert([A1, A2, A3], gs)
    return {"l2_noncommuting_2x2": w2, "l3_noncommuting_2x2": w3}


def check_ep_bias_row_match(bias_1s: Fraction, expected_bias_1s: Fraction, bias_ct: Fraction) -> bool:
    return bias_1s == expected_bias_1s and bias_ct == 0


def check_non_normal_overshoot(t1: Fraction, t2: Fraction, t3: Fraction, t10: Fraction) -> bool:
    return t1 > 1 and t2 > 1 and t3 > 1 and t10 < 1


def check_curl_oscillation_bracket(
    n1_sq: Fraction, rho_sq: Fraction, n2_sq: Fraction, skew_off: Fraction
) -> bool:
    return n1_sq < rho_sq < n2_sq and skew_off != 0


def certify_pillar2_ep_bias_and_truncation() -> dict[str, Any]:
    """Pillar 2: Exact rational O(beta) vs O(beta^2) EP bias and O(e*/beta) truncated-phase blowup."""
    theta = Fraction(1, 3)
    d = Fraction(1) - theta  # 2/3
    c = Fraction(2)
    q = Fraction(3, 2)
    x_star = c / d  # 3
    g_ift = (c * q) / (d * d)  # 27/4
    exact_rows = []
    for beta in (Fraction(1, 5), Fraction(1, 20), Fraction(1, 100)):
        x_p = x_star - beta * q / (d * d)
        x_m = x_star + beta * q / (d * d)
        r_p = d * x_p - c
        r_m = d * x_m - c
        g_p = -x_p * r_p
        g_m = -x_m * r_m
        g_1s = g_p / beta
        g_ct = (g_p - g_m) / (2 * beta)
        bias_1s = g_1s - g_ift
        bias_ct = g_ct - g_ift
        expected_bias_1s = -(q * q) * beta / (d * d * d)
        exact_rows.append({
            "beta_q": q_str(beta),
            "one_sided_q": q_str(g_1s),
            "centered_q": q_str(g_ct),
            "one_sided_bias_q": q_str(bias_1s),
            "centered_bias_q": q_str(bias_ct),
            "bias_matches_formula": check_ep_bias_row_match(bias_1s, expected_bias_1s, bias_ct),
        })

    # Truncated free-phase O(e*/beta) blowup witness
    delta0 = Fraction(1, 100)
    e0 = d * delta0  # 1/150
    x_free = x_star + delta0
    g_free = -x_free * e0  # nonzero!
    gamma_half = Fraction(1, 2)
    trunc_rows = []
    for beta in (Fraction(1, 50), Fraction(1, 500), Fraction(1, 5000)):
        # Case A: inherited half residual in nudge
        xp_a = x_star - beta * q / (d * d) + gamma_half * delta0
        xm_a = x_star + beta * q / (d * d) + gamma_half * delta0
        gp_a = -xp_a * (d * xp_a - c)
        gm_a = -xm_a * (d * xm_a - c)
        err_nosub_a = abs(gp_a / beta - g_ift)
        err_cent_a = abs((gp_a - gm_a) / (2 * beta) - g_ift)
        # Case B: converged nudge (gamma=0), truncated free phase -> subtracting g_free blows up!
        xp_b = x_star - beta * q / (d * d)
        gp_b = -xp_b * (d * xp_b - c)
        err_sub_b = abs((gp_b - g_free) / beta - g_ift)
        trunc_rows.append({
            "beta_q": q_str(beta),
            "nosub_inherited_abs_err_q": q_str(err_nosub_a),
            "sub_converged_nudge_abs_err_q": q_str(err_sub_b),
            "centered_inherited_abs_err_q": q_str(err_cent_a),
        })

    # Verify exact blowup monotonicity and exact centered pole cancellation (constant across all 3 betas!)
    c_errs = [r["centered_inherited_abs_err_q"] for r in trunc_rows]
    return {
        "theta_q": q_str(theta),
        "c_q": q_str(c),
        "q_cost_q": q_str(q),
        "exact_ift_grad_q": q_str(g_ift),
        "exact_phase_rows": exact_rows,
        "truncated_free_delta0_q": q_str(delta0),
        "truncated_free_e0_q": q_str(e0),
        "truncated_free_grad_q": q_str(g_free),
        "truncated_phase_rows": trunc_rows,
        "centered_pole_cancelled_beta_invariant": c_errs[0] == c_errs[1] == c_errs[2],
    }


def certify_pillar3_krein_bifurcation_nonnormal_curl() -> dict[str, Any]:
    """Pillar 3: Contractive SPD + GD cliff, bifurcation shadow, Krein inertia, non-normal & curl."""
    # (1) Contractive 2-node loop a=b=1/2 -> rho=1/4 yet lambda_max(H_PC)=9/4 > 2 (eta_crit=8/9)
    a_c, b_c = Fraction(1, 2), Fraction(1, 2)
    J_con = [[Fraction(1), -a_c], [-b_c, Fraction(1)]]
    H_con = q_mul(q_transpose(J_con), J_con)
    lmax_con = (Fraction(1) + a_c) ** 2
    eta_crit_con = Fraction(2) / lmax_con

    # (2) Critical bifurcation a=2, b=1/2 -> M=1, det(H_PC)=0, shadow vector v=(2, 1)
    a_b, b_b = Fraction(2), Fraction(1, 2)
    J_bif = [[Fraction(1), -a_b], [-b_b, Fraction(1)]]
    H_bif = q_mul(q_transpose(J_bif), J_bif)
    v_shadow = [Fraction(2), Fraction(1)]
    j_v = q_mat_vec(J_bif, v_shadow)
    h_v = q_mat_vec(H_bif, v_shadow)

    # (3) Krein saddle-point inertia for 2x2 contractive M vs rank-1 singular M
    M_spd = [[Fraction(1, 4), Fraction(1, 5)], [Fraction(0), Fraction(1, 3)]]
    ImM_spd = q_sub(q_eye(2), M_spd)
    K_spd = [
        [Fraction(0), Fraction(0), ImM_spd[0][0], ImM_spd[1][0]],
        [Fraction(0), Fraction(0), ImM_spd[0][1], ImM_spd[1][1]],
        [ImM_spd[0][0], ImM_spd[0][1], Fraction(0), Fraction(0)],
        [ImM_spd[1][0], ImM_spd[1][1], Fraction(0), Fraction(0)],
    ]
    M_sing = [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1, 2)]]
    ImM_sing = q_sub(q_eye(2), M_sing)
    K_sing = [
        [Fraction(0), Fraction(0), ImM_sing[0][0], ImM_sing[1][0]],
        [Fraction(0), Fraction(0), ImM_sing[0][1], ImM_sing[1][1]],
        [ImM_sing[0][0], ImM_sing[0][1], Fraction(0), Fraction(0)],
        [ImM_sing[1][0], ImM_sing[1][1], Fraction(0), Fraction(0)],
    ]

    # (4) Non-normal transient amplification: M = [[1/2, 2], [0, 1/2]] -> rho=1/2 < 1, ||M^t e2||^2 > 1 for t=1,2,3
    M_nn = [[Fraction(1, 2), Fraction(2)], [Fraction(0), Fraction(1, 2)]]
    e2 = [Fraction(0), Fraction(1)]
    pow_norms_sq: dict[str, str] = {}
    Mp = q_eye(2)
    for t in range(1, 11):
        Mp = q_mul(Mp, M_nn)
        vec = q_mat_vec(Mp, e2)
        if t in (1, 2, 3, 10):
            pow_norms_sq[f"t{t}"] = q_str(vec[0] * vec[0] + vec[1] * vec[1])

    # (5) Elliptic complex curl: M = [[3/10, -8/5], [2/5, 3/10]] -> rho^2=73/100 < 1, ||M e1||^2 < rho^2 < ||M e2||^2
    c_r, s_r, k_r = Fraction(3, 10), Fraction(2, 5), Fraction(2)
    M_curl = [[c_r, -(k_r * k_r) * s_r], [s_r, c_r]]
    rho_sq_curl = c_r * c_r + (k_r * k_r) * (s_r * s_r)
    n1_sq = M_curl[0][0] ** 2 + M_curl[1][0] ** 2
    n2_sq = M_curl[0][1] ** 2 + M_curl[1][1] ** 2
    skew_off = (M_curl[0][1] - M_curl[1][0]) / 2

    return {
        "contractive_gd_cliff": {
            "rho_q": q_str(a_c * b_c),
            "h_pc_inertia": q_sylvester_inertia(H_con),
            "det_h_q": q_str(q_det(H_con)),
            "lambda_max_h_q": q_str(lmax_con),
            "plain_gd_eta_crit_q": q_str(eta_crit_con),
        },
        "critical_bifurcation_shadow": {
            "h_pc_inertia": q_sylvester_inertia(H_bif),
            "det_h_q": q_str(q_det(H_bif)),
            "shadow_vector_in_ker_jr": j_v == [Fraction(0), Fraction(0)],
            "shadow_vector_in_ker_hpc": h_v == [Fraction(0), Fraction(0)],
        },
        "krein_lagrangian_inertia": {
            "contractive_k_inertia": q_sylvester_inertia(K_spd),
            "contractive_det_k_q": q_str(q_det(K_spd)),
            "bifurcation_k_inertia": q_sylvester_inertia(K_sing),
            "bifurcation_det_k_q": q_str(q_det(K_sing)),
        },
        "non_normal_transient_amplification": {
            "spectral_radius_q": "1/2",
            "norm_sq_e2_by_step": pow_norms_sq,
            "overshoot_t1_to_t3_then_decay_t10": check_non_normal_overshoot(
                Fraction(pow_norms_sq["t1"]),
                Fraction(pow_norms_sq["t2"]),
                Fraction(pow_norms_sq["t3"]),
                Fraction(pow_norms_sq["t10"]),
            ),
        },
        "elliptic_complex_curl_obstruction": {
            "rho_sq_q": q_str(rho_sq_curl),
            "norm_sq_e1_q": q_str(n1_sq),
            "norm_sq_e2_q": q_str(n2_sq),
            "skew_curl_entry_q": q_str(skew_off),
            "strict_oscillation_bracket": check_curl_oscillation_bracket(n1_sq, rho_sq_curl, n2_sq, skew_off),
        },
    }


def certify_pillar4_live_anchor(anchor: dict[str, Any]) -> dict[str, Any]:
    """Pure-Z/Q certification of the frozen live CircularEP best.json anchor receipt."""
    require_ok(type(anchor) is dict, "INVALID_ANCHOR", "anchor must be exact dict")
    validate_strict_json_tree(anchor, "live_anchor")
    require_ok(anchor.get("schema_version") == ANCHOR_SCHEMA_VERSION, "INVALID_ANCHOR_SCHEMA", "schema mismatch")
    require_ok(anchor.get("track_id") == TRACK_ID, "INVALID_ANCHOR_SCHEMA", "track_id mismatch")

    up = anchor["upstream"]
    require_ok(up["repo"] == "rel-int/CircularEP" and up["arxiv_id"] == "2611.27610", "INVALID_ANCHOR", "upstream id")
    require_hex64(up["best_json_sha256"], "best_json_sha256")
    require_hex64(up["puzzles_json_sha256"], "puzzles_json_sha256")
    require_hex64(up["model_js_sha256"], "model_js_sha256")
    require_hex64(up["core_ep_py_sha256"], "core_ep_py_sha256")
    require_hex64(up["core_diagnostics_py_sha256"], "core_diagnostics_py_sha256")

    # Verify float32 parity on both heavy-ball and plain-GD references
    par = anchor["float32_parity"]
    for pk in ("parity", "parity_alt"):
        pr = par[pk]
        require_ok(
            require_exact_int(pr["iters"], f"{pk}.iters", lo=1, hi=150)
            == require_exact_int(pr["ref_iters"], f"{pk}.ref_iters", lo=1, hi=150),
            "PARITY_MISMATCH",
            f"{pk} iters mismatch",
        )
        for fk in ("max_abs_du_free_sci", "max_abs_ds_free_sci", "max_abs_du_nudge_sci", "max_abs_ds_nudge_sci"):
            require_ok(parse_decimal_or_sci_to_q(pr[fk], fk) < Fraction(1, 10**5), "PARITY_MISMATCH", f"{pk}.{fk}")
        require_ok(
            parse_decimal_or_sci_to_q(pr["max_ep_grad_norm_err_sci"], "gnorm_err") < Fraction(1, 10**4),
            "PARITY_MISMATCH",
            f"{pk}.gnorm_err",
        )

    tom = anchor["tomography_300_puzzles"]
    n_puz = require_exact_int(tom["n_puzzles"], "n_puzzles", lo=300, hi=300)
    solved = require_exact_int(tom["solved_count"], "solved_count", lo=0, hi=n_puz)
    wrong = require_exact_int(tom["converged_wrong_count"], "converged_wrong_count", lo=0, hi=n_puz)
    stalled = require_exact_int(tom["stalled_count"], "stalled_count", lo=0, hi=n_puz)
    require_ok(solved + wrong + stalled == n_puz, "COUNT_MISMATCH", "solved+wrong+stalled != 300")
    require_ok(
        solved == require_exact_int(tom["ref_solved_count"], "ref_solved")
        and wrong == require_exact_int(tom["ref_converged_wrong_count"], "ref_wrong"),
        "PARITY_MISMATCH",
        "shipped solved/wrong counts mismatch",
    )

    r128 = tom["rho_first_128_test"]
    require_ok(
        abs(parse_decimal_or_sci_to_q(r128["median_dec6"], "r128_med")
            - parse_decimal_or_sci_to_q(r128["ref_median_dec6"], "r128_ref_med")) <= Fraction(1, 10**4),
        "PARITY_MISMATCH",
        "rho_128 median drift",
    )

    eq = tom["equilibrium_spectra"]
    rho_max = parse_decimal_or_sci_to_q(eq["rho_max_dec6"], "rho_max")
    norm2_max = parse_decimal_or_sci_to_q(eq["norm2_max_dec6"], "norm2_max")
    nn_med = parse_decimal_or_sci_to_q(eq["non_normality_median_dec6"], "nn_med")
    nn_max = parse_decimal_or_sci_to_q(eq["non_normality_max_dec6"], "nn_max")
    cx_cnt = require_exact_int(eq["complex_dominant_count"], "complex_dominant_count", lo=1, hi=n_puz)
    re_cnt = require_exact_int(eq["real_dominant_count"], "real_dominant_count", lo=1, hi=n_puz)
    require_ok(cx_cnt + re_cnt == n_puz, "COUNT_MISMATCH", "cx+re != 300")
    require_ok(rho_max < 1 and norm2_max < 1 and nn_med > 2, "SPECTRAL_BOUND_FAIL", "contractive + non-normal")

    sch = tom["loop_schur_and_hessian_512x512"]
    require_exact_int(sch["n_verified"], "schur_n", lo=300, hi=300)
    sch_err = parse_decimal_or_sci_to_q(sch["max_schur_identity_abs_err_sci"], "schur_err")
    g_lo = parse_decimal_or_sci_to_q(sch["g_loop_lambda_max_lo_dec6"], "g_lo")
    g_hi = parse_decimal_or_sci_to_q(sch["g_loop_lambda_max_hi_dec6"], "g_hi")
    require_ok(sch_err < Fraction(1, 10**12) and g_lo > 1 and g_hi > g_lo, "SCHUR_ANCHOR_FAIL", "Loop-Schur anchor")

    gd = tom["plain_gd_eta_0p8_cliff"]
    gd_conv = require_exact_int(gd["converged_count"], "gd_conv", lo=1, hi=n_puz)
    gd_div = require_exact_int(gd["diverged_count"], "gd_div", lo=1, hi=n_puz)
    gd_conv_le = require_exact_int(gd["converged_with_lmax_le_2p5"], "gd_conv_le", lo=0, hi=gd_conv)
    gd_div_gt = require_exact_int(gd["diverged_with_lmax_gt_2p5"], "gd_div_gt", lo=0, hi=gd_div)
    require_ok(gd_conv + gd_div == n_puz and gd_conv_le == gd_conv, "GD_CLIFF_FAIL", "all converged must satisfy lmax <= 2.5")

    pi = tom["power_iter_60_curl_bias"]
    pi_real_med = parse_decimal_or_sci_to_q(pi["real_dom_median_rel_err_sci"], "pi_real_med")
    pi_cx_med = parse_decimal_or_sci_to_q(pi["complex_dom_median_rel_err_dec6"], "pi_cx_med")
    require_ok(pi_real_med > 0 and pi_cx_med > pi_real_med * (10 ** 8), "CURL_BIAS_FAIL", "power-iter complex bias > 1e8x")
    pi_ratio = pi_cx_med / pi_real_med

    # Verify exact-phase O(beta) vs O(beta^2) ratios & truncated-phase blowup on test-0016 & test-0065
    ep_summary: dict[str, Any] = {}
    for pid in ("test-0016", "test-0065"):
        pt = anchor["ep_gradient_tomography"][pid]
        adj_err = parse_decimal_or_sci_to_q(pt["gloop_adjoint_cancel_max_abs_err_sci"], f"{pid}.adj_err")
        require_ok(adj_err < Fraction(1, 10**14), "ADJOINT_CANCEL_FAIL", pid)
        ex_by_b = {r["beta"]: r for r in pt["exact_phase_beta_sweep"]}
        e1_001 = parse_decimal_or_sci_to_q(ex_by_b["0.01"]["one_sided_rel_err_dec8"], "e1_001")
        e1_0002 = parse_decimal_or_sci_to_q(ex_by_b["0.002"]["one_sided_rel_err_dec8"], "e1_0002")
        ec_001 = parse_decimal_or_sci_to_q(ex_by_b["0.01"]["centered_rel_err_dec8"], "ec_001")
        ec_0002 = parse_decimal_or_sci_to_q(ex_by_b["0.002"]["centered_rel_err_dec8"], "ec_0002")
        r1_step = e1_001 / e1_0002  # expect ~5 (O(beta))
        rc_step = ec_001 / ec_0002  # expect ~25 (O(beta^2))
        require_ok(Fraction(45, 10) <= r1_step <= Fraction(55, 10), "EP_ORDER_FAIL", f"{pid} O(beta)")
        require_ok(Fraction(24, 1) <= rc_step <= Fraction(26, 1), "EP_ORDER_FAIL", f"{pid} O(beta^2)")

        tr_by_name = {t["regime"]: t for t in pt["truncated_free_phase_sweep"]}
        t10_rows = {r["beta"]: r for r in tr_by_name["T10"]["beta_rows"]}
        def_rows = {r["beta"]: r for r in tr_by_name["default_E_lt_1e6"]["beta_rows"]}
        t10_nosub_0005 = parse_decimal_or_sci_to_q(t10_rows["0.0005"]["nosub_rel_err_dec6"], "t10_nosub")
        t10_sub_0005 = parse_decimal_or_sci_to_q(t10_rows["0.0005"]["sub_rel_err_dec6"], "t10_sub")
        t10_cent_0005 = parse_decimal_or_sci_to_q(t10_rows["0.0005"]["centered_rel_err_dec6"], "t10_cent")
        def_sub_0005 = parse_decimal_or_sci_to_q(def_rows["0.0005"]["sub_rel_err_dec6"], "def_sub")
        def_cent_0005 = parse_decimal_or_sci_to_q(def_rows["0.0005"]["centered_rel_err_dec6"], "def_cent")
        require_ok(
            t10_nosub_0005 > 1 and t10_sub_0005 > 1000 and def_sub_0005 > 5 and t10_cent_0005 < Fraction(1, 100) and def_cent_0005 < Fraction(1, 100),
            "EP_BLOWUP_FAIL",
            pid,
        )
        ep_summary[pid] = {
            "exact_1s_ratio_0p01_over_0p002_dec2": dec_from_q(r1_step, 2),
            "exact_centered_ratio_0p01_over_0p002_dec2": dec_from_q(rc_step, 2),
            "t10_beta_0p0005_nosub_err_dec4": dec_from_q(t10_nosub_0005, 4),
            "t10_beta_0p0005_sub_err_dec2": dec_from_q(t10_sub_0005, 2),
            "t10_beta_0p0005_centered_err_dec4": dec_from_q(t10_cent_0005, 4),
            "default_E1e6_beta_0p0005_sub_err_dec4": dec_from_q(def_sub_0005, 4),
            "default_E1e6_beta_0p0005_centered_err_dec4": dec_from_q(def_cent_0005, 4),
            "centered_advantage_vs_nosub_t10_dec1": dec_from_q(t10_nosub_0005 / t10_cent_0005, 1),
        }

    sv = tom["solved_vs_wrong_separation"]
    solved_med_rho = parse_decimal_or_sci_to_q(sv["solved_median_rho_dec6"], "solved_med_rho")
    wrong_med_rho = parse_decimal_or_sci_to_q(sv["wrong_median_rho_dec6"], "wrong_med_rho")
    require_ok(wrong_med_rho > solved_med_rho, "SOLVED_WRONG_SEP_FAIL", "wrong median rho must exceed solved")

    return {
        "upstream_repo": up["repo"],
        "upstream_commit_sha": up["commit_sha"],
        "best_json_sha256": up["best_json_sha256"],
        "puzzles_json_sha256": up["puzzles_json_sha256"],
        "float32_parity_verified": True,
        "shipped_solved_count": solved,
        "shipped_converged_wrong_count": wrong,
        "shipped_solved_pct_dec2": dec_from_q(Fraction(solved * 100, n_puz), 2),
        "contractive_at_equilibrium": True,
        "eq_rho_max_dec6": eq["rho_max_dec6"],
        "eq_norm2_max_dec6": eq["norm2_max_dec6"],
        "non_normality_median_dec4": dec_from_q(nn_med, 4),
        "non_normality_max_dec4": dec_from_q(nn_max, 4),
        "complex_dominant_count": cx_cnt,
        "complex_dominant_pct_dec2": dec_from_q(Fraction(cx_cnt * 100, n_puz), 2),
        "wrong_vs_solved_median_rho_pct_dec2": dec_from_q((wrong_med_rho - solved_med_rho) * 100 / solved_med_rho, 2),
        "loop_schur_300_verified": True,
        "loop_schur_300_max_abs_err_sci": sch["max_schur_identity_abs_err_sci"],
        "g_loop_softening_max_dec4": dec_from_q(g_hi, 4),
        "plain_gd_eta_0p8_converged_le_2p5_exact": f"{gd_conv_le}/{gd_conv}",
        "plain_gd_eta_0p8_diverged_gt_2p5_exact": f"{gd_div_gt}/{gd_div}",
        "power_iter_complex_vs_real_error_ratio_dec0": dec_from_q(pi_ratio, 0),
        "ep_gradient_summary": ep_summary,
    }


def build_certificate(
    *,
    anchor: dict[str, Any],
    anchor_sha256: str,
    lean_source_sha256: str,
    toolchain_sha256: str,
    lakefile_sha256: str,
) -> dict[str, Any]:
    """Assemble deterministic canonical Track S76 certificate (pure-Z/Q, zero floats)."""
    require_hex64(anchor_sha256, "anchor_sha256")
    require_hex64(lean_source_sha256, "lean_source_sha256")
    require_hex64(toolchain_sha256, "toolchain_sha256")
    require_hex64(lakefile_sha256, "lakefile_sha256")

    p1 = certify_pillar1_loop_schur_and_holonomy()
    p2 = certify_pillar2_ep_bias_and_truncation()
    p3 = certify_pillar3_krein_bifurcation_nonnormal_curl()
    p4 = certify_pillar4_live_anchor(anchor)

    payload = {
        "schema_version": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "oracle_class": "exact+anchor",
        "novelty_classification": "N1",
        "pinned_artifacts": {
            "lean_source": "CircularPCLoopSchur.lean",
            "lean_source_sha256": lean_source_sha256,
            "lean_toolchain": EXPECTED_LEAN_TOOLCHAIN,
            "lean_toolchain_sha256": toolchain_sha256,
            "lakefile_sha256": lakefile_sha256,
            "live_anchor_file": "s76_circularep_live_anchor.json",
            "live_anchor_sha256": anchor_sha256,
            "lean_theorem_count": len(LEAN_THEOREM_NAMES),
            "lean_theorem_names": list(LEAN_THEOREM_NAMES),
        },
        "pillar1_loop_schur_and_holonomy": p1,
        "pillar2_ep_bias_and_truncation": p2,
        "pillar3_krein_bifurcation_nonnormal_curl": p3,
        "pillar4_live_circularep_anchor": p4,
    }
    p_sha = sha256_hex(canonical_json_bytes(payload))
    env = {
        "schema_version": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": p_sha,
        "payload": payload,
    }
    c_sha = sha256_hex(canonical_json_bytes(env))
    env["certificate_sha256"] = c_sha
    return env
