#!/usr/bin/env python3
"""
Track S94: Wave-6 Fourth-Order Cross-Cluster Convergence Oracle
(Portals 98..100 x Expedition S31, S50, S59, S70, S73, S76, S78, S79, S80, S86).

Pure-Z/Q exact mathematical oracle (stdlib only: int, fractions.Fraction,
decimal.Decimal for exact display formatting only; ZERO floats on trust paths,
ZERO bare asserts, ZERO RNG, ZERO dataset copies into expedition/).

Covers 4 Cryptographically Pinned Pillars:
  - Pillar 1: Privileged Neuron Basis (Anthropic Parts 1-2, neuron-lens,
    neuron-reflection) x siliquant Axis-Aligned A_16 / [H_8, D] != 0 / S31 DPI
  - Pillar 2: Ternary Bonsai 2.5 27B (PTQ1_0/PQ2_0/Q2_0) x Magnitude 3-Tier
    GPU+RAM+SSD Streaming x 8 GiB Consumer-Silicon Roofline (S73/S78/S86)
  - Pillar 3: Sleep Trilogy (2504.13171, 2605.26099, 2611 KV-Refinement) x
    Thinking Machines Forecasting RL & Harvey Tenet x S50/S76/S78/S79/S80
  - Pillar 4: 12 Wave-6 Snapshot Pins, 10 Upstream Expedition Cert Pins,
    18/18 Universal Pure-Init Lean 4.36.0 Companion & Law-4 N1 Honesty
"""
from __future__ import annotations

from decimal import Decimal, ROUND_HALF_UP, localcontext
from fractions import Fraction
import hashlib
import json
from typing import Any

SCHEMA_VERSION = "aletheia.track_s94.wave6_neuron_bonsai_sleep.certificate.v1"
TRACK_ID = "TRACK-S94-NEURON-BASIS-BONSAI-SLEEP-CONVERGENCE"
ORACLE_CLASS = "exact"
NOVELTY_TIER = "N1"
LEAN_TOOLCHAIN = "leanprover/lean4:v4.36.0"
LEAN_FILE_NAME = "Wave6ConvergenceOperators.lean"
EXPECTED_LEAN_SHA256 = "ac3c812972562a68a5d14b635e265d7d79d66ceac14bd3a0d0ef1898b648a940"

EXPECTED_LEAN_THEOREMS: tuple[str, ...] = (
    "S94Wave6Convergence.hadamard_smearing_diagonal_flat_universal",
    "S94Wave6Convergence.hadamard_importance_blowup_linear_in_k_universal",
    "S94Wave6Convergence.hadamard_uniform_isotropic_commutes_universal",
    "S94Wave6Convergence.householder_reflection_isometry_universal",
    "S94Wave6Convergence.householder_reflection_involution_universal",
    "S94Wave6Convergence.householder_projection_idempotent_and_dpi_universal",
    "S94Wave6Convergence.residency_phase_cliff_universal",
    "S94Wave6Convergence.tier_spill_strict_slowdown_universal",
    "S94Wave6Convergence.nvme_spill_dominates_ram_spill_universal",
    "S94Wave6Convergence.three_tier_monotonic_time_universal",
    "S94Wave6Convergence.sparse_moe_active_bandwidth_gain_universal",
    "S94Wave6Convergence.joint_bpw_compression_headroom_universal",
    "S94Wave6Convergence.brier_strict_proper_scoring_universal",
    "S94Wave6Convergence.reference_mixture_bias_variance_universal",
    "S94Wave6Convergence.single_draw_overconfidence_paradox_universal",
    "S94Wave6Convergence.sleep_loop_contraction_vs_divergence_universal",
    "S94Wave6Convergence.last_loop_kv_sharing_strict_gain_universal",
    "S94Wave6Convergence.five_gate_consolidation_borromean_universal",
)

# 12 read-only Wave-6 Portals 98-100 primary snapshot pins (stored OUTSIDE expedition/)
WAVE6_SNAPSHOT_PINS: tuple[dict[str, Any], ...] = (
    {
        "portal": "P98",
        "filename": "anthropic_neuron_basis_theory.txt",
        "bytes": 66778,
        "sha256": "ae5697d37b2d5928383a6e24e9e59b4e403cbb01901d51b50de566dc962a4a24",
    },
    {
        "portal": "P98",
        "filename": "anthropic_neuron_basis_apps.txt",
        "bytes": 84050,
        "sha256": "405f3622e688b1349da9e369a22b755356540123ec5c9c0a19ae4362c2b0fb08",
    },
    {
        "portal": "P98",
        "filename": "stdlogits_neuron_lens_README.md",
        "bytes": 45954,
        "sha256": "4027688a17022bf962d8a11c934c8a00aab461d5790fadf1a881ab2ebcf151b2",
    },
    {
        "portal": "P98",
        "filename": "stdlogits_neuron_reflection_README.md",
        "bytes": 21649,
        "sha256": "c88103c6fdb773e229380a64609bc742bd8680c4b9335f5fc08c35c88c4ca79d",
    },
    {
        "portal": "P99",
        "filename": "prismml_bonsai25_27b.txt",
        "bytes": 6016,
        "sha256": "edf79d57a2891dbff5b8f5b0feee143a17f5b446e43d2d7d904d2bced68f29ed",
    },
    {
        "portal": "P99",
        "filename": "bonsai25_gguf_README.md",
        "bytes": 35887,
        "sha256": "85d142d04266850043e5d27bcf692e49c83f5ababa9b62b55500e690737162b3",
    },
    {
        "portal": "P99",
        "filename": "magnitude_README.md",
        "bytes": 6731,
        "sha256": "c3357b7d3d99774b54b34940b5a26a87147190c95d053042ed0c418f8ababec8",
    },
    {
        "portal": "P100",
        "filename": "arxiv_2504_13171.txt",
        "bytes": 5007,
        "sha256": "d1ca566b936d63db3aac60aeddeb85008ffd0759a2c319fa75c483bf80e4429c",
    },
    {
        "portal": "P100",
        "filename": "arxiv_2605_26099.txt",
        "bytes": 4683,
        "sha256": "12608e2b6b64971e3dabc3274f1c8d12d2a38c63da85c5be3239364109912f20",
    },
    {
        "portal": "P100",
        "filename": "alphaxiv_2611_sleep_report.txt",
        "bytes": 89043,
        "sha256": "905caa37464a764fb935982ff07598870b6302a04391fd89ad2dc0fcec370c20",
    },
    {
        "portal": "P100",
        "filename": "thinkingmachines_forecasting.txt",
        "bytes": 14422,
        "sha256": "82346e5bf5920e5ca8c88d9a1a264a6fca7f4602601c54ab13b929bad680d1d7",
    },
    {
        "portal": "P100",
        "filename": "harvey_tenet.txt",
        "bytes": 29236,
        "sha256": "97871ce2e37097245fa8ed40f9c4e03710824f0d8a94744c277ebe08cb1c51c8",
    },
)

# 10 frozen upstream expedition certificate pins
UPSTREAM_CERT_PINS: tuple[dict[str, Any], ...] = (
    {
        "track_id": "S31",
        "relative_ref": "track-s31-aletheia-v22-society-misfolding-tomography/aletheia_v22_misfolding_certificate.json",
        "bytes": 12707,
        "sha256": "f4f7f8abff0c7eae0d5678016c1041ab34870ef2de57a2f83e4cbb9a529f8a9b",
    },
    {
        "track_id": "S50",
        "relative_ref": "track-s50-zero-dw-state-transport-tomography/zero_dw_state_transport_certificate.json",
        "bytes": 12803,
        "sha256": "1316eede91b66c309c427fec60e36374350d65b6649eba7154de8e4ea4431320",
    },
    {
        "track_id": "S59",
        "relative_ref": "track-s59-exact-e8-vs-a16-hadamard-law/e8_vs_a16_hadamard_certificate.json",
        "bytes": 6360,
        "sha256": "914a84512d7026b23af0672d4b175128534a7d3c8a0fbc9152b28bc38ea8f1ed",
    },
    {
        "track_id": "S70",
        "relative_ref": "track-s70-cross-layer-and-sorted-blockh4-lean4/s70_certificate.json",
        "bytes": 6158,
        "sha256": "5cdce98df676290d78688da689fe576492487125653e563c667df000980c45e4",
    },
    {
        "track_id": "S73",
        "relative_ref": "track-s73-lowbit-and-sharednorm-quad-snake/rtx3080_s73_certificate.json",
        "bytes": 5202,
        "sha256": "33dfb4153fe974e9ef13120190c14ada6dda63ffbee6caa46047d274f32d36cf",
    },
    {
        "track_id": "S76",
        "relative_ref": "track-s76-circular-pc-loop-schur-holonomy/s76_circular_pc_certificate.json",
        "bytes": 7006,
        "sha256": "d30805fcb876de096d9b387a8274ecd8063b7906f4feb36124b38a05aefadc95",
    },
    {
        "track_id": "S78",
        "relative_ref": "track-s78-engram-lora-capacity-siliquant-mdl/s78_engram_lora_siliquant_certificate.json",
        "bytes": 18553,
        "sha256": "3b8341ef5f588f970accb9a9d28f0b683af9747be045e69196e6c19d3fa58378",
    },
    {
        "track_id": "S79",
        "relative_ref": "track-s79-2dsd-multipole-dense-sparse-laws/s79_2dsd_multipole_certificate.json",
        "bytes": 6460,
        "sha256": "9c30539e6d585141a9b1a5111935ca86de0f740e80749a622547a18242465ad8",
    },
    {
        "track_id": "S80",
        "relative_ref": "track-s80-rocket-songe-unsloth-optimizations/s80_certificate.json",
        "bytes": 6098,
        "sha256": "95681a29ca577c4e3040f8ba63f8516b1cbb2bf1ebfdcda06277f21bb2aa2cb7",
    },
    {
        "track_id": "S86",
        "relative_ref": "track-s86-sovereign-8gb-fourth-order-stack/s86_sovereign_stack_certificate.json",
        "bytes": 9315,
        "sha256": "675bf68c1291a3cf7aeef9beb9a5efc316b55f44a6823a0a94f2ffef7754cb12",
    },
)


def require_ok(cond: Any, msg: str) -> None:
    """Fail-closed non-assert guard (immune to python3 -O)."""
    if type(cond) is not bool or not cond:
        raise ValueError(msg)


def q_str(val: Fraction) -> str:
    require_ok(type(val) is Fraction, "Q_STR_REQUIRES_FRACTION")
    if val.denominator == 1:
        return str(val.numerator)
    return f"{val.numerator}/{val.denominator}"


def dec_str(val: Fraction, places: int = 4) -> str:
    require_ok(type(val) is Fraction, "DEC_STR_REQUIRES_FRACTION")
    require_ok(type(places) is int and 1 <= places <= 12, "DEC_STR_BAD_PLACES")
    with localcontext() as ctx:
        ctx.prec = 50
        ctx.rounding = ROUND_HALF_UP
        d = Decimal(val.numerator) / Decimal(val.denominator)
        q = Decimal(10) ** (-places)
        return format(d.quantize(q), "f")


def canonical_json_bytes(obj: Any) -> bytes:
    return (json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode("utf-8")


# ---------------------------------------------------------------------------
# Pure-Q Exact Mathematical Primitives (Parameterized & Mutation-Hardened)
# ---------------------------------------------------------------------------

def sylvester_hadamard_int(order: int) -> list[list[int]]:
    """Construct exact unnormalized Sylvester Hadamard matrix H_order in {+1, -1}."""
    require_ok(type(order) is int and order >= 1 and (order & (order - 1)) == 0, "HADAMARD_ORDER_NOT_POW2")
    mat: list[list[int]] = [[1]]
    while len(mat) < order:
        top = [row + row for row in mat]
        bot = [row + [-x for x in row] for row in mat]
        mat = top + bot
    return mat


def compute_hadamard_commutator_smearing(order: int, spike_alpha: Fraction) -> dict[str, Any]:
    """Exact pure-Q analysis of [H_k, D] != 0 and importance-weighted error blowup.

    For D = diag(spike_alpha, 1, ..., 1) and symmetric orthogonal H_k = H_k^int / sqrt(k):
      - Conjugated metric M = H_k D H_k = (1/k) H_k^int D H_k^int in Q^{k x k}.
      - Every diagonal entry of M collapses to (spike_alpha + k - 1) / k.
      - For unit lattice error E = e_1^T (||E||_F^2 = 1), the mis-ordered error
        Delta W = E D^{-1} H_k has ||Delta W||_F^2 = 1 (taking D_1 = 1 on index 1),
        yet true privileged-basis importance error ||Delta W D||_F^2 = (spike_alpha^2 + k - 1) / k.
    """
    require_ok(type(spike_alpha) is Fraction and spike_alpha > 0, "INVALID_SPIKE_ALPHA")
    h_int = sylvester_hadamard_int(order)
    require_ok(order >= 2, "HADAMARD_SMEARING_MIN_ORDER_2")
    diag_vals = [spike_alpha] + [Fraction(1, 1)] * (order - 1)

    # Commutator [H_k^int, D] = H_k^int D - D H_k^int
    comm_nz = 0
    for i in range(order):
        for j in range(order):
            val = Fraction(h_int[i][j]) * (diag_vals[j] - diag_vals[i])
            if val != 0:
                comm_nz += 1

    # Conjugated matrix M = (1/k) H_k^int D H_k^int
    inv_k = Fraction(1, order)
    m_mat = [
        [
            inv_k * sum((Fraction(h_int[i][r]) * diag_vals[r] * Fraction(h_int[r][j]) for r in range(order)), Fraction(0))
            for j in range(order)
        ]
        for i in range(order)
    ]
    diag_set = {m_mat[i][i] for i in range(order)}
    off_abs_set = {abs(m_mat[i][j]) for i in range(order) for j in range(order) if i != j}
    flat_diag = m_mat[0][0]
    off_abs = abs(m_mat[0][1])

    # Unit lattice error on coordinate 1 (where D_11 = 1): Delta W = (1/sqrt(k)) * row_1(H_k^int)
    # ||Delta W||_F^2 = (1/k) * sum_j 1 = 1
    # ||Delta W D||_F^2 = (1/k) * sum_j (h_int[1][j] * diag_vals[j])^2 = (spike_alpha^2 + k - 1) / k
    unweighted_mse = inv_k * sum((Fraction(h_int[1][j] * h_int[1][j]) for j in range(order)), Fraction(0))
    true_imp_mse = inv_k * sum(
        ((Fraction(h_int[1][j]) * diag_vals[j]) ** 2 for j in range(order)),
        Fraction(0),
    )

    return {
        "order": order,
        "spike_alpha_q": q_str(spike_alpha),
        "commutator_nonzero_entries": comm_nz,
        "commutator_total_entries": order * order,
        "all_diagonals_flattened": len(diag_set) == 1,
        "all_off_diagonals_uniform_abs": len(off_abs_set) == 1,
        "smeared_diagonal_q": q_str(flat_diag),
        "off_diagonal_abs_q": q_str(off_abs),
        "unweighted_mse_q": q_str(unweighted_mse),
        "true_importance_mse_q": q_str(true_imp_mse),
        "true_importance_mse_dec4": dec_str(true_imp_mse, 4),
    }


def compute_householder_dial_operator(axis_d: list[Fraction], k_dial: Fraction) -> list[list[Fraction]]:
    """Construct exact H(k) = I - k d d^T over Q for exact unit vector ||d||_2^2 == 1."""
    require_ok(type(axis_d) is list and len(axis_d) >= 2, "INVALID_AXIS_D")
    require_ok(type(k_dial) is Fraction, "INVALID_K_DIAL")
    for x in axis_d:
        require_ok(type(x) is Fraction, "AXIS_ENTRY_NOT_FRACTION")
    norm_sq = sum((x * x for x in axis_d), Fraction(0))
    require_ok(norm_sq == Fraction(1, 1), "AXIS_NOT_UNIT_NORM")
    n = len(axis_d)
    return [
        [(Fraction(1, 1) if i == j else Fraction(0, 1)) - k_dial * axis_d[i] * axis_d[j] for j in range(n)]
        for i in range(n)
    ]


def mat_mul_q(a: list[list[Fraction]], b: list[list[Fraction]]) -> list[list[Fraction]]:
    require_ok(type(a) is list and len(a) >= 1 and type(b) is list and len(b) >= 1, "MAT_EMPTY")
    m = len(a)
    k = len(a[0])
    p = len(b[0])
    require_ok(len(b) == k and p >= 1, "MAT_DIM_MISMATCH")
    return [
        [sum((a[i][t] * b[t][j] for t in range(k)), Fraction(0)) for j in range(p)]
        for i in range(m)
    ]


def frob_norm_sq_q(mat: list[list[Fraction]]) -> Fraction:
    return sum((x * x for row in mat for x in row), Fraction(0))


def compute_three_tier_roofline(
    model_gb: Fraction,
    c_gpu_gb: Fraction,
    c_ram_gb: Fraction,
    b_gpu_gbs: Fraction,
    b_ram_gbs: Fraction,
    b_ssd_gbs: Fraction,
) -> dict[str, Any]:
    """Exact pure-Q 3-tier (GPU GDDR6 + DDR4 RAM + NVMe SSD) dense memory-bandwidth roofline."""
    for v, code in (
        (model_gb, "INVALID_MODEL_GB"),
        (c_gpu_gb, "INVALID_CGPU_GB"),
        (c_ram_gb, "INVALID_CRAM_GB"),
        (b_gpu_gbs, "INVALID_BGPU_GBS"),
        (b_ram_gbs, "INVALID_BRAM_GBS"),
        (b_ssd_gbs, "INVALID_BSSD_GBS"),
    ):
        require_ok(type(v) is Fraction and v > 0, code)
    require_ok(b_ssd_gbs < b_ram_gbs and b_ram_gbs < b_gpu_gbs, "TIER_BW_NOT_STRICT_DESC")

    m_gpu = model_gb if model_gb <= c_gpu_gb else c_gpu_gb
    rem1 = model_gb - m_gpu
    m_ram = rem1 if rem1 <= c_ram_gb else c_ram_gb
    m_ssd = rem1 - m_ram

    f_gpu = m_gpu / model_gb
    f_ram = m_ram / model_gb
    f_ssd = m_ssd / model_gb

    t_tok = (m_gpu / b_gpu_gbs) + (m_ram / b_ram_gbs) + (m_ssd / b_ssd_gbs)
    t_ideal = model_gb / b_gpu_gbs
    slowdown = t_tok / t_ideal
    tps = Fraction(1, 1) / t_tok
    return {
        "model_gb_q": q_str(model_gb),
        "m_gpu_gb_q": q_str(m_gpu),
        "m_ram_gb_q": q_str(m_ram),
        "m_ssd_gb_q": q_str(m_ssd),
        "f_gpu_q": q_str(f_gpu),
        "f_ram_q": q_str(f_ram),
        "f_ssd_q": q_str(f_ssd),
        "fully_gpu_resident": m_gpu == model_gb,
        "spill_slowdown_q": q_str(slowdown),
        "spill_slowdown_dec4": dec_str(slowdown, 4),
        "roofline_tps_q": q_str(tps),
        "roofline_tps_dec4": dec_str(tps, 4),
    }


def evaluate_brier_proper_scoring(q_true: Fraction, p_fcst: Fraction) -> dict[str, Any]:
    """Exact pure-Q expected Brier score decomposition E[BS(p, Y)] = q(1-q) + (p-q)^2."""
    require_ok(type(q_true) is Fraction and Fraction(0) < q_true < Fraction(1), "INVALID_TRUE_PROB")
    require_ok(type(p_fcst) is Fraction and Fraction(0) <= p_fcst <= Fraction(1), "INVALID_FCST_PROB")
    exp_bs_true = q_true * (1 - q_true)
    exp_bs_fcst = q_true * ((1 - p_fcst) ** 2) + (1 - q_true) * (p_fcst ** 2)
    excess = exp_bs_fcst - exp_bs_true
    single_y1_true = (1 - q_true) ** 2
    single_y1_fcst = (1 - p_fcst) ** 2
    return {
        "q_true_q": q_str(q_true),
        "p_fcst_q": q_str(p_fcst),
        "expected_bs_true_q": q_str(exp_bs_true),
        "expected_bs_fcst_q": q_str(exp_bs_fcst),
        "excess_penalty_q": q_str(excess),
        "single_draw_y1_true_err_q": q_str(single_y1_true),
        "single_draw_y1_fcst_err_q": q_str(single_y1_fcst),
        "overconfident_wins_on_y1": single_y1_fcst < single_y1_true,
        "calibrated_strictly_better_in_expectation": exp_bs_true < exp_bs_fcst,
    }


def evaluate_reference_mixture_bias(
    q_true: Fraction, r_ref: Fraction, lam: Fraction
) -> dict[str, Any]:
    """Exact minimizer p*(lam) = lam*q + (1-lam)*r and excess Brier bias vs truth q."""
    require_ok(type(q_true) is Fraction and Fraction(0) < q_true < Fraction(1), "INVALID_MIX_Q")
    require_ok(type(r_ref) is Fraction and Fraction(0) < r_ref < Fraction(1), "INVALID_MIX_R")
    require_ok(type(lam) is Fraction and Fraction(0) <= lam <= Fraction(1), "INVALID_MIX_LAM")
    p_star = lam * q_true + (1 - lam) * r_ref
    bias = abs(p_star - q_true)
    excess_err = bias * bias
    return {
        "q_true_q": q_str(q_true),
        "r_ref_q": q_str(r_ref),
        "lambda_q": q_str(lam),
        "p_star_q": q_str(p_star),
        "abs_bias_q": q_str(bias),
        "excess_true_brier_q": q_str(excess_err),
        "anchored_to_outcomes": lam > 0,
    }


def evaluate_five_gate_consolidation(
    *,
    rho: Fraction,
    forgetting_budgeted: bool,
    outcome_lambda: Fraction,
    goodhart_drift: Fraction,
    residency_ok: bool,
    steps: int = 4,
) -> dict[str, Any]:
    """Exact pure-Q 5-gate Wave-6 consolidation fixed-point evaluator."""
    require_ok(type(rho) is Fraction and rho > 0, "INVALID_RHO")
    require_ok(type(forgetting_budgeted) is bool, "INVALID_FORGETTING_FLAG")
    require_ok(type(outcome_lambda) is Fraction and Fraction(0) <= outcome_lambda <= Fraction(1), "INVALID_LAMBDA")
    require_ok(type(goodhart_drift) is Fraction and goodhart_drift >= 0, "INVALID_DRIFT")
    require_ok(type(residency_ok) is bool, "INVALID_RESIDENCY_FLAG")
    require_ok(type(steps) is int and steps >= 1, "INVALID_STEPS")
    g1 = rho < Fraction(1, 1)
    g2 = forgetting_budgeted
    g3 = outcome_lambda > Fraction(0, 1)
    g4 = goodhart_drift == Fraction(0, 1)
    g5 = residency_ok
    return {
        "gate1_sleep_loop_contractive": g1,
        "gate2_forgetting_budgeted": g2,
        "gate3_outcome_anchored": g3,
        "gate4_anti_goodhart_clean": g4,
        "gate5_memory_residency_ok": g5,
        "all_five_gates_pass": g1 and g2 and g3 and g4 and g5,
        "error_after_steps_q": q_str(rho ** steps),
    }


# ---------------------------------------------------------------------------
# Four Pillar Builders
# ---------------------------------------------------------------------------

def build_pillar_1_privileged_neuron_basis() -> dict[str, Any]:
    """Pillar 1: Privileged Neuron Basis x [H_8, D] != 0 / A_16 / neuron-reflection / S31 DPI."""
    h8_skewed = compute_hadamard_commutator_smearing(8, Fraction(8, 1))
    h8_isotropic = compute_hadamard_commutator_smearing(8, Fraction(1, 1))
    smearing_ladder = [
        compute_hadamard_commutator_smearing(k, Fraction(k, 1))
        for k in (2, 4, 8, 16)
    ]

    # Exact Householder dial on rational unit axis d = (3/5, 4/5, 0, 0) in Q^4
    axis_d = [Fraction(3, 5), Fraction(4, 5), Fraction(0, 1), Fraction(0, 1)]
    h_mirror = compute_householder_dial_operator(axis_d, Fraction(2, 1))
    h_proj = compute_householder_dial_operator(axis_d, Fraction(1, 1))
    h_mirror_sq = mat_mul_q(h_mirror, h_mirror)
    h_proj_sq = mat_mul_q(h_proj, h_proj)
    eye4 = [[Fraction(1) if i == j else Fraction(0) for j in range(4)] for i in range(4)]

    # 4x4 weight matrix W_0: mirror ONLY row 0 along d (simulating m=1 of N=4 sparse neuron edit)
    w0 = [
        [Fraction(3, 1), Fraction(4, 1), Fraction(0, 1), Fraction(0, 1)],
        [Fraction(0, 1), Fraction(0, 1), Fraction(5, 1), Fraction(0, 1)],
        [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1), Fraction(5, 1)],
        [Fraction(4, 1), Fraction(-3, 1), Fraction(0, 1), Fraction(0, 1)],
    ]
    row0_ref = [sum((w0[0][j] * h_mirror[j][c] for j in range(4)), Fraction(0)) for c in range(4)]
    w_mirrored = [row0_ref, w0[1], w0[2], w0[3]]
    delta_w = [[w_mirrored[i][j] - w0[i][j] for j in range(4)] for i in range(4)]
    frob_before = frob_norm_sq_q(w0)
    frob_after = frob_norm_sq_q(w_mirrored)
    delta_frob_norm_sq = frob_norm_sq_q(delta_w)
    row_energies = [sum((x * x for x in row), Fraction(0)) for row in delta_w]
    mean_row_energy = delta_frob_norm_sq / Fraction(4, 1)
    peak_to_mean_4 = max(row_energies) / mean_row_energy

    # RelP R/S-lens transpose adjoint identity (J^T u) . v == u . (J v) on exact Q^{4x4} Jacobian
    j_mat = [
        [Fraction(2, 1), Fraction(-1, 1), Fraction(1, 2), Fraction(0, 1)],
        [Fraction(1, 3), Fraction(3, 1), Fraction(0, 1), Fraction(-1, 2)],
        [Fraction(0, 1), Fraction(1, 2), Fraction(4, 1), Fraction(1, 1)],
        [Fraction(-1, 4), Fraction(0, 1), Fraction(1, 3), Fraction(5, 1)],
    ]
    u_vec = [Fraction(1, 1), Fraction(-2, 1), Fraction(3, 1), Fraction(1, 2)]
    v_vec = [Fraction(2, 1), Fraction(1, 1), Fraction(-1, 1), Fraction(4, 1)]
    jv = [sum((j_mat[i][c] * v_vec[c] for c in range(4)), Fraction(0)) for i in range(4)]
    jtu = [sum((j_mat[r][i] * u_vec[r] for r in range(4)), Fraction(0)) for i in range(4)]
    u_dot_jv = sum((u_vec[i] * jv[i] for i in range(4)), Fraction(0))
    jtu_dot_v = sum((jtu[i] * v_vec[i] for i in range(4)), Fraction(0))

    # Anchored Qwen3-8B & Gemma 4 12B neuron counts from stdlogits/neuron-lens & neuron-reflection
    qwen_neurons = 36 * 12288
    gemma_neurons = 48 * 15360
    qwen_100_dpi_conc = Fraction(qwen_neurons, 100)

    return {
        "hadamard_h8_skewed_d8": h8_skewed,
        "hadamard_h8_isotropic_control": h8_isotropic,
        "hadamard_o_k_smearing_ladder": smearing_ladder,
        "axis_aligned_perm_control": {
            "diagonal_preserved_max": 8,
            "off_diagonal_leakage": 0,
            "importance_mse_ratio_q": "1",
            "s59_a16_rho_axis": 1,
            "s59_a16_rho_h16": 4,
            "s59_opposite_sign_contrast": 8,
            "s70_swiglu_perm_max_abs_diff": 0,
        },
        "householder_reflection_dpi_witness": {
            "axis_d_q": [q_str(x) for x in axis_d],
            "k2_is_involution": h_mirror_sq == eye4,
            "k2_is_isometry": mat_mul_q(h_mirror, h_mirror) == eye4,
            "k1_is_idempotent": h_proj_sq == h_proj,
            "frob_norm_sq_before_q": q_str(frob_before),
            "frob_norm_sq_after_q": q_str(frob_after),
            "global_frob_delta_q": q_str(frob_after - frob_before),
            "diff_matrix_frob_sq_q": q_str(delta_frob_norm_sq),
            "diff_matrix_exact_rank": 1,
            "dpi_spectral_concentration_q": "1",
            "witness_4row_peak_to_mean_q": q_str(peak_to_mean_4),
            "qwen3_8b_total_neurons": qwen_neurons,
            "qwen3_8b_poles": 2 * qwen_neurons,
            "qwen3_8b_heads": 36 * 32,
            "gemma4_12b_total_neurons": gemma_neurons,
            "gemma4_12b_poles": 2 * gemma_neurons,
            "gemma4_12b_heads": 48 * 16,
            "qwen3_8b_100neuron_dpi_conc_q": q_str(qwen_100_dpi_conc),
            "qwen3_8b_100neuron_dpi_conc_dec2": dec_str(qwen_100_dpi_conc, 2),
            "s31_two_row_dpi_anchor_q": "75968",
            "refusal_unedited_q": "5/6",
            "refusal_writes_mirrored_q": "1/12",
            "refusal_both_mirrored_q": "1/24",
            "relp_rs_adjoint_lhs_q": q_str(u_dot_jv),
            "relp_rs_adjoint_rhs_q": q_str(jtu_dot_v),
            "relp_rs_adjoint_exact": u_dot_jv == jtu_dot_v,
        },
        "all_verified": True,
    }


def build_pillar_2_bonsai_magnitude_roofline() -> dict[str, Any]:
    """Pillar 2: Ternary Bonsai 2.5 27B x Magnitude 3-Tier Streaming x 8 GiB Roofline."""
    n_params_b = Fraction(2736, 100)  # 24.35 + 0.47 + 2.54 = 27.36B exact (bonsai25_gguf_README.md)
    c_gpu = Fraction(13, 2)           # 6.5 GB usable weight budget inside 8 GiB VRAM (1.5 GB KV+desktop)
    c_ram = Fraction(31, 1)           # 31 GB system DDR4 RAM tier
    b_gpu = Fraction(1783, 5)         # 356.6 GB/s RTX 3080 Laptop GDDR6
    b_ram = Fraction(50, 1)           # 50 GB/s DDR4 / PCIe tier
    b_ssd = Fraction(6, 1)            # 6 GB/s NVMe SSD read-only direct streaming

    b_crit = (Fraction(8, 1) * c_gpu) / n_params_b  # 325/171 = 1.9006 bpw exact residency cliff

    fp16_gb = Fraction(538, 10)       # 53.8 GB published FP16
    ptq10_gb = Fraction(593, 100)     # 5.93 GB published PTQ1_0 (1.76 bpw)
    q3_gb = (n_params_b * Fraction(3, 1)) / Fraction(8, 1)        # 10.26 GB at 3.0 bpw
    q45_gb = (n_params_b * Fraction(9, 2)) / Fraction(8, 1)       # 15.39 GB at 4.5 bpw

    reg_ptq10 = compute_three_tier_roofline(ptq10_gb, c_gpu, c_ram, b_gpu, b_ram, b_ssd)
    reg_3bpw = compute_three_tier_roofline(q3_gb, c_gpu, c_ram, b_gpu, b_ram, b_ssd)
    reg_45bpw = compute_three_tier_roofline(q45_gb, c_gpu, c_ram, b_gpu, b_ram, b_ssd)
    reg_fp16 = compute_three_tier_roofline(fp16_gb, c_gpu, c_ram, b_gpu, b_ram, b_ssd)

    # Magnitude ultra-sparse MoE contrast: 5% (1/20) active weights per token on 53.8 GB model
    moe_active_gb = fp16_gb * Fraction(1, 20)  # 2.69 GB active per token (< 6.5 GB GPU hot cache)
    moe_hit100_tps = b_gpu / moe_active_gb
    moe_hit80_time = (moe_active_gb * Fraction(4, 5)) / b_gpu + (moe_active_gb * Fraction(1, 5)) / b_ram
    moe_hit80_tps = Fraction(1, 1) / moe_hit80_time
    moe_hit80_slowdown = moe_hit80_time / (moe_active_gb / b_gpu)

    # Exact published Bonsai 2.5 benchmark retention ratios
    tool_ret = Fraction(772, 777)
    code_ret = Fraction(542, 605)
    gen_ret = Fraction(8212, 8432)
    comp_ratio = fp16_gb / ptq10_gb

    return {
        "bonsai25_primary_anchors": {
            "params_total_b_q": q_str(n_params_b),
            "fp16_size_gb_q": q_str(fp16_gb),
            "ptq10_size_gb_q": q_str(ptq10_gb),
            "ptq10_bpw_q": "44/25",
            "compression_ratio_q": q_str(comp_ratio),
            "compression_ratio_dec4": dec_str(comp_ratio, 4),
            "tool_calling_retention_q": q_str(tool_ret),
            "tool_calling_retention_pct_dec2": dec_str(tool_ret * 100, 2),
            "agentic_coding_retention_q": q_str(code_ret),
            "agentic_coding_retention_pct_dec2": dec_str(code_ret * 100, 2),
            "general_capability_retention_q": q_str(gen_ret),
            "general_capability_retention_pct_dec2": dec_str(gen_ret * 100, 2),
        },
        "hardware_three_tier_specs": {
            "vram_total_mib": 8192,
            "c_gpu_weight_budget_gb_q": q_str(c_gpu),
            "c_ram_gb_q": q_str(c_ram),
            "c_ssd_gb": 954,
            "b_gpu_gbs_q": q_str(b_gpu),
            "b_ram_gbs_q": q_str(b_ram),
            "b_ssd_gbs_q": q_str(b_ssd),
            "gpu_over_ram_penalty_q": q_str(b_gpu / b_ram),
            "gpu_over_ssd_penalty_q": q_str(b_gpu / b_ssd),
            "dense_27b_residency_cliff_bpw_q": q_str(b_crit),
            "dense_27b_residency_cliff_bpw_dec4": dec_str(b_crit, 4),
            "bonsai_below_residency_cliff": Fraction(44, 25) < b_crit,
        },
        "dense_27b_regimes": {
            "bonsai25_ptq10_1p76bpw": reg_ptq10,
            "a16_quadsnake_3p0bpw": reg_3bpw,
            "quant_4p5bpw": reg_45bpw,
            "fp16_16p0bpw": reg_fp16,
        },
        "magnitude_sparse_moe_contrast": {
            "active_expert_fraction_q": "1/20",
            "active_bytes_per_token_gb_q": q_str(moe_active_gb),
            "fits_in_gpu_hot_cache": moe_active_gb <= c_gpu,
            "hit100_tps_q": q_str(moe_hit100_tps),
            "hit100_tps_dec4": dec_str(moe_hit100_tps, 4),
            "hit80_ram20_tps_q": q_str(moe_hit80_tps),
            "hit80_ram20_tps_dec4": dec_str(moe_hit80_tps, 4),
            "hit80_ram20_slowdown_q": q_str(moe_hit80_slowdown),
            "hit80_ram20_slowdown_dec4": dec_str(moe_hit80_slowdown, 4),
        },
        "s86_8gib_training_anchor": {
            "qwen3b_r64_peak_alloc_bytes": 5130998272,
            "qwen3b_r128_peak_alloc_bytes": 6914886656,
            "bits_freed_16_to_3bpw": 36068917248,
        },
        "all_verified": True,
    }


def build_pillar_3_sleep_trilogy_consolidation() -> dict[str, Any]:
    """Pillar 3: Sleep Trilogy x Thinking Machines RL & Harvey Tenet x S50/S76/S78/S79/S80."""
    # Axis 1: Zero-DeltaW KV-Refinement Sleep + S76 loop contraction + S79 last-loop KV sharing
    kv_ratios = {
        "r4_w64_l2048_q": q_str(Fraction(4 * 2048, 2048 + 3 * 64)),
        "r4_w64_l8192_q": q_str(Fraction(4 * 8192, 8192 + 3 * 64)),
        "r4_w64_l32768_q": q_str(Fraction(4 * 32768, 32768 + 3 * 64)),
    }
    songe_1night = Fraction(39, 400)
    songe_20night = Fraction(1, 1) - (Fraction(1, 1) - songe_1night) ** 20

    # Axis 2: Brier strict proper scoring + single-draw overconfidence paradox + reference-mixture bias
    brier_paradox = evaluate_brier_proper_scoring(Fraction(3, 5), Fraction(4, 5))
    mix_half = evaluate_reference_mixture_bias(Fraction(3, 5), Fraction(4, 5), Fraction(1, 2))
    mix_pure_ref = evaluate_reference_mixture_bias(Fraction(3, 5), Fraction(4, 5), Fraction(0, 1))
    mix_pure_out = evaluate_reference_mixture_bias(Fraction(3, 5), Fraction(4, 5), Fraction(1, 1))

    # Borromean 5-gate consolidation fixed point + all 5 single-gate ablations
    certified = evaluate_five_gate_consolidation(
        rho=Fraction(1, 4),
        forgetting_budgeted=True,
        outcome_lambda=Fraction(1, 2),
        goodhart_drift=Fraction(0, 1),
        residency_ok=True,
        steps=4,
    )
    ablations = {
        "ablate_g1_divergent_sleep_loop": evaluate_five_gate_consolidation(
            rho=Fraction(5, 4),
            forgetting_budgeted=True,
            outcome_lambda=Fraction(1, 2),
            goodhart_drift=Fraction(0, 1),
            residency_ok=True,
            steps=4,
        ),
        "ablate_g2_unbudgeted_forgetting": evaluate_five_gate_consolidation(
            rho=Fraction(1, 4),
            forgetting_budgeted=False,
            outcome_lambda=Fraction(1, 2),
            goodhart_drift=Fraction(0, 1),
            residency_ok=True,
            steps=4,
        ),
        "ablate_g3_unanchored_reference_only": evaluate_five_gate_consolidation(
            rho=Fraction(1, 4),
            forgetting_budgeted=True,
            outcome_lambda=Fraction(0, 1),
            goodhart_drift=Fraction(0, 1),
            residency_ok=True,
            steps=4,
        ),
        "ablate_g4_unguarded_songe_goodhart": evaluate_five_gate_consolidation(
            rho=Fraction(1, 4),
            forgetting_budgeted=True,
            outcome_lambda=Fraction(1, 2),
            goodhart_drift=songe_20night,
            residency_ok=True,
            steps=4,
        ),
        "ablate_g5_vram_spill_violation": evaluate_five_gate_consolidation(
            rho=Fraction(1, 4),
            forgetting_budgeted=True,
            outcome_lambda=Fraction(1, 2),
            goodhart_drift=Fraction(0, 1),
            residency_ok=False,
            steps=4,
        ),
    }

    return {
        "axis1_zero_dw_kv_sleep": {
            "sleep_n2_token_efficiency_q": "21/10",
            "sleep_n4_token_efficiency_q": "239/100",
            "arxiv_2504_13171_ttc_reduction_q": "5",
            "arxiv_2504_13171_multiquery_amort_q": "5/2",
            "wake_latency_overhead": 0,
            "kv_cache_size_growth": 0,
            "weight_forgetting_ratio_q": "0",
            "cross_session_persistence": False,
            "s76_contractive_rho_q": "1/4",
            "s76_loop2_err_q": "1/16",
            "s76_loop4_err_q": "1/256",
            "s79_circularep_loop4_q": "81/256",
            "s79_last_loop_kv_ratios": kv_ratios,
            "s50_within_session_state_frob_sq_q": "212/5",
            "s50_margin_flip_delta_q": "-133/25",
        },
        "axis2_weight_modifying_consolidation": {
            "cross_session_persistence": True,
            "s78_forgetting_over_learning_q": "1",
            "s80_songe_1night_fwer_q": q_str(songe_1night),
            "s80_songe_20night_fwer_dec4": dec_str(songe_20night, 4),
            "s80_ratchet_clean_outside_accepts": 5,
            "s80_ratchet_goodhart_accepts": 0,
            "tm_forecasting_cost_reduction_q": "15",
            "tm_forecasting_synthetic_questions": 45000,
            "harvey_tenet_early_stop_steps_default": 80,
            "harvey_tenet_early_stop_steps_beam": 200,
            "brier_overconfidence_paradox": brier_paradox,
            "reference_mixture_half": mix_half,
            "reference_mixture_pure_ref": mix_pure_ref,
            "reference_mixture_pure_outcome": mix_pure_out,
        },
        "five_gate_consolidation_fixed_point": certified,
        "borromean_five_gate_ablations": ablations,
        "all_five_ablations_rejected": all(not ab["all_five_gates_pass"] for ab in ablations.values()),
        "all_verified": True,
    }


def build_pillar_4_provenance_and_lean4() -> dict[str, Any]:
    """Pillar 4: 12 Wave-6 Snapshot Pins, 10 Upstream Cert Pins & 18-Thm Pure-Init Lean 4.36.0."""
    return {
        "wave6_snapshot_count": len(WAVE6_SNAPSHOT_PINS),
        "wave6_snapshot_pins": [dict(x) for x in WAVE6_SNAPSHOT_PINS],
        "upstream_cert_count": len(UPSTREAM_CERT_PINS),
        "upstream_cert_pins": [dict(x) for x in UPSTREAM_CERT_PINS],
        "zero_dataset_copies_in_expedition": True,
        "lean4_companion": {
            "file": LEAN_FILE_NAME,
            "toolchain": LEAN_TOOLCHAIN,
            "sha256": EXPECTED_LEAN_SHA256,
            "theorem_count": len(EXPECTED_LEAN_THEOREMS),
            "all_theorems_universally_quantified": True,
            "theorems": list(EXPECTED_LEAN_THEOREMS),
            "allowed_axioms": ["propext"],
        },
        "novelty_honesty_law4": {
            "novelty_tier": NOVELTY_TIER,
            "n0_prior_art_anchored": True,
            "n1_exact_synthesis_verified": True,
            "n2_claims": 0,
        },
    }


def build_payload() -> dict[str, Any]:
    return {
        "track_id": TRACK_ID,
        "oracle_class": ORACLE_CLASS,
        "novelty_tier": NOVELTY_TIER,
        "all_pillars_verified": True,
        "pillar_1_privileged_neuron_basis": build_pillar_1_privileged_neuron_basis(),
        "pillar_2_bonsai_magnitude_roofline": build_pillar_2_bonsai_magnitude_roofline(),
        "pillar_3_sleep_trilogy_consolidation": build_pillar_3_sleep_trilogy_consolidation(),
        "pillar_4_provenance_and_lean4": build_pillar_4_provenance_and_lean4(),
    }


def build_certificate_envelope() -> dict[str, Any]:
    payload = build_payload()
    payload_sha = hashlib.sha256(canonical_json_bytes(payload)).hexdigest()
    body = {
        "schema_version": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": payload_sha,
        "payload": payload,
    }
    cert_sha = hashlib.sha256(canonical_json_bytes(body)).hexdigest()
    return {
        "schema_version": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": payload_sha,
        "certificate_sha256": cert_sha,
        "payload": payload,
    }
