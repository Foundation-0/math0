#!/usr/bin/env python3
"""Wave 2 Round 9 — Arm R9-5 (AUDIT-082):
Unified Off-Policy RL Geometry & Kernel-Invariance Composition.

Exact pure-Q (zero-float, stdlib-only) composition and interference oracle uniting:
  - Axis 1 (Kernel TIM / TII): REINFORCE Zero (alphaXiv:2611.reinforce-zero-...)
    + warp-drive Stage-1 RuntimeFlags (AUDIT-066R) + Magnitude (AUDIT-068R)
  - Axis 2 (First-Order Drift / Bregman KL): Score Centering (arXiv:2609.20807)
    + songe SNG-01 Bregman KL (AUDIT-073R) + Inkling LOOM-IR-03 Top-64 (AUDIT-074R)
  - Axis 3 (Second-Order Fisher-Rao / Trust Region): RIPO (arXiv:2607.10169)
    + warp-drive WI-4 Fisher-Schur F_p (AUDIT-064)

Strictly read-only on all external vectors; zero floats; zero bare asserts;
zero local absolute paths emitted in JSON certificates.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import sys
from typing import Any


EXPECTED_PINNED_SHA256: dict[str, str] = {
    "score-centering/arxiv_2609.20807.txt": (
        "a53342f3774e1effd43e386e06ae76766c0002262616d2cfa8a5726c90b87cd2"
    ),
    "score-centering/repo/losses.py": (
        "c9094e9663d1770badcfc0327c41aa201e408dd0b868d6656444c4f497b04820"
    ),
    "zhihu/zhihu_2092277762245538186_score_centering.md": (
        "74443b91fa1668f3aa15e170de2520a02f356f64be549a60de2bcc84484f6d3d"
    ),
    "ripo/arxiv_2607.10169.txt": (
        "05cf523283d28da243cc54038038b72a69b10783637cc34f0697fd4fc413e689"
    ),
    "zhihu/zhihu_2098101007368640039_ripo.md": (
        "d5a529c9e0c1a43294dce6e3b793affd476d4df9f243f37926c0accf08c23792"
    ),
    "reinforce-zero/REINFORCE-Zero.txt": (
        "5d2abc64df9674b690abffd62c72c2c88da9fe8942457f1ca85471db253702b8"
    ),
    "reinforce-zero/REINFORCE-Zero/ALGORITHM.md": (
        "0d02ac35222ae8877134c6c23c7eff1ef76b771f8dda120053231ab78c4f73a9"
    ),
    "reinforce-zero/zero-mismatch-rl/skill/numerical-contracts.md": (
        "c620e1e8a79fe2e69965f0fbae206f136c5fa2b644d078bd6a790d93092c3a03"
    ),
}

ANCHOR_SPECS: tuple[tuple[str, str, int, str], ...] = (
    (
        "SC-EQ3",
        "score-centering/arxiv_2609.20807.txt",
        388,
        "Covq (R, syt )",
    ),
    (
        "SC-FWD-KL",
        "score-centering/arxiv_2609.20807.txt",
        406,
        "negative gradient of the crossentropy",
    ),
    (
        "SC-EQ10-TAIL",
        "score-centering/arxiv_2609.20807.txt",
        994,
        "constant on the tail",
    ),
    (
        "SC-JAX-FLOOR",
        "score-centering/arxiv_2609.20807.txt",
        1067,
        "train_tail_mass = jnp.maximum",
    ),
    (
        "SC-LOSSES-RATIO",
        "score-centering/repo/losses.py",
        121,
        'c.stat == "ratio"',
    ),
    (
        "SC-LOSSES-RHO",
        "score-centering/repo/losses.py",
        147,
        "rho = jnp.maximum(q_tail, 0.0)",
    ),
    (
        "SC-ZHIHU-SLIP",
        "zhihu/zhihu_2092277762245538186_score_centering.md",
        42,
        "reverse KL",
    ),
    (
        "RIPO-DGEOM",
        "ripo/arxiv_2607.10169.txt",
        375,
        "dgeom (",
    ),
    (
        "RIPO-EQ11",
        "ripo/arxiv_2607.10169.txt",
        415,
        "|rs,a (",
    ),
    (
        "RIPO-DUALCLIP",
        "ripo/arxiv_2607.10169.txt",
        566,
        "0.5 and 10",
    ),
    (
        "RIPO-NOKL",
        "ripo/arxiv_2607.10169.txt",
        567,
        "remove the KL penalty term",
    ),
    (
        "RIPO-ZHIHU-VAR",
        "zhihu/zhihu_2098101007368640039_ripo.md",
        27,
        "sqrt",
    ),
    (
        "RZ-D3-PEAK",
        "reinforce-zero/REINFORCE-Zero.txt",
        279,
        "442.54",
    ),
    (
        "RZ-SC-VS-IS",
        "reinforce-zero/REINFORCE-Zero.txt",
        374,
        "score-mean drift and covariance bias",
    ),
    (
        "RZ-THM1",
        "reinforce-zero/REINFORCE-Zero.txt",
        1666,
        "Theorem 1 (Accumulated error and stability)",
    ),
    (
        "RZ-ALG-DECOMP",
        "reinforce-zero/REINFORCE-Zero/ALGORITHM.md",
        14,
        r"\log\frac{\pi_{\theta_k}}{\mu_v}",
    ),
    (
        "RZ-TOPK-CONTRACT",
        "reinforce-zero/zero-mismatch-rl/skill/numerical-contracts.md",
        19,
        "top-k/top-p truncation set",
    ),
)

ALLOWED_CERTIFIER_KEYS: frozenset[str] = frozenset(
    {
        "q",
        "p_old",
        "p",
        "features",
        "tii_flags_aligned",
        "max_tim_ratio",
        "max_tim_chi2",
        "weighting_mode",
        "centering_mode",
        "kl_mode",
        "delta",
        "delta_total",
        "dual_clip_low",
        "dual_clip_high",
        "allow_negative_lower_clip",
        "use_true_p_old_for_ripo",
        "top_k_indices",
        "max_tail_rho",
        "max_second_moment",
        "max_d3_upper",
        "eta",
        "step_variance_v",
    }
)

ALLOWED_WEIGHTING_MODES: frozenset[str] = frozenset(
    {"unclipped_is", "tis", "ripo_clamped"}
)
ALLOWED_CENTERING_MODES: frozenset[str] = frozenset(
    {"none", "naive_sc", "weighted_sc"}
)
ALLOWED_KL_MODES: frozenset[str] = frozenset(
    {"none", "exact_bregman", "chi2_fisher_rao", "clipped_ratio_kl"}
)


def frac_to_dict(value: Fraction) -> dict[str, int]:
    """Encode an exact Fraction as a canonical zero-float {num, den} object."""
    if not isinstance(value, Fraction):
        raise TypeError("frac_to_dict requires Fraction")
    return {"num": value.numerator, "den": value.denominator}


def exact_frac(value: Any, name: str) -> Fraction:
    """Strictly convert int or Fraction to Fraction; reject bool, float, str, etc."""
    if type(value) is int:
        return Fraction(value, 1)
    if isinstance(value, Fraction):
        return value
    raise ValueError(f"{name} must be exact int or Fraction")


def exact_bool(value: Any, name: str) -> bool:
    """Strictly validate a Python bool."""
    if type(value) is not bool:
        raise ValueError(f"{name} must be exact bool")
    return value


def exact_rational_sqrt(value: Fraction, name: str) -> Fraction:
    """Return exact sqrt(value) as Fraction iff reduced num and den are squares."""
    q_val = exact_frac(value, name)
    r_num = math.isqrt(q_val.numerator)
    r_den = math.isqrt(q_val.denominator)
    if r_num * r_num != q_val.numerator or r_den * r_den != q_val.denominator:
        raise ValueError(f"{name} is not a rational square")
    return Fraction(r_num, r_den)


def validate_simplex(dist: Any, name: str) -> list[Fraction]:
    """Validate a strictly positive rational probability simplex."""
    if not isinstance(dist, (list, tuple)) or len(dist) < 2:
        raise ValueError(f"{name} must be a sequence of length >= 2")
    out: list[Fraction] = []
    total = Fraction(0, 1)
    for idx, entry in enumerate(dist):
        prob = exact_frac(entry, f"{name}[{idx}]")
        if prob <= 0:
            raise ValueError(f"{name}[{idx}] must be strictly positive")
        out.append(prob)
        total += prob
    if total != 1:
        raise ValueError(f"{name} must sum to 1")
    return out


def softmax_scores(p: list[Fraction], features: list[Fraction]) -> list[Fraction]:
    """Compute exact centered softmax scores s_v = phi_v - E_p[phi]."""
    if len(p) != len(features):
        raise ValueError("p and features length mismatch")
    mean_phi = sum((p[i] * features[i] for i in range(len(p))), Fraction(0, 1))
    return [features[i] - mean_phi for i in range(len(p))]


def d3_rational_bounds(w: Fraction) -> tuple[Fraction, Fraction]:
    """Exact pure-Q Padé / Hermite-Hadamard bounds on D_3(w) = w - 1 - log(w).

    For w >= 1: (w-1)^2 / (2*w) <= D_3(w) <= (w-1)^2 / (w+1).
    For 0 < w < 1: (w-1)^2 / (w+1) <= D_3(w) <= (w-1)^2 / (2*w).
    """
    q_w = exact_frac(w, "w")
    if q_w <= 0:
        raise ValueError("w must be strictly positive")
    diff_sq = (q_w - 1) * (q_w - 1)
    b_harm = diff_sq / (2 * q_w)
    b_pade = diff_sq / (q_w + 1)
    if q_w >= 1:
        return (b_harm, b_pade)
    return (b_pade, b_harm)


def compute_ripo_exact_bound(
    base_prob: Fraction,
    delta: Fraction,
    dual_clip_low: Fraction,
    dual_clip_high: Fraction,
    allow_negative_lower_clip: bool,
) -> tuple[Fraction, Fraction, Fraction]:
    """Compute exact RIPO bounds (low, high, eps) when delta / base_prob is a square."""
    eps = exact_rational_sqrt(delta / base_prob, "delta/base_prob")
    raw_low = Fraction(1, 1) - eps
    raw_high = Fraction(1, 1) + eps
    if allow_negative_lower_clip:
        low = raw_low
    else:
        low = max(dual_clip_low, raw_low)
    high = min(dual_clip_high, raw_high)
    return (low, high, eps)


def ripo_membership_exact(
    ratio: Fraction,
    base_prob: Fraction,
    delta: Fraction,
) -> bool:
    """Square-free exact RIPO trust-region test: base_prob * (ratio - 1)^2 <= delta."""
    return base_prob * (ratio - 1) * (ratio - 1) <= delta


def clamp_ratio_ripo_exact(
    ratio: Fraction,
    base_prob: Fraction,
    delta: Fraction,
    dual_clip_low: Fraction,
    dual_clip_high: Fraction,
    allow_negative_lower_clip: bool,
) -> Fraction:
    """Clip ratio to the exact RIPO + dual-clip interval without floats.

    First applies the square-free dual-clip clamp and tests exact RIPO
    membership base_prob * (candidate - 1)^2 <= delta so dual-clip dominance
    never requires delta/base_prob to be a rational square. Falls back to
    exact_rational_sqrt only when the RIPO boundary itself strictly binds.
    """
    if ratio > 1:
        candidate = min(ratio, dual_clip_high)
        if ripo_membership_exact(candidate, base_prob, delta):
            return candidate
        return Fraction(1, 1) + exact_rational_sqrt(
            delta / base_prob, "delta/base_prob"
        )
    candidate = ratio if allow_negative_lower_clip else max(ratio, dual_clip_low)
    if ripo_membership_exact(candidate, base_prob, delta):
        return candidate
    return Fraction(1, 1) - exact_rational_sqrt(delta / base_prob, "delta/base_prob")


def verify_live_anchors(repos_dir: Path) -> dict[str, Any]:
    """Read-only SHA-256 + 1-based newline anchor verification over staged Round-9 inputs."""
    file_digests: list[dict[str, Any]] = []
    all_digests_ok = True
    for rel_path, expected_sha in EXPECTED_PINNED_SHA256.items():
        fpath = repos_dir / rel_path
        if not fpath.is_file():
            all_digests_ok = False
            file_digests.append(
                {
                    "path": rel_path,
                    "expected_sha256": expected_sha,
                    "observed_sha256": None,
                    "matched": False,
                }
            )
            continue
        raw = fpath.read_bytes()
        obs_sha = hashlib.sha256(raw).hexdigest()
        matched = obs_sha == expected_sha
        if not matched:
            all_digests_ok = False
        file_digests.append(
            {
                "path": rel_path,
                "expected_sha256": expected_sha,
                "observed_sha256": obs_sha,
                "matched": matched,
            }
        )

    anchor_results: list[dict[str, Any]] = []
    verified_count = 0
    for anchor_id, rel_path, lineno, expected_sub in ANCHOR_SPECS:
        fpath = repos_dir / rel_path
        matched = False
        if fpath.is_file():
            lines = fpath.read_text(encoding="utf-8").split("\n")
            if 1 <= lineno <= len(lines) and expected_sub in lines[lineno - 1]:
                matched = True
        if matched:
            verified_count += 1
        anchor_results.append(
            {
                "id": anchor_id,
                "path": rel_path,
                "expected_line": lineno,
                "matched": matched,
            }
        )

    return {
        "anchor_mode": "live_readonly",
        "files_total": len(EXPECTED_PINNED_SHA256),
        "all_file_digests_matched": all_digests_ok,
        "file_digests": file_digests,
        "anchors_total": len(ANCHOR_SPECS),
        "anchors_verified": verified_count,
        "all_anchors_matched": all_digests_ok and (verified_count == len(ANCHOR_SPECS)),
        "anchors": anchor_results,
    }


def prove_t1_three_axis_factorization() -> dict[str, Any]:
    """Theorem T1: Exact 3-axis ratio factorization, REINFORCE Zero Thm-1 pure-Q
    stability separation (kappa=0 vs kappa=1/5), and AUDIT-064 WI-4 Fisher-Schur
    identity connecting RIPO's local chi^2 metric to F_p.
    """
    q = [Fraction(2, 5), Fraction(2, 5), Fraction(1, 5)]
    p_old = [Fraction(1, 2), Fraction(3, 10), Fraction(1, 5)]
    p = [Fraction(3, 5), Fraction(1, 4), Fraction(3, 20)]

    r_tim = [p_old[i] / q[i] for i in range(3)]
    r_lag = [p[i] / p_old[i] for i in range(3)]
    r_tot = [p[i] / q[i] for i in range(3)]
    factorization_exact = all(r_tim[i] * r_lag[i] == r_tot[i] for i in range(3))

    chi2_tim_unaligned = sum(
        (q[i] * (r_tim[i] - 1) * (r_tim[i] - 1) for i in range(3)), Fraction(0, 1)
    )
    chi2_tim_aligned = sum(
        (p_old[i] * (p_old[i] / p_old[i] - 1) ** 2 for i in range(3)), Fraction(0, 1)
    )

    # Exact REINFORCE Zero Theorem 1 pure-Q stability separation (M=1, eta=3/5, sigma=1/5)
    eta = Fraction(3, 5)
    sigma = Fraction(1, 5)
    a0 = Fraction(3, 1)
    c0_poly = Fraction(5, 2)
    v0 = a0 - 1
    eta_max_0 = Fraction(2, 1) / (1 + v0)
    rho_0 = (1 - eta) ** 2 + eta * eta * v0
    c_0 = eta * eta * sigma * sigma * c0_poly
    v_inf_0 = c_0 / (1 - rho_0)

    # kappa = 1/5: exact rational Taylor lower bound exp(t) > 1 + t + t^2/2 for t = kappa^2 = 1/25
    kappa = Fraction(1, 5)
    t_sq = kappa * kappa
    exp_t_lo = Fraction(1, 1) + t_sq + (t_sq * t_sq) / 2
    poly_a_k = kappa**4 + 6 * kappa**2 + 3
    a_k_lo = exp_t_lo * poly_a_k
    v_k_lo = a_k_lo - 1
    eta_max_k_hi = Fraction(2, 1) / (1 + v_k_lo)
    rho_k_lo = (1 - eta) ** 2 + eta * eta * v_k_lo

    # Exact AUDIT-064 WI-4 Fisher-Schur identity: (1/2) sum p_old (dz)^2 == (1/2) dtheta^T F dtheta
    u_cols = [
        [Fraction(1, 1), Fraction(0, 1), Fraction(-1, 1)],
        [Fraction(0, 1), Fraction(1, 1), Fraction(-1, 1)],
    ]
    s_cols = [softmax_scores(p_old, col) for col in u_cols]
    f00 = sum((p_old[i] * s_cols[0][i] * s_cols[0][i] for i in range(3)), Fraction(0, 1))
    f01 = sum((p_old[i] * s_cols[0][i] * s_cols[1][i] for i in range(3)), Fraction(0, 1))
    f11 = sum((p_old[i] * s_cols[1][i] * s_cols[1][i] for i in range(3)), Fraction(0, 1))
    fisher_schur_s = f00 - (f01 * f01) / f11

    dtheta = [Fraction(1, 10), Fraction(-1, 20)]
    dz = [dtheta[0] * s_cols[0][i] + dtheta[1] * s_cols[1][i] for i in range(3)]
    ripo_half_chi2 = Fraction(1, 2) * sum(
        (p_old[i] * dz[i] * dz[i] for i in range(3)), Fraction(0, 1)
    )
    fisher_quad_half = Fraction(1, 2) * (
        f00 * dtheta[0] * dtheta[0]
        + 2 * f01 * dtheta[0] * dtheta[1]
        + f11 * dtheta[1] * dtheta[1]
    )

    return {
        "factorization_exact": factorization_exact,
        "chi2_tim_unaligned": frac_to_dict(chi2_tim_unaligned),
        "chi2_tim_aligned": frac_to_dict(chi2_tim_aligned),
        "reinforce_zero_thm1": {
            "eta": frac_to_dict(eta),
            "kappa_zero_v0": frac_to_dict(v0),
            "kappa_zero_eta_max": frac_to_dict(eta_max_0),
            "kappa_zero_rho": frac_to_dict(rho_0),
            "kappa_zero_c": frac_to_dict(c_0),
            "kappa_zero_v_inf": frac_to_dict(v_inf_0),
            "kappa_zero_stable": rho_0 < 1,
            "kappa_1_5_exp_lo": frac_to_dict(exp_t_lo),
            "kappa_1_5_a_lo": frac_to_dict(a_k_lo),
            "kappa_1_5_eta_max_hi": frac_to_dict(eta_max_k_hi),
            "kappa_1_5_rho_lo": frac_to_dict(rho_k_lo),
            "kappa_1_5_certified_unstable": (eta_max_k_hi < eta) and (rho_k_lo > 1),
        },
        "fisher_schur_bridge": {
            "f00": frac_to_dict(f00),
            "f01": frac_to_dict(f01),
            "f11": frac_to_dict(f11),
            "schur_complement_s": frac_to_dict(fisher_schur_s),
            "schur_strictly_below_f00": Fraction(0, 1) < fisher_schur_s < f00,
            "ripo_half_chi2": frac_to_dict(ripo_half_chi2),
            "fisher_quad_half": frac_to_dict(fisher_quad_half),
            "ripo_equals_wi4_fisher_exact": ripo_half_chi2 == fisher_quad_half,
        },
    }


def prove_t2_trap01_naive_sc_ripo() -> dict[str, Any]:
    """Theorem T2 (TRIAD-TRAP-01): Naive Score Centering + RIPO clipping breaks
    zero-drift (reversing sign and increasing |drift| from 47/180 to 48/180 = 4/15),
    whereas exact w-weighted Score Centering restores exact 0/1 drift.
    """
    q = [Fraction(4, 9), Fraction(4, 9), Fraction(1, 9)]
    p = [Fraction(2, 3), Fraction(1, 6), Fraction(1, 6)]
    delta = Fraction(1, 25)
    phi = [Fraction(1, 1), Fraction(-1, 1), Fraction(0, 1)]
    s = softmax_scores(p, phi)

    r = [p[i] / q[i] for i in range(3)]
    w = [
        clamp_ratio_ripo_exact(
            r[i], q[i], delta, Fraction(1, 10), Fraction(10, 1), False
        )
        for i in range(3)
    ]

    s_bar_q = sum((q[i] * s[i] for i in range(3)), Fraction(0, 1))
    e_w = sum((q[i] * w[i] for i in range(3)), Fraction(0, 1))
    e_ws = sum((q[i] * w[i] * s[i] for i in range(3)), Fraction(0, 1))

    uncentered_drift = e_ws
    naive_sc_drift = sum((q[i] * w[i] * (s[i] - s_bar_q) for i in range(3)), Fraction(0, 1))
    cov_q_w_s = e_ws - e_w * s_bar_q

    weighted_sc_additive_drift = sum(
        (q[i] * (w[i] * s[i] - e_ws) for i in range(3)), Fraction(0, 1)
    )
    s_bar_qw_norm = e_ws / e_w
    weighted_sc_normalized_drift = sum(
        (q[i] * w[i] * (s[i] - s_bar_qw_norm) for i in range(3)), Fraction(0, 1)
    )

    return {
        "delta": frac_to_dict(delta),
        "weights": [frac_to_dict(x) for x in w],
        "expected_weight_ew": frac_to_dict(e_w),
        "sampler_mean_score_s_bar_q": frac_to_dict(s_bar_q),
        "uncentered_ripo_drift": frac_to_dict(uncentered_drift),
        "naive_sc_ripo_drift": frac_to_dict(naive_sc_drift),
        "cov_q_w_s": frac_to_dict(cov_q_w_s),
        "naive_drift_equals_cov_exact": naive_sc_drift == cov_q_w_s,
        "naive_sc_sign_reversed": (uncentered_drift < 0) and (naive_sc_drift > 0),
        "naive_sc_worse_magnitude": abs(naive_sc_drift) > abs(uncentered_drift),
        "weighted_sc_additive_drift": frac_to_dict(weighted_sc_additive_drift),
        "weighted_sc_normalized_drift": frac_to_dict(weighted_sc_normalized_drift),
        "weighted_sc_exact_zero": (
            weighted_sc_additive_drift == 0 and weighted_sc_normalized_drift == 0
        ),
    }


def prove_t3_trap02_topk_ripo_split_tail_and_singularity() -> dict[str, Any]:
    """Theorem T3 (TRIAD-TRAP-02):
    Part A: Algebraic breakdown of Score Centering Top-K Eq. (10) when composed
      with RIPO (split-tail witness with zero tail reconstruction error) + exact
      rational sufficiency criterion max_{v in T} p_v * (1 - rho)^2 <= delta * rho.
    Part B: Tail-mass ratio singularity (20,000x spike & broken normalization under
      eps-floor) + Inkling LOOM-IR-03 hard Top-K truncation starvation.
    """
    q = [Fraction(289, 484), Fraction(169, 484), Fraction(25, 484), Fraction(1, 484)]
    p = [Fraction(200, 484), Fraction(180, 484), Fraction(100, 484), Fraction(4, 484)]
    delta_split = Fraction(25, 484)
    phi = [Fraction(0, 1), Fraction(0, 1), Fraction(1, 1), Fraction(-1, 1)]
    s = softmax_scores(p, phi)

    head = (0, 1)
    tail = (2, 3)
    q_tail = sum((q[i] for i in tail), Fraction(0, 1))
    p_tail = sum((p[i] for i in tail), Fraction(0, 1))
    rho = q_tail / p_tail
    q_hat_exact_match = all(rho * p[i] == q[i] for i in tail)

    r = [p[i] / q[i] for i in range(4)]
    w_split = [
        clamp_ratio_ripo_exact(
            r[i], q[i], delta_split, Fraction(1, 10), Fraction(10, 1), False
        )
        for i in range(4)
    ]
    true_ews_split = sum((q[i] * w_split[i] * s[i] for i in range(4)), Fraction(0, 1))

    # Evaluate Eq. (10) scalar-alpha head-only centering for alpha in {1, 1/2, 1/4}
    alpha_candidates = {
        "alpha_1_unclipped": Fraction(1, 1),
        "alpha_1_2_clipped_t2": Fraction(1, 2),
        "alpha_1_4_vanilla_rho": rho,
    }
    eq10_residuals: dict[str, dict[str, int]] = {}
    all_scalar_alphas_fail = True
    for label, alpha in alpha_candidates.items():
        eq10_est = sum(
            ((q[i] * w_split[i] - alpha * p[i]) * s[i] for i in head), Fraction(0, 1)
        )
        residual = true_ews_split - eq10_est
        eq10_residuals[label] = frac_to_dict(residual)
        if residual == 0:
            all_scalar_alphas_fail = False

    max_p_tail = max(p[i] for i in tail)
    split_lhs = max_p_tail * (1 - rho) * (1 - rho)
    split_rhs = delta_split * rho

    # Passing regime: increase delta to 225/484 so max_p_tail*(1-rho)^2 == delta*rho
    # -> every tail token is unclipped (w_2 = w_3 = 4 = 1/rho) and Eq. (10) with alpha=1 is EXACT!
    delta_pass = Fraction(225, 484)
    w_pass = [
        clamp_ratio_ripo_exact(
            r[i], q[i], delta_pass, Fraction(1, 10), Fraction(10, 1), False
        )
        for i in range(4)
    ]
    true_ews_pass = sum((q[i] * w_pass[i] * s[i] for i in range(4)), Fraction(0, 1))
    eq10_pass_alpha1 = sum(
        ((q[i] * w_pass[i] - p[i]) * s[i] for i in head), Fraction(0, 1)
    )
    pass_residual = true_ews_pass - eq10_pass_alpha1
    pass_rhs = delta_pass * rho

    # Part B: Tail-mass ratio singularity & eps-floor normalization break
    eps_floor = Fraction(1, 1_000_000)
    p_tail_peaked = Fraction(1, 100_000_000)
    q_tail_noisy = Fraction(1, 50)
    rho_exact_sing = q_tail_noisy / p_tail_peaked
    rho_floored_sing = q_tail_noisy / max(p_tail_peaked, eps_floor)
    q_hat_sum_floored = (Fraction(1, 1) - q_tail_noisy) + rho_floored_sing * p_tail_peaked
    alpha_sc_floored = rho_floored_sing
    alpha_tis_floored = rho_floored_sing * min(Fraction(1, 1) / rho_floored_sing, Fraction(2, 1))
    r_tail_floored = Fraction(1, 1) / rho_floored_sing
    alpha_mis_floored = (
        rho_floored_sing * r_tail_floored
        if (Fraction(1, 2) <= r_tail_floored <= Fraction(5, 1))
        else Fraction(0, 1)
    )

    # Inkling LOOM-IR-03 hard Top-64 truncation (q_tail == 0, p_tail == 35/64)
    p_tail_loom = Fraction(35, 64)
    q_tail_loom = Fraction(0, 1)
    rho_loom_exact = q_tail_loom / p_tail_loom
    rho_loom_paper_eps_floor = max(q_tail_loom, eps_floor) / max(p_tail_loom, eps_floor)

    return {
        "part_a_split_tail": {
            "rho": frac_to_dict(rho),
            "q_hat_zero_reconstruction_error": q_hat_exact_match,
            "tail_ratios_identical": r[2] == r[3] == Fraction(1, 1) / rho,
            "split_tail_weights": [frac_to_dict(w_split[2]), frac_to_dict(w_split[3])],
            "tail_weights_strictly_split": w_split[2] != w_split[3],
            "sufficiency_lhs": frac_to_dict(split_lhs),
            "sufficiency_rhs_split": frac_to_dict(split_rhs),
            "sufficiency_violated_in_split_case": split_lhs > split_rhs,
            "true_ews_split": frac_to_dict(true_ews_split),
            "eq10_scalar_alpha_residuals": eq10_residuals,
            "all_tested_scalar_alphas_nonzero_drift": all_scalar_alphas_fail,
            "sufficiency_rhs_pass": frac_to_dict(pass_rhs),
            "sufficiency_holds_in_pass_case": split_lhs <= pass_rhs,
            "pass_case_eq10_alpha1_residual": frac_to_dict(pass_residual),
            "pass_case_exact_zero_drift": pass_residual == 0,
        },
        "part_b_tail_singularity_and_loom": {
            "rho_exact_peaked": frac_to_dict(rho_exact_sing),
            "rho_floored_peaked": frac_to_dict(rho_floored_sing),
            "q_hat_sum_under_floor": frac_to_dict(q_hat_sum_floored),
            "normalization_broken_by_floor": q_hat_sum_floored != 1,
            "alpha_sc_floored": frac_to_dict(alpha_sc_floored),
            "alpha_tis_floored": frac_to_dict(alpha_tis_floored),
            "alpha_mis_floored": frac_to_dict(alpha_mis_floored),
            "tis_immune_to_rho_blowup": alpha_tis_floored == 1,
            "mis_drops_entire_tail": alpha_mis_floored == 0,
            "loom_ir03_rho_exact": frac_to_dict(rho_loom_exact),
            "loom_ir03_paper_eps_spurious_rho": frac_to_dict(rho_loom_paper_eps_floor),
            "loom_ir03_spurious_nonzero_under_eps_floor": rho_loom_paper_eps_floor > 0,
        },
    }


def prove_t4_trap03_tim_vs_ripo_dead_zone() -> dict[str, Any]:
    """Theorem T4 (TRIAD-TRAP-03):
    1) Synchronous (tau=0) kernel TIM causes 400/37x IS second-moment jump despite TV < 10%.
    2) Raw RIPO lower-clip dead zone when q < delta (1 - sqrt(delta/q) < 0) + 16x isometry break
       under dual-clip floor 0.5.
    3) Exact heteroscedasticity refutation of RIPO Eq. (14): v(4/5)/v(1/2000) = 2500/121 > 20x.
    4) Noisy rollout q corrupts RIPO trust region by 289x over true learner manifold distance.
    """
    # 1. Synchronous TIM second-moment jump
    p_sync = [Fraction(9, 10), Fraction(1, 10)]
    q_sync = [Fraction(999, 1000), Fraction(1, 1000)]
    tv_sync = Fraction(1, 2) * sum((abs(p_sync[i] - q_sync[i]) for i in range(2)), Fraction(0, 1))
    second_moment_tim = sum((p_sync[i] * p_sync[i] / q_sync[i] for i in range(2)), Fraction(0, 1))
    chi2_sync_tim = second_moment_tim - 1

    # 2. RIPO lower-clip dead zone at default delta = 1/20, q = 1/80
    delta_ripo = Fraction(1, 20)
    q_dead = Fraction(1, 80)
    raw_lo, raw_hi, eps_dead = compute_ripo_exact_bound(
        q_dead, delta_ripo, Fraction(1, 2), Fraction(10, 1), True
    )
    clamped_lo, _, _ = compute_ripo_exact_bound(
        q_dead, delta_ripo, Fraction(1, 2), Fraction(10, 1), False
    )
    neg_adv_ratio = Fraction(1, 100)
    unclipped_by_raw_ripo = raw_lo < neg_adv_ratio
    dual_clip_dist = q_dead * (clamped_lo - 1) * (clamped_lo - 1)
    isometry_shrink_factor = delta_ripo / dual_clip_dist

    # 3. Exact heteroscedasticity ratio at delta = 1/20
    q_lo = Fraction(1, 2000)
    q_hi = Fraction(4, 5)
    eps_lo = exact_rational_sqrt(delta_ripo / q_lo, "delta/q_lo")
    eps_hi = exact_rational_sqrt(delta_ripo / q_hi, "delta/q_hi")
    v_lo = q_lo * (1 + eps_lo) * (1 + eps_lo)
    v_hi = q_hi * (1 + eps_hi) * (1 + eps_hi)
    heteroscedasticity_ratio = v_hi / v_lo

    # 4. Kernel TIM corrupting RIPO trust region by 289x
    delta_tr = Fraction(1, 25)
    p_old_tok = Fraction(1, 100)
    q_noisy_tok = Fraction(1, 4)
    eps_noisy = exact_rational_sqrt(delta_tr / q_noisy_tok, "delta_tr/q_noisy")
    p_admitted = q_noisy_tok * (1 + eps_noisy)
    noisy_ripo_dist = q_noisy_tok * (p_admitted / q_noisy_tok - 1) ** 2
    true_learner_dist = p_old_tok * (p_admitted / p_old_tok - 1) ** 2
    trust_region_overshoot_factor = true_learner_dist / delta_tr

    return {
        "sync_tim_explosion": {
            "tv_distance": frac_to_dict(tv_sync),
            "is_second_moment": frac_to_dict(second_moment_tim),
            "chi2_divergence": frac_to_dict(chi2_sync_tim),
            "second_moment_exceeds_10x": second_moment_tim > 10,
        },
        "ripo_lower_clip_dead_zone": {
            "delta": frac_to_dict(delta_ripo),
            "q_token": frac_to_dict(q_dead),
            "eps": frac_to_dict(eps_dead),
            "raw_lower_bound": frac_to_dict(raw_lo),
            "raw_upper_bound": frac_to_dict(raw_hi),
            "raw_lower_negative": raw_lo < 0,
            "neg_adv_ratio_unclipped_raw": unclipped_by_raw_ripo,
            "dual_clip_floor": frac_to_dict(clamped_lo),
            "dual_clip_geom_dist": frac_to_dict(dual_clip_dist),
            "isometry_shrink_factor": frac_to_dict(isometry_shrink_factor),
        },
        "ripo_heteroscedasticity": {
            "v_q_1_2000": frac_to_dict(v_lo),
            "v_q_4_5": frac_to_dict(v_hi),
            "heteroscedasticity_ratio": frac_to_dict(heteroscedasticity_ratio),
            "exceeds_20x": heteroscedasticity_ratio > 20,
        },
        "tim_trust_region_corruption": {
            "delta": frac_to_dict(delta_tr),
            "p_old": frac_to_dict(p_old_tok),
            "q_noisy": frac_to_dict(q_noisy_tok),
            "p_admitted": frac_to_dict(p_admitted),
            "noisy_ripo_dist": frac_to_dict(noisy_ripo_dist),
            "noisy_ripo_passes": noisy_ripo_dist == delta_tr,
            "true_learner_dist": frac_to_dict(true_learner_dist),
            "overshoot_factor": frac_to_dict(trust_region_overshoot_factor),
        },
    }


def prove_t5_trap04_songe_bregman_and_d3_sandwich() -> dict[str, Any]:
    """Theorem T5 (TRIAD-TRAP-04):
    1) Exact clipped-ratio KL anti-teacher gradient reversal (+1/504) vs.
       exact quadratic Bregman (-496/63) and Score-Centering forward KL (-31/64)
       at p_teacher = 1/2, q_student = 1/64, clip_hi = 2 (songe SNG-01 bridge).
    2) Exact pure-Q Padé / Hermite-Hadamard D_3(w) = w - 1 - log(w) sandwich
       linking REINFORCE Zero's D_3 diagnostic to RIPO's chi^2 trust region.
    """
    p0 = Fraction(1, 2)
    p1 = Fraction(1, 1) - p0
    q0 = Fraction(1, 64)
    q1 = Fraction(1, 1) - q0
    r0 = p0 / q0  # 32 (exceeds clip_hi = 2)
    r1 = p1 / q1  # 32/63 (inside [0, 2])
    clip_hi = Fraction(2, 1)

    # Exact quadratic Bregman / chi^2 derivative dL/dq0 = (1 - r0^2)/2 - (1 - r1^2)/2 < 0
    dterm0_true = Fraction(1, 2) * (1 - r0 * r0)
    dterm1_true = Fraction(1, 2) * (1 - r1 * r1)
    dl_dq0_bregman = dterm0_true - dterm1_true
    dl_dz0_bregman = q0 * q1 * dl_dq0_bregman

    # Clipped ratio (r0 clamped at 2 -> constant (2 - 1)^2 / 2 = +1/2) flips sign > 0
    dterm0_clipped = Fraction(1, 2) * (clip_hi - 1) * (clip_hi - 1)
    dl_dq0_clipped = dterm0_clipped - dterm1_true
    dl_dz0_clipped = q0 * q1 * dl_dq0_clipped

    # Score-Centering forward KL gradient d/dz0 D_KL(p || q) = q0 - p0 = -31/64 < 0
    dl_dz0_forward_kl = q0 - p0

    # Exact D_3(w) = w - 1 - log(w) pure-Q sandwich on w > 1 and 0 < w < 1
    w_gt = Fraction(3, 2)
    d3_gt_lo, d3_gt_hi = d3_rational_bounds(w_gt)
    chi2_gt = Fraction(1, 2) * (w_gt - 1) * (w_gt - 1)

    w_lt = Fraction(1, 2)
    d3_lt_lo, d3_lt_hi = d3_rational_bounds(w_lt)
    chi2_lt = Fraction(1, 2) * (w_lt - 1) * (w_lt - 1)

    w_eq = Fraction(1, 1)
    d3_eq_lo, d3_eq_hi = d3_rational_bounds(w_eq)

    return {
        "clipped_kl_reversal": {
            "p_teacher": frac_to_dict(p0),
            "q_student": frac_to_dict(q0),
            "clip_hi": frac_to_dict(clip_hi),
            "dl_dq0_bregman": frac_to_dict(dl_dq0_bregman),
            "dl_dz0_bregman": frac_to_dict(dl_dz0_bregman),
            "dl_dq0_clipped": frac_to_dict(dl_dq0_clipped),
            "dl_dz0_clipped": frac_to_dict(dl_dz0_clipped),
            "dl_dz0_forward_kl": frac_to_dict(dl_dz0_forward_kl),
            "clipped_reverses_gradient_anti_teacher": dl_dz0_clipped > 0,
            "bregman_pulls_toward_teacher": dl_dz0_bregman < 0,
            "forward_kl_pulls_toward_teacher": dl_dz0_forward_kl < 0,
        },
        "d3_ripo_sandwich": {
            "w_3_2_lo": frac_to_dict(d3_gt_lo),
            "w_3_2_hi": frac_to_dict(d3_gt_hi),
            "w_3_2_half_sq": frac_to_dict(chi2_gt),
            "w_3_2_ordered": Fraction(0, 1) < d3_gt_lo < d3_gt_hi < chi2_gt,
            "w_1_2_lo": frac_to_dict(d3_lt_lo),
            "w_1_2_hi": frac_to_dict(d3_lt_hi),
            "w_1_2_half_sq": frac_to_dict(chi2_lt),
            "w_1_2_ordered": Fraction(0, 1) < chi2_lt < d3_lt_lo < d3_lt_hi,
            "w_1_vanishes": (d3_eq_lo == 0) and (d3_eq_hi == 0),
        },
    }


def _parse_topk_indices(raw_indices: Any, vocab_size: int) -> tuple[int, ...] | None:
    """Strictly validate optional top_k_indices (distinct int indices, 1 <= K < V)."""
    if raw_indices is None:
        return None
    if not isinstance(raw_indices, (list, tuple)):
        raise ValueError("top_k_indices must be list/tuple or None")
    if len(raw_indices) < 1 or len(raw_indices) >= vocab_size:
        raise ValueError("top_k_indices length must satisfy 1 <= K < V")
    seen: set[int] = set()
    out: list[int] = []
    for pos, idx in enumerate(raw_indices):
        if type(idx) is not int:
            raise ValueError(f"top_k_indices[{pos}] must be exact int")
        if idx < 0 or idx >= vocab_size or idx in seen:
            raise ValueError(f"top_k_indices[{pos}] out of range or duplicate")
        seen.add(idx)
        out.append(idx)
    return tuple(out)


def certify_unified_rl_step(step_spec: Any) -> dict[str, Any]:
    """Fail-closed Unified 3-Axis RL Stability & Trust-Region Certifier.

    Enforces all 6 orthogonal compositional gates across:
      G1: Axis-1 Kernel TII flags + max_tim_ratio + chi2_tim
      G2: Axis-1/3 IS second-moment + D_3 upper bound + REINFORCE Zero Thm-1 contraction
      G3: Axis-2 exact weighted Score Centering zero-drift (closes TRIAD-TRAP-01)
      G4: Axis-2x3 Top-K tail_mass_ratio bound + RIPO split-tail sufficiency (closes TRIAD-TRAP-02)
      G5: Axis-3 positive-clamped RIPO on true p_old + dead-zone refusal + total chi^2 budget (closes TRIAD-TRAP-03)
      G6: Axis-2/3 Bregman KL non-reversal refusal on clipped_ratio_kl (closes TRIAD-TRAP-04)
    """
    if not isinstance(step_spec, dict):
        raise ValueError("step_spec must be a dict")
    spec_keys = set(step_spec.keys())
    if spec_keys != ALLOWED_CERTIFIER_KEYS:
        raise ValueError("step_spec keys must match exact allowed schema")

    q = validate_simplex(step_spec["q"], "q")
    p_old = validate_simplex(step_spec["p_old"], "p_old")
    p = validate_simplex(step_spec["p"], "p")
    vocab_size = len(q)
    if len(p_old) != vocab_size or len(p) != vocab_size:
        raise ValueError("q, p_old, p must have identical length")

    raw_features = step_spec["features"]
    if not isinstance(raw_features, (list, tuple)) or len(raw_features) != vocab_size:
        raise ValueError("features must match vocabulary length")
    features = [exact_frac(raw_features[i], f"features[{i}]") for i in range(vocab_size)]

    tii_flags_aligned = exact_bool(step_spec["tii_flags_aligned"], "tii_flags_aligned")
    allow_negative_lower_clip = exact_bool(
        step_spec["allow_negative_lower_clip"], "allow_negative_lower_clip"
    )
    use_true_p_old_for_ripo = exact_bool(
        step_spec["use_true_p_old_for_ripo"], "use_true_p_old_for_ripo"
    )

    weighting_mode = step_spec["weighting_mode"]
    if type(weighting_mode) is not str or weighting_mode not in ALLOWED_WEIGHTING_MODES:
        raise ValueError("invalid weighting_mode")
    centering_mode = step_spec["centering_mode"]
    if type(centering_mode) is not str or centering_mode not in ALLOWED_CENTERING_MODES:
        raise ValueError("invalid centering_mode")
    kl_mode = step_spec["kl_mode"]
    if type(kl_mode) is not str or kl_mode not in ALLOWED_KL_MODES:
        raise ValueError("invalid kl_mode")

    max_tim_ratio = exact_frac(step_spec["max_tim_ratio"], "max_tim_ratio")
    max_tim_chi2 = exact_frac(step_spec["max_tim_chi2"], "max_tim_chi2")
    delta = exact_frac(step_spec["delta"], "delta")
    delta_total = exact_frac(step_spec["delta_total"], "delta_total")
    dual_clip_low = exact_frac(step_spec["dual_clip_low"], "dual_clip_low")
    dual_clip_high = exact_frac(step_spec["dual_clip_high"], "dual_clip_high")
    max_tail_rho = exact_frac(step_spec["max_tail_rho"], "max_tail_rho")
    max_second_moment = exact_frac(step_spec["max_second_moment"], "max_second_moment")
    max_d3_upper = exact_frac(step_spec["max_d3_upper"], "max_d3_upper")
    eta = exact_frac(step_spec["eta"], "eta")
    step_variance_v = exact_frac(step_spec["step_variance_v"], "step_variance_v")

    if max_tim_ratio < 1 or max_tim_chi2 < 0:
        raise ValueError("max_tim_ratio must be >= 1 and max_tim_chi2 >= 0")
    if delta <= 0 or delta_total <= 0:
        raise ValueError("delta and delta_total must be strictly positive")
    if dual_clip_low <= 0 or dual_clip_low > 1 or dual_clip_high < 1:
        raise ValueError("dual_clip bounds must satisfy 0 < low <= 1 <= high")
    if max_tail_rho < 1 or max_second_moment < 1 or max_d3_upper < 0:
        raise ValueError("max_tail_rho >= 1, max_second_moment >= 1, max_d3_upper >= 0 required")
    if eta <= 0 or step_variance_v < 0:
        raise ValueError("eta must be > 0 and step_variance_v >= 0")

    top_k_indices = _parse_topk_indices(step_spec["top_k_indices"], vocab_size)

    reasons: list[str] = []

    # --- Gate G1: Axis-1 Kernel TII Contract ---
    r_tim = [p_old[i] / q[i] for i in range(vocab_size)]
    observed_max_tim_ratio = max(max(x, Fraction(1, 1) / x) for x in r_tim)
    chi2_tim = sum(
        (q[i] * (r_tim[i] - 1) * (r_tim[i] - 1) for i in range(vocab_size)),
        Fraction(0, 1),
    )
    if not tii_flags_aligned:
        reasons.append("TII_KERNEL_FLAGS_UNALIGNED")
    if observed_max_tim_ratio > max_tim_ratio:
        reasons.append("TII_RATIO_EXCEEDS_BOUND")
    if chi2_tim > max_tim_chi2:
        reasons.append("TII_CHI2_EXCEEDS_BOUND")

    # --- Effective per-token weights ---
    r_tot = [p[i] / q[i] for i in range(vocab_size)]
    ripo_base = p_old if use_true_p_old_for_ripo else q
    if weighting_mode == "unclipped_is":
        w_eff = list(r_tot)
    elif weighting_mode == "tis":
        w_eff = [min(x, dual_clip_high) for x in r_tot]
    else:
        w_eff = [
            clamp_ratio_ripo_exact(
                r_tot[i],
                ripo_base[i],
                delta,
                dual_clip_low,
                dual_clip_high,
                allow_negative_lower_clip,
            )
            for i in range(vocab_size)
        ]

    # --- Gate G5: Axis-3 RIPO Trust Region, True p_old Basis & Lower-Clip Dead Zone ---
    if weighting_mode == "ripo_clamped":
        if not use_true_p_old_for_ripo:
            reasons.append("RIPO_NOISY_ROLLOUT_BASIS_POLICY")
        if allow_negative_lower_clip:
            reasons.append("RIPO_LOWER_CLIP_DEAD_ZONE_ENABLED")

    # Learner-manifold trust-region distance using effective probabilities induced by r_lag
    r_lag = [p[i] / p_old[i] for i in range(vocab_size)]
    learner_half_chi2 = Fraction(1, 2) * sum(
        (p_old[i] * (r_lag[i] - 1) * (r_lag[i] - 1) for i in range(vocab_size)),
        Fraction(0, 1),
    )
    if learner_half_chi2 > delta_total:
        reasons.append("TRUST_REGION_BUDGET_EXCEEDED")

    # --- Gate G2: IS Second Moment, D_3 Upper Bound & REINFORCE Zero Thm-1 Contraction ---
    second_moment = sum(
        (q[i] * w_eff[i] * w_eff[i] for i in range(vocab_size)), Fraction(0, 1)
    )
    d3_upper = sum(
        (q[i] * d3_rational_bounds(r_tot[i])[1] for i in range(vocab_size)),
        Fraction(0, 1),
    )
    # Effective variance multiplier scales base step_variance_v by observed IS second moment
    v_eff = step_variance_v * second_moment
    rho_step = (Fraction(1, 1) - eta) ** 2 + eta * eta * v_eff
    if second_moment > max_second_moment:
        reasons.append("IS_SECOND_MOMENT_EXCEEDED")
    if d3_upper > max_d3_upper:
        reasons.append("D3_DIAGNOSTIC_EXCEEDED")
    if rho_step >= 1:
        reasons.append("STEP_SIZE_STABILITY_VIOLATED")

    # --- Gate G3: Axis-2 Exact Weighted Score Centering Zero-Drift ---
    s = softmax_scores(p, features)
    s_bar_q = sum((q[i] * s[i] for i in range(vocab_size)), Fraction(0, 1))
    e_w = sum((q[i] * w_eff[i] for i in range(vocab_size)), Fraction(0, 1))
    e_ws = sum((q[i] * w_eff[i] * s[i] for i in range(vocab_size)), Fraction(0, 1))
    full_vocab_uncentered_zero = all(
        q[i] * w_eff[i] == e_w * p[i] for i in range(vocab_size)
    )
    if centering_mode == "weighted_sc":
        residual_drift = sum(
            (q[i] * (w_eff[i] * s[i] - e_ws) for i in range(vocab_size)), Fraction(0, 1)
        )
    elif centering_mode == "naive_sc":
        reasons.append("NAIVE_SC_POLICY_UNSOUND")
        residual_drift = sum(
            (q[i] * w_eff[i] * (s[i] - s_bar_q) for i in range(vocab_size)),
            Fraction(0, 1),
        )
    else:
        residual_drift = e_ws
    if residual_drift != 0 or (
        centering_mode == "none" and not full_vocab_uncentered_zero
    ):
        reasons.append("SCORE_CENTERING_RESIDUAL_DRIFT_NONZERO")

    # --- Gate G4: Axis-2x3 Top-K Tail Ratio & RIPO/TIS Split-Tail Exactness ---
    topk_tail_rho: Fraction | None = None
    if top_k_indices is not None:
        head_set = set(top_k_indices)
        tail_indices = [i for i in range(vocab_size) if i not in head_set]
        if min(q[i] for i in top_k_indices) < max(q[i] for i in tail_indices):
            reasons.append("TOPK_HEAD_NOT_DOMINATING_TAIL")
        q_tail = sum((q[i] for i in tail_indices), Fraction(0, 1))
        p_tail = sum((p[i] for i in tail_indices), Fraction(0, 1))
        topk_tail_rho = q_tail / p_tail
        sym_tail_rho = max(topk_tail_rho, Fraction(1, 1) / topk_tail_rho)
        if sym_tail_rho > max_tail_rho:
            reasons.append("TOPK_TAIL_MASS_RATIO_EXCEEDED")
        r_tail_modeled = Fraction(1, 1) / topk_tail_rho
        alpha_modeled = (
            topk_tail_rho * min(r_tail_modeled, dual_clip_high)
            if weighting_mode == "tis"
            else Fraction(1, 1)
        )
        actual_tail_mismatch = any(
            q[i] * w_eff[i] != alpha_modeled * p[i] for i in tail_indices
        )
        if weighting_mode == "ripo_clamped":
            max_p_tail = max(p[i] for i in tail_indices)
            split_tail_violated = (
                max_p_tail * (Fraction(1, 1) - topk_tail_rho) ** 2
                > delta * topk_tail_rho
            )
            tail_dual_clip_violated = (
                r_tail_modeled < dual_clip_low or r_tail_modeled > dual_clip_high
            )
            if split_tail_violated or tail_dual_clip_violated or actual_tail_mismatch:
                reasons.append("TOPK_RIPO_SPLIT_TAIL_VIOLATION")
        elif actual_tail_mismatch:
            reasons.append("TOPK_TAIL_WEIGHT_MISMATCH")

    # --- Gate G6: Axis-2/3 Bregman KL Non-Reversal Gate ---
    if kl_mode == "clipped_ratio_kl":
        reasons.append("NON_BREGMAN_CLIPPED_KL_REVERSAL")

    admitted = len(reasons) == 0
    return {
        "admitted": admitted,
        "status": "ADMITTED_UNIFIED_RL_STEP" if admitted else "REJECTED_UNIFIED_RL_STEP",
        "reasons": reasons,
        "diagnostics": {
            "observed_max_tim_ratio": frac_to_dict(observed_max_tim_ratio),
            "chi2_tim": frac_to_dict(chi2_tim),
            "learner_half_chi2": frac_to_dict(learner_half_chi2),
            "is_second_moment": frac_to_dict(second_moment),
            "d3_upper_bound": frac_to_dict(d3_upper),
            "step_contraction_rho": frac_to_dict(rho_step),
            "residual_drift": frac_to_dict(residual_drift),
            "topk_tail_rho": (
                frac_to_dict(topk_tail_rho) if topk_tail_rho is not None else None
            ),
        },
    }


def _demo_certifier_cases() -> dict[str, Any]:
    """Canonical admitted vs. multi-trap rejected step certificates."""
    # Clean unified step: TII aligned (q == p_old), weighted SC + clamped RIPO + exact Bregman KL,
    # Top-2 tail satisfies max_p_tail * (1 - rho)^2 <= delta * rho!
    q_good = [Fraction(4, 9), Fraction(4, 9), Fraction(1, 9)]
    p_good = [Fraction(1, 2), Fraction(7, 18), Fraction(1, 9)]
    good_spec: dict[str, Any] = {
        "q": q_good,
        "p_old": list(q_good),
        "p": p_good,
        "features": [Fraction(1, 1), Fraction(-1, 1), Fraction(0, 1)],
        "tii_flags_aligned": True,
        "max_tim_ratio": Fraction(1, 1),
        "max_tim_chi2": Fraction(0, 1),
        "weighting_mode": "ripo_clamped",
        "centering_mode": "weighted_sc",
        "kl_mode": "exact_bregman",
        "delta": Fraction(1, 25),
        "delta_total": Fraction(1, 10),
        "dual_clip_low": Fraction(1, 2),
        "dual_clip_high": Fraction(10, 1),
        "allow_negative_lower_clip": False,
        "use_true_p_old_for_ripo": True,
        "top_k_indices": [0, 1],
        "max_tail_rho": Fraction(5, 1),
        "max_second_moment": Fraction(2, 1),
        "max_d3_upper": Fraction(1, 5),
        "eta": Fraction(1, 2),
        "step_variance_v": Fraction(1, 1),
    }

    # Multi-trap failing step triggering ALL 6 orthogonal gate families simultaneously!
    bad_spec: dict[str, Any] = {
        "q": [Fraction(289, 484), Fraction(169, 484), Fraction(25, 484), Fraction(1, 484)],
        "p_old": [Fraction(1, 2), Fraction(1, 4), Fraction(3, 16), Fraction(1, 16)],
        "p": [Fraction(320, 484), Fraction(60, 484), Fraction(100, 484), Fraction(4, 484)],
        "features": [Fraction(0, 1), Fraction(0, 1), Fraction(1, 1), Fraction(-1, 1)],
        "tii_flags_aligned": False,
        "max_tim_ratio": Fraction(1, 1),
        "max_tim_chi2": Fraction(0, 1),
        "weighting_mode": "ripo_clamped",
        "centering_mode": "naive_sc",
        "kl_mode": "clipped_ratio_kl",
        "delta": Fraction(25, 484),
        "delta_total": Fraction(1, 100),
        "dual_clip_low": Fraction(1, 2),
        "dual_clip_high": Fraction(10, 1),
        "allow_negative_lower_clip": True,
        "use_true_p_old_for_ripo": False,
        "top_k_indices": [0, 1],
        "max_tail_rho": Fraction(1, 1),
        "max_second_moment": Fraction(1, 1),
        "max_d3_upper": Fraction(1, 100),
        "eta": Fraction(4, 5),
        "step_variance_v": Fraction(2, 1),
    }

    return {
        "hardened_unified_step": certify_unified_rl_step(good_spec),
        "multi_trap_unaligned_step": certify_unified_rl_step(bad_spec),
    }


def build_certificate(
    repos_dir: Path | None = None, standalone: bool = False
) -> dict[str, Any]:
    """Assemble the canonical zero-float AUDIT-082 certificate."""
    if standalone:
        anchor_section: dict[str, Any] = {
            "anchor_mode": "standalone",
            "files_total": len(EXPECTED_PINNED_SHA256),
            "all_file_digests_matched": None,
            "anchors_total": len(ANCHOR_SPECS),
            "anchors_verified": 0,
            "all_anchors_matched": None,
        }
    else:
        resolved = (
            repos_dir
            if repos_dir is not None
            else (Path(__file__).resolve().parent.parent / "repos")
        )
        anchor_section = verify_live_anchors(resolved)

    payload: dict[str, Any] = {
        "audit_id": "AUDIT-082",
        "arm": "R9-5",
        "title": "Unified Off-Policy RL Geometry & Kernel-Invariance Composition",
        "oracle_class": "exact+anchor",
        "novelty_class": "N1",
        "zero_float_enforced": True,
        "pinned_vectors": {
            "score_centering_arxiv": "arXiv:2609.20807v1",
            "score_centering_repo": "martin-marek/score-centering@fdca22b19793babdf08e33e5ba51537e82cbed2f",
            "ripo_arxiv": "arXiv:2607.10169v2",
            "reinforce_zero_alphaxiv": "alphaXiv:2611.reinforce-zero-kernel-alignment-asynchronous-rl",
            "reinforce_zero_repo": "hijkzzz/REINFORCE-Zero@a22153de4b8c4b47faf5bf88a598d6d54801bfc7",
            "zero_mismatch_rl_repo": "Inferact/zero-mismatch-rl@136aca87d8158adae94b5a272fa4a8a6d5cd6939",
        },
        "cross_pollination_targets": [
            "Moissanite-Labs/warp-drive#12 (AUDIT-064 WI-4 Fisher-Schur)",
            "Moissanite-Labs/warp-drive#15 (AUDIT-066R Stage-1 RuntimeFlags)",
            "Moissanite-Labs/warp-drive#21 (AUDIT-073R songe SNG-01 Bregman KL)",
            "Moissanite-Labs/siliquant#26 (AUDIT-068R Magnitude)",
            "Moissanite-Labs/siliquant#27 (AUDIT-074R Inkling LOOM-IR-03 Top-64)",
        ],
        "anchors": anchor_section,
        "proofs": {
            "t1_three_axis_factorization": prove_t1_three_axis_factorization(),
            "t2_trap01_naive_sc_ripo": prove_t2_trap01_naive_sc_ripo(),
            "t3_trap02_topk_ripo_split_tail": prove_t3_trap02_topk_ripo_split_tail_and_singularity(),
            "t4_trap03_tim_vs_ripo_dead_zone": prove_t4_trap03_tim_vs_ripo_dead_zone(),
            "t5_trap04_songe_bregman_d3_sandwich": prove_t5_trap04_songe_bregman_and_d3_sandwich(),
        },
        "certifier_cases": _demo_certifier_cases(),
    }
    canonical_bytes = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode(
        "utf-8"
    )
    payload["canonical_sha256"] = hashlib.sha256(canonical_bytes).hexdigest()
    return payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="AUDIT-082 pure-Q Unified RL Triad Composition & Stability Oracle"
    )
    parser.add_argument("--json", action="store_true", help="Print canonical JSON")
    parser.add_argument(
        "--standalone",
        action="store_true",
        help="Run pure-Q proofs without reading sibling repos directory",
    )
    parser.add_argument(
        "--repos-dir",
        type=str,
        default=None,
        help="Optional override path to Round-9 staged repos directory",
    )
    parser.add_argument(
        "--write-cert",
        type=str,
        default=None,
        help="Write canonical pretty JSON certificate to path",
    )
    args = parser.parse_args(argv)
    repos_path = Path(args.repos_dir) if args.repos_dir is not None else None
    cert = build_certificate(repos_dir=repos_path, standalone=args.standalone)
    text = json.dumps(cert, indent=2, sort_keys=True) + "\n"
    if args.write_cert is not None:
        Path(args.write_cert).write_text(text, encoding="utf-8")
    if args.json or args.write_cert is None:
        sys.stdout.write(text)
    if not args.standalone and not cert["anchors"]["all_anchors_matched"]:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
