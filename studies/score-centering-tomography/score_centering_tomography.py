#!/usr/bin/env python3
"""Exact pure-Q Score Centering tomography, live repo oracle, and fail-closed Top-K gate.

Targets (strictly read-only):
  - arXiv:2609.20807v1 (Marek & Ryabinin, 2026): Score Centering Stabilizes Off-policy RL
  - martin-marek/score-centering @ fdca22b19793babdf08e33e5ba51537e82cbed2f
  - Zhihu 2092277762245538186 (Aiolus, sanctioned read-only transcript)

100% pure Python 3 stdlib using exact int/Fraction arithmetic.
Zero floating-point literals or values; zero bare assert statements.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
from typing import Any, Sequence


SCHEMA_VERSION = "score-centering-tomography-v1"
AUDIT_ID = "AUDIT-080"
PINNED_REPO_COMMIT = "fdca22b19793babdf08e33e5ba51537e82cbed2f"

ALLOWED_CORRECTION_MODES = ("none", "tis", "mis", "unclipped_is")
ALLOWED_BATCH_MODES = ("none", "full_vocab", "topk_head")
ALLOWED_IS_LEVELS = ("none", "token", "seq_mean", "seq_sum")
ALLOWED_IS_STATS = ("ratio", "tv")
ALLOWED_BATCH_SPEC_KEYS = frozenset(
    {"batch_mode", "has_full_vocab", "has_topk_head", "is_level", "is_stat", "score_center"}
)

PINNED_SOURCE_DIGESTS: dict[str, dict[str, Any]] = {
    "score-centering/arxiv_2609.20807.pdf": {
        "bytes": 1354897,
        "sha256": "73173515a8f1244e7c20b5ffc2a47270b1e0fe31c099b075d35460af58b64019",
    },
    "score-centering/arxiv_2609.20807.txt": {
        "bytes": 56454,
        "sha256": "a53342f3774e1effd43e386e06ae76766c0002262616d2cfa8a5726c90b87cd2",
    },
    "score-centering/arxiv_2609.20807_layout.txt": {
        "bytes": 76219,
        "sha256": "01d1959f6f0e929e60bd571f8bb9c5b16abc5b918b44846303672fbaa761ae16",
    },
    "zhihu/zhihu_2092277762245538186_score_centering.md": {
        "bytes": 9437,
        "sha256": "74443b91fa1668f3aa15e170de2520a02f356f64be549a60de2bcc84484f6d3d",
    },
    "score-centering/repo/losses.py": {
        "bytes": 9013,
        "sha256": "c9094e9663d1770badcfc0327c41aa201e408dd0b868d6656444c4f497b04820",
    },
    "score-centering/repo/tests/test_loss.py": {
        "bytes": 2087,
        "sha256": "199fa0e2d684a6727940c7bfad9c6afee75e0446b7a0132911c9383c798aa91d",
    },
    "score-centering/repo/README.md": {
        "bytes": 8821,
        "sha256": "94422aa05a3dd0e43b74427fd8c9c80612f76256ee509d43b15207ec1b190c9c",
    },
}

VERBATIM_ANCHORS: tuple[tuple[str, str, int, str], ...] = (
    (
        "SC-ZHIHU-01",
        "zhihu/zhihu_2092277762245538186_score_centering.md",
        42,
        "reverse KL",
    ),
    (
        "SC-ZHIHU-02",
        "zhihu/zhihu_2092277762245538186_score_centering.md",
        112,
        "+ \\mathbb{E}_{\\mu}\\left[A\\right]\\mathbb{E}_{\\mu}\\left[z \\right]",
    ),
    (
        "SC-SING-01-ZHIHU",
        "zhihu/zhihu_2092277762245538186_score_centering.md",
        88,
        "tail_mass_ratio = (1 - jnp.exp(samp_logp).sum()) / (1 - jnp.exp(train_head_logp).sum())",
    ),
    (
        "SC-CODE-01-FULL",
        "score-centering/repo/losses.py",
        139,
        "if score_center and full:",
    ),
    (
        "SC-CODE-01-HEAD",
        "score-centering/repo/losses.py",
        143,
        'if "center_ids" in b:',
    ),
    (
        "SC-CODE-02-GATE",
        "score-centering/repo/losses.py",
        121,
        'c.stat == "ratio"',
    ),
    (
        "SC-CODE-02-SEQ",
        "score-centering/repo/losses.py",
        162,
        "if seq_c:",
    ),
    (
        "SC-CODE-02-GSPO",
        "score-centering/repo/README.md",
        132,
        "| GSPO | `level=seq_mean low=0.9997 high=1.0004 sign=ppo` |",
    ),
    (
        "SC-CODE-02-TOPR",
        "score-centering/repo/README.md",
        133,
        "| TOPR | `level=seq_sum high=1.0 outside=clamp sign=neg` |",
    ),
    (
        "SC-CODE-03-QTAIL",
        "score-centering/repo/losses.py",
        146,
        "q_tail = 1.0 - q_head.sum(-1)",
    ),
    (
        "SC-CODE-03-ALPHA",
        "score-centering/repo/losses.py",
        150,
        "alpha = jnp.exp(log_mass(0.0, jnp.log(rho), positive, token_c))",
    ),
    (
        "SC-CODE-04-EPS",
        "score-centering/repo/losses.py",
        147,
        "jnp.maximum(1.0 - p_head.sum(-1), 1e-6)",
    ),
    (
        "SC-CODE-05-TEST",
        "score-centering/repo/tests/test_loss.py",
        28,
        'if center == "topk":  # k = V - 1',
    ),
)


class ScoreCenteringAuditError(ValueError):
    """Fail-closed refusal raised whenever any mathematical or contract invariant fails."""


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ScoreCenteringAuditError(message)


def _require_exact_int(value: Any, name: str) -> int:
    _require(isinstance(value, int) and not isinstance(value, bool), f"exact-int:{name}")
    return value


def _require_exact_fraction(value: Any, name: str) -> Fraction:
    if isinstance(value, Fraction):
        return value
    if isinstance(value, int) and not isinstance(value, bool):
        return Fraction(value, 1)
    raise ScoreCenteringAuditError(f"exact-fraction:{name}")


def _require_exact_choice(value: Any, allowed: tuple[str, ...], name: str) -> str:
    _require(isinstance(value, str) and value in allowed, f"exact-choice:{name}")
    return value


def frac_str(value: Fraction) -> str:
    val = _require_exact_fraction(value, "frac_str")
    return f"{val.numerator}/{val.denominator}"


def vec_frac_str(vec: Sequence[Fraction]) -> list[str]:
    return [frac_str(x) for x in vec]


def _validate_simplex(dist: Sequence[Any], name: str, allow_zero: bool = True) -> tuple[Fraction, ...]:
    _require(isinstance(dist, (list, tuple)) and len(dist) >= 2, f"simplex-len:{name}")
    out: list[Fraction] = []
    total = Fraction(0, 1)
    for i, item in enumerate(dist):
        val = _require_exact_fraction(item, f"{name}[{i}]")
        if allow_zero:
            _require(val >= 0, f"simplex-nonneg:{name}[{i}]")
        else:
            _require(val > 0, f"simplex-pos:{name}[{i}]")
        out.append(val)
        total += val
    _require(total == 1, f"simplex-sum:{name}")
    return tuple(out)


def softmax_scores(trainer_probs: Sequence[Fraction]) -> tuple[tuple[Fraction, ...], ...]:
    """Exact tabular softmax score vectors s_v = e_v - p in Q^V."""
    p = _validate_simplex(trainer_probs, "trainer_probs", allow_zero=False)
    vocab = len(p)
    return tuple(
        tuple((Fraction(1, 1) if j == v else Fraction(0, 1)) - p[j] for j in range(vocab))
        for v in range(vocab)
    )


def expected_vec(probs: Sequence[Fraction], vectors: Sequence[Sequence[Fraction]]) -> tuple[Fraction, ...]:
    _require(len(probs) == len(vectors) and len(probs) > 0, "expected-vec-len")
    dim = len(vectors[0])
    out = [Fraction(0, 1)] * dim
    for weight, vec in zip(probs, vectors):
        _require(len(vec) == dim, "expected-vec-dim")
        for j in range(dim):
            out[j] += weight * vec[j]
    return tuple(out)


def vec_sub(a: Sequence[Fraction], b: Sequence[Fraction]) -> tuple[Fraction, ...]:
    _require(len(a) == len(b), "vec-sub-len")
    return tuple(x - y for x, y in zip(a, b))


def vec_add(a: Sequence[Fraction], b: Sequence[Fraction]) -> tuple[Fraction, ...]:
    _require(len(a) == len(b), "vec-add-len")
    return tuple(x + y for x, y in zip(a, b))


def vec_scale(scalar: Fraction, a: Sequence[Fraction]) -> tuple[Fraction, ...]:
    s = _require_exact_fraction(scalar, "vec_scale")
    return tuple(s * x for x in a)


def vec_l1(a: Sequence[Fraction]) -> Fraction:
    return sum((abs(x) for x in a), Fraction(0, 1))


def vec_l2_sq(a: Sequence[Fraction]) -> Fraction:
    return sum((x * x for x in a), Fraction(0, 1))


def vec_linf(a: Sequence[Fraction]) -> Fraction:
    _require(len(a) > 0, "vec-linf-empty")
    return max(abs(x) for x in a)


def covariance_vec(
    probs: Sequence[Fraction],
    advantages: Sequence[Fraction],
    scores: Sequence[Sequence[Fraction]],
) -> tuple[Fraction, ...]:
    mean_a = sum((pr * adv for pr, adv in zip(probs, advantages)), Fraction(0, 1))
    mean_s = expected_vec(probs, scores)
    centered = [vec_scale(adv - mean_a, vec_sub(sc, mean_s)) for adv, sc in zip(advantages, scores)]
    return expected_vec(probs, centered)


def analyze_pillar1_drift_kl_bias() -> dict[str, Any]:
    """Pillar 1: exact drift-signal decomposition, forward vs reverse KL, and bias sign."""
    p = (Fraction(1, 2), Fraction(1, 4), Fraction(1, 4))
    q = (Fraction(1, 4), Fraction(1, 2), Fraction(1, 4))
    scores = softmax_scores(p)

    # Exact score expectation identities
    e_p_score = expected_vec(p, scores)
    e_q_score = expected_vec(q, scores)
    grad_fwd_kl = vec_sub(p, q)  # grad_l KL(q || p) = p - q = -E_q[s]
    neg_grad_fwd_kl = vec_scale(Fraction(-1, 1), grad_fwd_kl)

    # Exact reverse KL gradient normalized by ln(2): log_2(p_v / q_v) = (+1, -1, 0)
    log2_ratios = (Fraction(1, 1), Fraction(-1, 1), Fraction(0, 1))
    rev_kl_grad_div_ln2 = expected_vec(
        p, [vec_scale(lr, sc) for lr, sc in zip(log2_ratios, scores)]
    )
    # Cross-product determinant on coordinates (0, 2) proves non-collinearity with E_q[s]
    collinearity_det_02 = (
        e_q_score[0] * rev_kl_grad_div_ln2[2] - e_q_score[2] * rev_kl_grad_div_ln2[0]
    )

    # Exact drift-signal invariance for non-constant advantage A = (4, 0, 0)
    adv_sample = (Fraction(4, 1), Fraction(0, 1), Fraction(0, 1))
    mean_adv_q = sum((qv * av for qv, av in zip(q, adv_sample)), Fraction(0, 1))
    drift_vec = vec_scale(mean_adv_q, e_q_score)
    cov_raw = covariance_vec(q, adv_sample, scores)
    centered_scores = [vec_sub(sc, e_q_score) for sc in scores]
    e_q_centered = expected_vec(q, centered_scores)
    cov_centered = covariance_vec(q, adv_sample, centered_scores)
    g_off = expected_vec(q, [vec_scale(a, s) for a, s in zip(adv_sample, scores)])
    g_sc = expected_vec(q, [vec_scale(a, s) for a, s in zip(adv_sample, centered_scores)])

    # Witness A: Delta < 0 (SC improves bias strictly) on V=2 binary softmax
    p2 = (Fraction(3, 4), Fraction(1, 4))
    q2 = (Fraction(1, 2), Fraction(1, 2))
    s2 = softmax_scores(p2)
    s2_bar = expected_vec(q2, s2)
    s2_centered = [vec_sub(sc, s2_bar) for sc in s2]

    def _bias_case(
        adv_pi: tuple[Fraction, Fraction], adv_mu: tuple[Fraction, Fraction]
    ) -> dict[str, Any]:
        g_true = expected_vec(p2, [vec_scale(a, s) for a, s in zip(adv_pi, s2)])
        g_off_c = expected_vec(q2, [vec_scale(a, s) for a, s in zip(adv_mu, s2)])
        g_sc_c = expected_vec(q2, [vec_scale(a, s) for a, s in zip(adv_mu, s2_centered)])
        dist_mismatch = vec_sub(
            covariance_vec(p2, adv_pi, s2), covariance_vec(q2, adv_pi, s2)
        )
        adv_mismatch = covariance_vec(q2, vec_sub(adv_pi, adv_mu), s2)
        delta_cov = vec_add(dist_mismatch, adv_mismatch)
        mean_a_mu = sum((qv * av for qv, av in zip(q2, adv_mu)), Fraction(0, 1))
        drift_c = vec_scale(mean_a_mu, s2_bar)
        err_sc = vec_sub(g_true, g_sc_c)
        err_off_exact = vec_sub(g_true, g_off_c)
        err_off_zhihu_bug = vec_add(delta_cov, drift_c)
        delta_l1_exact = vec_l1(err_sc) - vec_l1(err_off_exact)
        delta_l2_sq_exact = vec_l2_sq(err_sc) - vec_l2_sq(err_off_exact)
        delta_linf_exact = vec_linf(err_sc) - vec_linf(err_off_exact)
        delta_l1_zhihu_bug = vec_l1(delta_cov) - vec_l1(err_off_zhihu_bug)
        return {
            "adv_pi": vec_frac_str(adv_pi),
            "adv_mu": vec_frac_str(adv_mu),
            "g_true": vec_frac_str(g_true),
            "g_off": vec_frac_str(g_off_c),
            "g_sc": vec_frac_str(g_sc_c),
            "delta_cov": vec_frac_str(delta_cov),
            "drift": vec_frac_str(drift_c),
            "err_sc": vec_frac_str(err_sc),
            "err_sc_equals_delta_cov": err_sc == delta_cov,
            "err_off_exact": vec_frac_str(err_off_exact),
            "err_off_equals_delta_cov_minus_drift": err_off_exact == vec_sub(delta_cov, drift_c),
            "err_off_zhihu_l112_bug": vec_frac_str(err_off_zhihu_bug),
            "delta_l1_exact": frac_str(delta_l1_exact),
            "delta_l2_sq_exact": frac_str(delta_l2_sq_exact),
            "delta_linf_exact": frac_str(delta_linf_exact),
            "delta_l1_zhihu_l112_bug": frac_str(delta_l1_zhihu_bug),
        }

    # Case 1: Delta < 0 (constant advantage +1)
    case_delta_neg = _bias_case((Fraction(1, 1), Fraction(1, 1)), (Fraction(1, 1), Fraction(1, 1)))
    # Case 2: Delta > 0 (A = (3, -1): vanilla off-policy has ZERO bias, SC has bias 1/2!)
    # Zhihu L112 sign slip (+drift instead of -drift) flips +1/2 into -1/2!
    case_delta_pos = _bias_case((Fraction(3, 1), Fraction(-1, 1)), (Fraction(3, 1), Fraction(-1, 1)))
    # Case 3: Non-zero advantage mismatch A^pi != A^mu proving 2-term decomposition
    case_adv_mismatch = _bias_case(
        (Fraction(2, 1), Fraction(-2, 1)), (Fraction(1, 1), Fraction(-1, 1))
    )

    return {
        "kl_direction_disproof_sc_zhihu_01": {
            "trainer_p": vec_frac_str(p),
            "sampler_q": vec_frac_str(q),
            "expected_score_under_p": vec_frac_str(e_p_score),
            "expected_score_under_q": vec_frac_str(e_q_score),
            "grad_forward_kl_q_p": vec_frac_str(grad_fwd_kl),
            "neg_grad_forward_kl_q_p": vec_frac_str(neg_grad_fwd_kl),
            "equals_neg_forward_kl_grad": e_q_score == neg_grad_fwd_kl,
            "grad_reverse_kl_p_q_div_ln2": vec_frac_str(rev_kl_grad_div_ln2),
            "collinearity_det_coord_0_2": frac_str(collinearity_det_02),
            "equals_any_scalar_multiple_of_reverse_kl_grad": collinearity_det_02 == 0,
        },
        "drift_signal_invariance": {
            "advantages": vec_frac_str(adv_sample),
            "mean_advantage_q": frac_str(mean_adv_q),
            "drift_vec": vec_frac_str(drift_vec),
            "signal_cov_raw": vec_frac_str(cov_raw),
            "signal_cov_centered": vec_frac_str(cov_centered),
            "g_off": vec_frac_str(g_off),
            "g_sc": vec_frac_str(g_sc),
            "zero_drift_exact": all(x == 0 for x in e_q_centered),
            "signal_invariance_exact": cov_centered == cov_raw and g_off == vec_add(drift_vec, cov_raw) and g_sc == cov_raw,
        },
        "bias_sign_and_witnesses_sc_zhihu_02": {
            "binary_p": vec_frac_str(p2),
            "binary_q": vec_frac_str(q2),
            "delta_negative_sc_better": case_delta_neg,
            "delta_positive_sc_worse_and_zhihu_sign_flip": case_delta_pos,
            "advantage_mismatch_identity": case_adv_mismatch,
        },
    }


def tail_scale_alpha(rho: Fraction, mode: str) -> Fraction:
    """Exact rational tail-scale factor alpha(rho) = rho * w(1/rho) for vanilla SC, TIS, MIS."""
    r = _require_exact_fraction(rho, "rho")
    _require(r >= 0, "rho-nonneg")
    m = _require_exact_choice(mode, ALLOWED_CORRECTION_MODES, "mode")
    if r == 0:
        return Fraction(0, 1)
    inv_r = Fraction(1, 1) / r
    if m == "none":
        return r
    if m == "tis":
        w = min(inv_r, Fraction(2, 1))
        return r * w
    if m == "mis":
        if Fraction(1, 2) <= inv_r <= Fraction(5, 1):
            return Fraction(1, 1)
        return Fraction(0, 1)
    return Fraction(1, 1)


def analyze_pillar2_topk_singularity_and_tail_scales() -> dict[str, Any]:
    """Pillar 2: Top-K conservation vs head-residual sum, tail-shape drift, singularity, TIS/MIS."""
    p = (Fraction(1, 2), Fraction(1, 4), Fraction(1, 8), Fraction(1, 8))
    q = (Fraction(1, 4), Fraction(1, 4), Fraction(3, 8), Fraction(1, 8))
    head_ids = (0, 1)
    tail_ids = (2, 3)
    scores = softmax_scores(p)

    p_head_sum = sum((p[i] for i in head_ids), Fraction(0, 1))
    q_head_sum = sum((q[i] for i in head_ids), Fraction(0, 1))
    p_tail = Fraction(1, 1) - p_head_sum
    q_tail = Fraction(1, 1) - q_head_sum
    rho = q_tail / p_tail
    residuals_head = tuple(q[i] - rho * p[i] for i in head_ids)
    head_residual_sum = sum(residuals_head, Fraction(0, 1))
    q_hat = tuple(q[i] if i in head_ids else rho * p[i] for i in range(4))

    # Exact logit gradient of sum_{v in H} (q_v - rho p_v) log p_v
    grad_topk_corr = expected_vec(residuals_head, [scores[i] for i in head_ids])
    expected_qhat_minus_p = vec_sub(q_hat, p)

    # Expected centered score under q_hat is identically zero; under true q leaves exact tail-shape drift
    drift_under_qhat = vec_sub(expected_vec(q_hat, scores), grad_topk_corr)
    drift_under_true_q = vec_sub(expected_vec(q, scores), grad_topk_corr)
    tail_shape_formula = expected_vec(
        [q[i] - rho * p[i] for i in tail_ids], [scores[i] for i in tail_ids]
    )

    # Singularity Case C: eps = 1e-6 floor blowup (1 - P_H = 1e-7, 1 - Q_H = 1/10)
    eps = Fraction(1, 1_000_000)
    p_peaked = (
        Fraction(1, 2),
        Fraction(1, 2) - Fraction(1, 10_000_000),
        Fraction(1, 20_000_000),
        Fraction(1, 20_000_000),
    )
    q_heavy_tail = (Fraction(9, 20), Fraction(9, 20), Fraction(1, 20), Fraction(1, 20))
    p_tail_peaked = Fraction(1, 1) - (p_peaked[0] + p_peaked[1])
    q_tail_heavy = Fraction(1, 1) - (q_heavy_tail[0] + q_heavy_tail[1])
    rho_exact_peaked = q_tail_heavy / p_tail_peaked
    rho_eps_floored = q_tail_heavy / max(p_tail_peaked, eps)
    q_hat_eps_mass = (q_heavy_tail[0] + q_heavy_tail[1]) + rho_eps_floored * p_tail_peaked
    head_res_eps = tuple(q_heavy_tail[i] - rho_eps_floored * p_peaked[i] for i in head_ids)

    # Exact tail-scale dichotomy across rational grid
    rho_grid = (
        Fraction(1, 10),
        Fraction(1, 5),
        Fraction(1, 2),
        Fraction(1, 1),
        Fraction(2, 1),
        Fraction(5, 1),
        Fraction(100_000, 1),
    )
    dichotomy_rows = []
    for r_val in rho_grid:
        a_sc = tail_scale_alpha(r_val, "none")
        a_tis = tail_scale_alpha(r_val, "tis")
        a_mis = tail_scale_alpha(r_val, "mis")
        dichotomy_rows.append(
            {
                "rho": frac_str(r_val),
                "alpha_vanilla_sc": frac_str(a_sc),
                "alpha_tis_sc": frac_str(a_tis),
                "alpha_mis_sc": frac_str(a_mis),
            }
        )

    return {
        "topk_exact_identities": {
            "trainer_p": vec_frac_str(p),
            "sampler_q": vec_frac_str(q),
            "head_ids": list(head_ids),
            "p_head_sum": frac_str(p_head_sum),
            "q_head_sum": frac_str(q_head_sum),
            "rho": frac_str(rho),
            "head_residuals": vec_frac_str(residuals_head),
            "head_residual_sum": frac_str(head_residual_sum),
            "head_residual_sum_equals_one_minus_rho": head_residual_sum == Fraction(1, 1) - rho,
            "q_hat_reconstructed": vec_frac_str(q_hat),
            "q_hat_mass": frac_str(sum(q_hat, Fraction(0, 1))),
            "grad_topk_correction": vec_frac_str(grad_topk_corr),
            "grad_equals_q_hat_minus_p": grad_topk_corr == expected_qhat_minus_p,
            "full_vocab_logit_grad_sum": frac_str(sum(grad_topk_corr, Fraction(0, 1))),
            "drift_under_q_hat": vec_frac_str(drift_under_qhat),
            "drift_under_true_q_tail_shape_bias": vec_frac_str(drift_under_true_q),
            "tail_shape_matches_closed_form": drift_under_true_q == tail_shape_formula,
            "tail_shape_bias_l1": frac_str(vec_l1(drift_under_true_q)),
        },
        "singularity_and_eps_blowup_sc_sing_01": {
            "unprotected_zero_over_zero_trigger": {"P_H": "1/1", "Q_H": "1/1", "result": "0/0_NaN"},
            "unprotected_pos_over_zero_trigger": {"P_H": "1/1", "Q_H": "9/10", "result": "POS_INF"},
            "eps_floor": frac_str(eps),
            "peaked_p_tail": frac_str(p_tail_peaked),
            "heavy_q_tail": frac_str(q_tail_heavy),
            "rho_exact_unfloored": frac_str(rho_exact_peaked),
            "rho_eps_floored": frac_str(rho_eps_floored),
            "head_residuals_eps_floored": vec_frac_str(head_res_eps),
            "head_residual_l1_eps_floored": frac_str(vec_l1(head_res_eps)),
            "reconstructed_q_hat_total_mass": frac_str(q_hat_eps_mass),
            "simplex_mass_deficit": frac_str(Fraction(1, 1) - q_hat_eps_mass),
        },
        "tail_scale_dichotomy": dichotomy_rows,
    }


def analyze_pillar3_repo_code_oracles() -> dict[str, Any]:
    """Pillar 3: exact pure-Q mathematical witnesses for SC-CODE-01..05 in losses.py / test_loss.py."""
    # SC-CODE-01: Double-centering (losses.py:139 + 149 both run when batch has both keys)
    p3 = (Fraction(1, 2), Fraction(1, 4), Fraction(1, 4))
    q3 = (Fraction(1, 4), Fraction(1, 2), Fraction(1, 4))
    s3 = softmax_scores(p3)
    s3_bar = expected_vec(q3, s3)
    single_centered_drift = expected_vec(q3, [vec_sub(s, s3_bar) for s in s3])
    double_centered_drift = expected_vec(
        q3, [vec_sub(s, vec_scale(Fraction(2, 1), s3_bar)) for s in s3]
    )

    # SC-CODE-02: Sequence-level IS (exact README.md:132-133 GSPO & TOPR) + SC breaks zero drift!
    # Exact 2-token binary trajectory y = (y1, y2) with p = (3/4, 1/4), q = (1/2, 1/2)
    p2 = (Fraction(3, 4), Fraction(1, 4))
    q2 = (Fraction(1, 2), Fraction(1, 2))
    s2 = softmax_scores(p2)
    s2_bar = expected_vec(q2, s2)
    s2_tilde = tuple(vec_sub(s, s2_bar) for s in s2)
    r_tok = (p2[0] / q2[0], p2[1] / q2[1])  # (3/2, 1/2)

    gspo_low = Fraction(9997, 10_000)
    gspo_high = Fraction(10_004, 10_000)
    dual_clip = Fraction(3, 1)

    exp_topr_pos = [Fraction(0, 1), Fraction(0, 1)]
    exp_topr_neg = [Fraction(0, 1), Fraction(0, 1)]
    exp_gspo_pos = [Fraction(0, 1), Fraction(0, 1)]
    exp_gspo_neg = [Fraction(0, 1), Fraction(0, 1)]
    offdiag_zero_all = True
    for t1 in (0, 1):
        for t2 in (0, 1):
            prob_seq = q2[t1] * q2[t2]
            score_seq = vec_add(s2_tilde[t1], s2_tilde[t2])
            r_seq = r_tok[t1] * r_tok[t2]
            # TOPR (README.md:133): level=seq_sum, high=1.0, outside=clamp, sign=neg
            # sign=neg -> A >= 0 has w = 1 identically; A < 0 has w = min(r_seq, 1)
            w_topr_pos = Fraction(1, 1)
            w_topr_neg = min(r_seq, Fraction(1, 1))
            # GSPO (README.md:132): level=seq_mean, low=0.9997, high=1.0004, outside=drop, sign=ppo
            # On diagonal t1 == t2, geometric mean sqrt(r_t1 * r_t2) == r_t1 is exact in Q;
            # on off-diagonal t1 != t2, score_seq == (0, 0) identically so w_gspo multiplies 0.
            if t1 == t2:
                r_gm = r_tok[t1]
                w_gspo_pos = r_gm if r_gm <= gspo_high else Fraction(0, 1)
                w_gspo_neg = r_gm if (gspo_low <= r_gm <= dual_clip) else Fraction(0, 1)
            else:
                offdiag_zero_all = offdiag_zero_all and all(x == 0 for x in score_seq)
                w_gspo_pos = Fraction(0, 1)
                w_gspo_neg = Fraction(0, 1)
            for j in (0, 1):
                exp_topr_pos[j] += prob_seq * Fraction(1, 1) * w_topr_pos * score_seq[j]
                exp_topr_neg[j] += prob_seq * Fraction(-1, 1) * w_topr_neg * score_seq[j]
                exp_gspo_pos[j] += prob_seq * Fraction(1, 1) * w_gspo_pos * score_seq[j]
                exp_gspo_neg[j] += prob_seq * Fraction(-1, 1) * w_gspo_neg * score_seq[j]

    exp_topr_pos_t = tuple(exp_topr_pos)
    exp_topr_neg_t = tuple(exp_topr_neg)
    exp_gspo_pos_t = tuple(exp_gspo_pos)
    exp_gspo_neg_t = tuple(exp_gspo_neg)

    # SC-CODE-03: Dual zero-tail defect in losses.py:65-75, 146-152
    # (a) Unclamped negative q_tail in kl_head: overshoot delta = 1e-6 -> q_tail = -1e-6
    q_overshoot_tail = Fraction(-1, 1_000_000)
    # Rational conservative upper bound on ln(1e-9) < -20 (since e^20 < 4.86e8 < 1e9)
    ln_1e9_upper_bound = Fraction(-20, 1)
    spurious_kl_lower_bound = q_overshoot_tail * ln_1e9_upper_bound  # > +1/50000

    # (b) Missing-support IS drift under Q_H = 1, P_H < 1, c.high = inf (losses.py:150 alpha = 1 bug)
    p4 = (Fraction(1, 4), Fraction(1, 4), Fraction(1, 4), Fraction(1, 4))
    s4 = softmax_scores(p4)
    # True unclipped IS expectation under q4_trunc: sum_{v in H} q_v (p_v / q_v) s_v = sum_{v in H} p_v s_v
    true_is_drift_trunc = expected_vec((p4[0], p4[1]), (s4[0], s4[1]))
    # Buggy losses.py:150 with alpha = 1 -> residual = p_head - 1 * p_head = (0, 0) -> 0 correction!
    buggy_alpha = Fraction(1, 1)
    buggy_res = (p4[0] - buggy_alpha * p4[0], p4[1] - buggy_alpha * p4[1])
    buggy_corr_grad = expected_vec(buggy_res, (s4[0], s4[1]))
    buggy_remaining_drift = vec_sub(true_is_drift_trunc, buggy_corr_grad)
    # Fixed alpha = 0 when q_tail == 0 -> residual = p_head -> exact zero remaining drift!
    fixed_alpha = tail_scale_alpha(Fraction(0, 1), "unclipped_is")
    fixed_res = (p4[0] - fixed_alpha * p4[0], p4[1] - fixed_alpha * p4[1])
    fixed_corr_grad = expected_vec(fixed_res, (s4[0], s4[1]))
    fixed_remaining_drift = vec_sub(true_is_drift_trunc, fixed_corr_grad)

    # SC-CODE-05: Tautology of tests/test_loss.py:28 (k = V - 1 = 2 on V = 3 -> |T| = 1 -> q_hat == q identically)
    q3_head = q3[0] + q3[1]
    p3_head = p3[0] + p3[1]
    rho_v_minus_1 = (Fraction(1, 1) - q3_head) / (Fraction(1, 1) - p3_head)
    q3_hat_tail = rho_v_minus_1 * p3[2]

    return {
        "SC-CODE-01_double_centering": {
            "single_centered_drift": vec_frac_str(single_centered_drift),
            "double_centered_drift": vec_frac_str(double_centered_drift),
            "expected_sign_flipped_drift": vec_frac_str(vec_scale(Fraction(-1, 1), s3_bar)),
            "drift_sign_flipped": double_centered_drift == vec_scale(Fraction(-1, 1), s3_bar),
        },
        "SC-CODE-02_seq_is_breaks_zero_drift": {
            "offdiag_score_seq_zero": offdiag_zero_all,
            "topr_readme_l133_adv_pos1_expected_grad": vec_frac_str(exp_topr_pos_t),
            "topr_readme_l133_adv_neg1_expected_grad": vec_frac_str(exp_topr_neg_t),
            "topr_readme_l133_adv_neg1_drift_l1": frac_str(vec_l1(exp_topr_neg_t)),
            "gspo_readme_l132_adv_pos1_expected_grad": vec_frac_str(exp_gspo_pos_t),
            "gspo_readme_l132_adv_pos1_drift_l1": frac_str(vec_l1(exp_gspo_pos_t)),
            "gspo_readme_l132_adv_neg1_expected_grad": vec_frac_str(exp_gspo_neg_t),
            "gspo_readme_l132_adv_neg1_drift_l1": frac_str(vec_l1(exp_gspo_neg_t)),
        },
        "SC-CODE-03_zero_tail_and_missing_support": {
            "unclamped_negative_q_tail": frac_str(q_overshoot_tail),
            "spurious_positive_kl_lower_bound": frac_str(spurious_kl_lower_bound),
            "missing_support_true_is_drift": vec_frac_str(true_is_drift_trunc),
            "buggy_losses_py_alpha": frac_str(buggy_alpha),
            "buggy_remaining_drift": vec_frac_str(buggy_remaining_drift),
            "hardened_alpha": frac_str(fixed_alpha),
            "hardened_remaining_drift": vec_frac_str(fixed_remaining_drift),
        },
        "SC-CODE-05_tautological_k_eq_v_minus_1": {
            "V": 3,
            "k": 2,
            "tail_cardinality": 1,
            "rho_times_p_tail": frac_str(q3_hat_tail),
            "true_q_tail": frac_str(q3[2]),
            "q_hat_identically_equals_q": q3_hat_tail == q3[2],
        },
    }


def validate_batch_contract(batch_spec: Any) -> dict[str, Any]:
    """Fail-closed contract validator blocking SC-CODE-01 (double-centering) & SC-CODE-02 (seq/tv+SC)."""
    _require(isinstance(batch_spec, dict), "batch-spec-dict")
    unknown = sorted(set(batch_spec.keys()) - ALLOWED_BATCH_SPEC_KEYS)
    _require(len(unknown) == 0, f"batch-spec-unknown-keys:{','.join(unknown)}")
    missing = sorted(ALLOWED_BATCH_SPEC_KEYS - set(batch_spec.keys()))
    _require(len(missing) == 0, f"batch-spec-missing-keys:{','.join(missing)}")

    batch_mode = _require_exact_choice(batch_spec["batch_mode"], ALLOWED_BATCH_MODES, "batch_mode")
    has_full = batch_spec["has_full_vocab"]
    has_topk = batch_spec["has_topk_head"]
    score_center = batch_spec["score_center"]
    _require(isinstance(has_full, bool), "batch-bool:has_full_vocab")
    _require(isinstance(has_topk, bool), "batch-bool:has_topk_head")
    _require(isinstance(score_center, bool), "batch-bool:score_center")
    is_level = _require_exact_choice(batch_spec["is_level"], ALLOWED_IS_LEVELS, "is_level")
    is_stat = _require_exact_choice(batch_spec["is_stat"], ALLOWED_IS_STATS, "is_stat")
    _require(is_stat == "ratio" or is_level != "none", "is-none-requires-ratio")
    _require(is_stat == "ratio" or is_level != "seq_sum", "seq-sum-requires-ratio")

    if score_center:
        _require(has_full or has_topk, "sc-missing-sampler-logprobs")
        _require(not (has_full and has_topk), "sc-double-centering-forbidden")
        _require(is_level in ("none", "token"), "sc-seq-level-is-forbidden")
        _require(is_stat == "ratio", "sc-tv-stat-forbidden")
    else:
        _require(not (has_full and has_topk), "batch-ambiguous-vocab-sources")

    _require(
        (batch_mode == "none" and not has_full and not has_topk)
        or (batch_mode == "full_vocab" and has_full)
        or (batch_mode == "topk_head" and has_topk),
        "batch-mode-mismatch",
    )

    return {
        "contract_status": "VALID",
        "batch_mode": batch_mode,
        "score_center": score_center,
        "is_level": is_level,
        "is_stat": is_stat,
    }


def evaluate_hardened_topk_score_centering(
    *,
    trainer_probs: Sequence[Fraction],
    sampler_head_probs: Sequence[Fraction],
    topk_ids: Sequence[int],
    sampled_token: int,
    advantage: Fraction,
    correction_mode: str = "none",
    tail_floor: Fraction = Fraction(1, 1000),
    rho_max: Fraction = Fraction(10, 1),
) -> dict[str, Any]:
    """Hardened pure-Q fail-closed Top-K Score Centering operator.

    Eliminates:
      - 0/0 and +inf tail_mass_ratio singularities (SC-SING-01)
      - 10^5x eps-floor residual blowup (SC-CODE-04)
      - missing-support alpha = 1 hallucination when q_tail == 0 (SC-CODE-03)
    """
    p = _validate_simplex(trainer_probs, "trainer_probs", allow_zero=False)
    vocab = len(p)
    _require(
        isinstance(topk_ids, (list, tuple)) and 1 <= len(topk_ids) < vocab,
        "topk-ids-len",
    )
    _require(
        isinstance(sampler_head_probs, (list, tuple))
        and len(sampler_head_probs) == len(topk_ids),
        "sampler-head-len",
    )
    seen_ids: set[int] = set()
    clean_ids: list[int] = []
    for idx_pos, tok in enumerate(topk_ids):
        t_int = _require_exact_int(tok, f"topk_ids[{idx_pos}]")
        _require(0 <= t_int < vocab, f"topk-id-range:{t_int}")
        _require(t_int not in seen_ids, f"topk-id-duplicate:{t_int}")
        seen_ids.add(t_int)
        clean_ids.append(t_int)

    samp_tok = _require_exact_int(sampled_token, "sampled_token")
    _require(0 <= samp_tok < vocab, "sampled-token-range")
    adv = _require_exact_fraction(advantage, "advantage")
    mode = _require_exact_choice(correction_mode, ALLOWED_CORRECTION_MODES, "correction_mode")
    t_floor = _require_exact_fraction(tail_floor, "tail_floor")
    r_max = _require_exact_fraction(rho_max, "rho_max")
    _require(Fraction(0, 1) < t_floor < Fraction(1, 1), "tail-floor-range")
    _require(r_max >= Fraction(1, 1), "rho-max-ge-one")

    q_head: list[Fraction] = []
    q_head_sum = Fraction(0, 1)
    for idx_pos, qv_raw in enumerate(sampler_head_probs):
        qv = _require_exact_fraction(qv_raw, f"sampler_head_probs[{idx_pos}]")
        _require(Fraction(0, 1) <= qv <= Fraction(1, 1), f"sampler-head-range:{idx_pos}")
        q_head.append(qv)
        q_head_sum += qv
    _require(q_head_sum <= Fraction(1, 1), "sampler-head-sum-exceeds-one")
    _require(q_head_sum > Fraction(0, 1), "sampler-head-zero-mass")

    p_head = [p[i] for i in clean_ids]
    p_head_sum = sum(p_head, Fraction(0, 1))
    p_tail = Fraction(1, 1) - p_head_sum
    q_tail = Fraction(1, 1) - q_head_sum

    _require(
        (vocab - len(clean_ids)) * min(q_head) >= q_tail,
        "topk-pigeonhole-dominance",
    )

    if samp_tok in seen_ids:
        samp_head_pos = clean_ids.index(samp_tok)
        _require(q_head[samp_head_pos] > 0, "sampled-token-zero-sampler-prob")
    else:
        _require(q_tail > 0, "sampled-tail-token-zero-q-tail")

    if q_tail == 0:
        rho_raw_str = "0/1"
        rho_eff = Fraction(0, 1)
        alpha = Fraction(0, 1)
        gate_status = "ZERO_TAIL_SUPPORT_GUARDED"
    elif p_tail < t_floor or (q_tail / p_tail) > r_max:
        rho_raw_str = frac_str(q_tail / p_tail)
        damped = (q_tail + t_floor) / (p_tail + t_floor)
        rho_eff = min(r_max, damped)
        alpha = tail_scale_alpha(rho_eff, mode)
        gate_status = "DAMPED_FALLBACK_REQUIRED"
    else:
        rho_raw = q_tail / p_tail
        rho_raw_str = frac_str(rho_raw)
        rho_eff = rho_raw
        alpha = tail_scale_alpha(rho_eff, mode)
        gate_status = "EXACT_CENTERED"

    # Compute effective head mass q_v * w(p_v / q_v) safely when q_v == 0
    eff_head_mass: list[Fraction] = []
    for pv, qv in zip(p_head, q_head):
        if qv == 0:
            eff_head_mass.append(Fraction(0, 1))
        elif mode == "none":
            eff_head_mass.append(qv)
        elif mode == "tis":
            ratio = pv / qv
            eff_head_mass.append(qv * min(ratio, Fraction(2, 1)))
        elif mode == "mis":
            ratio = pv / qv
            eff_head_mass.append(pv if (Fraction(1, 2) <= ratio <= Fraction(5, 1)) else Fraction(0, 1))
        else:
            eff_head_mass.append(pv)

    residuals = tuple(m - alpha * pv for m, pv in zip(eff_head_mass, p_head))
    scores = softmax_scores(p)
    corr_logit_grad = expected_vec(residuals, [scores[i] for i in clean_ids])
    res_l1 = vec_l1(residuals)
    max_allowed_l1 = sum(eff_head_mass, Fraction(0, 1)) + alpha * p_head_sum
    logit_grad_sum = sum(corr_logit_grad, Fraction(0, 1))

    return {
        "gate_status": gate_status,
        "correction_mode": mode,
        "sampled_token": samp_tok,
        "advantage": frac_str(adv),
        "p_tail": frac_str(p_tail),
        "q_tail": frac_str(q_tail),
        "rho_raw": rho_raw_str,
        "rho_effective": frac_str(rho_eff),
        "alpha": frac_str(alpha),
        "residuals": vec_frac_str(residuals),
        "residual_l1_norm": frac_str(res_l1),
        "residual_l1_upper_bound": frac_str(max_allowed_l1),
        "residual_l1_within_bound": res_l1 <= max_allowed_l1,
        "correction_logit_grad": vec_frac_str(corr_logit_grad),
        "correction_logit_grad_sum": frac_str(logit_grad_sum),
    }


def analyze_pillar4_hardened_gate_and_bridges() -> dict[str, Any]:
    """Pillar 4: hardened gate receipts + AUDIT-073R (songe SNG-01) & AUDIT-074R (Inkling LOOM-IR-03) bridges."""
    # Gate demonstration 1: Exact centered healthy batch
    gate_healthy = evaluate_hardened_topk_score_centering(
        trainer_probs=(Fraction(1, 2), Fraction(1, 4), Fraction(1, 8), Fraction(1, 8)),
        sampler_head_probs=(Fraction(1, 4), Fraction(1, 4)),
        topk_ids=(0, 1),
        sampled_token=0,
        advantage=Fraction(1, 1),
        correction_mode="none",
    )
    # Gate demonstration 2: Peaked trainer + heavy TIM tail -> DAMPED_FALLBACK_REQUIRED (10^5x blocked!)
    gate_peaked = evaluate_hardened_topk_score_centering(
        trainer_probs=(
            Fraction(1, 2),
            Fraction(1, 2) - Fraction(1, 10_000_000),
            Fraction(1, 20_000_000),
            Fraction(1, 20_000_000),
        ),
        sampler_head_probs=(Fraction(9, 20), Fraction(9, 20)),
        topk_ids=(0, 1),
        sampled_token=0,
        advantage=Fraction(1, 1),
        correction_mode="none",
    )
    # Gate demonstration 3: Zero tail + unclipped IS -> ZERO_TAIL_SUPPORT_GUARDED (alpha=0, closes SC-CODE-03)
    gate_zero_tail = evaluate_hardened_topk_score_centering(
        trainer_probs=(Fraction(1, 4), Fraction(1, 4), Fraction(1, 4), Fraction(1, 4)),
        sampler_head_probs=(Fraction(1, 2), Fraction(1, 2)),
        topk_ids=(0, 1),
        sampled_token=0,
        advantage=Fraction(1, 1),
        correction_mode="unclipped_is",
    )

    # Bridge 1: AUDIT-073R (songe SNG-01) signed forward-KL anti-distillation when E_q[A] < 0
    # In losses.py:21 zero_minus mode: solved=0, unsolved=-1; pass rate 1/4 -> E_q[A] = -3/4
    p3 = (Fraction(1, 2), Fraction(1, 4), Fraction(1, 4))
    q3 = (Fraction(1, 4), Fraction(1, 2), Fraction(1, 4))
    s3 = softmax_scores(p3)
    e_q_s3 = expected_vec(q3, s3)
    mean_adv_zero_minus = Fraction(-3, 4)
    anti_distill_drift = vec_scale(mean_adv_zero_minus, e_q_s3)
    fwd_kl_grad = vec_sub(p3, q3)

    # Bridge 2: AUDIT-074R (Inkling LOOM-IR-03) silent top_k=64/200058 truncation (TV = 35/64)
    loom_kept_fraction = Fraction(64, 200_058)
    q_true_4 = (Fraction(15, 64), Fraction(14, 64), Fraction(20, 64), Fraction(15, 64))
    hidden_tail_mass = q_true_4[2] + q_true_4[3]
    q_loom_4 = (Fraction(15, 29), Fraction(14, 29), Fraction(0, 1), Fraction(0, 1))
    p_unif_4 = (Fraction(1, 4), Fraction(1, 4), Fraction(1, 4), Fraction(1, 4))
    s4 = softmax_scores(p_unif_4)
    true_drift_loom = expected_vec(q_true_4, s4)
    trunc_drift_loom = expected_vec(q_loom_4, s4)
    trunc_centering_error = vec_sub(true_drift_loom, trunc_drift_loom)

    return {
        "hardened_gate_receipts": {
            "healthy_exact_centered": gate_healthy,
            "peaked_trainer_damped_fallback": gate_peaked,
            "zero_tail_unclipped_is_guarded": gate_zero_tail,
        },
        "bridge_audit_073r_songe_sng01": {
            "reward_mode": "zero_minus",
            "pass_rate": "1/4",
            "mean_advantage_q": frac_str(mean_adv_zero_minus),
            "off_policy_drift": vec_frac_str(anti_distill_drift),
            "grad_forward_kl_q_p": vec_frac_str(fwd_kl_grad),
            "anti_distillation_factor_on_plus_grad_kl": "3/4",
            "matches_plus_three_quarters_grad_kl": anti_distill_drift == vec_scale(Fraction(3, 4), fwd_kl_grad),
        },
        "bridge_audit_074r_inkling_loom_ir03": {
            "loom_vocab": 200058,
            "loom_silent_top_k": 64,
            "loom_kept_vocab_fraction": frac_str(loom_kept_fraction),
            "hidden_pre_truncation_tail_mass_tv": frac_str(hidden_tail_mass),
            "true_full_vocab_drift": vec_frac_str(true_drift_loom),
            "loom_truncated_centered_target": vec_frac_str(trunc_drift_loom),
            "centering_mismatch_vector": vec_frac_str(trunc_centering_error),
            "centering_mismatch_l1": frac_str(vec_l1(trunc_centering_error)),
        },
    }


def _sha256_file(path: Path) -> tuple[int, str]:
    data = path.read_bytes()
    return len(data), hashlib.sha256(data).hexdigest()


def audit_live_repos(repos_dir: Path) -> dict[str, Any]:
    """Read-only SHA-256 and verbatim file:line verification of pinned Round 9 Arm R9-3 sources."""
    _require(repos_dir.is_dir(), f"repos-dir-missing:{repos_dir.name}")
    digest_results: dict[str, dict[str, Any]] = {}
    for rel_path, expected in PINNED_SOURCE_DIGESTS.items():
        full_path = repos_dir / rel_path
        _require(full_path.is_file(), f"source-file-missing:{rel_path}")
        actual_bytes, actual_sha = _sha256_file(full_path)
        _require(actual_bytes == expected["bytes"], f"source-bytes-mismatch:{rel_path}")
        _require(actual_sha == expected["sha256"], f"source-sha256-mismatch:{rel_path}")
        digest_results[rel_path] = {"bytes": actual_bytes, "sha256": actual_sha, "verified": True}

    anchor_results: list[dict[str, Any]] = []
    for anchor_id, rel_path, line_no, needle in VERBATIM_ANCHORS:
        lines = (repos_dir / rel_path).read_text(encoding="utf-8").splitlines()
        _require(1 <= line_no <= len(lines), f"anchor-line-range:{anchor_id}")
        line_text = lines[line_no - 1]
        _require(needle in line_text, f"anchor-text-mismatch:{anchor_id}")
        anchor_results.append(
            {
                "anchor_id": anchor_id,
                "file": rel_path,
                "line": line_no,
                "verified": True,
            }
        )

    git_dir = (repos_dir / "score-centering" / "repo" / ".git").resolve()
    git_head_path = git_dir / "HEAD"
    _require(git_head_path.is_file(), "repo-git-head-missing")
    head_raw = git_head_path.read_text(encoding="utf-8").strip()
    if head_raw.startswith("ref: "):
        ref_name = head_raw[5:]
        _require(
            ref_name.startswith("refs/")
            and "\\" not in ref_name
            and ".." not in Path(ref_name).parts,
            "repo-git-ref-invalid",
        )
        ref_path = (git_dir / ref_name).resolve()
        _require(ref_path.is_relative_to(git_dir), "repo-git-ref-escape")
        _require(ref_path.is_file(), "repo-git-ref-missing")
        commit_sha = ref_path.read_text(encoding="utf-8").strip()
    else:
        commit_sha = head_raw
    _require(commit_sha == PINNED_REPO_COMMIT, "repo-commit-mismatch")

    return {
        "mode": "live_read_only",
        "pinned_repo_commit": commit_sha,
        "verified_files": len(digest_results),
        "verified_anchors": len(anchor_results),
        "file_digests": digest_results,
        "anchors": anchor_results,
    }


def build_certificate(repos_dir: Path | None = None) -> dict[str, Any]:
    """Build deterministic zero-float JSON certificate with canonical SHA-256."""
    body: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "audit_id": AUDIT_ID,
        "pinned_repo_commit": PINNED_REPO_COMMIT,
        "pillar1_drift_kl_bias": analyze_pillar1_drift_kl_bias(),
        "pillar2_topk_singularity_tail_scales": analyze_pillar2_topk_singularity_and_tail_scales(),
        "pillar3_repo_code_oracles": analyze_pillar3_repo_code_oracles(),
        "pillar4_hardened_gate_and_bridges": analyze_pillar4_hardened_gate_and_bridges(),
        "live_source_verification": (
            audit_live_repos(repos_dir)
            if repos_dir is not None
            else {"mode": "standalone_pure_q", "verified_files": 0, "verified_anchors": 0}
        ),
    }
    canonical = json.dumps(body, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    cert_sha = hashlib.sha256(canonical.encode("ascii")).hexdigest()
    body["certificate_sha256"] = cert_sha
    return body


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Score Centering pure-Q tomography oracle.")
    parser.add_argument("--repos-dir", type=Path, default=None, help="Staged read-only repos root.")
    parser.add_argument("--json", action="store_true", help="Emit canonical JSON to stdout.")
    parser.add_argument("--write-cert", type=Path, default=None, help="Write JSON certificate path.")
    args = parser.parse_args(argv)

    cert = build_certificate(repos_dir=args.repos_dir)
    rendered = json.dumps(cert, indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    if args.write_cert is not None:
        args.write_cert.write_text(rendered, encoding="utf-8")
    if args.json:
        sys.stdout.write(rendered)
    else:
        mode = cert["live_source_verification"]["mode"]
        sys.stdout.write(
            f"{AUDIT_ID} | mode={mode} | files={cert['live_source_verification']['verified_files']} "
            f"| anchors={cert['live_source_verification']['verified_anchors']} "
            f"| sha256={cert['certificate_sha256']}\n"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
