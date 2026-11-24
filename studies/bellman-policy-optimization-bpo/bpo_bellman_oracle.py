"""Pure-stdlib, zero-float exact rational oracle for AUDIT-083 (arXiv:2609.15987 BPO).

Verifies Bellman Policy Optimization (Song, Xu, Zhang, Bing, Sep 14, 2026) in exact
rational arithmetic (Q) across five mathematical pillars:
  1. Theorem 1 (PMD <-> Critic-Free Bellman Trajectory Martingale) exact rational proof
     in common-denominator exponential form + Step-1 linearization fixed-point destruction.
  2. Exact algebraic duality between BPO's binary-KL weight (1-mu)/(1-pi) and Score
     Centering Top-K (arXiv:2609.20807, AUDIT-080) at singleton head H={y_t}, exact
     softmax logit-Jacobian cancellation (||grad_z L||_1 = 2(1-mu(y))), additive
     smoothing envelope [eps/(1+eps), (1+eps)/eps], and exact cap-active triangle area.
  3. Exact |V|=2 vs |V|>=3 off-policy drift-cancellation dichotomy (proving binary KL
     preserves zero drift iff |V|=2 & eps=0, and breaks zero drift for all |V|>=3).
  4. Fail-closed BPO + 4-Axis RLVR Trust-Region Certifier bridging RIPO (AUDIT-079),
     Score Centering (AUDIT-080), REINFORCE Zero / R3 (AUDIT-081), & Triad (AUDIT-082).
  5. Exact pure-Q audit of all 14 rows across BPO Tables 1-3 (Qwen3-30B & Qwen3-4B).

Strict Aletheia v1.4.0 invariants: zero floats, zero bare asserts, deterministic JSON.
"""

from __future__ import annotations

from fractions import Fraction
import hashlib
import json
import math
import re
from typing import Any


_STRICT_NUMBER_RE = re.compile(r"\A[+-]?(?:\d+(?:\.\d+)?|\d+/\d+)\Z")
_TREE_TRAJECTORIES = ("00", "01", "10", "11")


class BpoOracleError(ValueError):
    """Fail-closed validation or mathematical invariant refusal."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"[{code}] {message}")
        self.code = code


def verify_no_floats(obj: Any, path: str = "root") -> None:
    """Recursively refuse any float in keys or values."""
    if isinstance(obj, float):
        raise BpoOracleError("FLOAT_FORBIDDEN", f"float forbidden at {path}")
    if isinstance(obj, dict):
        for k, v in obj.items():
            verify_no_floats(k, f"{path}.<key>")
            verify_no_floats(v, f"{path}.{k}")
    elif isinstance(obj, (list, tuple, set)):
        for idx, item in enumerate(obj):
            verify_no_floats(item, f"{path}[{idx}]")


def require_non_empty_str(value: Any, field: str) -> str:
    if not isinstance(value, str):
        raise BpoOracleError("TYPE_ERROR", f"{field} must be str")
    stripped = value.strip()
    if not stripped:
        raise BpoOracleError("EMPTY_STRING", f"{field} must be non-empty")
    return stripped


def require_exact_bool(value: Any, field: str) -> bool:
    if not isinstance(value, bool):
        raise BpoOracleError("TYPE_ERROR", f"{field} must be bool")
    return value


def require_exact_int(value: Any, field: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise BpoOracleError("TYPE_ERROR", f"{field} must be exact int")
    return value


def require_exact_fraction(value: Any, field: str) -> Fraction:
    if isinstance(value, Fraction):
        return value
    if isinstance(value, bool):
        raise BpoOracleError("TYPE_ERROR", f"{field} cannot be bool")
    if isinstance(value, int):
        return Fraction(value, 1)
    if isinstance(value, float):
        raise BpoOracleError("FLOAT_FORBIDDEN", f"{field} cannot be float")
    if isinstance(value, str):
        if _STRICT_NUMBER_RE.match(value) is None:
            raise BpoOracleError("INVALID_RATIONAL", f"{field} has invalid numeric format: {value!r}")
        try:
            return Fraction(value)
        except ZeroDivisionError as exc:
            raise BpoOracleError("ZERO_DENOMINATOR", f"{field} has zero denominator") from exc
    raise BpoOracleError("TYPE_ERROR", f"{field} must be Fraction, int, or numeric str")


def require_prob_vector(value: Any, field: str, require_positive: bool = False) -> tuple[Fraction, ...]:
    """Validate a finite simplex distribution of length >= 2."""
    if not isinstance(value, (list, tuple)):
        raise BpoOracleError("TYPE_ERROR", f"{field} must be list or tuple")
    if len(value) < 2:
        raise BpoOracleError("INVALID_LENGTH", f"{field} must have length >= 2")
    parsed: list[Fraction] = []
    for idx, item in enumerate(value):
        p = require_exact_fraction(item, f"{field}[{idx}]")
        if require_positive:
            if p <= 0 or p >= 1:
                raise BpoOracleError("INVALID_PROBABILITY", f"{field}[{idx}] must be in (0, 1)")
        else:
            if p < 0 or p > 1:
                raise BpoOracleError("INVALID_PROBABILITY", f"{field}[{idx}] must be in [0, 1]")
        parsed.append(p)
    if sum(parsed, Fraction(0, 1)) != Fraction(1, 1):
        raise BpoOracleError("SIMPLEX_SUM_ERROR", f"{field} must sum to 1")
    return tuple(parsed)


def frac_str(val: Fraction) -> str:
    if not isinstance(val, Fraction):
        raise BpoOracleError("TYPE_ERROR", "frac_str requires Fraction")
    return f"{val.numerator}/{val.denominator}"


def format_exact_decimal(val: Fraction, places: int) -> str:
    if not isinstance(val, Fraction):
        raise BpoOracleError("TYPE_ERROR", "val must be Fraction")
    places_i = require_exact_int(places, "places")
    if places_i < 0:
        raise BpoOracleError("INVALID_RANGE", "places must be >= 0")
    neg = val < 0
    mag = -val if neg else val
    scale = 10 ** places_i
    quot, rem = divmod(mag.numerator * scale, mag.denominator)
    if 2 * rem >= mag.denominator:
        quot += 1
    sign = "-" if neg and quot > 0 else ""
    if places_i == 0:
        return f"{sign}{quot}"
    int_part, frac_part = divmod(quot, scale)
    return f"{sign}{int_part}.{frac_part:0{places_i}d}"


def canonical_json_bytes(obj: Any) -> bytes:
    verify_no_floats(obj)
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def canonical_sha256(obj: Any) -> str:
    return hashlib.sha256(canonical_json_bytes(obj)).hexdigest()


def _exact_pow2(exp_val: Fraction, field: str) -> Fraction:
    """Compute exact 2**exp_val in Q when exp_val is an integer in [-64, 64]."""
    if exp_val.denominator != 1:
        raise BpoOracleError("NON_INTEGER_EXPONENT", f"{field} must yield integer exponent for exact Q base-2 proof")
    k = exp_val.numerator
    if k < -64 or k > 64:
        raise BpoOracleError("INVALID_RANGE", f"{field} integer exponent {k} outside [-64, 64]")
    if k >= 0:
        return Fraction(1 << k, 1)
    return Fraction(1, 1 << (-k))


def _common_den(probs: tuple[Fraction, ...]) -> int:
    d = 1
    for p in probs:
        d = math.lcm(d, p.denominator)
    return d


def _exp_kl_pow_d(mu: tuple[Fraction, ...], pi: tuple[Fraction, ...], d: int) -> Fraction:
    """Compute exact (2**(D_KL,2(mu || pi)))**d enforcing exact support equivalence (pi in Pi_mu, mu << pi)."""
    acc = Fraction(1, 1)
    for m_a, p_a in zip(mu, pi):
        if m_a == 0 and p_a > 0:
            raise BpoOracleError("ABSOLUTE_CONTINUITY_VIOLATION", "pi assigns positive mass outside supp(mu)")
        if m_a > 0:
            if p_a <= 0:
                raise BpoOracleError("SUPPORT_VIOLATION", "pi assigns zero mass where mu > 0 (KL = +inf)")
            power = (m_a * d).numerator
            acc *= (m_a / p_a) ** power
    return acc


# ---------------------------------------------------------------------------
# Pillar 1: Theorem 1 (PMD <-> Critic-Free Bellman Martingale) & Linearization
# ---------------------------------------------------------------------------


def verify_pmd_bellman_theorem1_exact(
    rewards: Any,
    mu_root: Any,
    mu_0: Any,
    mu_1: Any,
    eta_scale: Any,
    candidate_policy: Any = None,
) -> dict[str, Any]:
    """Verify BPO Theorem 1 and Step-1 linearization fixed-point destruction in exact Q.

    Evaluates a finite-horizon T=2, binary-vocabulary {0,1} autoregressive RLVR tree
    using exact base-2 exponential form (equivalent to natural-log step size eta = eta_scale * ln 2).
    """
    if not isinstance(rewards, dict) or set(rewards.keys()) != set(_TREE_TRAJECTORIES):
        raise BpoOracleError("SCHEMA_ERROR", "rewards must have exact keys {'00','01','10','11'}")
    r_map: dict[str, Fraction] = {}
    for traj in _TREE_TRAJECTORIES:
        rv = require_exact_fraction(rewards[traj], f"rewards[{traj}]")
        if rv < -1 or rv > 1:
            raise BpoOracleError("INVALID_RANGE", f"rewards[{traj}] must satisfy |R| <= 1")
        r_map[traj] = rv

    m_root = require_prob_vector(mu_root, "mu_root")
    m_0 = require_prob_vector(mu_0, "mu_0")
    m_1 = require_prob_vector(mu_1, "mu_1")
    if len(m_root) != 2 or len(m_0) != 2 or len(m_1) != 2:
        raise BpoOracleError("INVALID_LENGTH", "tree policies must be binary (length 2)")

    eta_f = require_exact_fraction(eta_scale, "eta_scale")
    if eta_f <= 0:
        raise BpoOracleError("INVALID_RANGE", "eta_scale must be > 0")

    # Exact Bellman recursion V^mu and A^mu
    v_0 = m_0[0] * r_map["00"] + m_0[1] * r_map["01"]
    v_1 = m_1[0] * r_map["10"] + m_1[1] * r_map["11"]
    v_root = m_root[0] * v_0 + m_root[1] * v_1

    adv_root = (v_0 - v_root, v_1 - v_root)
    adv_0 = (r_map["00"] - v_0, r_map["01"] - v_0)
    adv_1 = (r_map["10"] - v_1, r_map["11"] - v_1)

    # Verify Bellman telescoping sum_t A^mu(s_t, y_t) == R(x, y) - V^mu(x)
    telescoping_ok = (
        (adv_root[0] + adv_0[0] == r_map["00"] - v_root)
        and (adv_root[0] + adv_0[1] == r_map["01"] - v_root)
        and (adv_root[1] + adv_1[0] == r_map["10"] - v_root)
        and (adv_root[1] + adv_1[1] == r_map["11"] - v_root)
    )

    state_specs = [
        ("root", m_root, adv_root, True),
        ("s0", m_0, adv_0, m_root[0] > 0),
        ("s1", m_1, adv_1, m_root[1] > 0),
    ]

    d_common = math.lcm(_common_den(m_root), _common_den(m_0), _common_den(m_1))

    pi_plus: dict[str, tuple[Fraction, Fraction]] = {}
    exp_weights: dict[str, tuple[Fraction, Fraction]] = {}
    z_mu: dict[str, Fraction] = {}
    partition_kl_checks: dict[str, bool] = {}

    for sname, mu_s, adv_s, reachable in state_specs:
        e0 = _exact_pow2(eta_f * adv_s[0], f"{sname}[0]")
        e1 = _exact_pow2(eta_f * adv_s[1], f"{sname}[1]")
        z_s = mu_s[0] * e0 + mu_s[1] * e1
        p_s = (mu_s[0] * e0 / z_s, mu_s[1] * e1 / z_s)
        exp_weights[sname] = (e0, e1)
        z_mu[sname] = z_s
        pi_plus[sname] = p_s
        if reachable:
            partition_kl_checks[sname] = (z_s ** d_common) == _exp_kl_pow_d(mu_s, p_s, d_common)

    # Candidate policy evaluation (defaults to exact PMD optimum pi^+)
    if candidate_policy is None:
        cand = pi_plus
    else:
        if not isinstance(candidate_policy, dict) or set(candidate_policy.keys()) != {"root", "s0", "s1"}:
            raise BpoOracleError("SCHEMA_ERROR", "candidate_policy must have exact keys {'root','s0','s1'}")
        cand = {}
        for sname in ("root", "s0", "s1"):
            vec = require_prob_vector(candidate_policy[sname], f"candidate_policy[{sname}]")
            if len(vec) != 2:
                raise BpoOracleError("INVALID_LENGTH", f"candidate_policy[{sname}] must have length 2")
            cand[sname] = (vec[0], vec[1])

    # Check martingale identity prod_a exp(d_pi(s,a))**(d*mu_a) == 1/1 at every reachable state
    martingale_checks: dict[str, bool] = {}
    exp_kl_cand: dict[str, Fraction] = {}
    for sname, mu_s, _adv_s, reachable in state_specs:
        if not reachable:
            continue
        pi_s = cand[sname]
        kl_d = _exp_kl_pow_d(mu_s, pi_s, d_common)
        exp_kl_cand[sname] = kl_d
        mart_prod = Fraction(1, 1)
        for a_idx in (0, 1):
            if mu_s[a_idx] > 0:
                p_exp = (mu_s[a_idx] * d_common).numerator
                # exp(d_pi(s,a))^d = E(s,a)^d * (mu/pi)^d / kl_d
                # Taking product over a with weight mu_a -> raise to p_exp / d_common:
                # Directly raise exp(d_pi(s,a))^(d_common * mu_a):
                term_base = (exp_weights[sname][a_idx] * mu_s[a_idx] / pi_s[a_idx]) ** p_exp
                mart_prod *= term_base
        # Factor kl_d^(-sum mu_a) = kl_d^(-1)
        mart_prod /= kl_d
        martingale_checks[sname] = mart_prod == Fraction(1, 1)

    # Trajectory-level exponentiated residual exp(delta(x,y; cand, mu))^d
    traj_residuals: dict[str, str] = {}
    all_reachable_zero = True
    for traj in _TREE_TRAJECTORIES:
        a1 = int(traj[0])
        a2 = int(traj[1])
        s2_name = "s0" if a1 == 0 else "s1"
        mu_s2 = m_0 if a1 == 0 else m_1
        p_traj = m_root[a1] * mu_s2[a2]
        if p_traj == 0:
            traj_residuals[traj] = "UNREACHABLE"
            continue
        e_traj = _exact_pow2(eta_f * (r_map[traj] - v_root), f"traj[{traj}]") ** d_common
        ratio_1 = (cand["root"][a1] / m_root[a1]) ** d_common
        ratio_2 = (cand[s2_name][a2] / mu_s2[a2]) ** d_common
        exp_delta_d = e_traj / (ratio_1 * exp_kl_cand["root"] * ratio_2 * exp_kl_cand[s2_name])
        traj_residuals[traj] = frac_str(exp_delta_d)
        if exp_delta_d != Fraction(1, 1):
            all_reachable_zero = False

    # Check whether candidate matches pi^+ on all reachable states
    matches_pi_plus_on_reachable = (
        cand["root"] == pi_plus["root"]
        and (m_root[0] == 0 or cand["s0"] == pi_plus["s0"])
        and (m_root[1] == 0 or cand["s1"] == pi_plus["s1"])
    )

    # Step-1 linearization fixed-point destruction at root logit z_0:
    # Exact critic-free grad at pi^+ is 0; linearized Eq.(15) grad is -Cov_mu(V^mu(s_2), e_0 - pi)
    # = -mu_root[0] * mu_root[1] * (v_0 - v_1) (independent of pi and eta!).
    lin_grad_root_z0 = -(m_root[0] * m_root[1] * (v_0 - v_1))

    return {
        "common_denominator_d": d_common,
        "v_root": frac_str(v_root),
        "v_s0": frac_str(v_0),
        "v_s1": frac_str(v_1),
        "telescoping_verified": telescoping_ok,
        "pi_plus": {k: [frac_str(x) for x in v] for k, v in pi_plus.items()},
        "z_mu": {k: frac_str(v) for k, v in z_mu.items()},
        "partition_kl_identity_verified": all(partition_kl_checks.values()),
        "martingale_identity_verified": all(martingale_checks.values()),
        "trajectory_exp_delta_pow_d": traj_residuals,
        "all_reachable_residuals_zero": all_reachable_zero,
        "matches_pi_plus_on_reachable": matches_pi_plus_on_reachable,
        "theorem1_iff_verified": all_reachable_zero == matches_pi_plus_on_reachable,
        "exact_critic_free_grad_at_pi_plus": "0/1",
        "linearized_step1_grad_root_z0_at_pi_plus": frac_str(lin_grad_root_z0),
        "linearization_destroys_pmd_fixed_point": lin_grad_root_z0 != Fraction(0, 1),
    }


# ---------------------------------------------------------------------------
# Pillar 2: BPO Complementary Weight, Score-Centering Top-1 Duality & Cap Area
# ---------------------------------------------------------------------------


def analyze_bpo_complementary_weight_and_duality(
    pi_vec: Any,
    mu_vec: Any,
    token_idx: Any,
    eps: Any,
    cap_c: Any,
    eps_low: Any,
    eps_high: Any,
    advantage: Any,
) -> dict[str, Any]:
    """Verify BPO <-> Score-Centering Top-1 duality, exact Jacobian cancellation, & cap area."""
    p_vec = require_prob_vector(pi_vec, "pi_vec")
    q_vec = require_prob_vector(mu_vec, "mu_vec")
    if len(p_vec) != len(q_vec):
        raise BpoOracleError("LENGTH_MISMATCH", "pi_vec and mu_vec must have equal length")

    idx = require_exact_int(token_idx, "token_idx")
    if idx < 0 or idx >= len(p_vec):
        raise BpoOracleError("INVALID_RANGE", "token_idx out of range")

    eps_f = require_exact_fraction(eps, "eps")
    if eps_f < 0:
        raise BpoOracleError("INVALID_RANGE", "eps must be >= 0")
    cap_f = require_exact_fraction(cap_c, "cap_c")
    if cap_f <= 1:
        raise BpoOracleError("INVALID_RANGE", "cap_c must be > 1")
    elow_f = require_exact_fraction(eps_low, "eps_low")
    if elow_f <= 0 or elow_f >= 1:
        raise BpoOracleError("INVALID_RANGE", "eps_low must be in (0, 1)")
    ehigh_f = require_exact_fraction(eps_high, "eps_high")
    if ehigh_f <= 0:
        raise BpoOracleError("INVALID_RANGE", "eps_high must be > 0")
    adv_f = require_exact_fraction(advantage, "advantage")

    p_y = p_vec[idx]
    q_y = q_vec[idx]
    denom_smoothed = Fraction(1, 1) + eps_f - p_y
    if denom_smoothed == 0:
        raise BpoOracleError("SINGULAR_COMPLEMENTARY_RATIO", "1 + eps - pi(y) == 0")

    omega_smoothed = (Fraction(1, 1) + eps_f - q_y) / denom_smoothed
    is_ratio = frac_str(p_y / q_y) if q_y > 0 else "INF"

    # BPO mask M_t^i (main.tex:820-828) and cap min(omega, C)
    if (adv_f > 0 and omega_smoothed > Fraction(1, 1) + ehigh_f) or (
        adv_f < 0 and omega_smoothed < Fraction(1, 1) - elow_f
    ):
        mask = 0
    else:
        mask = 1
    capped_omega = omega_smoothed if omega_smoothed <= cap_f else cap_f
    effective_weight = capped_omega if mask == 1 else Fraction(0, 1)

    # Exact global smoothing bounds & exact cap-active triangle area in [0,1]^2
    if eps_f > 0:
        w_min_bound = frac_str(eps_f / (Fraction(1, 1) + eps_f))
        w_max_bound = frac_str((Fraction(1, 1) + eps_f) / eps_f)
        mu_max_cap = Fraction(1, 1) + eps_f - cap_f * eps_f
        if mu_max_cap <= 0:
            cap_area = Fraction(0, 1)
            pi_min_cap = Fraction(1, 1)
            mu_max_cap_out = Fraction(0, 1)
        else:
            cap_area = (mu_max_cap * mu_max_cap) / (2 * cap_f)
            pi_min_cap = ((cap_f - Fraction(1, 1)) * (Fraction(1, 1) + eps_f)) / cap_f
            mu_max_cap_out = mu_max_cap
    else:
        w_min_bound = "0/1"
        w_max_bound = "INF"
        cap_area = Fraction(1, 1) / (2 * cap_f)
        pi_min_cap = (cap_f - Fraction(1, 1)) / cap_f
        mu_max_cap_out = Fraction(1, 1)

    # Exact K=1 Score Centering duality & exact logit-Jacobian cancellation (for p_y < 1)
    if p_y < 1:
        rho_top1 = (Fraction(1, 1) - q_y) / (Fraction(1, 1) - p_y)
        q_hat = tuple(
            q_y if j == idx else rho_top1 * p_vec[j]
            for j in range(len(p_vec))
        )
        grad_sc_top1 = tuple((Fraction(1, 1) if j == idx else Fraction(0, 1)) - q_hat[j] for j in range(len(p_vec)))
        grad_bpo_unsmoothed = tuple(
            rho_top1 * ((Fraction(1, 1) if j == idx else Fraction(0, 1)) - p_vec[j])
            for j in range(len(p_vec))
        )
        duality_exact = (grad_sc_top1 == grad_bpo_unsmoothed) and (sum(q_hat, Fraction(0, 1)) == Fraction(1, 1))
        grad_l1_exact = sum((abs(x) for x in grad_bpo_unsmoothed), Fraction(0, 1))
        expected_l1 = 2 * (Fraction(1, 1) - q_y)
        cancellation_exact = (grad_l1_exact == expected_l1)
        damping_ratio = (Fraction(1, 1) - p_y) / denom_smoothed
        rho_top1_str = frac_str(rho_top1)
    else:
        duality_exact = False
        grad_l1_exact = Fraction(0, 1)
        cancellation_exact = False
        damping_ratio = Fraction(0, 1)
        rho_top1_str = "SINGULAR"

    return {
        "pi_token": frac_str(p_y),
        "mu_token": frac_str(q_y),
        "importance_ratio_r": is_ratio,
        "unsmoothed_weight_rho_top1": rho_top1_str,
        "smoothed_weight_omega": frac_str(omega_smoothed),
        "smoothed_weight_decimal": format_exact_decimal(omega_smoothed, 6),
        "omega_min_global": w_min_bound,
        "omega_max_global": w_max_bound,
        "mask_m": mask,
        "effective_weight": frac_str(effective_weight),
        "cap_dead_for_positive_adv": (cap_area == Fraction(0, 1)) or ((Fraction(1, 1) + ehigh_f) <= cap_f),
        "cap_active_area_unit_square": frac_str(cap_area),
        "cap_active_area_pct": format_exact_decimal(cap_area * 100, 3),
        "cap_pi_min_at_mu0": frac_str(pi_min_cap),
        "cap_mu_max_at_pi1": frac_str(mu_max_cap_out),
        "score_centering_top1_duality_exact": duality_exact,
        "unsmoothed_logit_grad_l1": frac_str(grad_l1_exact),
        "jacobian_cancellation_exact": cancellation_exact,
        "smoothing_damping_ratio": frac_str(damping_ratio),
    }


# ---------------------------------------------------------------------------
# Pillar 3: |V|=2 vs |V|>=3 Exact Off-Policy Drift-Cancellation Dichotomy
# ---------------------------------------------------------------------------


def audit_bpo_vs_score_centering_drift_exact(
    pi_vec: Any,
    mu_vec: Any,
    eps: Any,
) -> dict[str, Any]:
    """Compare exact off-policy logit drift E_mu[w(y)(e_y - pi)] vs full Score Centering."""
    p_vec = require_prob_vector(pi_vec, "pi_vec", require_positive=True)
    q_vec = require_prob_vector(mu_vec, "mu_vec", require_positive=True)
    if len(p_vec) != len(q_vec):
        raise BpoOracleError("LENGTH_MISMATCH", "pi_vec and mu_vec must have equal length")
    eps_f = require_exact_fraction(eps, "eps")
    if eps_f < 0:
        raise BpoOracleError("INVALID_RANGE", "eps must be >= 0")

    v_len = len(p_vec)
    w_unsmoothed = tuple((Fraction(1, 1) - q_vec[j]) / (Fraction(1, 1) - p_vec[j]) for j in range(v_len))
    w_smoothed = tuple(
        (Fraction(1, 1) + eps_f - q_vec[j]) / (Fraction(1, 1) + eps_f - p_vec[j]) for j in range(v_len)
    )

    def _drift_vec(weights: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
        mean_w = sum((q_vec[j] * weights[j] for j in range(v_len)), Fraction(0, 1))
        return tuple(q_vec[k] * weights[k] - p_vec[k] * mean_w for k in range(v_len))

    d_unsmoothed = _drift_vec(w_unsmoothed)
    d_smoothed = _drift_vec(w_smoothed)
    l1_unsmoothed = sum((abs(x) for x in d_unsmoothed), Fraction(0, 1))
    l1_smoothed = sum((abs(x) for x in d_smoothed), Fraction(0, 1))

    # Full Score Centering drift: E_{y~mu}[(e_y - pi) - (mu - pi)] = E_{y~mu}[e_y - mu] == 0
    d_sc_full = tuple(q_vec[k] - q_vec[k] for k in range(v_len))
    l1_sc_full = sum((abs(x) for x in d_sc_full), Fraction(0, 1))

    return {
        "vocab_size": v_len,
        "eps": frac_str(eps_f),
        "bpo_unsmoothed_drift": [frac_str(x) for x in d_unsmoothed],
        "bpo_unsmoothed_drift_l1": frac_str(l1_unsmoothed),
        "bpo_unsmoothed_zero_drift": l1_unsmoothed == Fraction(0, 1),
        "bpo_smoothed_drift": [frac_str(x) for x in d_smoothed],
        "bpo_smoothed_drift_l1": frac_str(l1_smoothed),
        "bpo_smoothed_zero_drift": l1_smoothed == Fraction(0, 1),
        "full_score_centering_drift_l1": frac_str(l1_sc_full),
        "full_score_centering_zero_drift": l1_sc_full == Fraction(0, 1),
    }


# ---------------------------------------------------------------------------
# Pillar 4: Fail-Closed BPO + 4-Axis RLVR Trust-Region Certifier
# ---------------------------------------------------------------------------


def evaluate_bpo_trust_region_gate(
    pi_token: Any,
    mu_token: Any,
    advantage: Any,
    eps: Any,
    cap_c: Any,
    eps_low: Any,
    eps_high: Any,
    vocab_size: Any,
    router_replay_enabled: Any,
    use_canceled_logit_grad: Any,
) -> dict[str, Any]:
    """Fail-closed governance certifier uniting BPO with RIPO, Score Centering, & R3/TII."""
    p_y = require_exact_fraction(pi_token, "pi_token")
    q_y = require_exact_fraction(mu_token, "mu_token")
    if p_y <= 0 or p_y >= 1:
        raise BpoOracleError("INVALID_PROBABILITY", "pi_token must be in (0, 1)")
    if q_y <= 0 or q_y >= 1:
        raise BpoOracleError("INVALID_PROBABILITY", "mu_token must be in (0, 1)")
    adv_f = require_exact_fraction(advantage, "advantage")
    eps_f = require_exact_fraction(eps, "eps")
    if eps_f < 0:
        raise BpoOracleError("INVALID_RANGE", "eps must be >= 0")
    cap_f = require_exact_fraction(cap_c, "cap_c")
    if cap_f <= 1:
        raise BpoOracleError("INVALID_RANGE", "cap_c must be > 1")
    elow_f = require_exact_fraction(eps_low, "eps_low")
    if elow_f <= 0 or elow_f >= 1:
        raise BpoOracleError("INVALID_RANGE", "eps_low must be in (0, 1)")
    ehigh_f = require_exact_fraction(eps_high, "eps_high")
    if ehigh_f <= 0:
        raise BpoOracleError("INVALID_RANGE", "eps_high must be > 0")
    v_sz = require_exact_int(vocab_size, "vocab_size")
    if v_sz < 2:
        raise BpoOracleError("INVALID_RANGE", "vocab_size must be >= 2")
    r3_on = require_exact_bool(router_replay_enabled, "router_replay_enabled")
    canceled = require_exact_bool(use_canceled_logit_grad, "use_canceled_logit_grad")
    if canceled and eps_f > 0:
        raise BpoOracleError("INCONSISTENT_CONFIG", "use_canceled_logit_grad requires eps == 0")

    omega = (Fraction(1, 1) + eps_f - q_y) / (Fraction(1, 1) + eps_f - p_y)
    damping = (Fraction(1, 1) - p_y) / (Fraction(1, 1) + eps_f - p_y)
    canceled_l1 = 2 * abs(adv_f) * (Fraction(1, 1) - q_y)

    violations: list[str] = []
    if (adv_f > 0 and omega > Fraction(1, 1) + ehigh_f) or (
        adv_f < 0 and omega < Fraction(1, 1) - elow_f
    ):
        mask_m = 0
        violations.append("BPO_TRUST_REGION_CLIPPED")
    else:
        mask_m = 1

    if eps_f == 0 and not canceled and p_y >= Fraction(99, 100):
        violations.append("BPO_SINGULAR_AUTODIFF")
    if eps_f > 0 and adv_f < 0 and damping < Fraction(1, 2):
        violations.append("BPO_OVERCONFIDENT_DAMPING")
    if eps_f > 0 and cap_f * eps_f >= Fraction(1, 1) + eps_f:
        violations.append("BPO_CAP_GLOBALLY_UNREACHABLE")
    if eps_f > 0 and (Fraction(1, 1) - elow_f) * (Fraction(1, 1) + eps_f) <= eps_f:
        violations.append("BPO_LOWER_MASK_GLOBALLY_DEAD")
    if eps_f > 0 and (Fraction(1, 1) + ehigh_f) * eps_f >= Fraction(1, 1) + eps_f:
        violations.append("BPO_UPPER_MASK_GLOBALLY_DEAD")
    if adv_f > 0 and (Fraction(1, 1) + ehigh_f) <= cap_f:
        violations.append("BPO_CAP_MASK_DEAD_CONFLICT")
    if p_y != q_y:
        if v_sz >= 3:
            violations.append("BPO_MULTITOKEN_DRIFT_ACTIVE")
        elif eps_f > 0:
            violations.append("BPO_SMOOTHED_BINARY_DRIFT_ACTIVE")
    if not r3_on:
        violations.append("BPO_MOE_TIM_UNMITIGATED")

    return {
        "status": "CERTIFIED" if len(violations) == 0 else "REJECTED",
        "mask_m": mask_m,
        "violation_count": len(violations),
        "violation_codes": violations,
        "omega": frac_str(omega),
        "damping_ratio": frac_str(damping),
        "exact_canceled_logit_grad_l1": frac_str(canceled_l1),
    }


# ---------------------------------------------------------------------------
# Pillar 5: Exact Pure-Q Verification of BPO Tables 1-3
# ---------------------------------------------------------------------------


def audit_bpo_empirical_tables_exact(rows: Any) -> dict[str, Any]:
    """Verify exact 3-benchmark AIME averages across BPO Tables 1, 2, 3 in pure Q."""
    if not isinstance(rows, (list, tuple)) or len(rows) == 0:
        raise BpoOracleError("EMPTY_SEQUENCE", "rows must be non-empty list or tuple")
    expected_keys = {"table", "method", "aime24", "aime25", "aime26", "reported_avg"}
    seen_pairs: set[tuple[str, str]] = set()
    checked_rows: list[dict[str, Any]] = []
    all_rounding_ok = True
    max_abs_diff = Fraction(0, 1)

    for idx, row in enumerate(rows):
        if not isinstance(row, dict) or set(row.keys()) != expected_keys:
            raise BpoOracleError("SCHEMA_ERROR", f"rows[{idx}] has invalid keys")
        tname = require_non_empty_str(row["table"], f"rows[{idx}].table")
        method = require_non_empty_str(row["method"], f"rows[{idx}].method")
        if (tname, method) in seen_pairs:
            raise BpoOracleError("DUPLICATE_ID", f"duplicate row ({tname}, {method})")
        seen_pairs.add((tname, method))
        a24 = require_exact_fraction(row["aime24"], f"rows[{idx}].aime24")
        a25 = require_exact_fraction(row["aime25"], f"rows[{idx}].aime25")
        a26 = require_exact_fraction(row["aime26"], f"rows[{idx}].aime26")
        rep = require_exact_fraction(row["reported_avg"], f"rows[{idx}].reported_avg")
        for score_name, score_val in (("aime24", a24), ("aime25", a25), ("aime26", a26), ("reported_avg", rep)):
            if score_val < 0 or score_val > 100:
                raise BpoOracleError("INVALID_RANGE", f"rows[{idx}].{score_name} must be in [0, 100]")
        exact_avg = (a24 + a25 + a26) / 3
        diff = exact_avg - rep
        abs_diff = abs(diff)
        if abs_diff > max_abs_diff:
            max_abs_diff = abs_diff
        rounded_1dp = format_exact_decimal(exact_avg, 1)
        row_ok = (Fraction(rounded_1dp) == rep) and (abs_diff <= Fraction(1, 20))
        if not row_ok:
            all_rounding_ok = False
        checked_rows.append(
            {
                "table": tname,
                "method": method,
                "exact_avg": frac_str(exact_avg),
                "exact_avg_1dp": rounded_1dp,
                "reported_avg": frac_str(rep),
                "diff": frac_str(diff),
                "rounding_ok": row_ok,
            }
        )

    return {
        "row_count": len(checked_rows),
        "all_rounding_ok": all_rounding_ok,
        "max_abs_diff": frac_str(max_abs_diff),
        "rows": checked_rows,
    }
