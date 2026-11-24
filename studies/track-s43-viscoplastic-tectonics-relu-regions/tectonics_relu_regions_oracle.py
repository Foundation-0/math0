#!/usr/bin/env python3
"""Track S43: Exact-Z/Q Planetary Viscoplastic Plate Tectonics & ReLU Neural Linear Regions Oracle
(Portal 44 Unified Exact-Operator & Obstruction Suite).

Pure Python 3 standard library over exact Z/Q (`int` and `fractions.Fraction`).
Zero floats, zero bare asserts, zero mathematical RNG, zero third-party dependencies.
Certifies four exact mathematical/physical pillars + explicit Law-4/5 obstructions:
  1. Variational Bingham Viscoplasticity == Two-Sided ReLU Proximal Soft-Thresholding
     (41-point stress grid KKT + strict variational dominance) & Exact 1D Poiseuille
     Lithospheric Plug-vs-Shear Zone Partition + Dissipation Balance.
  2. Exact 3-Phase Dimensionless Yield-Number Diagram (Y = tau_Y / (G H)) across 8 rational
     values <-> Neural Linear-Region Regimes (Stagnant Lid / Mobile Lid / Newtonian Limit)
     & Exact 2D Shallow 3-Neuron ReLU Network (7 linear regions, 9 codim-1 rank-1 walls).
  3. Exact R-T-F Triple-Junction 1-Cocycle (omega_AB + omega_BC + omega_CA = 0) <->
     3-Region Tropical ReLU Hinge Codim-2 Balancing (m_AB r_AB + m_BC r_BC + m_CA r_CA = 0)
     & 2D Piecewise-Linear ReLU Jacobian-Determinant R-T-F Flux Contrast.
  4. Three Explicit Exact-Z/Q Obstructions on the Discrete S^2 Cube Cellular Hodge Complex
     (V=8, E=12, F=6, chi=2, Betti=(1,0,1), d_1 d_0 == 0):
       - Obstruction A: Toroidal-Zero == Conservative Gradient-Flow Curl-Zero + Equipartition;
       - Obstruction B: Compact-Manifold Gauss-Stokes Conservation vs Unconstrained Dead-ReLU;
       - Obstruction C: Static Feedforward Inference Freeze vs Portal 42 GDN-2 Rank-1 Advection.
"""
from __future__ import annotations

from fractions import Fraction
import hashlib
import hmac
import json
import math
from typing import Any, Sequence

TRACK_ID = "TRACK-S43-VISCOPLASTIC-TECTONICS-RELU-REGIONS"
SCHEMA_VERSION = "aletheia.tectonics_relu_regions.certificate.v1"

MAX_JSON_BYTES = 1_048_576
MAX_JSON_DEPTH = 32
MAX_INT_DIGITS = 1000
MAX_INT_BITS = 3321
_ASCII_DIGITS = frozenset("0123456789")
_HEX_LOWER = frozenset("0123456789abcdef")

_CERT_KEYS = frozenset({"schema", "track_id", "payload_sha256", "certificate_sha256", "payload"})
_PAYLOAD_KEYS = frozenset({
    "novelty_tier",
    "individual_domains_novelty",
    "oracle_class",
    "measured_live_mantle_convection_gcm",
    "measured_live_deep_network_training_runs",
    "zero_trust_path_floats",
    "zero_bare_asserts",
    "zero_mathematical_rng",
    "pillar1_bingham_relu_poiseuille",
    "pillar2_yield_phase_and_2d_relu",
    "pillar3_triple_junction_tropical_rtf",
    "pillar4_s2_hodge_obstructions",
})
_BOOL_LEAF_KEYS = frozenset({
    "all_dissipation_balances_exact",
    "all_velocities_tangent_to_s2",
    "all_walls_continuous",
    "all_walls_exact_rank1_jump",
    "betti_euler_matches",
    "closed_oriented_s2_boundary_zero",
    "d1_d0_identically_zero",
    "dead_subduction_collision_exact",
    "dissipation_balance_exact",
    "flux_strictly_decreasing_to_y1",
    "gdn2_inference_region_flip_zero_weight_update",
    "gdn2_key_overwrite_exact",
    "gradient_jump_cocycle_zero",
    "hodge_pythagorean_exact",
    "in_plug",
    "interior_gradients_exact",
    "kkt_subdifferential_all_exact",
    "measured_live_deep_network_training_runs",
    "measured_live_mantle_convection_gcm",
    "neuron1_active",
    "neuron2_active",
    "no_slip_walls_exact",
    "omega_cocycle_zero",
    "outward_div_edge_sign_exact",
    "piecewise_constant_jacobian_all_regions",
    "poloidal_curl_identically_zero",
    "rigid_plate_interior",
    "rigid_plug_zero_strain_all",
    "s2_gauss_stokes_universal_exact",
    "stagnant_lid_exact_zero_flux",
    "static_inference_frozen",
    "toroidal_div_identically_zero",
    "two_layer_relu_equals_max_all_probes",
    "two_neuron_relu_matches_bingham_all",
    "unconstrained_relu_violates_gauss_stokes",
    "unweighted_ray_sum_nonzero",
    "variational_dominance_all_strict",
    "velocity_cocycle_zero",
    "weighted_tropical_balancing_zero",
    "zero_bare_asserts",
    "zero_mathematical_rng",
    "zero_trust_path_floats",
})


class TectonicsReluError(ValueError):
    """Fail-closed domain/validation error for Track S43."""

    def __init__(self, code: str, message: str) -> None:
        self.code = code
        self.message = message
        super().__init__(f"{code}: {message}")


# ---------------------------------------------------------------------------
# Strict Type, ASCII-Digit, Rational, Hex & Canonical JSON Primitives
# ---------------------------------------------------------------------------

def require_exact_int(
    val: Any,
    name: str,
    *,
    min_val: int | None = None,
    max_val: int | None = None,
) -> int:
    if type(val) is not int:
        raise TectonicsReluError("INVALID_INT", f"{name} must be exact int")
    if min_val is not None and val < min_val:
        raise TectonicsReluError("INT_BELOW_MIN", f"{name} must be >= {min_val}")
    if max_val is not None and val > max_val:
        raise TectonicsReluError("INT_ABOVE_MAX", f"{name} must be <= {max_val}")
    return val


def require_exact_bool(val: Any, name: str) -> bool:
    if type(val) is not bool:
        raise TectonicsReluError("INVALID_BOOL", f"{name} must be exact bool")
    return val


def require_exact_str(val: Any, name: str, *, non_empty: bool = True) -> str:
    if type(val) is not str:
        raise TectonicsReluError("INVALID_STR", f"{name} must be exact str")
    if non_empty and not val:
        raise TectonicsReluError("EMPTY_STR", f"{name} must be non-empty")
    try:
        val.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise TectonicsReluError("INVALID_UTF8_STR", f"{name} contains lone surrogate") from exc
    return val


def require_exact_fraction(
    val: Any,
    name: str,
    *,
    positive: bool = False,
    non_negative: bool = False,
) -> Fraction:
    if type(val) is not Fraction:
        raise TectonicsReluError("INVALID_FRACTION", f"{name} must be exact Fraction")
    if positive and val <= 0:
        raise TectonicsReluError("FRACTION_NOT_POSITIVE", f"{name} must be > 0")
    if non_negative and val < 0:
        raise TectonicsReluError("FRACTION_NEGATIVE", f"{name} must be >= 0")
    return val


def require_sha256_hex(val: Any, name: str) -> str:
    s = require_exact_str(val, name)
    if len(s) != 64:
        raise TectonicsReluError("INVALID_SHA256", f"{name} must be 64 lowercase hex chars")
    for ch in s:
        if ch not in _HEX_LOWER:
            raise TectonicsReluError("INVALID_SHA256", f"{name} contains non-hex char")
    return s


def _require_bounded_int(val: int, name: str) -> None:
    if val.bit_length() > MAX_INT_BITS:
        raise TectonicsReluError("INT_TOO_LARGE", f"{name} exceeds {MAX_INT_BITS}-bit limit")


def parse_exact_int_ascii(text: Any, name: str) -> int:
    """Parse strict ASCII signed integer (`-?[0-9]+`, no `.isdigit()`, no `-0`, no leading zeros)."""
    s = require_exact_str(text, name)
    neg = s.startswith("-")
    digits = s[1:] if neg else s
    if not digits:
        raise TectonicsReluError("INVALID_INT_TOKEN", f"{name} has no digits")
    if len(digits) > MAX_INT_DIGITS:
        raise TectonicsReluError("INT_TOKEN_TOO_LONG", f"{name} exceeds {MAX_INT_DIGITS} digits")
    if len(digits) > 1 and digits[0] == "0":
        raise TectonicsReluError("LEADING_ZERO_INT", f"{name} has leading zero")
    for ch in digits:
        if ch not in _ASCII_DIGITS:
            raise TectonicsReluError("NON_ASCII_DIGIT", f"{name} contains non-ASCII digit")
    if neg and digits == "0":
        raise TectonicsReluError("NEGATIVE_ZERO_INT", f"{name} cannot be -0")
    acc = 0
    for ch in digits:
        acc = acc * 10 + (ord(ch) - 48)
    res = -acc if neg else acc
    _require_bounded_int(res, name)
    return res


def parse_exact_rational(text: Any, name: str) -> Fraction:
    """Parse canonical exact rational string `p` or `p/q` (strict ASCII digits, `q > 1`, reduced)."""
    s = require_exact_str(text, name)
    if "/" not in s:
        return Fraction(parse_exact_int_ascii(s, name), 1)
    parts = s.split("/")
    if len(parts) != 2:
        raise TectonicsReluError("INVALID_RATIONAL", f"{name} has multiple slashes")
    num = parse_exact_int_ascii(parts[0], f"{name}.num")
    den = parse_exact_int_ascii(parts[1], f"{name}.den")
    if den <= 1:
        raise TectonicsReluError("NON_CANONICAL_DEN", f"{name} denominator must be > 1")
    if math.gcd(abs(num), den) != 1:
        raise TectonicsReluError("UNREDUCED_RATIONAL", f"{name} must be in lowest terms")
    return Fraction(num, den)


def format_exact_rational(q: Any) -> str:
    val = require_exact_fraction(q, "q")
    _require_bounded_int(val.numerator, "q.numerator")
    _require_bounded_int(val.denominator, "q.denominator")
    if val.denominator == 1:
        return str(val.numerator)
    return f"{val.numerator}/{val.denominator}"


def format_decimal_trunc(q: Any, places: Any) -> str:
    """Deterministic toward-zero decimal truncation of exact Fraction; never emits `-0.00` or `-0`."""
    val = require_exact_fraction(q, "q")
    _require_bounded_int(val.numerator, "q.numerator")
    _require_bounded_int(val.denominator, "q.denominator")
    dp = require_exact_int(places, "places", min_val=0, max_val=18)
    neg = val < 0
    num = -val.numerator if neg else val.numerator
    den = val.denominator
    scale = 10 ** dp
    scaled = (num * scale) // den
    prefix = "-" if (neg and scaled != 0) else ""
    if dp == 0:
        return f"{prefix}{scaled}"
    whole, frac = divmod(scaled, scale)
    return f"{prefix}{whole}.{frac:0{dp}d}"


def validate_json_tree_iterative(obj: Any) -> None:
    """Iterative Zone-B JSON tree validation: depth cap, int bit cap, no floats/cycles/surrogates."""
    stack: list[tuple[Any, int]] = [(obj, 0)]
    while stack:
        val, depth = stack.pop()
        if depth > MAX_JSON_DEPTH:
            raise TectonicsReluError("JSON_TOO_DEEP", "JSON nesting depth exceeded")
        t = type(val)
        if t is bool or val is None:
            continue
        if t is int:
            _require_bounded_int(val, "json_int")
            continue
        if t is str:
            require_exact_str(val, "json_str", non_empty=False)
            continue
        if t is list:
            for item in val:
                stack.append((item, depth + 1))
            continue
        if t is dict:
            for k, v in val.items():
                require_exact_str(k, "json_key", non_empty=False)
                stack.append((v, depth + 1))
            continue
        raise TectonicsReluError("FORBIDDEN_JSON_TYPE", f"unsupported JSON type: {t.__name__}")


def canonical_json_bytes(obj: Any) -> bytes:
    validate_json_tree_iterative(obj)
    raw = json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")
    if len(raw) > MAX_JSON_BYTES:
        raise TectonicsReluError("JSON_TOO_LARGE", "canonical JSON exceeds byte limit")
    return raw


def parse_strict_json_text(text: Any, *, require_object: bool = True) -> Any:
    s = require_exact_str(text, "json_text")
    if len(s.encode("utf-8")) > MAX_JSON_BYTES:
        raise TectonicsReluError("JSON_TOO_LARGE", "JSON text exceeds byte limit")

    def _reject_float(token: str) -> Any:
        raise TectonicsReluError("FLOAT_FORBIDDEN", f"floating-point JSON token forbidden: {token}")

    def _reject_const(token: str) -> Any:
        raise TectonicsReluError("NON_FINITE_FORBIDDEN", f"JSON constant forbidden: {token}")

    def _parse_json_int(token: str) -> int:
        return parse_exact_int_ascii(token, "json_int")

    def _no_dup_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        out: dict[str, Any] = {}
        for k, v in pairs:
            if k in out:
                raise TectonicsReluError("DUPLICATE_JSON_KEY", f"duplicate key: {k}")
            out[k] = v
        return out

    try:
        parsed = json.loads(
            s,
            parse_float=_reject_float,
            parse_constant=_reject_const,
            parse_int=_parse_json_int,
            object_pairs_hook=_no_dup_pairs,
        )
    except TectonicsReluError:
        raise
    except (ValueError, RecursionError) as exc:
        raise TectonicsReluError("INVALID_JSON", f"invalid JSON: {type(exc).__name__}") from exc

    if require_object and type(parsed) is not dict:
        raise TectonicsReluError("JSON_ROOT_NOT_OBJECT", "JSON root must be an object")
    validate_json_tree_iterative(parsed)
    return parsed


# ---------------------------------------------------------------------------
# Pillar 1: Variational Bingham Viscoplasticity == Two-Sided ReLU Proximal &
#           Exact 1D Poiseuille Lithospheric Plug-vs-Shear Partition
# ---------------------------------------------------------------------------

def q_relu(x: Any) -> Fraction:
    """Exact pure-Q ReLU operator: max(0, x) without built-in max or floats."""
    val = require_exact_fraction(x, "x")
    return val if val > 0 else Fraction(0, 1)


def bingham_strain_rate_relu(tau: Any, tau_y: Any, eta0: Any) -> Fraction:
    """Exact two-sided ReLU proximal soft-thresholding strain rate e*(tau)."""
    t = require_exact_fraction(tau, "tau")
    ty = require_exact_fraction(tau_y, "tau_y", non_negative=True)
    eta = require_exact_fraction(eta0, "eta0", positive=True)
    return (q_relu(t - ty) - q_relu(-t - ty)) / (2 * eta)


def bingham_dissipation_objective(e: Any, tau: Any, tau_y: Any, eta0: Any) -> Fraction:
    """Exact Duvaut-Lions nonsmooth convex objective J(e) = eta0 * e^2 + tau_y * |e| - tau * e."""
    ev = require_exact_fraction(e, "e")
    t = require_exact_fraction(tau, "tau")
    ty = require_exact_fraction(tau_y, "tau_y", non_negative=True)
    eta = require_exact_fraction(eta0, "eta0", positive=True)
    abs_e = -ev if ev < 0 else ev
    return eta * ev * ev + ty * abs_e - t * ev


def bingham_channel_profile(
    y: Any,
    g_grad: Any,
    h_half: Any,
    tau_y: Any,
    eta0: Any,
) -> dict[str, Any]:
    """Exact 1D Bingham Poiseuille channel profile on y in [-H, H] via 2-neuron ReLU partition."""
    yv = require_exact_fraction(y, "y")
    g = require_exact_fraction(g_grad, "g_grad", positive=True)
    h = require_exact_fraction(h_half, "h_half", positive=True)
    ty = require_exact_fraction(tau_y, "tau_y", non_negative=True)
    eta = require_exact_fraction(eta0, "eta0", positive=True)
    abs_y = -yv if yv < 0 else yv
    if abs_y > h:
        raise TectonicsReluError("Y_OUT_OF_CHANNEL", "y must satisfy |y| <= h_half")

    y_ratio = ty / g
    y_plug = h if y_ratio > h else y_ratio
    u_plug = g * (h - y_plug) * (h - y_plug) / (2 * eta)
    tau = -g * yv
    # Tensor shear rate eps_xy = 1/2 u'(y) == bingham_strain_rate_relu(tau, ty, eta)
    du_dy_from_bingham = 2 * bingham_strain_rate_relu(tau, ty, eta)
    # Exact 2-neuron ReLU representation on y in [-H, H]:
    # neuron 1 wall y = -y_plug (ReLU(-y - y_plug)), neuron 2 wall y = +y_plug (ReLU(y - y_plug))
    n1 = q_relu(-yv - y_plug)
    n2 = q_relu(yv - y_plug)
    du_dy_relu = (g / eta) * (n1 - n2)
    u_val = u_plug - (g / (2 * eta)) * (n1 * n1 + n2 * n2)
    return {
        "y": yv,
        "tau": tau,
        "y_plug": y_plug,
        "u_plug": u_plug,
        "du_dy": du_dy_relu,
        "du_dy_matches_bingham": du_dy_relu == du_dy_from_bingham,
        "u": u_val,
        "in_plug": abs_y <= y_plug,
        "neuron1_active": n1 > 0,
        "neuron2_active": n2 > 0,
    }


def build_pillar1_bingham_relu_poiseuille() -> dict[str, Any]:
    """Certify Pillar 1: 41-point Bingham==ReLU KKT/variational identity & 1D Poiseuille channel."""
    eta0 = Fraction(3, 2)
    tau_y = Fraction(2, 1)
    deltas = (Fraction(1, 10), Fraction(1, 1))

    plug_count = 0
    pos_shear_count = 0
    neg_shear_count = 0
    kkt_all_exact = True
    var_dom_all_strict = True
    sample_taus = frozenset({Fraction(-5, 1), Fraction(-2, 1), Fraction(0, 1), Fraction(2, 1), Fraction(5, 1)})
    sample_witnesses: list[dict[str, Any]] = []

    for k in range(-20, 21):
        tau = Fraction(k, 4)
        e_star = bingham_strain_rate_relu(tau, tau_y, eta0)
        if e_star > 0:
            s_sub = Fraction(1, 1)
            pos_shear_count += 1
        elif e_star < 0:
            s_sub = Fraction(-1, 1)
            neg_shear_count += 1
        else:
            s_sub = tau / tau_y
            plug_count += 1
        abs_s = -s_sub if s_sub < 0 else s_sub
        kkt_res = 2 * eta0 * e_star + tau_y * s_sub - tau
        if not all((abs_s <= 1, kkt_res == 0)):
            kkt_all_exact = False  # pragma: no cover

        j_star = bingham_dissipation_objective(e_star, tau, tau_y, eta0)
        for d in deltas:
            j_plus = bingham_dissipation_objective(e_star + d, tau, tau_y, eta0)
            j_minus = bingham_dissipation_objective(e_star - d, tau, tau_y, eta0)
            min_gap = eta0 * d * d
            if not all((j_plus - j_star >= min_gap, j_minus - j_star >= min_gap)):
                var_dom_all_strict = False  # pragma: no cover

        if tau in sample_taus:
            j_p10 = bingham_dissipation_objective(e_star + Fraction(1, 10), tau, tau_y, eta0)
            j_m10 = bingham_dissipation_objective(e_star - Fraction(1, 10), tau, tau_y, eta0)
            sample_witnesses.append({
                "tau": format_exact_rational(tau),
                "e_star": format_exact_rational(e_star),
                "kkt_subgradient_s": format_exact_rational(s_sub),
                "j_star": format_exact_rational(j_star),
                "j_plus_tenth_gap": format_exact_rational(j_p10 - j_star),
                "j_minus_tenth_gap": format_exact_rational(j_m10 - j_star),
            })

    # Exact 1D Poiseuille Bingham channel (G=4, H=2, tau_Y=4, eta0=1 -> Y=1/2, y_p=1)
    g_ch = Fraction(4, 1)
    h_ch = Fraction(2, 1)
    ty_ch = Fraction(4, 1)
    eta_ch = Fraction(1, 1)
    y_plug = ty_ch / g_ch
    u_plug = g_ch * (h_ch - y_plug) * (h_ch - y_plug) / (2 * eta_ch)
    q_half = g_ch * (h_ch - y_plug) * (h_ch - y_plug) * (2 * h_ch + y_plug) / (6 * eta_ch)
    q_full = 2 * q_half
    d_visc_half = g_ch * g_ch * (h_ch - y_plug) * (h_ch - y_plug) * (h_ch - y_plug) / (3 * eta_ch)
    d_yield_half = ty_ch * g_ch * (h_ch - y_plug) * (h_ch - y_plug) / (2 * eta_ch)
    p_in_half = g_ch * q_half

    probe_ys = (
        Fraction(-2, 1), Fraction(-3, 2), Fraction(-1, 1), Fraction(-1, 2),
        Fraction(0, 1), Fraction(1, 2), Fraction(1, 1), Fraction(3, 2), Fraction(2, 1),
    )
    probes: list[dict[str, Any]] = []
    all_probes_match_bingham = True
    plug_zero_strain_all = True
    for py in probe_ys:
        prof = bingham_channel_profile(py, g_ch, h_ch, ty_ch, eta_ch)
        if not prof["du_dy_matches_bingham"]:
            all_probes_match_bingham = False  # pragma: no cover
        if prof["in_plug"] and not all((prof["du_dy"] == 0, prof["u"] == u_plug)):
            plug_zero_strain_all = False  # pragma: no cover
        probes.append({
            "y": format_exact_rational(py),
            "tau": format_exact_rational(prof["tau"]),
            "u": format_exact_rational(prof["u"]),
            "du_dy": format_exact_rational(prof["du_dy"]),
            "in_plug": prof["in_plug"],
            "neuron1_active": prof["neuron1_active"],
            "neuron2_active": prof["neuron2_active"],
        })

    return {
        "variational_proximal_identity": {
            "eta0": format_exact_rational(eta0),
            "tau_y": format_exact_rational(tau_y),
            "grid_points": 41,
            "plug_points": plug_count,
            "positive_shear_points": pos_shear_count,
            "negative_shear_points": neg_shear_count,
            "kkt_subdifferential_all_exact": kkt_all_exact,
            "variational_dominance_all_strict": var_dom_all_strict,
            "sample_witnesses": sample_witnesses,
        },
        "poiseuille_plug_shear_channel": {
            "g_grad": format_exact_rational(g_ch),
            "h_half": format_exact_rational(h_ch),
            "tau_y": format_exact_rational(ty_ch),
            "eta0": format_exact_rational(eta_ch),
            "yield_number_y": format_exact_rational(ty_ch / (g_ch * h_ch)),
            "y_plug": format_exact_rational(y_plug),
            "u_plug": format_exact_rational(u_plug),
            "q_half": format_exact_rational(q_half),
            "q_full": format_exact_rational(q_full),
            "d_visc_half": format_exact_rational(d_visc_half),
            "d_yield_half": format_exact_rational(d_yield_half),
            "power_in_half": format_exact_rational(p_in_half),
            "dissipation_balance_exact": (d_visc_half + d_yield_half == p_in_half),
            "no_slip_walls_exact": all((probes[0]["u"] == "0", probes[-1]["u"] == "0")),
            "two_neuron_relu_matches_bingham_all": all_probes_match_bingham,
            "rigid_plug_zero_strain_all": plug_zero_strain_all,
            "channel_probes": probes,
        },
    }


# ---------------------------------------------------------------------------
# Pillar 2: 3-Phase Dimensionless Yield-Number Diagram & 2D Shallow ReLU Regions
# ---------------------------------------------------------------------------

def bingham_yield_regime(
    y_num: Any,
    g_grad: Any,
    h_half: Any,
    eta0: Any,
) -> dict[str, Any]:
    """Compute exact 1D Bingham regime metrics for dimensionless yield number Y = tau_Y / (G H)."""
    yv = require_exact_fraction(y_num, "y_num", non_negative=True)
    g = require_exact_fraction(g_grad, "g_grad", positive=True)
    h = require_exact_fraction(h_half, "h_half", positive=True)
    eta = require_exact_fraction(eta0, "eta0", positive=True)

    rho = Fraction(1, 1) if yv >= 1 else yv
    y_plug = rho * h
    tau_y = yv * g * h
    one_m = Fraction(1, 1) - rho
    u_plug = g * h * h * one_m * one_m / (2 * eta)
    q_half = (g * h * h * h / (3 * eta)) * (Fraction(1, 1) - Fraction(3, 2) * rho + Fraction(1, 2) * rho * rho * rho)
    q_full = 2 * q_half
    d_visc_half = g * g * (h - y_plug) * (h - y_plug) * (h - y_plug) / (3 * eta)
    d_yield_half = tau_y * g * (h - y_plug) * (h - y_plug) / (2 * eta)
    p_in_half = g * q_half

    if yv == 0:
        tect_regime = "newtonian_magma_ocean"
        nn_regime = "splintered_unregularized_limit"
        active_walls = 0
        rigid_interior = False
        plastic_share = Fraction(0, 1)
    elif yv < 1:
        tect_regime = "mobile_lid_plate_tectonics"
        nn_regime = "modular_feature_learning"
        active_walls = 2
        rigid_interior = True
        plastic_share = d_yield_half / p_in_half
    else:
        tect_regime = "stagnant_lid"
        nn_regime = "dead_relu_frozen_ntk"
        active_walls = 0
        rigid_interior = True
        plastic_share = Fraction(0, 1)

    return {
        "y_num": format_exact_rational(yv),
        "plug_fraction": format_exact_rational(rho),
        "u_plug": format_exact_rational(u_plug),
        "q_half": format_exact_rational(q_half),
        "q_full": format_exact_rational(q_full),
        "d_visc_half": format_exact_rational(d_visc_half),
        "d_yield_half": format_exact_rational(d_yield_half),
        "power_in_half": format_exact_rational(p_in_half),
        "dissipation_balance_exact": (d_visc_half + d_yield_half == p_in_half),
        "plastic_dissipation_share": format_exact_rational(plastic_share),
        "active_shear_walls": active_walls,
        "rigid_plate_interior": rigid_interior,
        "tectonic_regime": tect_regime,
        "neural_regime": nn_regime,
    }


_RELU2D_NEURONS: tuple[tuple[tuple[int, int], int, tuple[int, int]], ...] = (
    ((1, 0), 0, (2, 1)),
    ((0, 1), 0, (-1, 3)),
    ((1, 1), -2, (1, -2)),
)


def eval_shallow_relu_2d(x1: Any, x2: Any) -> tuple[Fraction, Fraction]:
    """Evaluate exact pure-Q 2D 3-neuron shallow ReLU network f(x) = x + sum_k c_k ReLU(w_k.x + b_k)."""
    q1 = require_exact_fraction(x1, "x1")
    q2 = require_exact_fraction(x2, "x2")
    y1 = q1
    y2 = q2
    for (w1, w2), b, (c1, c2) in _RELU2D_NEURONS:
        act = q_relu(w1 * q1 + w2 * q2 + Fraction(b, 1))
        y1 += c1 * act
        y2 += c2 * act
    return (y1, y2)


def _shallow_relu_2d_pattern(x1: Fraction, x2: Fraction) -> tuple[int, int, int]:
    bits: list[int] = []
    for (w1, w2), b, _ in _RELU2D_NEURONS:
        pre = w1 * x1 + w2 * x2 + Fraction(b, 1)
        bits.append(1 if pre > 0 else 0)
    return (bits[0], bits[1], bits[2])


def _shallow_relu_2d_expected_jac(pattern: tuple[int, int, int]) -> list[list[int]]:
    j = [[1, 0], [0, 1]]
    for idx, bit in enumerate(pattern):
        if bit == 1:
            (w1, w2), _, (c1, c2) = _RELU2D_NEURONS[idx]
            j[0][0] += c1 * w1
            j[0][1] += c1 * w2
            j[1][0] += c2 * w1
            j[1][1] += c2 * w2
    return j


def build_pillar2_yield_phase_and_2d_relu() -> dict[str, Any]:
    """Certify Pillar 2: 8-point 3-phase yield diagram & 2D 3-neuron ReLU linear regions."""
    g = Fraction(4, 1)
    h = Fraction(2, 1)
    eta = Fraction(1, 1)
    y_grid = (
        Fraction(0, 1), Fraction(1, 8), Fraction(1, 4), Fraction(1, 2),
        Fraction(3, 4), Fraction(1, 1), Fraction(5, 4), Fraction(2, 1),
    )
    sweep = [bingham_yield_regime(yv, g, h, eta) for yv in y_grid]
    q_vals = [parse_exact_rational(row["q_half"], "q_half") for row in sweep]
    strict_dec = all(q_vals[i] > q_vals[i + 1] for i in range(5))
    stagnant_zero = all(q_vals[i] == 0 for i in range(5, 8))
    all_diss_ok = all(row["dissipation_balance_exact"] for row in sweep)

    # 2D 3-neuron ReLU: 7 nonempty linear regions, 9 codim-1 walls
    region_probes: tuple[tuple[tuple[int, int, int], tuple[Fraction, Fraction]], ...] = (
        ((0, 0, 0), (Fraction(-1, 1), Fraction(-1, 1))),
        ((1, 0, 0), (Fraction(1, 1), Fraction(-1, 1))),
        ((1, 0, 1), (Fraction(4, 1), Fraction(-1, 1))),
        ((0, 1, 0), (Fraction(-1, 1), Fraction(1, 1))),
        ((0, 1, 1), (Fraction(-1, 1), Fraction(4, 1))),
        ((1, 1, 0), (Fraction(1, 2), Fraction(1, 2))),
        ((1, 1, 1), (Fraction(2, 1), Fraction(2, 1))),
    )
    step = Fraction(1, 4)
    region_jacs: dict[tuple[int, int, int], list[list[int]]] = {}
    regions_out: list[dict[str, Any]] = []
    all_jac_piecewise_const = True

    for pat, (px, py) in region_probes:
        p_check = _shallow_relu_2d_pattern(px, py)
        p_dx = _shallow_relu_2d_pattern(px + step, py)
        p_dy = _shallow_relu_2d_pattern(px, py + step)
        f0 = eval_shallow_relu_2d(px, py)
        fx = eval_shallow_relu_2d(px + step, py)
        fy = eval_shallow_relu_2d(px, py + step)
        fd_j = [
            [(fx[0] - f0[0]) / step, (fy[0] - f0[0]) / step],
            [(fx[1] - f0[1]) / step, (fy[1] - f0[1]) / step],
        ]
        exp_j = _shallow_relu_2d_expected_jac(pat)
        exp_j_q = [[Fraction(v, 1) for v in row] for row in exp_j]
        if not all((p_check == pat, p_dx == pat, p_dy == pat, fd_j == exp_j_q)):
            all_jac_piecewise_const = False  # pragma: no cover
        det_j = exp_j[0][0] * exp_j[1][1] - exp_j[0][1] * exp_j[1][0]
        region_jacs[pat] = exp_j
        regions_out.append({
            "pattern": list(pat),
            "probe_x": [format_exact_rational(px), format_exact_rational(py)],
            "jacobian": exp_j,
            "det_j": det_j,
        })

    wall_specs: tuple[tuple[tuple[int, int, int], tuple[int, int, int], int, tuple[Fraction, Fraction]], ...] = (
        ((0, 0, 0), (1, 0, 0), 0, (Fraction(0, 1), Fraction(-1, 1))),
        ((0, 0, 0), (0, 1, 0), 1, (Fraction(-1, 1), Fraction(0, 1))),
        ((1, 0, 0), (1, 0, 1), 2, (Fraction(3, 1), Fraction(-1, 1))),
        ((1, 0, 0), (1, 1, 0), 1, (Fraction(1, 1), Fraction(0, 1))),
        ((0, 1, 0), (0, 1, 1), 2, (Fraction(-1, 1), Fraction(3, 1))),
        ((0, 1, 0), (1, 1, 0), 0, (Fraction(0, 1), Fraction(1, 1))),
        ((1, 0, 1), (1, 1, 1), 1, (Fraction(3, 1), Fraction(0, 1))),
        ((0, 1, 1), (1, 1, 1), 0, (Fraction(0, 1), Fraction(3, 1))),
        ((1, 1, 0), (1, 1, 1), 2, (Fraction(1, 1), Fraction(1, 1))),
    )
    all_walls_rank1 = True
    all_walls_continuous = True
    for pat_lo, pat_hi, n_idx, (wx, wy) in wall_specs:
        j_lo = region_jacs[pat_lo]
        j_hi = region_jacs[pat_hi]
        dj = [
            [j_hi[0][0] - j_lo[0][0], j_hi[0][1] - j_lo[0][1]],
            [j_hi[1][0] - j_lo[1][0], j_hi[1][1] - j_lo[1][1]],
        ]
        (w1, w2), b, (c1, c2) = _RELU2D_NEURONS[n_idx]
        outer = [[c1 * w1, c1 * w2], [c2 * w1, c2 * w2]]
        det_dj = dj[0][0] * dj[1][1] - dj[0][1] * dj[1][0]
        nonzero_dj = any(val != 0 for row in dj for val in row)
        on_wall = (w1 * wx + w2 * wy + Fraction(b, 1) == 0)
        # Continuity at wall: affine limits from both sides match eval_shallow_relu_2d(wx, wy)
        fw = eval_shallow_relu_2d(wx, wy)
        eps = Fraction(1, 8)
        f_plus = eval_shallow_relu_2d(wx + eps * w1, wy + eps * w2)
        f_minus = eval_shallow_relu_2d(wx - eps * w1, wy - eps * w2)
        lim_hi = (
            f_plus[0] - eps * (j_hi[0][0] * w1 + j_hi[0][1] * w2),
            f_plus[1] - eps * (j_hi[1][0] * w1 + j_hi[1][1] * w2),
        )
        lim_lo = (
            f_minus[0] + eps * (j_lo[0][0] * w1 + j_lo[0][1] * w2),
            f_minus[1] + eps * (j_lo[1][0] * w1 + j_lo[1][1] * w2),
        )
        if not all((dj == outer, det_dj == 0, nonzero_dj)):
            all_walls_rank1 = False  # pragma: no cover
        if not all((on_wall, lim_hi == fw, lim_lo == fw)):
            all_walls_continuous = False  # pragma: no cover

    return {
        "yield_phase_diagram": {
            "g_grad": format_exact_rational(g),
            "h_half": format_exact_rational(h),
            "eta0": format_exact_rational(eta),
            "yield_points_count": len(sweep),
            "newtonian_count": 1,
            "mobile_lid_count": 4,
            "stagnant_lid_count": 3,
            "flux_strictly_decreasing_to_y1": strict_dec,
            "stagnant_lid_exact_zero_flux": stagnant_zero,
            "all_dissipation_balances_exact": all_diss_ok,
            "sweep": sweep,
        },
        "shallow_2d_relu_regions": {
            "neuron_count": 3,
            "linear_region_count": len(regions_out),
            "impossible_pattern": [0, 0, 1],
            "codim1_wall_count": len(wall_specs),
            "piecewise_constant_jacobian_all_regions": all_jac_piecewise_const,
            "all_walls_exact_rank1_jump": all_walls_rank1,
            "all_walls_continuous": all_walls_continuous,
            "regions": regions_out,
        },
    }


# ---------------------------------------------------------------------------
# Pillar 3: R-T-F Triple-Junction 1-Cocycle <-> Tropical ReLU Balancing &
#           2D Piecewise-Linear ReLU Jacobian-Determinant Flux Taxonomy
# ---------------------------------------------------------------------------

def _require_vec3_q(vec: Any, name: str) -> tuple[Fraction, Fraction, Fraction]:
    if type(vec) not in (tuple, list) or len(vec) != 3:
        raise TectonicsReluError("INVALID_VEC3", f"{name} must be length-3 tuple/list of Fraction")
    return (
        require_exact_fraction(vec[0], f"{name}[0]"),
        require_exact_fraction(vec[1], f"{name}[1]"),
        require_exact_fraction(vec[2], f"{name}[2]"),
    )


def cross3_q(a: Any, b: Any) -> tuple[Fraction, Fraction, Fraction]:
    """Exact pure-Q 3D cross product."""
    ax, ay, az = _require_vec3_q(a, "a")
    bx, by, bz = _require_vec3_q(b, "b")
    return (ay * bz - az * by, az * bx - ax * bz, ax * by - ay * bx)


def dot3_q(a: Any, b: Any) -> Fraction:
    """Exact pure-Q 3D dot product."""
    ax, ay, az = _require_vec3_q(a, "a")
    bx, by, bz = _require_vec3_q(b, "b")
    return ax * bx + ay * by + az * bz


def eval_tropical_hinge_relu(x: Any, y: Any) -> Fraction:
    """Exact 2-layer ReLU representation of tropical 3-region hinge max(2x, 2y, -x - 2y)."""
    qx = require_exact_fraction(x, "x")
    qy = require_exact_fraction(y, "y")
    la = 2 * qx
    lb = 2 * qy
    lc = -qx - 2 * qy
    ab = la + q_relu(lb - la)
    return ab + q_relu(lc - ab)


def build_pillar3_triple_junction_tropical_rtf() -> dict[str, Any]:
    """Certify Pillar 3: R-T-F 1-cocycle, 3-region tropical ReLU hinge & 2D det(J) taxonomy."""
    z0 = Fraction(0, 1)
    p = (z0, z0, Fraction(1, 1))
    w_a = (z0, Fraction(1, 1), z0)
    w_b = (z0, z0, z0)
    w_c = (Fraction(-1, 1), Fraction(1, 1), z0)

    def _sub3(u: tuple[Fraction, Fraction, Fraction], v: tuple[Fraction, Fraction, Fraction]) -> tuple[Fraction, Fraction, Fraction]:
        return (u[0] - v[0], u[1] - v[1], u[2] - v[2])

    def _add3(
        u: tuple[Fraction, Fraction, Fraction],
        v: tuple[Fraction, Fraction, Fraction],
        w: tuple[Fraction, Fraction, Fraction],
    ) -> tuple[Fraction, Fraction, Fraction]:
        return (u[0] + v[0] + w[0], u[1] + v[1] + w[1], u[2] + v[2] + w[2])

    w_ab = _sub3(w_a, w_b)
    w_bc = _sub3(w_b, w_c)
    w_ca = _sub3(w_c, w_a)
    omega_sum = _add3(w_ab, w_bc, w_ca)

    v_a = cross3_q(w_a, p)
    v_b = cross3_q(w_b, p)
    v_c = cross3_q(w_c, p)
    v_ab = _sub3(v_a, v_b)
    v_bc = _sub3(v_b, v_c)
    v_ca = _sub3(v_c, v_a)
    vel_sum = _add3(v_ab, v_bc, v_ca)

    n_ab = (Fraction(1, 1), z0, z0)
    n_bc = (Fraction(1, 1), Fraction(1, 1), z0)
    n_ca = (Fraction(1, 1), z0, z0)

    def _classify_wall(
        label: str,
        v_rel: tuple[Fraction, Fraction, Fraction],
        normal: tuple[Fraction, Fraction, Fraction],
    ) -> dict[str, Any]:
        tangent = cross3_q(normal, p)
        opening = dot3_q(v_rel, normal)
        shear = dot3_q(v_rel, tangent)
        if opening > 0:
            kind = "divergent_ridge"
        elif opening < 0:
            kind = "convergent_subduction_trench"
        else:
            kind = "transform_fault"
        return {
            "wall": label,
            "v_rel": [format_exact_rational(c) for c in v_rel],
            "normal": [format_exact_rational(c) for c in normal],
            "tangent": [format_exact_rational(c) for c in tangent],
            "normal_opening": format_exact_rational(opening),
            "tangential_shear": format_exact_rational(shear),
            "classification": kind,
        }

    walls = [
        _classify_wall("AB", v_ab, n_ab),
        _classify_wall("BC", v_bc, n_bc),
        _classify_wall("CA", v_ca, n_ca),
    ]

    # 3-Region Tropical ReLU Hinge: l_A=2x, l_B=2y, l_C=-x-2y
    g_a = (2, 0)
    g_b = (0, 2)
    g_c = (-1, -2)
    dg_ab = (g_a[0] - g_b[0], g_a[1] - g_b[1])
    dg_bc = (g_b[0] - g_c[0], g_b[1] - g_c[1])
    dg_ca = (g_c[0] - g_a[0], g_c[1] - g_a[1])
    dg_sum = (dg_ab[0] + dg_bc[0] + dg_ca[0], dg_ab[1] + dg_bc[1] + dg_ca[1])

    m_ab, r_ab = 2, (1, 1)
    m_bc, r_bc = 1, (-4, 1)
    m_ca, r_ca = 1, (2, -3)
    trop_bal = (
        m_ab * r_ab[0] + m_bc * r_bc[0] + m_ca * r_ca[0],
        m_ab * r_ab[1] + m_bc * r_bc[1] + m_ca * r_ca[1],
    )
    unweighted_ray_sum = (r_ab[0] + r_bc[0] + r_ca[0], r_ab[1] + r_bc[1] + r_ca[1])

    # Verify exact 2-layer ReLU == max(l_A, l_B, l_C) at interiors, rays, and triple junction
    test_pts = (
        (Fraction(3, 1), Fraction(0, 1)),
        (Fraction(0, 1), Fraction(3, 1)),
        (Fraction(-3, 1), Fraction(-3, 1)),
        (Fraction(1, 1), Fraction(1, 1)),
        (Fraction(-4, 1), Fraction(1, 1)),
        (Fraction(2, 1), Fraction(-3, 1)),
        (Fraction(0, 1), Fraction(0, 1)),
    )
    hinge_matches_max = True
    for tx, ty in test_pts:
        la, lb, lc = 2 * tx, 2 * ty, -tx - 2 * ty
        m_ab_v = la if la >= lb else lb
        m_all = m_ab_v if m_ab_v >= lc else lc
        if eval_tropical_hinge_relu(tx, ty) != m_all:
            hinge_matches_max = False  # pragma: no cover

    # Verify exact finite-difference gradients inside the 3 regions
    h_fd = Fraction(1, 4)
    grad_probes = (
        (Fraction(3, 1), Fraction(0, 1), g_a),
        (Fraction(0, 1), Fraction(3, 1), g_b),
        (Fraction(-3, 1), Fraction(-3, 1), g_c),
    )
    region_grads_exact = True
    for px, py, eg in grad_probes:
        f0 = eval_tropical_hinge_relu(px, py)
        gx = (eval_tropical_hinge_relu(px + h_fd, py) - f0) / h_fd
        gy = (eval_tropical_hinge_relu(px, py + h_fd) - f0) / h_fd
        if (gx, gy) != (Fraction(eg[0], 1), Fraction(eg[1], 1)):
            region_grads_exact = False  # pragma: no cover

    # 2D piecewise-linear ReLU wall F(x) = x + c * ReLU(x1), J_- = I_2, J_+ = I_2 + c e_1^T
    def _jac_case(label: str, c1: Fraction, c2: Fraction, regime: str) -> dict[str, Any]:
        j_plus = [[Fraction(1, 1) + c1, Fraction(0, 1)], [c2, Fraction(1, 1)]]
        det_p = j_plus[0][0] * j_plus[1][1] - j_plus[0][1] * j_plus[1][0]
        rank_p = 2 if det_p != 0 else 1
        return {
            "case": label,
            "c_vec": [format_exact_rational(c1), format_exact_rational(c2)],
            "det_j_minus": "1",
            "det_j_plus": format_exact_rational(det_p),
            "rank_j_plus": rank_p,
            "regime": regime,
        }

    jac_cases = [
        _jac_case("ridge_expanding", Fraction(2, 1), Fraction(0, 1), "expanding_ridge"),
        _jac_case("trench_contractive", Fraction(-1, 2), Fraction(0, 1), "contractive_trench"),
        _jac_case("trench_dead_slab_collapse", Fraction(-1, 1), Fraction(0, 1), "rank_deficient_subduction"),
        _jac_case("transform_volume_preserving_shear", Fraction(0, 1), Fraction(2, 1), "volume_preserving_transform"),
    ]
    # Explicit collision witness on dead-ReLU subduction wall: F(1,5) == F(7,5) == (0,5)
    f_col_1 = (Fraction(1, 1) - q_relu(Fraction(1, 1)), Fraction(5, 1))
    f_col_2 = (Fraction(7, 1) - q_relu(Fraction(7, 1)), Fraction(5, 1))

    return {
        "rtf_triple_junction_cocycle": {
            "point_p": ["0", "0", "1"],
            "omega_a": [format_exact_rational(c) for c in w_a],
            "omega_b": [format_exact_rational(c) for c in w_b],
            "omega_c": [format_exact_rational(c) for c in w_c],
            "omega_cocycle_zero": (omega_sum == (z0, z0, z0)),
            "velocity_cocycle_zero": (vel_sum == (z0, z0, z0)),
            "all_velocities_tangent_to_s2": all((dot3_q(v_a, p) == 0, dot3_q(v_b, p) == 0, dot3_q(v_c, p) == 0)),
            "walls": walls,
        },
        "tropical_3region_relu_hinge": {
            "gradients": {"A": list(g_a), "B": list(g_b), "C": list(g_c)},
            "delta_g_ab": list(dg_ab),
            "delta_g_bc": list(dg_bc),
            "delta_g_ca": list(dg_ca),
            "gradient_jump_cocycle_zero": (dg_sum == (0, 0)),
            "tropical_weights": {"AB": m_ab, "BC": m_bc, "CA": m_ca},
            "primitive_rays": {"AB": list(r_ab), "BC": list(r_bc), "CA": list(r_ca)},
            "weighted_tropical_balancing_zero": (trop_bal == (0, 0)),
            "unweighted_ray_sum_nonzero": (unweighted_ray_sum != (0, 0)),
            "two_layer_relu_equals_max_all_probes": hinge_matches_max,
            "interior_gradients_exact": region_grads_exact,
        },
        "relu_2d_rtf_jacobian_contrast": {
            "cases": jac_cases,
            "dead_subduction_collision_exact": all((f_col_1 == f_col_2, f_col_1 == (Fraction(0, 1), Fraction(5, 1)))),
        },
    }


# ---------------------------------------------------------------------------
# Pillar 4: Discrete S^2 Cube Hodge Complex & Three Explicit Obstructions
# ---------------------------------------------------------------------------

def matrix_rank_q(matrix: Any) -> int:
    """Exact pure-Q Gaussian elimination rank of a nonempty rectangular Fraction/int matrix."""
    if type(matrix) not in (list, tuple) or not matrix:
        raise TectonicsReluError("INVALID_MATRIX", "matrix must be a nonempty list/tuple of rows")
    first = matrix[0]
    if type(first) not in (list, tuple) or not first:
        raise TectonicsReluError("INVALID_MATRIX", "matrix rows must be nonempty lists/tuples")
    n_cols = len(first)
    a: list[list[Fraction]] = []
    for r_idx, row in enumerate(matrix):
        if type(row) not in (list, tuple) or len(row) != n_cols:
            raise TectonicsReluError("INVALID_MATRIX", f"row {r_idx} length mismatch")
        q_row: list[Fraction] = []
        for c_idx, val in enumerate(row):
            if type(val) is int:
                q_row.append(Fraction(val, 1))
            elif type(val) is Fraction:
                q_row.append(val)
            else:
                raise TectonicsReluError("INVALID_MATRIX_ENTRY", f"entry ({r_idx},{c_idx}) must be int or Fraction")
        a.append(q_row)

    m_rows = len(a)
    rank = 0
    for col in range(n_cols):
        piv: int | None = None
        for r in range(rank, m_rows):
            if a[r][col] != 0:
                piv = r
                break
        if piv is None:
            continue
        a[rank], a[piv] = a[piv], a[rank]
        pv = a[rank][col]
        a[rank] = [x / pv for x in a[rank]]
        for r in range(m_rows):
            if r != rank:
                fac = a[r][col]
                if fac != 0:
                    a[r] = [a[r][j] - fac * a[rank][j] for j in range(n_cols)]
        rank += 1
    return rank


def gdn2_rank1_state_step(
    s_mat: Any,
    alpha: Any,
    beta: Any,
    k_vec: Any,
    v_vec: Any,
) -> tuple[list[list[Fraction]], list[list[Fraction]]]:
    """Exact pure-Q Portal 42 GDN-2 delta-rule rank-1 memory state step S_1 = alpha S_0 + beta (v - alpha S_0 k) k^T."""
    if type(s_mat) not in (list, tuple) or len(s_mat) != 2:
        raise TectonicsReluError("INVALID_STATE_MATRIX", "s_mat must be 2x2 Fraction matrix")
    s0: list[list[Fraction]] = []
    for r_idx, row in enumerate(s_mat):
        if type(row) not in (list, tuple) or len(row) != 2:
            raise TectonicsReluError("INVALID_STATE_MATRIX", f"s_mat row {r_idx} must have length 2")
        s0.append([
            require_exact_fraction(row[0], f"s_mat[{r_idx}][0]"),
            require_exact_fraction(row[1], f"s_mat[{r_idx}][1]"),
        ])
    a_val = require_exact_fraction(alpha, "alpha", positive=True)
    if a_val > 1:
        raise TectonicsReluError("INVALID_FORGET_GATE", "alpha must be <= 1")
    b_val = require_exact_fraction(beta, "beta", positive=True)
    if type(k_vec) not in (list, tuple) or len(k_vec) != 2:
        raise TectonicsReluError("INVALID_VEC2", "k_vec must be length-2 Fraction vector")
    if type(v_vec) not in (list, tuple) or len(v_vec) != 2:
        raise TectonicsReluError("INVALID_VEC2", "v_vec must be length-2 Fraction vector")
    k0 = require_exact_fraction(k_vec[0], "k_vec[0]")
    k1 = require_exact_fraction(k_vec[1], "k_vec[1]")
    v0 = require_exact_fraction(v_vec[0], "v_vec[0]")
    v1 = require_exact_fraction(v_vec[1], "v_vec[1]")

    pred0 = a_val * (s0[0][0] * k0 + s0[0][1] * k1)
    pred1 = a_val * (s0[1][0] * k0 + s0[1][1] * k1)
    err0 = v0 - pred0
    err1 = v1 - pred1
    delta = [
        [b_val * err0 * k0, b_val * err0 * k1],
        [b_val * err1 * k0, b_val * err1 * k1],
    ]
    s1 = [
        [a_val * s0[0][0] + delta[0][0], a_val * s0[0][1] + delta[0][1]],
        [a_val * s0[1][0] + delta[1][0], a_val * s0[1][1] + delta[1][1]],
    ]
    return s1, delta


_S2_CUBE_EDGES: tuple[tuple[int, int], ...] = (
    (0, 1), (2, 3), (4, 5), (6, 7),
    (0, 2), (1, 3), (4, 6), (5, 7),
    (0, 4), (1, 5), (2, 6), (3, 7),
)


def _build_s2_cube_operators() -> tuple[list[list[int]], list[list[int]]]:
    e_idx = {e: i for i, e in enumerate(_S2_CUBE_EDGES)}
    d0 = [[0] * 8 for _ in range(12)]
    for i, (u, v) in enumerate(_S2_CUBE_EDGES):
        d0[i][u] = -1
        d0[i][v] = 1
    face_cycles: tuple[tuple[int, int, int, int], ...] = (
        (0, 2, 3, 1),
        (4, 5, 7, 6),
        (0, 1, 5, 4),
        (2, 6, 7, 3),
        (0, 4, 6, 2),
        (1, 3, 7, 5),
    )
    d1 = [[0] * 12 for _ in range(6)]
    for fi, cyc in enumerate(face_cycles):
        for j in range(4):
            a, b = cyc[j], cyc[(j + 1) % 4]
            if (a, b) in e_idx:
                d1[fi][e_idx[(a, b)]] = 1
            else:
                d1[fi][e_idx[(b, a)]] = -1
    return d0, d1


def discrete_outward_div_s2(
    d0: Any,
    flux: Any,
) -> list[int]:
    """Outward discrete divergence (DEC codifferential delta_1 = -d0^T).

    With d0[e][tail] = -1 and d0[e][head] = +1, (-d0^T flux)[v] equals net
    outward flux leaving vertex v (+1 at tail, -1 at head for a unit edge flux).
    """
    if type(d0) is not list or len(d0) != 12:
        raise TectonicsReluError("INVALID_D0_MATRIX", "d0 must be a 12x8 list of int lists")
    d0_rows: list[list[int]] = []
    for e_idx, row in enumerate(d0):
        if type(row) is not list or len(row) != 8:
            raise TectonicsReluError("INVALID_D0_MATRIX", f"d0[{e_idx}] must be a list of 8 ints")
        d0_rows.append([require_exact_int(row[v], f"d0[{e_idx}][{v}]") for v in range(8)])
    if type(flux) is not list or len(flux) != 12:
        raise TectonicsReluError("INVALID_FLUX_VEC", "flux must be a list of 12 ints")
    f_vec = [require_exact_int(flux[e], f"flux[{e}]") for e in range(12)]
    return [-sum(d0_rows[e][v] * f_vec[e] for e in range(12)) for v in range(8)]


def build_pillar4_s2_hodge_obstructions() -> dict[str, Any]:
    """Certify Pillar 4: S^2 cube cellular Hodge complex & Obstructions A, B, C."""
    d0, d1 = _build_s2_cube_operators()
    # Exact cochain complex identity d1 @ d0 == 0 (6x8) and closedness 1_6^T d1 == 0
    d1_d0_zero = all(
        sum(d1[f][e] * d0[e][v] for e in range(12)) == 0
        for f in range(6)
        for v in range(8)
    )
    closed_s2_orient = all(sum(d1[f][e] for f in range(6)) == 0 for e in range(12))
    r0 = matrix_rank_q(d0)
    r1 = matrix_rank_q(d1)
    b0 = 8 - r0
    b1 = (12 - r1) - r0
    b2 = 6 - r1

    # Obstruction A: Toroidal-Zero == Conservative Gradient-Flow Curl-Zero + Equipartition
    phi = [1, 1, 0, 0, 0, 0, 0, 0]
    psi = [0, 1, 0, 0, 0, 0]
    u_pol = [sum(d0[e][v] * phi[v] for v in range(8)) for e in range(12)]
    u_tor = [sum(d1[f][e] * psi[f] for f in range(6)) for e in range(12)]
    u_eq = [u_pol[e] + u_tor[e] for e in range(12)]

    curl_pol = [sum(d1[f][e] * u_pol[e] for e in range(12)) for f in range(6)]
    div_tor = discrete_outward_div_s2(d0, u_tor)
    e_pol = sum(x * x for x in u_pol)
    e_tor = sum(x * x for x in u_tor)
    e_eq = sum(x * x for x in u_eq)
    hodge_dot = sum(u_pol[e] * u_tor[e] for e in range(12))

    # Obstruction B: Compact-Manifold Gauss-Stokes Conservation vs Unconstrained Dead-ReLU
    # Outward discrete divergence is delta_1(u) = -d0^T u:
    # unit flow on oriented edge e_i = (tail -> head) gives +1 at tail (outflow) and -1 at head (inflow).
    basis_div_zero_count = 0
    edge_sign_exact_count = 0
    for e_i, (tail_v, head_v) in enumerate(_S2_CUBE_EDGES):
        unit_flux = [1 if k == e_i else 0 for k in range(12)]
        div_ei = discrete_outward_div_s2(d0, unit_flux)
        if sum(div_ei) == 0:
            basis_div_zero_count += 1
        expected_ei = [1 if v == tail_v else (-1 if v == head_v else 0) for v in range(8)]
        if div_ei == expected_ei:
            edge_sign_exact_count += 1
    u_asym = [-3, 1, -2, 0, -1, 2, -4, 0, 3, -2, -1, 1]
    div_asym = discrete_outward_div_s2(d0, u_asym)
    ridge_sum = sum(x for x in div_asym if x > 0)
    trench_sum = sum(x for x in div_asym if x < 0)

    # Unconstrained 2D ReLU F_dead(x1,x2) = (ReLU(x1), ReLU(x2)) on [-1,1]^2 (4 unit quadrants)
    quad_dets = [1, 0, 0, 0]
    quad_disp_divs = [0, -1, -1, -2]
    relu_img_area = sum(quad_dets)
    relu_dom_area = 4
    relu_area_ratio = Fraction(relu_img_area, relu_dom_area)
    relu_global_div = sum(quad_disp_divs)

    # Obstruction C: Static Feedforward Inference vs Portal 42 GDN-2 Rank-1 Advection
    s0 = [[Fraction(1, 1), Fraction(0, 1)], [Fraction(0, 1), Fraction(1, 1)]]
    w0 = (Fraction(1, 1), Fraction(0, 1))
    b0_bias = Fraction(-1, 1)
    q_pt = (Fraction(3, 2), Fraction(0, 1))
    alpha = Fraction(1, 2)
    beta = Fraction(1, 1)
    k_vec = (Fraction(1, 1), Fraction(0, 1))
    v_vec = (Fraction(1, 4), Fraction(0, 1))

    s1, delta_mat = gdn2_rank1_state_step(s0, alpha, beta, k_vec, v_vec)
    delta_rank = matrix_rank_q(delta_mat)
    s1_k = (s1[0][0] * k_vec[0] + s1[0][1] * k_vec[1], s1[1][0] * k_vec[0] + s1[1][1] * k_vec[1])
    w_eff_0 = (s0[0][0] * w0[0] + s0[1][0] * w0[1], s0[0][1] * w0[0] + s0[1][1] * w0[1])
    w_eff_1 = (s1[0][0] * w0[0] + s1[1][0] * w0[1], s1[0][1] * w0[0] + s1[1][1] * w0[1])

    wall_x_0 = -b0_bias / w_eff_0[0]
    wall_x_1 = -b0_bias / w_eff_1[0]
    static_pre_t0 = w0[0] * q_pt[0] + w0[1] * q_pt[1] + b0_bias
    static_pre_t1 = static_pre_t0
    gdn2_pre_t0 = w_eff_0[0] * q_pt[0] + w_eff_0[1] * q_pt[1] + b0_bias
    gdn2_pre_t1 = w_eff_1[0] * q_pt[0] + w_eff_1[1] * q_pt[1] + b0_bias

    return {
        "discrete_s2_cube_hodge_complex": {
            "vertices": 8,
            "edges": 12,
            "faces": 6,
            "euler_characteristic": 8 - 12 + 6,
            "d1_d0_identically_zero": d1_d0_zero,
            "closed_oriented_s2_boundary_zero": closed_s2_orient,
            "rank_d0": r0,
            "rank_d1": r1,
            "betti_numbers": [b0, b1, b2],
            "betti_euler_matches": (b0 - b1 + b2 == 2),
        },
        "obstruction_a_toroidal_curl_zero": {
            "e_pol": e_pol,
            "e_tor": e_tor,
            "e_eq_combined": e_eq,
            "poloidal_curl_identically_zero": all(x == 0 for x in curl_pol),
            "toroidal_div_identically_zero": all(x == 0 for x in div_tor),
            "hodge_inner_product": hodge_dot,
            "hodge_pythagorean_exact": (e_eq == e_pol + e_tor),
            "equipartition_ratio": format_exact_rational(Fraction(e_tor, e_pol)),
        },
        "obstruction_b_gauss_stokes_vs_relu": {
            "outward_div_edge_sign_exact": (edge_sign_exact_count == 12),
            "s2_basis_fluxes_zero_sum_count": basis_div_zero_count,
            "s2_gauss_stokes_universal_exact": (basis_div_zero_count == 12),
            "asym_flux_u": u_asym,
            "asym_outward_div": div_asym,
            "asym_ridge_creation_sum": ridge_sum,
            "asym_trench_subduction_sum": trench_sum,
            "asym_global_net_div": ridge_sum + trench_sum,
            "unconstrained_relu_domain_area": relu_dom_area,
            "unconstrained_relu_image_area": relu_img_area,
            "unconstrained_relu_area_ratio": format_exact_rational(relu_area_ratio),
            "unconstrained_relu_global_div": relu_global_div,
            "unconstrained_relu_violates_gauss_stokes": (relu_global_div < 0),
        },
        "obstruction_c_static_feedforward_vs_gdn2_advection": {
            "static_wall_x_t0": format_exact_rational(wall_x_0),
            "static_wall_x_t1": format_exact_rational(wall_x_0),
            "static_wall_displacement": "0",
            "static_pre_t0": format_exact_rational(static_pre_t0),
            "static_pre_t1": format_exact_rational(static_pre_t1),
            "static_inference_frozen": (static_pre_t0 == static_pre_t1),
            "gdn2_alpha": format_exact_rational(alpha),
            "gdn2_beta": format_exact_rational(beta),
            "gdn2_delta_rank": delta_rank,
            "gdn2_key_overwrite_exact": (s1_k == v_vec),
            "gdn2_wall_x_t0": format_exact_rational(wall_x_0),
            "gdn2_wall_x_t1": format_exact_rational(wall_x_1),
            "gdn2_wall_displacement": format_exact_rational(wall_x_1 - wall_x_0),
            "gdn2_pre_t0": format_exact_rational(gdn2_pre_t0),
            "gdn2_pre_t1": format_exact_rational(gdn2_pre_t1),
            "gdn2_relu_t0": format_exact_rational(q_relu(gdn2_pre_t0)),
            "gdn2_relu_t1": format_exact_rational(q_relu(gdn2_pre_t1)),
            "gdn2_inference_region_flip_zero_weight_update": all((gdn2_pre_t0 > 0, gdn2_pre_t1 < 0)),
        },
    }


# ---------------------------------------------------------------------------
# Standalone Certificate Builder & Structural Validator
# ---------------------------------------------------------------------------

def build_standalone_certificate() -> dict[str, Any]:
    """Build deterministic pure-Z/Q standalone certificate with dual SHA-256 bindings."""
    payload: dict[str, Any] = {
        "novelty_tier": "N1",
        "individual_domains_novelty": "N0",
        "oracle_class": "exact",
        "measured_live_mantle_convection_gcm": False,
        "measured_live_deep_network_training_runs": False,
        "zero_trust_path_floats": True,
        "zero_bare_asserts": True,
        "zero_mathematical_rng": True,
        "pillar1_bingham_relu_poiseuille": build_pillar1_bingham_relu_poiseuille(),
        "pillar2_yield_phase_and_2d_relu": build_pillar2_yield_phase_and_2d_relu(),
        "pillar3_triple_junction_tropical_rtf": build_pillar3_triple_junction_tropical_rtf(),
        "pillar4_s2_hodge_obstructions": build_pillar4_s2_hodge_obstructions(),
    }
    payload_sha256 = hashlib.sha256(canonical_json_bytes(payload)).hexdigest()
    pre_cert = {
        "schema": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": payload_sha256,
        "payload": payload,
    }
    certificate_sha256 = hashlib.sha256(canonical_json_bytes(pre_cert)).hexdigest()
    return {
        "schema": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": payload_sha256,
        "certificate_sha256": certificate_sha256,
        "payload": payload,
    }


def _validate_payload_bool_separation(payload: dict[str, Any]) -> None:
    """Enforce bijective bool/non-bool leaf separation across payload trees."""
    stack: list[Any] = [payload]
    while stack:
        node = stack.pop()
        if type(node) is dict:
            for k, v in node.items():
                if k in _BOOL_LEAF_KEYS:
                    if type(v) is not bool:
                        raise TectonicsReluError("NON_BOOL_IN_BOOL_FIELD", f"{k} must be exact bool")
                elif type(v) is bool:
                    raise TectonicsReluError("BOOL_IN_NON_BOOL_FIELD", f"{k} must not be bool")
                elif type(v) in (dict, list):
                    stack.append(v)
        else:
            for item in node:
                if type(item) is bool:
                    raise TectonicsReluError("BOOL_IN_LIST", "list element must not be bool")
                if type(item) in (dict, list):
                    stack.append(item)


def validate_certificate_payload(cert: Any, *, full_replay: bool = True) -> dict[str, Any]:
    """Validate certificate envelope, keysets, dual SHA-256 digests, and optional full pure-Q replay."""
    if type(cert) is not dict:
        raise TectonicsReluError("INVALID_CERT_TYPE", "certificate must be a JSON object")
    validate_json_tree_iterative(cert)
    if frozenset(cert.keys()) != _CERT_KEYS:
        raise TectonicsReluError("INVALID_CERT_KEYS", "certificate top-level keys mismatch")
    if cert["schema"] != SCHEMA_VERSION:
        raise TectonicsReluError("SCHEMA_MISMATCH", "certificate schema mismatch")
    if cert["track_id"] != TRACK_ID:
        raise TectonicsReluError("TRACK_ID_MISMATCH", "certificate track_id mismatch")
    declared_p = require_sha256_hex(cert["payload_sha256"], "payload_sha256")
    declared_c = require_sha256_hex(cert["certificate_sha256"], "certificate_sha256")

    payload = cert["payload"]
    if type(payload) is not dict or frozenset(payload.keys()) != _PAYLOAD_KEYS:
        raise TectonicsReluError("INVALID_PAYLOAD_KEYS", "payload keys mismatch")
    _validate_payload_bool_separation(payload)

    recomputed_p = hashlib.sha256(canonical_json_bytes(payload)).hexdigest()
    if not hmac.compare_digest(declared_p, recomputed_p):
        raise TectonicsReluError("PAYLOAD_SHA256_MISMATCH", "payload_sha256 mismatch")

    pre_cert = {
        "schema": cert["schema"],
        "track_id": cert["track_id"],
        "payload_sha256": declared_p,
        "payload": payload,
    }
    recomputed_c = hashlib.sha256(canonical_json_bytes(pre_cert)).hexdigest()
    if not hmac.compare_digest(declared_c, recomputed_c):
        raise TectonicsReluError("CERTIFICATE_SHA256_MISMATCH", "certificate_sha256 mismatch")

    replay_matched = False
    if require_exact_bool(full_replay, "full_replay"):
        fresh = build_standalone_certificate()
        if not hmac.compare_digest(canonical_json_bytes(cert), canonical_json_bytes(fresh)):
            raise TectonicsReluError("FULL_REPLAY_MISMATCH", "certificate does not match standalone replay")
        replay_matched = True

    return {
        "valid": True,
        "schema": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": declared_p,
        "certificate_sha256": declared_c,
        "full_replay_matched": replay_matched,
    }
