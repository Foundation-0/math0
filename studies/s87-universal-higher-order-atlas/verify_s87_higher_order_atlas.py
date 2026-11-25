#!/usr/bin/env python3
"""
Track S87 Hardened Standalone Verifier, Upstream Manifest Auditor & R10+ Lean 4.36.0 Gate.

Supports:
  --standalone --json         Compute and emit canonical zero-float certificate JSON to stdout
  --write <cert.json>         Atomically write canonical 0o600 certificate JSON via dir_fd + fsync
  --check <cert.json>         Fail-closed Zone-B hardened verification of certificate JSON on disk
  --verify-lean <file.lean>   Full R10+ static Lean 4 audit + live Lean 4.36.0 axiom check
  --verify-upstream <dir>     Verify all 24 pinned upstream corpus certificate SHA-256s on disk

Zero floats on trust paths, zero bare asserts, zero external dependencies, zero RNG calls.
"""
from __future__ import annotations

import argparse
import errno
from fractions import Fraction
import hashlib
import hmac
import json
import math
import os
from pathlib import Path
import re
import secrets
import shutil
import stat
import subprocess
import sys
import threading
from typing import Any

_SCRIPT_DIR = str(Path(__file__).resolve().parent)
if _SCRIPT_DIR not in sys.path:
    sys.path.insert(0, _SCRIPT_DIR)

from s87_higher_order_atlas_oracle import (
    CERT_SCHEMA,
    CERT_TRACK_ID,
    LEAN_FILE_NAME,
    LEAN_FILE_SHA256,
    LEAN_THEOREMS,
    MAX_INT_BITS,
    MAX_JSON_DEPTH,
    S87Error,
    UPSTREAM_CERT_MANIFEST,
    build_certificate,
    canonical_json_bytes,
    require_ok,
)

MAX_JSON_BYTES = 1_048_576
_READ_CHUNK_BYTES = 65_536
MAX_INT_DIGITS = 617
_HEX_LOWER = frozenset("0123456789abcdef")
_CERT_KEYS = frozenset({"schema", "track_id", "payload_sha256", "certificate_sha256", "payload"})
_RAT_KEYS = frozenset({"num", "den"})
_PAYLOAD_KEYS = frozenset(
    {
        "pillar1_meta_a_competing_potential",
        "pillar2_meta_b_grafting_proxy_blindness",
        "pillar3_meta_c_f2_three_wall_fracture",
        "pillar4_meta_d_ceer_closed_loop_fixed_point",
        "pillar5_corpus_provenance_and_lean4",
    }
)
_P1_KEYS = frozenset(
    {
        "s71_quartic_barrier_flip",
        "universal_linear_threshold_model",
        "s71_mesi_repulsion_ratio_q",
        "s71_mesi_repulsion_dec",
        "s71_read_fusion_ratio_q",
        "s71_read_fusion_dec",
        "s59_opposite_sign_anisotropy_inversion_q",
        "s59_e8_regime_delta_q",
        "s59_a16_regime_delta_q",
        "s59_a16_matched_kl_ratio_q",
        "s73_3bpw_rel_drop_q",
        "s73b_4p5bpw_rel_drop_q",
        "s73_vs_s73b_lowbit_amplification_q",
        "s73_vs_s73b_lowbit_amplification_dec",
        "s28_adm_null_witness_q",
        "s33_hopf_inertia_flip",
        "s34_rosen_cusp_roots",
        "law5_three_regime_obstruction",
        "pillar_verified",
    }
)
_P1_S71Q_KEYS = frozenset(
    {"a", "b", "c", "r_below", "r_at_barrier", "delta_pot_r_below", "delta_pot_r_at_barrier", "sign_flip_exact"}
)
_P1_LIN_KEYS = frozenset({"slope_q", "r_star_q", "r_lo_q", "r_hi_q", "v_lo_q", "v_hi_q", "sign_flip_exact"})
_P1_L5_KEYS = frozenset(
    {
        "strictly_euclidean_2x2",
        "degenerate_rank1_2x2",
        "strictly_cat0_s75_2x2",
        "s81_r3_gram4_det_q",
        "s81_r3_gram3_minor_det_q",
        "naive_isometry_blocked",
    }
)
_SYLV_KEYS = frozenset(
    {
        "p_q",
        "q_q",
        "s_q",
        "det_q",
        "inertia_pos_zero_neg",
        "regime",
        "witness_vec_q",
        "witness_quadform_q",
        "sylvester_identity_exact",
    }
)
_P2_KEYS = frozenset(
    {
        "ambient_dimension_lift",
        "s31_iso_mdl_concentration_q",
        "s31_selective_omission_ratio_q",
        "s50_zero_dw_transport",
        "s42_kintsugi_avg_kl_q",
        "s77_mellin_granite_gamma_nl_sq_q",
        "s77_mellin_active_push_exact",
        "s77_wsp_cs08_all_delta_q",
        "s77_wsp_cs08_finished_delta_q",
        "s81_portal77_kyfan_ppl_width_wall_q",
        "s81_motifbench_group3",
        "law5_redundant_oracle_obstruction",
        "pillar_verified",
    }
)
_LIFT_KEYS = frozenset(
    {
        "base_dim",
        "lifted_dim",
        "inner_product_q",
        "base_norm_sq_q",
        "graft_norm_sq_q",
        "combined_norm_sq_q",
        "exact_orthogonality",
        "pythagorean_exact",
    }
)
_S50_KEYS = frozenset(
    {
        "margin_before_q",
        "margin_after_q",
        "margin_delta_q",
        "delta_s_frob_norm_sq_q",
        "yield_wall_advection_before",
        "yield_wall_advection_after",
        "orthogonal_probe_delta_q",
        "zero_delta_w",
    }
)
_S81_G3_KEYS = frozenset(
    {
        "group1_solved_of_10",
        "group3_solved_of_10",
        "k3_holonomy_dof",
        "orphan_drop_q",
        "orphan_drop_dec",
        "dual_oracle_bayes_ppv",
    }
)
_PPV_KEYS = frozenset(
    {
        "single_ppv_q",
        "dual_ppv_q",
        "ppv_gain_q",
        "ppv_amplification_ratio_q",
        "ppv_amplification_dec",
        "strict_amplification",
    }
)
_P3_KEYS = frozenset(
    {
        "wall1_carry_obstruction",
        "wall2_non_orthogonality_obstruction",
        "wall3_boundary_offload_obstruction",
        "law5_three_wall_mutual_independence",
        "pillar_verified",
    }
)
_W1_KEYS = frozenset(
    {
        "active_carry_witness",
        "carry_free_control",
        "s22c_f2x_odd_polys_deg2_to_24",
        "s22c_odd_perfects_found",
        "s41_polya_total_f2_tables",
        "s41_polya_valid_sign_flips",
        "s41_praxis_sos_det_q",
    }
)
_CARRY_KEYS = frozenset(
    {"a", "b", "f2_xor_sum", "carry_bits", "z_integer_sum", "carry_defect", "carry_wall_active"}
)
_W2_KEYS = frozenset(
    {
        "s82_cnot_circuits_verified",
        "shear_det_q",
        "shear_gram_trace_q",
        "shear_gram_det_q",
        "kappa2_bracket_lo_q",
        "kappa2_bracket_hi_q",
        "charpoly_at_lo_q",
        "charpoly_at_hi_q",
        "s59_hadamard_q4_exact_orthogonal",
        "s59_hadamard_kappa2_q",
    }
)
_W3_KEYS = frozenset({"s54_cs21_mirage", "s54_cs21_genuine_uncompute"})
_CS21_KEYS = frozenset(
    {
        "baseline_total",
        "candidate_total",
        "apparent_ratio_q",
        "true_net_ratio_q",
        "true_net_ratio_dec",
        "candidate_hidden_share_q",
        "mirage_detected",
        "genuine_net_improvement",
    }
)
_P3_L5_KEYS = frozenset(
    {"wall1_only_fails", "wall2_only_fails", "wall3_only_fails", "all_three_walls_independent"}
)
_P4_KEYS = frozenset(
    {
        "s76_loop_schur_rho_q",
        "s76_gd_cliff_eta_q",
        "s76_g_loop_det_q",
        "s83_firewall_direct_flux_before",
        "s83_firewall_direct_flux_after",
        "s83_edge_retention_q",
        "s83_triangle_retention_q",
        "s80_songe_1night_fwer_q",
        "s80_songe_20night_fwer_dec",
        "s80_ratchet_clean_outside_accepts",
        "s80_ratchet_goodhart_accepts",
        "s82_dual_kernel_negative_controls_killed",
        "s82_dual_kernel_negative_controls_total",
        "certified_five_gate_fixed_point",
        "borromean_five_gate_ablations",
        "all_five_ablations_rejected",
        "pillar_verified",
    }
)
_CEER_STEP_KEYS = frozenset(
    {
        "gate1_loop_schur_contractive",
        "gate2_law3_firewall_clean",
        "gate3_anti_goodhart_clean",
        "gate4_dual_kernel_clean",
        "gate5_cs21_net_gain",
        "all_five_gates_pass",
        "error_after_steps_q",
        "net_cost_ratio_q",
    }
)
_ABLATION_TARGET_GATE: tuple[tuple[str, str], ...] = (
    ("ablate_g1_contraction_s76", "gate1_loop_schur_contractive"),
    ("ablate_g2_firewall_s83", "gate2_law3_firewall_clean"),
    ("ablate_g3_ratchet_s80", "gate3_anti_goodhart_clean"),
    ("ablate_g4_dual_kernel_s82", "gate4_dual_kernel_clean"),
    ("ablate_g5_cs21_cost_s54", "gate5_cs21_net_gain"),
)
_ABLATION_KEYS = frozenset(k for k, _ in _ABLATION_TARGET_GATE)
_GATE_NAMES = tuple(g for _, g in _ABLATION_TARGET_GATE)
_P5_KEYS = frozenset({"upstream_corpus_count", "upstream_cert_manifest", "lean4_certificate", "novelty_honesty_law4"})
_MANIFEST_ENTRY_KEYS = frozenset({"track_id", "rel_path", "sha256"})
_LEAN_CERT_KEYS = frozenset({"file", "sha256", "theorem_count", "theorems", "allowed_axioms"})
_NOVELTY_KEYS = frozenset({"novelty_tier", "n0_prior_art_anchored", "n1_exact_synthesis_verified", "n2_claims"})
_PAYLOAD_BOOL_KEYS = frozenset(
    {
        "all_five_ablations_rejected",
        "all_five_gates_pass",
        "all_three_walls_independent",
        "carry_wall_active",
        "exact_orthogonality",
        "gate1_loop_schur_contractive",
        "gate2_law3_firewall_clean",
        "gate3_anti_goodhart_clean",
        "gate4_dual_kernel_clean",
        "gate5_cs21_net_gain",
        "genuine_net_improvement",
        "mirage_detected",
        "n0_prior_art_anchored",
        "n1_exact_synthesis_verified",
        "naive_isometry_blocked",
        "pillar_verified",
        "pythagorean_exact",
        "s59_hadamard_q4_exact_orthogonal",
        "sign_flip_exact",
        "single_proxy_blind_on_orthogonal_probe",
        "strict_amplification",
        "sylvester_identity_exact",
        "zero_delta_w",
    }
)
_EXACT_PATH_TYPES = (Path, type(Path()))
_TEMP_NAME_LOCK = threading.Lock()
_ALLOWED_LEAN_AXIOMS = frozenset({"propext"})


# ---------------------------------------------------------------------------
# Strict Zone-B Zero-Float JSON, Rational & Digest Primitives
# ---------------------------------------------------------------------------

def validate_json_tree_iterative(obj: Any, max_depth: int = MAX_JSON_DEPTH) -> None:
    if type(max_depth) is not int or max_depth < 1 or max_depth > 256:
        raise S87Error("INVALID_MAX_DEPTH", "max_depth must be int in [1, 256]")
    stack: list[tuple[Any, int]] = [(obj, 0)]
    while stack:
        cur, depth = stack.pop()
        if depth > max_depth:
            raise S87Error("JSON_DEPTH_EXCEEDED", f"nesting depth > {max_depth}")
        t = type(cur)
        if t is dict:
            for k, v in cur.items():
                if type(k) is not str:
                    raise S87Error("NON_STR_KEY", "dict keys must be strict str")
                try:
                    k.encode("utf-8")
                except UnicodeEncodeError as exc:
                    raise S87Error("INVALID_UNICODE_STR", f"lone surrogate key: {exc}") from exc
                stack.append((v, depth + 1))
        elif t is list:
            for item in cur:
                stack.append((item, depth + 1))
        elif t is int:
            if cur.bit_length() > MAX_INT_BITS:
                raise S87Error("INT_BIT_LIMIT", f"int exceeds {MAX_INT_BITS} bits")
        elif t is str:
            try:
                cur.encode("utf-8")
            except UnicodeEncodeError as exc:
                raise S87Error("INVALID_UNICODE_STR", f"lone surrogate str: {exc}") from exc
        elif t is bool or cur is None:
            continue
        else:
            raise S87Error("FORBIDDEN_JSON_TYPE", f"forbidden JSON value type: {t.__name__}")


def _no_dups_hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise S87Error("DUPLICATE_JSON_KEY", f"duplicate key: {k}")
        out[k] = v
    return out


def _forbid_float(token: str) -> Any:
    raise S87Error("FLOAT_FORBIDDEN", f"float literal forbidden: {token}")


def _forbid_constant(token: str) -> Any:
    raise S87Error("NONFINITE_CONSTANT", f"non-finite constant forbidden: {token}")


def _parse_capped_int_token(token: str) -> int:
    digits = token[1:] if token.startswith("-") else token
    if len(digits) > MAX_INT_DIGITS:
        raise S87Error("INT_DIGIT_LIMIT", f"integer token exceeds {MAX_INT_DIGITS} digits")
    val = int(token)
    if val.bit_length() > MAX_INT_BITS:
        raise S87Error("INT_BIT_LIMIT", f"integer token exceeds {MAX_INT_BITS} bits")
    return val


def parse_strict_json(text: str) -> Any:
    if type(text) is not str:
        raise S87Error("INVALID_JSON_TEXT", "JSON text must be strict str")
    try:
        encoded = text.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise S87Error("INVALID_UNICODE_STR", f"lone surrogate in JSON text: {exc}") from exc
    if len(encoded) > MAX_JSON_BYTES:
        raise S87Error("JSON_TOO_LARGE", f"JSON exceeds {MAX_JSON_BYTES} bytes")
    try:
        parsed = json.loads(
            text,
            object_pairs_hook=_no_dups_hook,
            parse_int=_parse_capped_int_token,
            parse_float=_forbid_float,
            parse_constant=_forbid_constant,
        )
    except S87Error:
        raise
    except (json.JSONDecodeError, ValueError, RecursionError) as exc:
        raise S87Error("JSON_DECODE_ERROR", f"invalid JSON: {exc}") from exc
    validate_json_tree_iterative(parsed)
    return parsed


def require_sha256_hex(val: Any, label: str) -> str:
    if type(val) is not str:
        raise S87Error("INVALID_DIGEST_TYPE", f"{label} must be strict str")
    if len(val) != 64:
        raise S87Error("INVALID_DIGEST_LEN", f"{label} must have length 64")
    if any(ch not in _HEX_LOWER for ch in val):
        raise S87Error("INVALID_DIGEST_HEX", f"{label} must be lowercase ASCII hex")
    return val


def exact_typed_equal(lhs: Any, rhs: Any) -> bool:
    """Iterative strict structural + exact-type equality (rejects bool/int swaps & subclasses)."""
    stack: list[tuple[Any, Any]] = [(lhs, rhs)]
    while stack:
        a, b = stack.pop()
        ta, tb = type(a), type(b)
        if ta is not tb:
            return False
        if ta is dict:
            if len(a) != len(b):
                return False
            for k, va in a.items():
                if k not in b:
                    return False
                stack.append((va, b[k]))
        elif ta is list:
            if len(a) != len(b):
                return False
            for va, vb in zip(a, b):
                stack.append((va, vb))
        elif a != b:
            return False
    return True


def _req_dict(obj: Any, expected_keys: frozenset[str], code: str) -> dict[str, Any]:
    require_ok(type(obj) is dict, code, f"{code}: expected strict dict")
    require_ok(frozenset(obj.keys()) == expected_keys, code, f"{code}: exact keys mismatch")
    return obj


def _req_int(obj: Any, code: str) -> int:
    require_ok(type(obj) is int, code, f"{code}: expected exact int")
    return obj


def _parse_rat_dict(obj: Any) -> Fraction:
    if type(obj) is not dict or frozenset(obj.keys()) != _RAT_KEYS:
        raise S87Error("BAD_RATIONAL_DICT", "rational dict must have exact keys {num, den}")
    num_v = obj["num"]
    den_v = obj["den"]
    require_ok(
        type(num_v) is int and type(den_v) is int and den_v > 0 and math.gcd(abs(num_v), den_v) == 1,
        "BAD_RATIONAL_DICT",
        "rational dict must have canonical coprime int num and positive int den",
    )
    return Fraction(num_v, den_v)


def _check_invariants(checks: list[tuple[bool, str]]) -> None:
    for ok, code in checks:
        require_ok(ok, code, f"semantic invariant failed: {code}")


def _audit_sylvester_entry(entry: Any, expected_sign: int) -> None:
    d = _req_dict(entry, _SYLV_KEYS, "BAD_SYLVESTER_SCHEMA")
    p = _parse_rat_dict(d["p_q"])
    q = _parse_rat_dict(d["q_q"])
    s = _parse_rat_dict(d["s_q"])
    det = _parse_rat_dict(d["det_q"])
    w_val = _parse_rat_dict(d["witness_quadform_q"])
    vec = d["witness_vec_q"]
    require_ok(type(vec) is list and len(vec) == 2, "BAD_SYLVESTER_VEC", "witness_vec_q must have 2 rationals")
    vx = _parse_rat_dict(vec[0])
    vy = _parse_rat_dict(vec[1])
    det_sign = 1 if det > 0 else (-1 if det < 0 else 0)
    qform_calc = p * vx * vx + Fraction(2, 1) * q * vx * vy + s * vy * vy
    _check_invariants(
        [
            (p > 0, "BAD_SYLVESTER_INV"),
            (det == p * s - q * q, "BAD_SYLVESTER_INV"),
            (det_sign == expected_sign, "BAD_SYLVESTER_INV"),
            (vx == -q, "BAD_SYLVESTER_INV"),
            (vy == p, "BAD_SYLVESTER_INV"),
            (w_val == qform_calc, "BAD_SYLVESTER_INV"),
            (d["sylvester_identity_exact"] is True, "BAD_SYLVESTER_INV"),
        ]
    )


def _audit_ppv_entry(entry: Any, expect_strict: bool) -> None:
    d = _req_dict(entry, _PPV_KEYS, "BAD_PPV_SCHEMA")
    single = _parse_rat_dict(d["single_ppv_q"])
    dual = _parse_rat_dict(d["dual_ppv_q"])
    gain = _parse_rat_dict(d["ppv_gain_q"])
    amp = _parse_rat_dict(d["ppv_amplification_ratio_q"])
    _check_invariants(
        [
            (single > 0, "BAD_PPV_INV"),
            (dual > 0, "BAD_PPV_INV"),
            (gain == dual - single, "BAD_PPV_INV"),
            (amp == dual / single, "BAD_PPV_INV"),
            (d["strict_amplification"] is expect_strict, "BAD_PPV_INV"),
            ((amp > Fraction(1, 1)) is expect_strict, "BAD_PPV_INV"),
        ]
    )


def _audit_carry_entry(entry: Any, expect_active: bool) -> None:
    d = _req_dict(entry, _CARRY_KEYS, "BAD_CARRY_SCHEMA")
    a = _req_int(d["a"], "BAD_CARRY_INV")
    b = _req_int(d["b"], "BAD_CARRY_INV")
    xor_v = _req_int(d["f2_xor_sum"], "BAD_CARRY_INV")
    carry_v = _req_int(d["carry_bits"], "BAD_CARRY_INV")
    z_sum = _req_int(d["z_integer_sum"], "BAD_CARRY_INV")
    defect = _req_int(d["carry_defect"], "BAD_CARRY_INV")
    _check_invariants(
        [
            (a >= 0, "BAD_CARRY_INV"),
            (b >= 0, "BAD_CARRY_INV"),
            (xor_v == (a ^ b), "BAD_CARRY_INV"),
            (carry_v == (a & b), "BAD_CARRY_INV"),
            (defect == 2 * carry_v, "BAD_CARRY_INV"),
            (z_sum == a + b, "BAD_CARRY_INV"),
            (z_sum == xor_v + defect, "BAD_CARRY_INV"),
            (d["carry_wall_active"] is expect_active, "BAD_CARRY_INV"),
            ((carry_v > 0) is expect_active, "BAD_CARRY_INV"),
        ]
    )


def _audit_cs21_entry(entry: Any, expect_mirage: bool) -> None:
    d = _req_dict(entry, _CS21_KEYS, "BAD_CS21_SCHEMA")
    base_t = _req_int(d["baseline_total"], "BAD_CS21_INV")
    cand_t = _req_int(d["candidate_total"], "BAD_CS21_INV")
    true_r = _parse_rat_dict(d["true_net_ratio_q"])
    _parse_rat_dict(d["apparent_ratio_q"])
    _parse_rat_dict(d["candidate_hidden_share_q"])
    _check_invariants(
        [
            (base_t > 0, "BAD_CS21_INV"),
            (cand_t > 0, "BAD_CS21_INV"),
            (true_r == Fraction(cand_t, base_t), "BAD_CS21_INV"),
            (d["mirage_detected"] is expect_mirage, "BAD_CS21_INV"),
            (d["genuine_net_improvement"] is (not expect_mirage), "BAD_CS21_INV"),
            ((true_r > Fraction(1, 1)) is expect_mirage, "BAD_CS21_INV"),
        ]
    )


def _audit_pillar1(p1: dict[str, Any]) -> None:
    s71q = _req_dict(p1["s71_quartic_barrier_flip"], _P1_S71Q_KEYS, "BAD_P1_S71Q")
    lin = _req_dict(p1["universal_linear_threshold_model"], _P1_LIN_KEYS, "BAD_P1_LIN")
    l5 = _req_dict(p1["law5_three_regime_obstruction"], _P1_L5_KEYS, "BAD_P1_L5")
    s34 = _req_dict(p1["s34_rosen_cusp_roots"], frozenset({"positive_a_root_count", "negative_a_root_count"}), "BAD_P1_S34")
    _audit_sylvester_entry(l5["strictly_euclidean_2x2"], 1)
    _audit_sylvester_entry(l5["degenerate_rank1_2x2"], 0)
    _audit_sylvester_entry(l5["strictly_cat0_s75_2x2"], -1)
    a = _req_int(s71q["a"], "BAD_P1_INV")
    b = _req_int(s71q["b"], "BAD_P1_INV")
    c = _req_int(s71q["c"], "BAD_P1_INV")
    r0 = _req_int(s71q["r_below"], "BAD_P1_INV")
    r1 = _req_int(s71q["r_at_barrier"], "BAD_P1_INV")
    d0 = _req_int(s71q["delta_pot_r_below"], "BAD_P1_INV")
    d1 = _req_int(s71q["delta_pot_r_at_barrier"], "BAD_P1_INV")
    slope = _parse_rat_dict(lin["slope_q"])
    r_star = _parse_rat_dict(lin["r_star_q"])
    r_lo = _parse_rat_dict(lin["r_lo_q"])
    r_hi = _parse_rat_dict(lin["r_hi_q"])
    v_lo = _parse_rat_dict(lin["v_lo_q"])
    v_hi = _parse_rat_dict(lin["v_hi_q"])
    s73_d = _parse_rat_dict(p1["s73_3bpw_rel_drop_q"])
    s73b_d = _parse_rat_dict(p1["s73b_4p5bpw_rel_drop_q"])
    s73_amp = _parse_rat_dict(p1["s73_vs_s73b_lowbit_amplification_q"])
    _check_invariants(
        [
            (p1["pillar_verified"] is True, "BAD_P1_INV"),
            (d0 == b * r0 * (r0 + 1) * (2 * r0 + 1) - a * (r0 * r0 + c) * ((r0 + 1) * (r0 + 1) + c), "BAD_P1_INV"),
            (d1 == b * r1 * (r1 + 1) * (2 * r1 + 1) - a * (r1 * r1 + c) * ((r1 + 1) * (r1 + 1) + c), "BAD_P1_INV"),
            (d0 > 0, "BAD_P1_INV"),
            (d1 < 0, "BAD_P1_INV"),
            (s71q["sign_flip_exact"] is True, "BAD_P1_INV"),
            (slope > 0, "BAD_P1_INV"),
            (v_lo == slope * (r_star - r_lo), "BAD_P1_INV"),
            (v_hi == slope * (r_star - r_hi), "BAD_P1_INV"),
            (v_lo > 0, "BAD_P1_INV"),
            (v_hi < 0, "BAD_P1_INV"),
            (lin["sign_flip_exact"] is True, "BAD_P1_INV"),
            (_parse_rat_dict(p1["s71_mesi_repulsion_ratio_q"]) > Fraction(16, 1), "BAD_P1_INV"),
            (_parse_rat_dict(p1["s71_read_fusion_ratio_q"]) > Fraction(2, 1), "BAD_P1_INV"),
            (_parse_rat_dict(p1["s59_opposite_sign_anisotropy_inversion_q"]) == Fraction(8, 1), "BAD_P1_INV"),
            (_parse_rat_dict(p1["s59_e8_regime_delta_q"]) > 0, "BAD_P1_INV"),
            (_parse_rat_dict(p1["s59_a16_regime_delta_q"]) < 0, "BAD_P1_INV"),
            (s73b_d > 0, "BAD_P1_INV"),
            (s73_amp == s73_d / s73b_d, "BAD_P1_INV"),
            (_parse_rat_dict(p1["s28_adm_null_witness_q"]) < 0, "BAD_P1_INV"),
            (s34["positive_a_root_count"] == 1, "BAD_P1_INV"),
            (s34["negative_a_root_count"] == 3, "BAD_P1_INV"),
            (_parse_rat_dict(l5["s81_r3_gram4_det_q"]) == 0, "BAD_P1_INV"),
            (_parse_rat_dict(l5["s81_r3_gram3_minor_det_q"]) > 0, "BAD_P1_INV"),
            (l5["naive_isometry_blocked"] is True, "BAD_P1_INV"),
        ]
    )


def _audit_pillar2(p2: dict[str, Any]) -> None:
    lift = _req_dict(p2["ambient_dimension_lift"], _LIFT_KEYS, "BAD_P2_LIFT")
    s50 = _req_dict(p2["s50_zero_dw_transport"], _S50_KEYS, "BAD_P2_S50")
    s81 = _req_dict(p2["s81_motifbench_group3"], _S81_G3_KEYS, "BAD_P2_S81")
    l5 = _req_dict(
        p2["law5_redundant_oracle_obstruction"],
        frozenset({"collinear_second_oracle", "single_proxy_blind_on_orthogonal_probe"}),
        "BAD_P2_L5",
    )
    _audit_ppv_entry(s81["dual_oracle_bayes_ppv"], True)
    _audit_ppv_entry(l5["collinear_second_oracle"], False)
    bdim = _req_int(lift["base_dim"], "BAD_P2_INV")
    ldim = _req_int(lift["lifted_dim"], "BAD_P2_INV")
    g1_s = _req_int(s81["group1_solved_of_10"], "BAD_P2_INV")
    g3_s = _req_int(s81["group3_solved_of_10"], "BAD_P2_INV")
    m_bef = _parse_rat_dict(s50["margin_before_q"])
    m_aft = _parse_rat_dict(s50["margin_after_q"])
    m_del = _parse_rat_dict(s50["margin_delta_q"])
    _check_invariants(
        [
            (p2["pillar_verified"] is True, "BAD_P2_INV"),
            (ldim == bdim + 1, "BAD_P2_INV"),
            (_parse_rat_dict(lift["inner_product_q"]) == 0, "BAD_P2_INV"),
            (
                _parse_rat_dict(lift["combined_norm_sq_q"])
                == _parse_rat_dict(lift["base_norm_sq_q"]) + _parse_rat_dict(lift["graft_norm_sq_q"]),
                "BAD_P2_INV",
            ),
            (lift["exact_orthogonality"] is True, "BAD_P2_INV"),
            (lift["pythagorean_exact"] is True, "BAD_P2_INV"),
            (m_bef > 0, "BAD_P2_INV"),
            (m_aft < 0, "BAD_P2_INV"),
            (m_del == m_aft - m_bef, "BAD_P2_INV"),
            (_parse_rat_dict(s50["orthogonal_probe_delta_q"]) == 0, "BAD_P2_INV"),
            (s50["zero_delta_w"] is True, "BAD_P2_INV"),
            (_parse_rat_dict(p2["s77_mellin_granite_gamma_nl_sq_q"]) > 0, "BAD_P2_INV"),
            (_req_int(p2["s77_mellin_active_push_exact"], "BAD_P2_INV") > 0, "BAD_P2_INV"),
            (_parse_rat_dict(p2["s77_wsp_cs08_all_delta_q"]) > 0, "BAD_P2_INV"),
            (_parse_rat_dict(p2["s77_wsp_cs08_finished_delta_q"]) < 0, "BAD_P2_INV"),
            (_parse_rat_dict(p2["s81_portal77_kyfan_ppl_width_wall_q"]) > Fraction(1000, 1), "BAD_P2_INV"),
            (g3_s < g1_s, "BAD_P2_INV"),
            (s81["k3_holonomy_dof"] == 12, "BAD_P2_INV"),
            (l5["single_proxy_blind_on_orthogonal_probe"] is True, "BAD_P2_INV"),
        ]
    )


def _audit_pillar3(p3: dict[str, Any]) -> None:
    w1 = _req_dict(p3["wall1_carry_obstruction"], _W1_KEYS, "BAD_P3_W1")
    w2 = _req_dict(p3["wall2_non_orthogonality_obstruction"], _W2_KEYS, "BAD_P3_W2")
    w3 = _req_dict(p3["wall3_boundary_offload_obstruction"], _W3_KEYS, "BAD_P3_W3")
    l5 = _req_dict(p3["law5_three_wall_mutual_independence"], _P3_L5_KEYS, "BAD_P3_L5")
    _audit_carry_entry(w1["active_carry_witness"], True)
    _audit_carry_entry(w1["carry_free_control"], False)
    _audit_cs21_entry(w3["s54_cs21_mirage"], True)
    _audit_cs21_entry(w3["s54_cs21_genuine_uncompute"], False)
    lo_b = _parse_rat_dict(w2["kappa2_bracket_lo_q"])
    hi_b = _parse_rat_dict(w2["kappa2_bracket_hi_q"])
    p_lo = _parse_rat_dict(w2["charpoly_at_lo_q"])
    p_hi = _parse_rat_dict(w2["charpoly_at_hi_q"])
    _check_invariants(
        [
            (p3["pillar_verified"] is True, "BAD_P3_INV"),
            (w1["s22c_odd_perfects_found"] == 0, "BAD_P3_INV"),
            (w1["s41_polya_valid_sign_flips"] == 0, "BAD_P3_INV"),
            (_parse_rat_dict(w1["s41_praxis_sos_det_q"]) > 0, "BAD_P3_INV"),
            (_parse_rat_dict(w2["shear_det_q"]) == 1, "BAD_P3_INV"),
            (_parse_rat_dict(w2["shear_gram_det_q"]) == 1, "BAD_P3_INV"),
            (_parse_rat_dict(w2["shear_gram_trace_q"]) == 3, "BAD_P3_INV"),
            (p_lo == lo_b * lo_b - 3 * lo_b + 1, "BAD_P3_INV"),
            (p_lo < 0, "BAD_P3_INV"),
            (p_hi == hi_b * hi_b - 3 * hi_b + 1, "BAD_P3_INV"),
            (p_hi > 0, "BAD_P3_INV"),
            (w2["s59_hadamard_q4_exact_orthogonal"] is True, "BAD_P3_INV"),
            (_parse_rat_dict(w2["s59_hadamard_kappa2_q"]) == 1, "BAD_P3_INV"),
            (l5["all_three_walls_independent"] is True, "BAD_P3_INV"),
            (l5["wall1_only_fails"] == [1, 0, 0], "BAD_P3_INV"),
            (l5["wall2_only_fails"] == [0, 1, 0], "BAD_P3_INV"),
            (l5["wall3_only_fails"] == [0, 0, 1], "BAD_P3_INV"),
        ]
    )


def _audit_pillar4(p4: dict[str, Any]) -> None:
    cert_fp = _req_dict(p4["certified_five_gate_fixed_point"], _CEER_STEP_KEYS, "BAD_P4_CERT_FP")
    abls = _req_dict(p4["borromean_five_gate_ablations"], _ABLATION_KEYS, "BAD_P4_ABLS")
    checks: list[tuple[bool, str]] = [
        (p4["pillar_verified"] is True, "BAD_P4_INV"),
        (p4["all_five_ablations_rejected"] is True, "BAD_P4_INV"),
        (cert_fp["all_five_gates_pass"] is True, "BAD_P4_INV"),
        (_parse_rat_dict(cert_fp["error_after_steps_q"]) < Fraction(1, 1), "BAD_P4_INV"),
        (_parse_rat_dict(cert_fp["net_cost_ratio_q"]) < Fraction(1, 1), "BAD_P4_INV"),
        (p4["s80_ratchet_goodhart_accepts"] == 0, "BAD_P4_INV"),
        (p4["s83_firewall_direct_flux_after"] == 0, "BAD_P4_INV"),
        (p4["s82_dual_kernel_negative_controls_killed"] == p4["s82_dual_kernel_negative_controls_total"], "BAD_P4_INV"),
    ]
    for gname in _GATE_NAMES:
        checks.append((cert_fp[gname] is True, "BAD_P4_INV"))
    for abl_key, target_gate in _ABLATION_TARGET_GATE:
        ab = _req_dict(abls[abl_key], _CEER_STEP_KEYS, "BAD_P4_ABL_SCHEMA")
        checks.append((ab["all_five_gates_pass"] is False, "BAD_P4_INV"))
        for gname in _GATE_NAMES:
            checks.append((ab[gname] is (gname != target_gate), "BAD_P4_INV"))
    _check_invariants(checks)


def _audit_pillar5(p5: dict[str, Any]) -> None:
    require_ok(
        p5["upstream_corpus_count"] == len(UPSTREAM_CERT_MANIFEST),
        "BAD_CORPUS_COUNT",
        "upstream_corpus_count mismatch",
    )
    manifest = p5["upstream_cert_manifest"]
    require_ok(
        type(manifest) is list and len(manifest) == len(UPSTREAM_CERT_MANIFEST),
        "BAD_MANIFEST_LIST",
        "upstream_cert_manifest length mismatch",
    )
    for entry, (exp_tid, exp_rel, exp_sha) in zip(manifest, UPSTREAM_CERT_MANIFEST):
        ed = _req_dict(entry, _MANIFEST_ENTRY_KEYS, "BAD_MANIFEST_ENTRY")
        e_sha = require_sha256_hex(ed["sha256"], "upstream_cert_manifest.sha256")
        _check_invariants(
            [
                (ed["track_id"] == exp_tid, "BAD_MANIFEST_PIN"),
                (ed["rel_path"] == exp_rel, "BAD_MANIFEST_PIN"),
                (hmac.compare_digest(e_sha, exp_sha), "BAD_MANIFEST_PIN"),
            ]
        )
    lean_cert = _req_dict(p5["lean4_certificate"], _LEAN_CERT_KEYS, "BAD_LEAN_CERT_SCHEMA")
    lean_sha = require_sha256_hex(lean_cert["sha256"], "lean4_certificate.sha256")
    _check_invariants(
        [
            (lean_cert["file"] == LEAN_FILE_NAME, "BAD_LEAN_PIN"),
            (hmac.compare_digest(lean_sha, LEAN_FILE_SHA256), "BAD_LEAN_PIN"),
            (lean_cert["theorem_count"] == len(LEAN_THEOREMS), "BAD_THEOREM_COUNT"),
            (lean_cert["theorems"] == list(LEAN_THEOREMS), "BAD_THEOREM_LIST"),
            (lean_cert["allowed_axioms"] == ["propext"], "BAD_ALLOWED_AXIOMS"),
        ]
    )
    nov = _req_dict(p5["novelty_honesty_law4"], _NOVELTY_KEYS, "BAD_NOVELTY_SCHEMA")
    _check_invariants(
        [
            (nov["novelty_tier"] == "N1", "BAD_NOVELTY_CLAIMS"),
            (nov["n0_prior_art_anchored"] is True, "BAD_NOVELTY_CLAIMS"),
            (nov["n1_exact_synthesis_verified"] is True, "BAD_NOVELTY_CLAIMS"),
            (nov["n2_claims"] == 0, "BAD_NOVELTY_CLAIMS"),
        ]
    )


def secondary_audit_payload(payload: Any) -> dict[str, Any]:
    """Fail-closed in-memory Zone-B secondary auditor verifying schemas & algebraic invariants across all 5 pillars."""
    validate_json_tree_iterative(payload)
    if type(payload) is not dict:
        raise S87Error("BAD_PAYLOAD_TYPE", "payload must be strict dict")
    if frozenset(payload.keys()) != _PAYLOAD_KEYS:
        raise S87Error("BAD_PAYLOAD_KEYS", "payload keys mismatch")

    stack: list[Any] = [payload]
    while stack:
        cur = stack.pop()
        if type(cur) is dict:
            if "num" in cur or "den" in cur:
                _parse_rat_dict(cur)
            for k, v in cur.items():
                if type(v) is bool:
                    require_ok(k in _PAYLOAD_BOOL_KEYS, "UNEXPECTED_BOOL_FIELD", f"unexpected bool at {k}")
                elif k == "sha256":
                    require_sha256_hex(v, "sha256")
                elif type(v) in (dict, list):
                    stack.append(v)
        else:
            for item in cur:
                require_ok(type(item) is not bool, "UNEXPECTED_BOOL_ITEM", "unexpected bool in payload list")
                if type(item) in (dict, list):
                    stack.append(item)

    _audit_pillar1(_req_dict(payload["pillar1_meta_a_competing_potential"], _P1_KEYS, "BAD_P1_SCHEMA"))
    _audit_pillar2(_req_dict(payload["pillar2_meta_b_grafting_proxy_blindness"], _P2_KEYS, "BAD_P2_SCHEMA"))
    _audit_pillar3(_req_dict(payload["pillar3_meta_c_f2_three_wall_fracture"], _P3_KEYS, "BAD_P3_SCHEMA"))
    _audit_pillar4(_req_dict(payload["pillar4_meta_d_ceer_closed_loop_fixed_point"], _P4_KEYS, "BAD_P4_SCHEMA"))
    _audit_pillar5(_req_dict(payload["pillar5_corpus_provenance_and_lean4"], _P5_KEYS, "BAD_P5_SCHEMA"))
    return payload


def verify_certificate_dict(cert: Any, *, full_replay: bool = True) -> dict[str, Any]:
    """Fail-closed in-memory Zone-B verifier supporting FR1 (full_replay=True) and FR0 (full_replay=False)."""
    require_ok(type(full_replay) is bool, "INVALID_FULL_REPLAY", "full_replay must be strict bool")
    validate_json_tree_iterative(cert)
    if type(cert) is not dict:
        raise S87Error("NON_OBJECT_ROOT", "certificate root must be strict dict")
    if frozenset(cert.keys()) != _CERT_KEYS:
        raise S87Error("BAD_CERT_KEYS", "certificate keys mismatch")
    if cert["schema"] != CERT_SCHEMA:
        raise S87Error("BAD_SCHEMA", "schema mismatch")
    if cert["track_id"] != CERT_TRACK_ID:
        raise S87Error("BAD_TRACK_ID", "track_id mismatch")

    payload = cert["payload"]
    if type(payload) is not dict:
        raise S87Error("BAD_PAYLOAD_TYPE", "payload must be strict dict")

    claimed_p_sha = require_sha256_hex(cert["payload_sha256"], "payload_sha256")
    claimed_c_sha = require_sha256_hex(cert["certificate_sha256"], "certificate_sha256")

    calc_p_sha = hashlib.sha256(canonical_json_bytes(payload)).hexdigest()
    if not hmac.compare_digest(claimed_p_sha, calc_p_sha):
        raise S87Error("PAYLOAD_SHA_MISMATCH", "payload_sha256 mismatch")

    envelope = {
        "schema": cert["schema"],
        "track_id": cert["track_id"],
        "payload_sha256": claimed_p_sha,
        "payload": payload,
    }
    calc_c_sha = hashlib.sha256(canonical_json_bytes(envelope)).hexdigest()
    if not hmac.compare_digest(claimed_c_sha, calc_c_sha):
        raise S87Error("CERT_SHA_MISMATCH", "certificate_sha256 mismatch")

    secondary_audit_payload(payload)

    if full_replay:
        expected = build_certificate()
        if not exact_typed_equal(payload, expected["payload"]):
            raise S87Error("PAYLOAD_ORACLE_MISMATCH", "payload disagrees with exact-Q oracle")
        if not hmac.compare_digest(claimed_c_sha, expected["certificate_sha256"]):
            raise S87Error("ORACLE_CERT_SHA_MISMATCH", "certificate_sha256 disagrees with exact-Q oracle")
    return cert


def audit_certificate_object(cert: Any) -> dict[str, Any]:
    """Fail-closed in-memory Zone-B hardened full-replay auditor."""
    return verify_certificate_dict(cert, full_replay=True)


# ---------------------------------------------------------------------------
# Hardened dir_fd File I/O (TOCTOU, Symlink, FIFO, Hardlink, 0o600 Atomic Write)
# ---------------------------------------------------------------------------

def _validate_path(path: Any) -> None:
    if type(path) not in _EXACT_PATH_TYPES:
        raise S87Error("INVALID_PATH_TYPE", "path must be concrete pathlib.Path")
    raw = str(path)
    try:
        raw.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise S87Error("INVALID_UNICODE_STR", f"lone surrogate in path: {exc}") from exc
    if "\x00" in raw:
        raise S87Error("INVALID_PATH_NUL", "NUL byte forbidden in path")


def _is_symlink_at(dfd: int, name: str) -> bool:
    try:
        return stat.S_ISLNK(os.lstat(name, dir_fd=dfd).st_mode)
    except OSError:
        return False


def _check_pwd_no_symlinks() -> None:
    pwd = os.environ.get("PWD")
    if pwd is None or not os.path.isabs(pwd):
        return
    try:
        pwd.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise S87Error("INVALID_UNICODE_STR", f"lone surrogate in PWD: {exc}") from exc
    cur_fd = os.open("/", os.O_RDONLY | os.O_DIRECTORY)
    try:
        for comp in Path(pwd).parts[1:]:
            try:
                nxt = os.open(comp, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=cur_fd)
            except OSError as exc:
                if _is_symlink_at(cur_fd, comp):
                    raise S87Error("SYMLINK_ANCESTOR_FORBIDDEN", f"symlink in PWD: {comp}") from exc
                return
            os.close(cur_fd)
            cur_fd = nxt
    finally:
        os.close(cur_fd)


def _open_parent_dir_fd(path: Path) -> tuple[int, str]:
    _validate_path(path)
    is_abs = path.is_absolute()
    if not is_abs:
        _check_pwd_no_symlinks()
    parts = path.parts[1:] if is_abs else path.parts
    if len(parts) == 0 or parts[-1] == "..":
        raise S87Error("INVALID_PATH", "path must name a regular file")
    ancestors, leaf = parts[:-1], parts[-1]
    cur_fd = os.open("/" if is_abs else ".", os.O_RDONLY | os.O_DIRECTORY)
    try:
        for comp in ancestors:
            try:
                nxt = os.open(comp, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=cur_fd)
            except OSError as exc:
                if _is_symlink_at(cur_fd, comp):
                    raise S87Error("SYMLINK_ANCESTOR_FORBIDDEN", f"symlink ancestor: {comp}") from exc
                raise S87Error("PARENT_DIR_ERROR", f"cannot open ancestor {comp}: {exc}") from exc
            os.close(cur_fd)
            cur_fd = nxt
        return cur_fd, leaf
    except BaseException:
        os.close(cur_fd)
        raise


def read_regular_file_bytes(path: Path, *, max_bytes: int = MAX_JSON_BYTES) -> bytes:
    dir_fd, leaf = _open_parent_dir_fd(path)
    fd = -1
    try:
        try:
            fd = os.open(leaf, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=dir_fd)
        except OSError as exc:
            if exc.errno == errno.ELOOP:
                raise S87Error("SYMLINK_FORBIDDEN", f"symlink forbidden: {path}") from exc
            raise S87Error("FILE_READ_ERROR", f"cannot open {path}: {exc}") from exc
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise S87Error("NOT_REGULAR_FILE", f"not a regular file: {path}")
        if st.st_nlink != 1:
            raise S87Error("HARDLINK_FORBIDDEN", f"hardlink forbidden (st_nlink={st.st_nlink})")
        if st.st_size > max_bytes:
            raise S87Error("FILE_TOO_LARGE", f"file exceeds {max_bytes} bytes")
        chunks: list[bytes] = []
        total = 0
        while True:
            try:
                chunk = os.read(fd, _READ_CHUNK_BYTES)
            except OSError as exc:
                raise S87Error("FILE_READ_ERROR", f"read error on {path}: {exc}") from exc
            if not chunk:
                break
            total += len(chunk)
            if total > max_bytes:
                raise S87Error("FILE_TOO_LARGE", f"stream exceeded {max_bytes} bytes")
            chunks.append(chunk)
        return b"".join(chunks)
    finally:
        if fd >= 0:
            os.close(fd)
        os.close(dir_fd)


def write_atomic_0600_bytes(path: Path, data: bytes) -> None:
    dir_fd, leaf = _open_parent_dir_fd(path)
    tmp_name = ""
    fd = -1
    try:
        if _is_symlink_at(dir_fd, leaf):
            raise S87Error("SYMLINK_FORBIDDEN", f"symlink target forbidden: {path}")
        try:
            st_existing = os.lstat(leaf, dir_fd=dir_fd)
            if not stat.S_ISREG(st_existing.st_mode):
                raise S87Error("NOT_REGULAR_FILE", f"target is not a regular file: {path}")
            if st_existing.st_nlink > 1:
                raise S87Error("HARDLINK_FORBIDDEN", f"target hardlink forbidden: {path}")
        except FileNotFoundError:
            pass
        with _TEMP_NAME_LOCK:
            tmp_name = f".{leaf}.tmp.{secrets.token_hex(8)}"
            fd = os.open(
                tmp_name,
                os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_NONBLOCK,
                0o600,
                dir_fd=dir_fd,
            )
        os.fchmod(fd, 0o600)
        view = memoryview(data)
        written = 0
        while written < len(data):
            n = os.write(fd, view[written:])
            if n <= 0:
                raise S87Error("FILE_WRITE_ERROR", "short zero write")
            written += n
        os.fsync(fd)
        st_tmp = os.fstat(fd)
        if st_tmp.st_nlink != 1:
            raise S87Error("HARDLINK_FORBIDDEN", "temp file gained extra hardlink")
        os.close(fd)
        fd = -1
        os.replace(tmp_name, leaf, src_dir_fd=dir_fd, dst_dir_fd=dir_fd)
        tmp_name = ""
        os.fsync(dir_fd)
    except S87Error:
        raise
    except OSError as exc:
        raise S87Error("FILE_WRITE_ERROR", f"atomic write failed: {exc}") from exc
    finally:
        if fd >= 0:
            os.close(fd)
        if tmp_name:
            try:
                os.unlink(tmp_name, dir_fd=dir_fd)
            except OSError:
                pass
        os.close(dir_fd)


def check_certificate_file(path: Path) -> dict[str, Any]:
    raw = read_regular_file_bytes(path, max_bytes=MAX_JSON_BYTES)
    if b"\r" in raw:
        raise S87Error("CRLF_FORBIDDEN", "CR/CRLF bytes forbidden in canonical certificate")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise S87Error("INVALID_UTF8", f"invalid UTF-8: {exc}") from exc
    parsed = parse_strict_json(text)
    cert = audit_certificate_object(parsed)
    expected_bytes = canonical_json_bytes(cert) + b"\n"
    if raw != expected_bytes:
        raise S87Error("NONCANONICAL_BYTES", "certificate file bytes are not canonical LF-terminated JSON")
    return cert


def verify_upstream_manifest(exp_root: Path) -> dict[str, Any]:
    """Fail-closed verification of all 24 pinned upstream certificate SHA-256s on disk."""
    _validate_path(exp_root)
    verified = 0
    for tid, rel, expected_sha in UPSTREAM_CERT_MANIFEST:
        raw = read_regular_file_bytes(exp_root / rel, max_bytes=MAX_JSON_BYTES)
        actual_sha = hashlib.sha256(raw).hexdigest()
        require_ok(
            hmac.compare_digest(actual_sha, expected_sha),
            "UPSTREAM_SHA_MISMATCH",
            f"upstream certificate SHA mismatch for {tid}",
        )
        verified += 1
    return {
        "status": "UPSTREAM_VERIFIED",
        "tracks_verified": verified,
        "expected_tracks": len(UPSTREAM_CERT_MANIFEST),
    }


# ---------------------------------------------------------------------------
# R10+ Static Lean 4 Scanner + Live Lean 4.36.0 Axiom Verifier
# ---------------------------------------------------------------------------

_LEAN4_HARD_LINE_RULES: tuple[tuple[re.Pattern[str], str], ...] = (
    (re.compile(r"\bsorry\b"), "LEAN4_SORRY"),
    (re.compile(r"\badmit\b"), "LEAN4_ADMIT"),
    (re.compile(r"(?<!\.)\baxiom\b"), "LEAN4_AXIOM"),
    (re.compile(r"(?<!\.)\bunsafe\b"), "LEAN4_UNSAFE"),
    (re.compile(r"\bnative_decide\b"), "LEAN4_NATIVE_DECIDE"),
    (re.compile(r"\bsorryAx\b"), "LEAN4_SORRY_AX"),
    (re.compile(r"\bLean\.Meta\.mkSorry\b|\bmkSorry\b"), "LEAN4_MK_SORRY"),
    (re.compile(r"\bLean\.ofReduceBool\b|\bofReduceBool\b"), "LEAN4_OF_REDUCE_BOOL"),
    (re.compile(r"\bLean\.ofReduceNat\b|\bofReduceNat\b"), "LEAN4_OF_REDUCE_NAT"),
    (re.compile(r"\bLean\.trustCompiler\b|\btrustCompiler\b"), "LEAN4_TRUST_COMPILER"),
)
_LEAN4_PARTIAL_DECL_RE = re.compile(r"(?<!\.)\bpartial\s+(?:def|instance|abbrev)\b", flags=re.DOTALL)
_LEAN4_GUILLEMET_RE = re.compile(r"«([A-Za-z_][A-Za-z0-9_']*)»")
_LEAN4_SIMPLE_GUILLEMET_RE = re.compile(r"\A[A-Za-z_][A-Za-z0-9_']*\Z")
_LEAN4_DEBUG_RE = re.compile(
    r"\bdebug\s*\.\s*(?:skipKernelTC|byAsSorry|proofAsSorry|terminalTacticsAsSorry)\b",
    flags=re.DOTALL,
)
_LEAN4_PRINT_KW = (
    "def|theorem|lemma|axiom|inductive|structure|class|instance|opaque|abbrev|example|"
    "namespace|section|end|open|variable|universe|import|set_option|attribute|"
    "local|scoped|private|protected|noncomputable|partial|unsafe|meta|where|by|in|let|have"
)
_LEAN4_SPOOF_RE = re.compile(
    r"#(?:eval!?(?![\w'!?])|reduce(?![\w'!?])|exit(?![\w'!?])|"
    r"print(?![\w'!?])(?!\s+axioms[ \t]+(?!(?:" + _LEAN4_PRINT_KW + r")(?![\w'!?]))[A-Za-z_]))"
    r"|(?<!\.)\b(?:run_cmd|run_meta|initialize|builtin_initialize)\b",
    flags=re.DOTALL,
)
_LEAN4_IMPORT_RE = re.compile(
    r"(?:^|\n)[ \t]*(?:(?:public|private|meta)\s+)*import\s+([A-Za-z0-9_.]+)",
    flags=re.DOTALL,
)
_LEAN4_ATTR_OPEN_RE = re.compile(r"(?:@|(?<!\.)\battribute\s*)\[", flags=re.DOTALL)
_LEAN4_HARD_ATTR_RE = re.compile(r"\b(extern|implemented_by|csimp)\b")
_LEAN4_META_SYNTAX_RE = re.compile(
    r"(?<!\.)\b(?:syntax|macro_rules|macro|elab|elab_rules|declare_syntax_cat|notation|prefix|infixl|infixr|infix|postfix)\b"
)
_LEAN4_CHAR_PREV_IDENT = "_'»!?"
_LEAN4_HEX_DIGITS = frozenset("0123456789abcdefABCDEF")
_LEAN4_INTERP_BANG_WORDS = frozenset(
    ("s", "f", "m", "v", "println", "reportIssue", "reportDbgIssue", "reportEMatchIssue")
)
_LEAN4_INTERP_KEYWORDS = frozenset(("dbg_trace", "throwError"))
_LEAN4_DECIDE_KW_RE = re.compile(r"\bdecide\b")
_LEAN4_FLAG_TOK_RE = re.compile(r"[+-][A-Za-z0-9_]+")
_LEAN4_OPT_PREFIX_RE = re.compile(r"\s*([A-Za-z0-9_]+)\s*:=")
_LEAN4_CONFIG_NATIVE_RE = re.compile(r"\bnative\b(?:\s*:=\s*([^},]*))?")
_LEAN4_CONFIG_WITH_RE = re.compile(r"\bwith\b")
_LEAN4_DECIDE_CFG_BIND_RE = re.compile(
    r"\b(?:DecideConfig|Decide\.Config)\b[ \t)]*:=\s*(?:\(\s*)*\{[^}{]*\bnative\s*:=\s*([^}{,]*)(?:,[^}{]*)?\}"
    r"|\{[^}{]*\bnative\s*:=\s*([^}{,]*)(?:,[^}{]*)?\}\s*:\s*(?:[A-Za-z_][A-Za-z0-9_]*\.)*(?:DecideConfig|Decide\.Config)\b",
    flags=re.DOTALL,
)
_LEAN4_AXIOM_OUT_RE = re.compile(
    r"^'([^']+)'\s+(?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])$"
)


def _is_lean4_ident_prev(source: str, pos: int) -> bool:
    if pos < 0:
        return False
    ch = source[pos]
    if ch.isalnum() or ch in "_.'":
        return True
    if ch in "!?":
        for k in range(pos - 1, -1, -1):
            if source[k] not in "!?":
                return source[k].isalnum() or source[k] in "_'"
        return False
    return False


def _match_lean4_char_literal_end(source: str, i: int, n: int) -> int | None:
    """Return end index of a Lean 4 Char literal starting at source[i] == "'", or None."""
    if i + 2 < n and source[i + 1] not in ("\\", "\n") and source[i + 2] == "'":
        return i + 3
    if i + 3 < n and source[i + 1] == "\\":
        esc = source[i + 2]
        if source[i + 3] == "'" and esc != "\n":
            return i + 4
        if (
            esc == "x"
            and i + 5 < n
            and source[i + 5] == "'"
            and all(c in _LEAN4_HEX_DIGITS for c in source[i + 3 : i + 5])
        ):
            return i + 6
        if (
            esc == "u"
            and i + 7 < n
            and source[i + 7] == "'"
            and all(c in _LEAN4_HEX_DIGITS for c in source[i + 3 : i + 7])
        ):
            return i + 8
    return None


def _strip_lean4_r10(source: str) -> tuple[str, list[str]]:
    """R10+ Lean 4 comment/char/string/raw-string/spaced-interp/unknown-bang stripper."""
    out: list[str] = []
    errors: list[str] = []
    i = 0
    n = len(source)
    depth = 0
    in_str = False
    in_interp = False
    pending_interp = False
    interp_stack: list[int] = []
    raw_hashes = -1
    while i < n:
        ch = source[i]
        nxt = source[i + 1] if i + 1 < n else ""
        if depth > 0:
            if ch == "/" and nxt == "-":
                depth += 1
                out.append("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if raw_hashes >= 0:
            close_seq = '"' + ("#" * raw_hashes)
            if source.startswith(close_seq, i):
                out.append(" " * len(close_seq))
                i += len(close_seq)
                raw_hashes = -1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if in_str:
            if ch == "\\":
                out.append(" \n" if nxt == "\n" else "  ")
                i += 2
            elif ch == '"':
                in_str = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if in_interp:
            if ch == "\\":
                out.append(" \n" if nxt == "\n" else "  ")
                i += 2
            elif ch == "{":
                interp_stack.append(1)
                in_interp = False
                out.append(" ")
                i += 1
            elif ch == '"':
                in_interp = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if ch == "/" and nxt == "-":
            depth = 1
            out.append("  ")
            i += 2
            continue
        if ch == "-" and nxt == "-":
            while i < n and source[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if ch.isspace():
            out.append(ch)
            i += 1
            continue
        if ch != '"':
            pending_interp = False
        if interp_stack:
            if ch == "{":
                interp_stack[-1] += 1
                out.append(ch)
                i += 1
                continue
            if ch == "}":
                interp_stack[-1] -= 1
                out.append(ch)
                i += 1
                if interp_stack[-1] == 0:
                    interp_stack.pop()
                    in_interp = True
                continue
        if ch == '"':
            if pending_interp:
                in_interp = True
                pending_interp = False
            else:
                if _is_lean4_ident_prev(source, i - 2) and source[i - 1] == "!":
                    is_panic = (
                        source[i - 6 : i] == "panic!"
                        and not _is_lean4_ident_prev(source, i - 7)
                    )
                    if not is_panic:
                        errors.append("LEAN4_UNKNOWN_BANG_STRING")
                in_str = True
            out.append(" ")
            i += 1
        elif ch == "«":
            end_g = source.find("»", i + 1)
            if end_g == -1:
                errors.append("LEAN4_UNTERMINATED_IDENT")
                break
            inner = source[i + 1 : end_g]
            if _LEAN4_SIMPLE_GUILLEMET_RE.match(inner) is not None and inner != "axioms":
                out.append(source[i : end_g + 1])
            else:
                out.append(" " * (end_g - i + 1))
            i = end_g + 1
        elif ch == "'" and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in _LEAN4_CHAR_PREV_IDENT)):
            char_end = _match_lean4_char_literal_end(source, i, n)
            if char_end is not None:
                out.append(" " * (char_end - i))
                i = char_end
            else:
                out.append(ch)
                i += 1
        elif ch == "r" and not _is_lean4_ident_prev(source, i - 1):
            j = i + 1
            while j < n and source[j] == "#":
                j += 1
            if j < n and source[j] == '"':
                raw_hashes = j - (i + 1)
                out.append(" " * (j - i + 1))
                i = j + 1
            else:
                out.append(ch)
                i += 1
        elif ch.isalpha() and not _is_lean4_ident_prev(source, i - 1):
            w_end = i + 1
            while w_end < n and (source[w_end].isalnum() or source[w_end] == "_"):
                w_end += 1
            word = source[i:w_end]
            next_ch = source[w_end] if w_end < n else ""
            if next_ch == "!" and word in _LEAN4_INTERP_BANG_WORDS:
                pending_interp = True
                out.append(source[i : w_end + 1])
                i = w_end + 1
                continue
            if word in _LEAN4_INTERP_KEYWORDS:
                pending_interp = True
            out.append(word)
            i = w_end
        else:
            out.append(ch)
            i += 1
    if depth > 0:
        errors.append("LEAN4_UNTERMINATED_COMMENT")
    elif in_str or in_interp or raw_hashes >= 0 or interp_stack:
        errors.append("LEAN4_UNTERMINATED_STRING")
    return "".join(out), errors


def _strip_outer_parens(rhs: str) -> str:
    s = rhs.strip()
    while len(s) >= 2 and s[0] == "(" and s[-1] == ")":
        s = s[1:-1].strip()
    return s


def _is_native_false(rhs: str) -> bool:
    return _strip_outer_parens(rhs) in ("false", "Bool.false")


def _scan_decide_native(cleaned: str) -> bool:
    for mc in _LEAN4_DECIDE_CFG_BIND_RE.finditer(cleaned):
        for g in mc.groups():
            if g is not None and not _is_native_false(g):
                return True
    n = len(cleaned)
    match_rp: dict[int, int] = {}
    pstack: list[int] = []
    for idx, ch in enumerate(cleaned):
        if ch == "(":
            pstack.append(idx)
        elif ch == ")" and pstack:
            match_rp[pstack.pop()] = idx
    for m in _LEAN4_DECIDE_KW_RE.finditer(cleaned):
        pos = m.end()
        while True:
            while pos < n and cleaned[pos].isspace():
                pos += 1
            if pos >= n:
                break
            ch = cleaned[pos]
            if ch in "+-":
                mf = _LEAN4_FLAG_TOK_RE.match(cleaned, pos)
                if mf is None:
                    break
                if mf.group(0) == "+native":
                    return True
                pos = mf.end()
                continue
            if ch == "(":
                close_i = match_rp.get(pos)
                if close_i is None:
                    break
                mp = _LEAN4_OPT_PREFIX_RE.match(cleaned, pos + 1, close_i)
                if mp is None:
                    break
                key = mp.group(1)
                rhs = cleaned[mp.end() : close_i].strip()
                if key == "native" and not _is_native_false(rhs):
                    return True
                if key == "config":
                    inner = _strip_outer_parens(rhs)
                    if not (inner.startswith("{") and inner.endswith("}")):
                        return True
                    body = inner[1:-1]
                    if "{" in body or "}" in body or _LEAN4_CONFIG_WITH_RE.search(body) is not None:
                        return True
                    for mn in _LEAN4_CONFIG_NATIVE_RE.finditer(body):
                        if mn.group(1) is None or not _is_native_false(mn.group(1)):
                            return True
                pos = close_i + 1
                continue
            break
    return False


def audit_lean4_source_r10(source: str) -> list[str]:
    """Return list of R10+ static Lean 4 finding codes (empty list iff clean)."""
    if type(source) is not str:
        raise S87Error("INVALID_LEAN_SOURCE", "Lean source must be strict str")
    cleaned, findings = _strip_lean4_r10(source)
    cleaned = _LEAN4_GUILLEMET_RE.sub(r"\1", cleaned)
    for line in cleaned.splitlines():
        for pat, code in _LEAN4_HARD_LINE_RULES:
            if pat.search(line) is not None:
                findings.append(code)
    for m_imp in _LEAN4_IMPORT_RE.finditer(cleaned):
        root_pkg = m_imp.group(1).split(".")[0]
        if root_pkg not in ("Init", "Std"):
            findings.append("LEAN4_NON_INIT_IMPORT")
    if _LEAN4_PARTIAL_DECL_RE.search(cleaned) is not None:
        findings.append("LEAN4_PARTIAL")
    if _scan_decide_native(cleaned):
        findings.append("LEAN4_DECIDE_NATIVE")
    if _LEAN4_DEBUG_RE.search(cleaned) is not None:
        findings.append("LEAN4_SKIP_KERNEL_TC")
    if _LEAN4_SPOOF_RE.search(cleaned) is not None:
        findings.append("LEAN4_EVAL_SPOOF")
    if _LEAN4_META_SYNTAX_RE.search(cleaned) is not None:
        findings.append("LEAN4_META_SYNTAX_ESCAPE")
    match_rb: dict[int, int] = {}
    bstack: list[int] = []
    for idx, ch in enumerate(cleaned):
        if ch == "[":
            bstack.append(idx)
        elif ch == "]" and bstack:
            match_rb[bstack.pop()] = idx
    for m_open in _LEAN4_ATTR_OPEN_RE.finditer(cleaned):
        lb = m_open.end() - 1
        rb = match_rb.get(lb)
        if rb is not None and _LEAN4_HARD_ATTR_RE.search(cleaned, lb + 1, rb) is not None:
            findings.append("LEAN4_ATTR_TRUST_ESCAPE")
    return findings


def _find_lean_binary() -> str:
    env_bin = os.environ.get("LEAN_BIN")
    if env_bin:
        p = Path(env_bin)
        if p.is_file():
            return str(p)
        raise S87Error("LEAN_BINARY_NOT_FOUND", "LEAN_BIN does not name an existing file")
    found = shutil.which("lean")
    if found is not None:
        return found
    elan_lean = Path.home() / ".elan" / "bin" / "lean"
    if elan_lean.is_file():
        return str(elan_lean)
    raise S87Error("LEAN_BINARY_NOT_FOUND", "lean binary not found on PATH, LEAN_BIN, or $HOME/.elan/bin")


def verify_lean_file(path: Path, *, check_pinned_sha: bool = True) -> dict[str, Any]:
    require_ok(type(check_pinned_sha) is bool, "INVALID_CHECK_PINNED_SHA", "check_pinned_sha must be strict bool")
    raw = read_regular_file_bytes(path, max_bytes=MAX_JSON_BYTES)
    if b"\r" in raw:
        raise S87Error("CRLF_FORBIDDEN", "CR/CRLF forbidden in Lean file")
    try:
        source = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise S87Error("INVALID_UTF8", f"invalid UTF-8 in Lean file: {exc}") from exc
    sha = hashlib.sha256(raw).hexdigest()
    if check_pinned_sha and not hmac.compare_digest(sha, LEAN_FILE_SHA256):
        raise S87Error("LEAN_SHA_MISMATCH", "Lean file SHA-256 does not match pinned digest")
    findings = audit_lean4_source_r10(source)
    require_ok(len(findings) == 0, "LEAN_R10_STATIC_FINDING", f"R10 findings: {findings}")
    lean_bin = _find_lean_binary()
    proc = subprocess.run(
        [lean_bin, str(path)],
        capture_output=True,
        text=True,
        timeout=120,
        check=False,
    )
    require_ok(proc.returncode == 0, "LEAN_COMPILE_FAILED", f"lean exited {proc.returncode}: {proc.stderr}")
    require_ok(proc.stderr == "", "LEAN_STDERR_NONEMPTY", f"unexpected lean stderr: {proc.stderr}")
    records: list[str] = []
    for raw_line in proc.stdout.splitlines():
        s = raw_line.strip()
        if records and "[" in records[-1] and "]" not in records[-1]:
            records[-1] = records[-1] + " " + s
        else:
            records.append(s)
    seen: dict[str, list[str]] = {}
    for line in records:
        m = _LEAN4_AXIOM_OUT_RE.match(line)
        require_ok(m is not None, "LEAN_UNEXPECTED_OUTPUT", f"unexpected lean output line: {line}")
        thm = m.group(1)
        require_ok(thm not in seen, "LEAN_DUPLICATE_THEOREM", f"duplicate #print axioms for {thm}")
        ax_raw = m.group(2)
        ax_list = [] if ax_raw is None else [a.strip() for a in ax_raw.split(",") if a.strip()]
        for ax in ax_list:
            require_ok(ax in _ALLOWED_LEAN_AXIOMS, "LEAN_FORBIDDEN_AXIOM", f"{thm} uses forbidden axiom {ax}")
        seen[thm] = ax_list
    require_ok(len(seen) >= 1, "LEAN_NO_THEOREMS_VERIFIED", "at least one theorem axiom printout required")
    if check_pinned_sha:
        require_ok(tuple(seen.keys()) == LEAN_THEOREMS, "LEAN_THEOREM_SET_MISMATCH", "theorem set mismatch")
    return {
        "lean_file": path.name,
        "sha256": sha,
        "r10_findings": 0,
        "theorems_verified": len(seen),
        "allowed_axioms": sorted(_ALLOWED_LEAN_AXIOMS),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Track S87 Universal Higher-Order Meta-Convergence Atlas Verifier")
    mode = parser.add_mutually_exclusive_group(required=False)
    mode.add_argument("--standalone", action="store_true", help="Run exact-Q oracle and emit canonical JSON")
    mode.add_argument("--write", type=Path, help="Atomically write canonical 0o600 certificate JSON")
    mode.add_argument("--check", type=Path, help="Verify canonical certificate JSON fail-closed")
    mode.add_argument("--verify-lean", type=Path, help="Run R10+ static + live Lean 4.36.0 kernel verification")
    mode.add_argument("--verify-upstream", type=Path, help="Verify all 24 pinned upstream certificate SHA-256s")
    parser.add_argument("--json", action="store_true", help="Emit JSON output")
    args = parser.parse_args(argv)

    try:
        if args.write is not None:
            cert = build_certificate()
            audit_certificate_object(cert)
            out_bytes = canonical_json_bytes(cert) + b"\n"
            write_atomic_0600_bytes(args.write, out_bytes)
            if args.json:
                sys.stdout.buffer.write(
                    canonical_json_bytes(
                        {"status": "WRITTEN", "certificate_sha256": cert["certificate_sha256"]}
                    )
                    + b"\n"
                )
            return 0
        if args.check is not None:
            cert = check_certificate_file(args.check)
            if args.json:
                sys.stdout.buffer.write(
                    canonical_json_bytes(
                        {"status": "PASS", "certificate_sha256": cert["certificate_sha256"]}
                    )
                    + b"\n"
                )
            return 0
        if args.verify_lean is not None:
            res = verify_lean_file(args.verify_lean, check_pinned_sha=True)
            if args.json:
                sys.stdout.buffer.write(canonical_json_bytes(res) + b"\n")
            return 0
        if args.verify_upstream is not None:
            res = verify_upstream_manifest(args.verify_upstream)
            if args.json:
                sys.stdout.buffer.write(canonical_json_bytes(res) + b"\n")
            return 0
        cert = build_certificate()
        audit_certificate_object(cert)
        out_bytes = canonical_json_bytes(cert) + b"\n"
        sys.stdout.buffer.write(out_bytes)
        return 0
    except S87Error as exc:
        sys.stderr.write(f"ERROR [{exc.code}]: {exc.message}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
