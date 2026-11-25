#!/usr/bin/env python3
"""
Track S94 Hardened Zone-B Verifier, Read-Only Pin Auditor & R10+ Lean 4.36.0 Gate.

Supports:
  --standalone --json       Compute canonical certificate and print to stdout
  --write <cert.json>       Atomically write canonical 0o600 certificate JSON via dir_fd + fsync
  --check <cert.json>       Fail-closed Zone-B verification of certificate JSON on disk
  --verify-lean <file>      R10+ static Lean 4 audit + live Lean 4.36.0 --stdin kernel check
  --verify-pins             Verify all 10 upstream certs (--expedition-root) and/or 12 Wave-6
                            snapshots (--wave6-root) strictly read-only on disk

Zero floats, zero bare asserts, zero external dependencies, zero RNG.
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
from typing import Any

_SCRIPT_DIR = str(Path(__file__).resolve().parent)
if _SCRIPT_DIR not in sys.path:
    sys.path.insert(0, _SCRIPT_DIR)

from s94_wave6_convergence_oracle import (
    EXPECTED_LEAN_SHA256,
    EXPECTED_LEAN_THEOREMS,
    LEAN_FILE_NAME,
    LEAN_TOOLCHAIN,
    NOVELTY_TIER,
    ORACLE_CLASS,
    SCHEMA_VERSION,
    TRACK_ID,
    UPSTREAM_CERT_PINS,
    WAVE6_SNAPSHOT_PINS,
    build_certificate_envelope,
    canonical_json_bytes,
    dec_str,
    q_str,
    require_ok,
)

MAX_JSON_BYTES = 1_048_576
MAX_JSON_DEPTH = 48
MAX_INT_BITS = 2048
MAX_INT_DIGITS = 617
_READ_CHUNK = 65_536
_EXACT_PATH_TYPES = (Path, type(Path()))

REQUIRED_CERT_KEYS = frozenset({"schema_version", "track_id", "payload_sha256", "certificate_sha256", "payload"})
REQUIRED_PAYLOAD_KEYS = frozenset(
    {
        "track_id",
        "oracle_class",
        "novelty_tier",
        "all_pillars_verified",
        "pillar_1_privileged_neuron_basis",
        "pillar_2_bonsai_magnitude_roofline",
        "pillar_3_sleep_trilogy_consolidation",
        "pillar_4_provenance_and_lean4",
    }
)
_PAYLOAD_BOOL_KEYS = frozenset(
    {
        "all_diagonals_flattened",
        "all_five_ablations_rejected",
        "all_five_gates_pass",
        "all_off_diagonals_uniform_abs",
        "all_pillars_verified",
        "all_theorems_universally_quantified",
        "all_verified",
        "anchored_to_outcomes",
        "bonsai_below_residency_cliff",
        "calibrated_strictly_better_in_expectation",
        "cross_session_persistence",
        "fits_in_gpu_hot_cache",
        "fully_gpu_resident",
        "gate1_sleep_loop_contractive",
        "gate2_forgetting_budgeted",
        "gate3_outcome_anchored",
        "gate4_anti_goodhart_clean",
        "gate5_memory_residency_ok",
        "k1_is_idempotent",
        "k2_is_involution",
        "k2_is_isometry",
        "n0_prior_art_anchored",
        "n1_exact_synthesis_verified",
        "overconfident_wins_on_y1",
        "relp_rs_adjoint_exact",
        "zero_dataset_copies_in_expedition",
    }
)
HEX64_RE = re.compile(r"\A[0-9a-f]{64}\Z")
_CANON_INT_RE = re.compile(r"\A(?:0|-?[1-9][0-9]*)\Z")
_CANON_POS_INT_RE = re.compile(r"\A[1-9][0-9]*\Z")

# R10+ Strict Static Lean 4 Scanner (Comment-Only Strip + Quote/Guillemet Ban + End-Anchored decide)
_LEAN_QUOTE_OR_GUILLEMET_RE = re.compile(r'["\'«»]')
_LEAN_FORBIDDEN_RE = re.compile(
    r"\b(?:sorry|admit|axiom|unsafe|native_decide|sorryAx|"
    r"ofReduceBool|ofReduceNat|trustCompiler|mkSorry|"
    r"elab|elab_rules|macro|macro_rules|syntax|declare_syntax_cat|"
    r"notation|prefix|infix|infixl|infixr|postfix|"
    r"initialize|builtin_initialize|opaque|dbg_trace|throwError|"
    r"run_cmd|run_meta|interpolatedStr)\b"
)
_LEAN_PARTIAL_RE = re.compile(r"(?<!\.)\bpartial\s+(?:def|instance|abbrev|theorem)\b")
_LEAN_DECIDE_NATIVE_RE = re.compile(
    r"(?<!\w)\+\s*native\b"
    r"|\bnative\s*:=(?!\s*(?:Bool\.)?false\s*(?:[),}]|\Z))"
    r"|\{[^}]*\bnative\b(?!\s*:=\s*(?:Bool\.)?false\s*[,}])"
    r"|\bconfig\s*:=(?!\s*\{\s*native\s*:=\s*(?:Bool\.)?false\s*\}\s*[)])"
    r"|\bDecide(?:Config|\.Config)\b"
    r"|\bdecide\s*\(\s*revert\b"
)
_LEAN_SKIP_TC_RE = re.compile(
    r"\bdebug\s*\.\s*(?:skipKernelTC|byAsSorry|proofAsSorry|terminalTacticsAsSorry)\b"
)
_LEAN_EVAL_SPOOF_RE = re.compile(
    r"#(?:eval!?|reduce|guard_msgs|exit)\b|"
    r"#print\s+(?!axioms\s+(?!example\b|def\b|theorem\b|lemma\b)[A-Za-z0-9_.]+\s*(?:\n|\Z))"
)
_LEAN_ATTR_ESCAPE_RE = re.compile(
    r"(?:@\[|\battribute\s*\[)[^\]]*\b(?:extern|implemented_by|export|csimp)\b"
)
_LEAN_IMPORT_RE = re.compile(
    r"(?:^|\n)\s*(?:(?:public|private|meta)\s+)*import\s+([A-Za-z0-9_.]+)"
)
_ZERO_AXIOM_LINE_RE = re.compile(r"\A'([A-Za-z0-9_.]+)' does not depend on any axioms\Z")
_DEPENDS_AXIOM_LINE_RE = re.compile(r"\A'([A-Za-z0-9_.]+)' depends on axioms: \[([A-Za-z0-9_., ]+)\]\Z")
_ALLOWED_LEAN_AXIOMS = frozenset({"propext"})


# ---------------------------------------------------------------------------
# Strict Zone-B Zero-Float JSON, Rational & Digest Primitives
# ---------------------------------------------------------------------------

def _is_sha256_hex(val: Any) -> bool:
    return type(val) is str and bool(HEX64_RE.match(val))


def parse_canonical_q(val: Any, code: str) -> Fraction:
    """Parse strict canonical reduced rational string ('0', '-3', '71/8'); rejects '-0', '01', '2/4', '3/1'."""
    require_ok(type(val) is str, code)
    if "/" not in val:
        require_ok(bool(_CANON_INT_RE.match(val)), code)
        return Fraction(int(val), 1)
    parts = val.split("/")
    require_ok(len(parts) == 2, code)
    n_s, d_s = parts
    require_ok(bool(_CANON_INT_RE.match(n_s)) and bool(_CANON_POS_INT_RE.match(d_s)), code)
    num, den = int(n_s), int(d_s)
    require_ok(den >= 2 and math.gcd(abs(num), den) == 1, code)
    return Fraction(num, den)


def _check_json_tree(root: Any) -> None:
    """Iterative exact-type JSON tree validator (blocks subclasses, huge ints, surrogates, cycles, DoS)."""
    active: set[int] = set()
    frames: list[tuple[Any, int, bool]] = [(root, 0, False)]
    while frames:
        obj, depth, is_exit = frames.pop()
        if is_exit:
            active.discard(obj)
            continue
        require_ok(depth <= MAX_JSON_DEPTH, "JSON_MAX_DEPTH_EXCEEDED")
        t = type(obj)
        if obj is None or t is bool:
            continue
        if t is int:
            require_ok(obj.bit_length() <= MAX_INT_BITS, "JSON_INT_TOO_LARGE")
            continue
        if t is str:
            require_ok("\x00" not in obj, "JSON_NUL_IN_STRING")
            for ch in obj:
                c = ord(ch)
                require_ok(not (0xD800 <= c <= 0xDFFF), "JSON_LONE_SURROGATE")
            continue
        if t is list:
            oid = id(obj)
            require_ok(oid not in active, "JSON_CYCLE")
            active.add(oid)
            frames.append((oid, depth, True))
            for item in obj:
                frames.append((item, depth + 1, False))
            continue
        if t is dict:
            oid = id(obj)
            require_ok(oid not in active, "JSON_CYCLE")
            active.add(oid)
            frames.append((oid, depth, True))
            for k, v in obj.items():
                require_ok(type(k) is str, "JSON_NON_STRING_KEY")
                frames.append((k, depth + 1, False))
                frames.append((v, depth + 1, False))
            continue
        raise ValueError(f"JSON_DISALLOWED_TYPE:{t.__name__}")


def _no_dup_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        require_ok(k not in out, f"JSON_DUPLICATE_KEY:{k}")
        out[k] = v
    return out


def _parse_capped_int(token: str) -> int:
    digits = token[1:] if token.startswith("-") else token
    require_ok(len(digits) <= MAX_INT_DIGITS, "JSON_INT_TOO_LARGE")
    val = int(token)
    require_ok(val.bit_length() <= MAX_INT_BITS, "JSON_INT_TOO_LARGE")
    return val


def _forbid_float(token: str) -> Any:
    raise ValueError(f"JSON_FLOAT_FORBIDDEN:{token}")


def _forbid_constant(token: str) -> Any:
    raise ValueError(f"JSON_CONSTANT_FORBIDDEN:{token}")


def parse_strict_json_bytes(raw: bytes) -> dict[str, Any]:
    require_ok(b"\r" not in raw, "CRLF_FORBIDDEN")
    require_ok(b"\x00" not in raw, "NUL_BYTE_IN_JSON")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValueError("INVALID_UTF8") from exc
    try:
        parsed = json.loads(
            text,
            object_pairs_hook=_no_dup_keys,
            parse_int=_parse_capped_int,
            parse_float=_forbid_float,
            parse_constant=_forbid_constant,
        )
    except ValueError:
        raise
    except RecursionError as exc:
        raise ValueError("JSON_MAX_DEPTH_EXCEEDED") from exc
    require_ok(type(parsed) is dict, "JSON_ROOT_NOT_OBJECT")
    _check_json_tree(parsed)
    require_ok(raw == canonical_json_bytes(parsed), "NON_CANONICAL_JSON_BYTES")
    return parsed


def exact_typed_equal(lhs: Any, rhs: Any) -> bool:
    stack: list[tuple[Any, Any]] = [(lhs, rhs)]
    while stack:
        a, b = stack.pop()
        if type(a) is not type(b):
            return False
        if type(a) is dict:
            if len(a) != len(b):
                return False
            for k, va in a.items():
                if k not in b:
                    return False
                stack.append((va, b[k]))
        elif type(a) is list:
            if len(a) != len(b):
                return False
            for va, vb in zip(a, b):
                stack.append((va, vb))
        elif a != b:
            return False
    return True


# ---------------------------------------------------------------------------
# Hardened dir_fd File I/O (PWD Symlink, FIFO, Hardlink, 0o600 Atomic Write)
# ---------------------------------------------------------------------------

def _validate_path(path: Any) -> None:
    require_ok(type(path) in _EXACT_PATH_TYPES, "INVALID_PATH_TYPE")
    raw = str(path)
    require_ok("\x00" not in raw, "INVALID_PATH")
    for ch in raw:
        require_ok(not (0xD800 <= ord(ch) <= 0xDFFF), "INVALID_PATH_SURROGATE")


def _check_pwd_no_symlinks() -> None:
    pwd = os.environ.get("PWD")
    if pwd is None or not os.path.isabs(pwd):
        return
    for ch in pwd:
        require_ok(not (0xD800 <= ord(ch) <= 0xDFFF), "INVALID_PWD_SURROGATE")
    cur_fd = os.open("/", os.O_RDONLY | os.O_DIRECTORY)
    try:
        for comp in Path(pwd).parts[1:]:
            try:
                nxt = os.open(comp, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=cur_fd)
            except OSError as exc:
                if exc.errno in (errno.ELOOP, errno.ENOTDIR):
                    raise ValueError(f"SYMLINK_IN_PATH:{comp}") from exc
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
    require_ok(len(parts) >= 1 and parts[-1] not in ("", ".", ".."), "INVALID_PATH")
    ancestors, leaf = parts[:-1], parts[-1]
    cur_fd = os.open("/" if is_abs else ".", os.O_RDONLY | os.O_DIRECTORY)
    try:
        for comp in ancestors:
            try:
                nxt = os.open(comp, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=cur_fd)
            except OSError as exc:
                if exc.errno in (errno.ELOOP, errno.ENOTDIR):
                    raise ValueError(f"SYMLINK_IN_PATH:{comp}") from exc
                raise ValueError(f"INVALID_PARENT_DIR:{comp}") from exc
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
                raise ValueError(f"SYMLINK_IN_PATH:{leaf}") from exc
            raise ValueError(f"FILE_OPEN_ERROR:{leaf}") from exc
        st = os.fstat(fd)
        require_ok(stat.S_ISREG(st.st_mode), "NOT_REGULAR_FILE")
        require_ok(st.st_nlink == 1, "HARDLINK_FORBIDDEN")
        require_ok(st.st_size <= max_bytes, "FILE_TOO_LARGE")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(fd, _READ_CHUNK)
            if not chunk:
                break
            total += len(chunk)
            require_ok(total <= max_bytes, "FILE_TOO_LARGE")
            chunks.append(chunk)
        return b"".join(chunks)
    finally:
        if fd >= 0:
            os.close(fd)
        os.close(dir_fd)


def atomic_write_0600(path: Path, data: bytes) -> None:
    dir_fd, leaf = _open_parent_dir_fd(path)
    tmp_name = ""
    fd = -1
    try:
        try:
            st_ex = os.lstat(leaf, dir_fd=dir_fd)
            require_ok(not stat.S_ISLNK(st_ex.st_mode), "SYMLINK_IN_PATH")
            require_ok(stat.S_ISREG(st_ex.st_mode), "TARGET_NOT_REGULAR")
            require_ok(st_ex.st_nlink == 1, "HARDLINK_FORBIDDEN")
        except FileNotFoundError:
            pass
        tmp_name = f".{leaf}.{secrets.token_hex(8)}.tmp"
        fd = os.open(tmp_name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_NONBLOCK, 0o600, dir_fd=dir_fd)
        os.fchmod(fd, 0o600)
        view = memoryview(data)
        written = 0
        while written < len(data):
            n = os.write(fd, view[written:])
            if n <= 0:
                raise OSError("SHORT_WRITE")
            written += n
        os.fsync(fd)
        st_tmp = os.fstat(fd)
        require_ok(st_tmp.st_nlink == 1, "TMP_HARDLINK_DETECTED")
        os.close(fd)
        fd = -1
        try:
            st_re = os.lstat(leaf, dir_fd=dir_fd)
            require_ok(not stat.S_ISLNK(st_re.st_mode), "SYMLINK_IN_PATH")
        except FileNotFoundError:
            pass
        os.replace(tmp_name, leaf, src_dir_fd=dir_fd, dst_dir_fd=dir_fd)
        tmp_name = ""
        os.fsync(dir_fd)
    finally:
        if fd >= 0:
            os.close(fd)
        if tmp_name:
            try:
                os.unlink(tmp_name, dir_fd=dir_fd)
            except OSError:
                pass
        os.close(dir_fd)


# ---------------------------------------------------------------------------
# Genuine Non-Hollow Independent Semantic Auditor (SEC & FR0)
# ---------------------------------------------------------------------------

_P1_KEYS = frozenset(
    {
        "hadamard_h8_skewed_d8",
        "hadamard_h8_isotropic_control",
        "hadamard_o_k_smearing_ladder",
        "axis_aligned_perm_control",
        "householder_reflection_dpi_witness",
        "all_verified",
    }
)
_P1_H_KEYS = frozenset(
    {
        "order",
        "spike_alpha_q",
        "commutator_nonzero_entries",
        "commutator_total_entries",
        "all_diagonals_flattened",
        "all_off_diagonals_uniform_abs",
        "smeared_diagonal_q",
        "off_diagonal_abs_q",
        "unweighted_mse_q",
        "true_importance_mse_q",
        "true_importance_mse_dec4",
    }
)
_P1_PERM_KEYS = frozenset(
    {
        "diagonal_preserved_max",
        "off_diagonal_leakage",
        "importance_mse_ratio_q",
        "s59_a16_rho_axis",
        "s59_a16_rho_h16",
        "s59_opposite_sign_contrast",
        "s70_swiglu_perm_max_abs_diff",
    }
)
_P1_HH_KEYS = frozenset(
    {
        "axis_d_q",
        "k2_is_involution",
        "k2_is_isometry",
        "k1_is_idempotent",
        "frob_norm_sq_before_q",
        "frob_norm_sq_after_q",
        "global_frob_delta_q",
        "diff_matrix_frob_sq_q",
        "diff_matrix_exact_rank",
        "dpi_spectral_concentration_q",
        "witness_4row_peak_to_mean_q",
        "qwen3_8b_total_neurons",
        "qwen3_8b_poles",
        "qwen3_8b_heads",
        "gemma4_12b_total_neurons",
        "gemma4_12b_poles",
        "gemma4_12b_heads",
        "qwen3_8b_100neuron_dpi_conc_q",
        "qwen3_8b_100neuron_dpi_conc_dec2",
        "s31_two_row_dpi_anchor_q",
        "refusal_unedited_q",
        "refusal_writes_mirrored_q",
        "refusal_both_mirrored_q",
        "relp_rs_adjoint_lhs_q",
        "relp_rs_adjoint_rhs_q",
        "relp_rs_adjoint_exact",
    }
)
_P2_KEYS = frozenset(
    {
        "bonsai25_primary_anchors",
        "hardware_three_tier_specs",
        "dense_27b_regimes",
        "magnitude_sparse_moe_contrast",
        "s86_8gib_training_anchor",
        "all_verified",
    }
)
_P2_BA_KEYS = frozenset(
    {
        "params_total_b_q",
        "fp16_size_gb_q",
        "ptq10_size_gb_q",
        "ptq10_bpw_q",
        "compression_ratio_q",
        "compression_ratio_dec4",
        "tool_calling_retention_q",
        "tool_calling_retention_pct_dec2",
        "agentic_coding_retention_q",
        "agentic_coding_retention_pct_dec2",
        "general_capability_retention_q",
        "general_capability_retention_pct_dec2",
    }
)
_P2_HW_KEYS = frozenset(
    {
        "vram_total_mib",
        "c_gpu_weight_budget_gb_q",
        "c_ram_gb_q",
        "c_ssd_gb",
        "b_gpu_gbs_q",
        "b_ram_gbs_q",
        "b_ssd_gbs_q",
        "gpu_over_ram_penalty_q",
        "gpu_over_ssd_penalty_q",
        "dense_27b_residency_cliff_bpw_q",
        "dense_27b_residency_cliff_bpw_dec4",
        "bonsai_below_residency_cliff",
    }
)
_P2_REG_KEYS = frozenset(
    {
        "model_gb_q",
        "m_gpu_gb_q",
        "m_ram_gb_q",
        "m_ssd_gb_q",
        "f_gpu_q",
        "f_ram_q",
        "f_ssd_q",
        "fully_gpu_resident",
        "spill_slowdown_q",
        "spill_slowdown_dec4",
        "roofline_tps_q",
        "roofline_tps_dec4",
    }
)
_P2_MOE_KEYS = frozenset(
    {
        "active_expert_fraction_q",
        "active_bytes_per_token_gb_q",
        "fits_in_gpu_hot_cache",
        "hit100_tps_q",
        "hit100_tps_dec4",
        "hit80_ram20_tps_q",
        "hit80_ram20_tps_dec4",
        "hit80_ram20_slowdown_q",
        "hit80_ram20_slowdown_dec4",
    }
)
_P2_S86_KEYS = frozenset(
    {
        "qwen3b_r64_peak_alloc_bytes",
        "qwen3b_r128_peak_alloc_bytes",
        "bits_freed_16_to_3bpw",
    }
)
_P3_KEYS = frozenset(
    {
        "axis1_zero_dw_kv_sleep",
        "axis2_weight_modifying_consolidation",
        "five_gate_consolidation_fixed_point",
        "borromean_five_gate_ablations",
        "all_five_ablations_rejected",
        "all_verified",
    }
)
_P3_A1_KEYS = frozenset(
    {
        "sleep_n2_token_efficiency_q",
        "sleep_n4_token_efficiency_q",
        "arxiv_2504_13171_ttc_reduction_q",
        "arxiv_2504_13171_multiquery_amort_q",
        "wake_latency_overhead",
        "kv_cache_size_growth",
        "weight_forgetting_ratio_q",
        "cross_session_persistence",
        "s76_contractive_rho_q",
        "s76_loop2_err_q",
        "s76_loop4_err_q",
        "s79_circularep_loop4_q",
        "s79_last_loop_kv_ratios",
        "s50_within_session_state_frob_sq_q",
        "s50_margin_flip_delta_q",
    }
)
_P3_KVR_KEYS = frozenset({"r4_w64_l2048_q", "r4_w64_l8192_q", "r4_w64_l32768_q"})
_P3_A2_KEYS = frozenset(
    {
        "cross_session_persistence",
        "s78_forgetting_over_learning_q",
        "s80_songe_1night_fwer_q",
        "s80_songe_20night_fwer_dec4",
        "s80_ratchet_clean_outside_accepts",
        "s80_ratchet_goodhart_accepts",
        "tm_forecasting_cost_reduction_q",
        "tm_forecasting_synthetic_questions",
        "harvey_tenet_early_stop_steps_default",
        "harvey_tenet_early_stop_steps_beam",
        "brier_overconfidence_paradox",
        "reference_mixture_half",
        "reference_mixture_pure_ref",
        "reference_mixture_pure_outcome",
    }
)
_P3_BP_KEYS = frozenset(
    {
        "q_true_q",
        "p_fcst_q",
        "expected_bs_true_q",
        "expected_bs_fcst_q",
        "excess_penalty_q",
        "single_draw_y1_true_err_q",
        "single_draw_y1_fcst_err_q",
        "overconfident_wins_on_y1",
        "calibrated_strictly_better_in_expectation",
    }
)
_P3_MIX_KEYS = frozenset(
    {
        "q_true_q",
        "r_ref_q",
        "lambda_q",
        "p_star_q",
        "abs_bias_q",
        "excess_true_brier_q",
        "anchored_to_outcomes",
    }
)
_P3_GATE_KEYS = frozenset(
    {
        "gate1_sleep_loop_contractive",
        "gate2_forgetting_budgeted",
        "gate3_outcome_anchored",
        "gate4_anti_goodhart_clean",
        "gate5_memory_residency_ok",
        "all_five_gates_pass",
        "error_after_steps_q",
    }
)
_P4_KEYS = frozenset(
    {
        "wave6_snapshot_count",
        "wave6_snapshot_pins",
        "upstream_cert_count",
        "upstream_cert_pins",
        "zero_dataset_copies_in_expedition",
        "lean4_companion",
        "novelty_honesty_law4",
    }
)
_P4_W6_PIN_KEYS = frozenset({"portal", "filename", "bytes", "sha256"})
_P4_UP_PIN_KEYS = frozenset({"track_id", "relative_ref", "bytes", "sha256"})
_P4_LEAN_KEYS = frozenset(
    {
        "file",
        "toolchain",
        "sha256",
        "theorem_count",
        "all_theorems_universally_quantified",
        "theorems",
        "allowed_axioms",
    }
)
_P4_NOV_KEYS = frozenset({"novelty_tier", "n0_prior_art_anchored", "n1_exact_synthesis_verified", "n2_claims"})


def _req_dict(val: Any, code: str) -> dict[str, Any]:
    require_ok(type(val) is dict, code)
    return val


def _req_exact_dict(val: Any, expected_keys: frozenset[str], code: str) -> dict[str, Any]:
    d = _req_dict(val, code)
    require_ok(frozenset(d.keys()) == expected_keys, code)
    return d


def _req_list(val: Any, code: str) -> list[Any]:
    require_ok(type(val) is list, code)
    return val


def _req_int(val: Any, code: str) -> int:
    require_ok(type(val) is int, code)
    return val


def _check_invariants(checks: list[tuple[bool, str]]) -> None:
    for ok, code in checks:
        require_ok(ok, code)


def _audit_hadamard_row(row: Any, exp_k: int, exp_alpha: Fraction, prefix: str) -> None:
    rd = _req_exact_dict(row, _P1_H_KEYS, f"{prefix}_SCHEMA")
    exp_comm = 0 if exp_alpha == 1 else 2 * (exp_k - 1)
    exp_diag = (exp_alpha + exp_k - 1) / exp_k
    exp_off = abs(exp_alpha - 1) / exp_k
    exp_imp = (exp_alpha * exp_alpha + exp_k - 1) / exp_k
    _check_invariants(
        [
            (rd["order"] == exp_k, f"{prefix}_ORDER"),
            (parse_canonical_q(rd["spike_alpha_q"], f"{prefix}_ALPHA") == exp_alpha, f"{prefix}_ALPHA_VAL"),
            (rd["commutator_nonzero_entries"] == exp_comm, f"{prefix}_COMM"),
            (rd["commutator_total_entries"] == exp_k * exp_k, f"{prefix}_COMM"),
            (rd["all_diagonals_flattened"] is True, f"{prefix}_FLAT"),
            (rd["all_off_diagonals_uniform_abs"] is True, f"{prefix}_FLAT"),
            (parse_canonical_q(rd["smeared_diagonal_q"], f"{prefix}_DIAG") == exp_diag, f"{prefix}_DIAG_VAL"),
            (parse_canonical_q(rd["off_diagonal_abs_q"], f"{prefix}_OFF") == exp_off, f"{prefix}_OFF_VAL"),
            (parse_canonical_q(rd["unweighted_mse_q"], f"{prefix}_UNW") == Fraction(1, 1), f"{prefix}_UNW_VAL"),
            (parse_canonical_q(rd["true_importance_mse_q"], f"{prefix}_IMP") == exp_imp, f"{prefix}_IMP_VAL"),
            (rd["true_importance_mse_dec4"] == dec_str(exp_imp, 4), f"{prefix}_DEC4"),
        ]
    )


def _audit_pillar_1_semantics(p1: dict[str, Any]) -> None:
    p1 = _req_exact_dict(p1, _P1_KEYS, "P1_SCHEMA")
    _audit_hadamard_row(p1["hadamard_h8_skewed_d8"], 8, Fraction(8, 1), "P1_H8")
    _audit_hadamard_row(p1["hadamard_h8_isotropic_control"], 8, Fraction(1, 1), "P1_ISO")

    ladder = _req_list(p1["hadamard_o_k_smearing_ladder"], "P1_LADDER_NOT_LIST")
    require_ok(len(ladder) == 4, "P1_LADDER_LEN")
    for row, exp_k in zip(ladder, (2, 4, 8, 16)):
        _audit_hadamard_row(row, exp_k, Fraction(exp_k, 1), "P1_LADDER")

    perm = _req_exact_dict(p1["axis_aligned_perm_control"], _P1_PERM_KEYS, "P1_PERM_SCHEMA")
    hh = _req_exact_dict(p1["householder_reflection_dpi_witness"], _P1_HH_KEYS, "P1_HH_SCHEMA")
    d_list = _req_list(hh["axis_d_q"], "P1_HH_AXIS")
    require_ok(len(d_list) == 4, "P1_HH_AXIS_LEN")
    d_vals = [parse_canonical_q(x, "P1_HH_AXIS_Q") for x in d_list]
    fb = parse_canonical_q(hh["frob_norm_sq_before_q"], "P1_HH_FB")
    fa = parse_canonical_q(hh["frob_norm_sq_after_q"], "P1_HH_FA")
    fd = parse_canonical_q(hh["global_frob_delta_q"], "P1_HH_FD")
    qn = _req_int(hh["qwen3_8b_total_neurons"], "P1_QWEN_N")
    gn = _req_int(hh["gemma4_12b_total_neurons"], "P1_GEMMA_N")
    q_conc = Fraction(qn, 100)
    r_un = parse_canonical_q(hh["refusal_unedited_q"], "P1_REF_UN")
    r_wr = parse_canonical_q(hh["refusal_writes_mirrored_q"], "P1_REF_WR")
    r_bo = parse_canonical_q(hh["refusal_both_mirrored_q"], "P1_REF_BO")

    _check_invariants(
        [
            (p1["all_verified"] is True, "P1_NOT_VERIFIED"),
            (perm["diagonal_preserved_max"] == 8, "P1_PERM_MAX"),
            (perm["off_diagonal_leakage"] == 0, "P1_PERM_LEAK"),
            (perm["s70_swiglu_perm_max_abs_diff"] == 0, "P1_PERM_LEAK"),
            (perm["s59_a16_rho_axis"] == 1, "P1_S59_RHO"),
            (perm["s59_a16_rho_h16"] == 4, "P1_S59_RHO"),
            (perm["s59_opposite_sign_contrast"] == 8, "P1_S59_CONTRAST"),
            (parse_canonical_q(perm["importance_mse_ratio_q"], "P1_PERM_MSE") == Fraction(1, 1), "P1_PERM_MSE_VAL"),
            (sum((x * x for x in d_vals), Fraction(0)) == Fraction(1, 1), "P1_HH_UNIT"),
            (hh["k2_is_involution"] is True, "P1_HH_K2"),
            (hh["k2_is_isometry"] is True, "P1_HH_K2"),
            (hh["k1_is_idempotent"] is True, "P1_HH_K1"),
            (fb > 0, "P1_HH_ZERO_FROB_DELTA"),
            (fa == fb, "P1_HH_ZERO_FROB_DELTA"),
            (fd == 0, "P1_HH_ZERO_FROB_DELTA"),
            (parse_canonical_q(hh["diff_matrix_frob_sq_q"], "P1_HH_DF") > 0, "P1_HH_DIFF_NONZERO"),
            (hh["diff_matrix_exact_rank"] == 1, "P1_HH_RANK1"),
            (parse_canonical_q(hh["dpi_spectral_concentration_q"], "P1_HH_DPI") == Fraction(1, 1), "P1_HH_DPI_VAL"),
            (parse_canonical_q(hh["witness_4row_peak_to_mean_q"], "P1_HH_P2M") == Fraction(4, 1), "P1_HH_P2M_VAL"),
            (qn == 442368, "P1_QWEN_COUNTS"),
            (hh["qwen3_8b_poles"] == 2 * qn, "P1_QWEN_COUNTS"),
            (hh["qwen3_8b_heads"] == 1152, "P1_QWEN_COUNTS"),
            (gn == 737280, "P1_GEMMA_COUNTS"),
            (hh["gemma4_12b_poles"] == 2 * gn, "P1_GEMMA_COUNTS"),
            (hh["gemma4_12b_heads"] == 768, "P1_GEMMA_COUNTS"),
            (parse_canonical_q(hh["qwen3_8b_100neuron_dpi_conc_q"], "P1_QWEN_CONC") == q_conc, "P1_QWEN_CONC_VAL"),
            (hh["qwen3_8b_100neuron_dpi_conc_dec2"] == dec_str(q_conc, 2), "P1_QWEN_CONC_DEC2"),
            (parse_canonical_q(hh["s31_two_row_dpi_anchor_q"], "P1_S31_DPI") == Fraction(75968, 1), "P1_S31_DPI_VAL"),
            (r_un == Fraction(5, 6), "P1_REFUSAL_VALS"),
            (r_wr == Fraction(1, 12), "P1_REFUSAL_VALS"),
            (r_bo == Fraction(1, 24), "P1_REFUSAL_VALS"),
            (hh["relp_rs_adjoint_exact"] is True, "P1_RELP_ADJOINT"),
            (
                parse_canonical_q(hh["relp_rs_adjoint_lhs_q"], "P1_RELP_LHS")
                == parse_canonical_q(hh["relp_rs_adjoint_rhs_q"], "P1_RELP_RHS"),
                "P1_RELP_EQ",
            ),
        ]
    )


def _audit_pillar_2_semantics(p2: dict[str, Any]) -> None:
    p2 = _req_exact_dict(p2, _P2_KEYS, "P2_SCHEMA")
    ba = _req_exact_dict(p2["bonsai25_primary_anchors"], _P2_BA_KEYS, "P2_BA_SCHEMA")
    hw = _req_exact_dict(p2["hardware_three_tier_specs"], _P2_HW_KEYS, "P2_HW_SCHEMA")
    regs = _req_dict(p2["dense_27b_regimes"], "P2_REGS_NOT_DICT")
    moe = _req_exact_dict(p2["magnitude_sparse_moe_contrast"], _P2_MOE_KEYS, "P2_MOE_SCHEMA")
    s86 = _req_exact_dict(p2["s86_8gib_training_anchor"], _P2_S86_KEYS, "P2_S86_SCHEMA")

    n_b = parse_canonical_q(ba["params_total_b_q"], "P2_NB")
    fp16_gb = parse_canonical_q(ba["fp16_size_gb_q"], "P2_FP16")
    ptq_gb = parse_canonical_q(ba["ptq10_size_gb_q"], "P2_PTQ")
    ptq_bpw = parse_canonical_q(ba["ptq10_bpw_q"], "P2_BPW")
    comp = fp16_gb / ptq_gb
    tool_r = parse_canonical_q(ba["tool_calling_retention_q"], "P2_TOOL")
    code_r = parse_canonical_q(ba["agentic_coding_retention_q"], "P2_CODE")
    gen_r = parse_canonical_q(ba["general_capability_retention_q"], "P2_GEN")

    c_gpu = parse_canonical_q(hw["c_gpu_weight_budget_gb_q"], "P2_CGPU")
    c_ram = parse_canonical_q(hw["c_ram_gb_q"], "P2_CRAM")
    b_gpu = parse_canonical_q(hw["b_gpu_gbs_q"], "P2_BGPU")
    b_ram = parse_canonical_q(hw["b_ram_gbs_q"], "P2_BRAM")
    b_ssd = parse_canonical_q(hw["b_ssd_gbs_q"], "P2_BSSD")
    b_crit = (Fraction(8, 1) * c_gpu) / n_b

    act_frac = parse_canonical_q(moe["active_expert_fraction_q"], "P2_MOE_FRAC")
    act_gb = parse_canonical_q(moe["active_bytes_per_token_gb_q"], "P2_MOE_GB")
    h100_tps = b_gpu / act_gb
    h80_time = (act_gb * Fraction(4, 5)) / b_gpu + (act_gb * Fraction(1, 5)) / b_ram
    h80_tps = Fraction(1, 1) / h80_time
    h80_slow = h80_time / (act_gb / b_gpu)

    r64 = _req_int(s86["qwen3b_r64_peak_alloc_bytes"], "P2_S86_INT")
    r128 = _req_int(s86["qwen3b_r128_peak_alloc_bytes"], "P2_S86_INT")
    bits_f = _req_int(s86["bits_freed_16_to_3bpw"], "P2_S86_INT")

    checks: list[tuple[bool, str]] = [
        (p2["all_verified"] is True, "P2_NOT_VERIFIED"),
        (parse_canonical_q(ba["compression_ratio_q"], "P2_COMP") == comp, "P2_COMP_VAL"),
        (ba["compression_ratio_dec4"] == dec_str(comp, 4), "P2_COMP_DEC4"),
        (tool_r == Fraction(772, 777), "P2_TOOL_VAL"),
        (ba["tool_calling_retention_pct_dec2"] == dec_str(tool_r * 100, 2), "P2_TOOL_DEC2"),
        (code_r == Fraction(542, 605), "P2_CODE_VAL"),
        (ba["agentic_coding_retention_pct_dec2"] == dec_str(code_r * 100, 2), "P2_CODE_DEC2"),
        (gen_r == Fraction(2053, 2108), "P2_GEN_VAL"),
        (ba["general_capability_retention_pct_dec2"] == dec_str(gen_r * 100, 2), "P2_GEN_DEC2"),
        (hw["vram_total_mib"] == 8192, "P2_HW_VRAM"),
        (_req_int(hw["c_ssd_gb"], "P2_HW_SSD") > 0, "P2_HW_SSD"),
        (b_ssd < b_ram, "P2_BW_ORDER"),
        (b_ram < b_gpu, "P2_BW_ORDER"),
        (parse_canonical_q(hw["gpu_over_ram_penalty_q"], "P2_PEN_RAM") == b_gpu / b_ram, "P2_PEN_RAM_VAL"),
        (parse_canonical_q(hw["gpu_over_ssd_penalty_q"], "P2_PEN_SSD") == b_gpu / b_ssd, "P2_PEN_SSD_VAL"),
        (parse_canonical_q(hw["dense_27b_residency_cliff_bpw_q"], "P2_BCRIT") == b_crit, "P2_BCRIT_VAL"),
        (hw["dense_27b_residency_cliff_bpw_dec4"] == dec_str(b_crit, 4), "P2_BCRIT_DEC4"),
        (hw["bonsai_below_residency_cliff"] is True, "P2_BELOW_CLIFF"),
        (ptq_bpw < b_crit, "P2_BELOW_CLIFF"),
        (act_frac == Fraction(1, 20), "P2_MOE_GB_VAL"),
        (act_gb == fp16_gb * act_frac, "P2_MOE_GB_VAL"),
        (moe["fits_in_gpu_hot_cache"] is True, "P2_MOE_FITS"),
        (act_gb <= c_gpu, "P2_MOE_FITS"),
        (parse_canonical_q(moe["hit100_tps_q"], "P2_MOE_H100") == h100_tps, "P2_MOE_H100_VAL"),
        (moe["hit100_tps_dec4"] == dec_str(h100_tps, 4), "P2_MOE_H100_DEC4"),
        (parse_canonical_q(moe["hit80_ram20_tps_q"], "P2_MOE_H80") == h80_tps, "P2_MOE_H80_VAL"),
        (moe["hit80_ram20_tps_dec4"] == dec_str(h80_tps, 4), "P2_MOE_H80_DEC4"),
        (parse_canonical_q(moe["hit80_ram20_slowdown_q"], "P2_MOE_H80S") == h80_slow, "P2_MOE_H80S_VAL"),
        (moe["hit80_ram20_slowdown_dec4"] == dec_str(h80_slow, 4), "P2_MOE_H80S_DEC4"),
        (r64 == 5130998272, "P2_S86_VALS"),
        (r128 == 6914886656, "P2_S86_VALS"),
        (bits_f == 36068917248, "P2_S86_VALS"),
    ]

    exp_sizes = {
        "bonsai25_ptq10_1p76bpw": ptq_gb,
        "a16_quadsnake_3p0bpw": (n_b * Fraction(3, 1)) / Fraction(8, 1),
        "quant_4p5bpw": (n_b * Fraction(9, 2)) / Fraction(8, 1),
        "fp16_16p0bpw": fp16_gb,
    }
    require_ok(frozenset(regs.keys()) == frozenset(exp_sizes.keys()), "P2_REGS_KEYS")
    for name, exp_m in exp_sizes.items():
        r = _req_exact_dict(regs[name], _P2_REG_KEYS, "P2_REG_ROW")
        m_val = parse_canonical_q(r["model_gb_q"], "P2_REG_M")
        mg = m_val if m_val <= c_gpu else c_gpu
        mr = (m_val - mg) if (m_val - mg) <= c_ram else c_ram
        ms = m_val - mg - mr
        t_tok = mg / b_gpu + mr / b_ram + ms / b_ssd
        exp_slow = t_tok / (m_val / b_gpu)
        exp_tps = Fraction(1, 1) / t_tok
        checks.extend(
            [
                (m_val == exp_m, "P2_REG_M_VAL"),
                (parse_canonical_q(r["m_gpu_gb_q"], "P2_MG") == mg, "P2_MG_VAL"),
                (parse_canonical_q(r["m_ram_gb_q"], "P2_MR") == mr, "P2_MR_VAL"),
                (parse_canonical_q(r["m_ssd_gb_q"], "P2_MS") == ms, "P2_MS_VAL"),
                (parse_canonical_q(r["f_gpu_q"], "P2_FG") == mg / m_val, "P2_FG_VAL"),
                (parse_canonical_q(r["f_ram_q"], "P2_FR") == mr / m_val, "P2_FR_VAL"),
                (parse_canonical_q(r["f_ssd_q"], "P2_FS") == ms / m_val, "P2_FS_VAL"),
                (parse_canonical_q(r["spill_slowdown_q"], "P2_SLOW") == exp_slow, "P2_SLOW_VAL"),
                (r["spill_slowdown_dec4"] == dec_str(exp_slow, 4), "P2_SLOW_DEC4"),
                (parse_canonical_q(r["roofline_tps_q"], "P2_TPS") == exp_tps, "P2_TPS_VAL"),
                (r["roofline_tps_dec4"] == dec_str(exp_tps, 4), "P2_TPS_DEC4"),
                (r["fully_gpu_resident"] is (mg == m_val), "P2_RESIDENT_FLAG"),
            ]
        )
    _check_invariants(checks)


def _audit_ref_mixture(entry: Any, exp_lam: Fraction, prefix: str) -> None:
    md = _req_exact_dict(entry, _P3_MIX_KEYS, f"{prefix}_SCHEMA")
    mq = parse_canonical_q(md["q_true_q"], f"{prefix}_Q")
    mr = parse_canonical_q(md["r_ref_q"], f"{prefix}_R")
    ml = parse_canonical_q(md["lambda_q"], f"{prefix}_L")
    mp = parse_canonical_q(md["p_star_q"], f"{prefix}_P")
    _check_invariants(
        [
            (ml == exp_lam, f"{prefix}_LAM_VAL"),
            (mp == ml * mq + (1 - ml) * mr, f"{prefix}_PSTAR"),
            (parse_canonical_q(md["abs_bias_q"], f"{prefix}_BIAS") == abs(mp - mq), f"{prefix}_BIAS_VAL"),
            (parse_canonical_q(md["excess_true_brier_q"], f"{prefix}_EX") == (mp - mq) ** 2, f"{prefix}_EX_VAL"),
            (md["anchored_to_outcomes"] is (ml > 0), f"{prefix}_ANCHOR"),
        ]
    )


def _audit_pillar_3_semantics(p3: dict[str, Any]) -> None:
    p3 = _req_exact_dict(p3, _P3_KEYS, "P3_SCHEMA")
    a1 = _req_exact_dict(p3["axis1_zero_dw_kv_sleep"], _P3_A1_KEYS, "P3_A1_SCHEMA")
    kvr = _req_exact_dict(a1["s79_last_loop_kv_ratios"], _P3_KVR_KEYS, "P3_KVR_SCHEMA")
    a2 = _req_exact_dict(p3["axis2_weight_modifying_consolidation"], _P3_A2_KEYS, "P3_A2_SCHEMA")
    bp = _req_exact_dict(a2["brier_overconfidence_paradox"], _P3_BP_KEYS, "P3_BP_SCHEMA")
    fp = _req_exact_dict(p3["five_gate_consolidation_fixed_point"], _P3_GATE_KEYS, "P3_FP_SCHEMA")
    abls = _req_dict(p3["borromean_five_gate_ablations"], "P3_ABLS_NOT_DICT")

    rho = parse_canonical_q(a1["s76_contractive_rho_q"], "P3_RHO")
    fwer1 = parse_canonical_q(a2["s80_songe_1night_fwer_q"], "P3_S80_1N")
    fwer20 = Fraction(1, 1) - (Fraction(1, 1) - fwer1) ** 20
    qt = parse_canonical_q(bp["q_true_q"], "P3_BP_Q")
    pf = parse_canonical_q(bp["p_fcst_q"], "P3_BP_P")
    bs_t = parse_canonical_q(bp["expected_bs_true_q"], "P3_BP_BST")
    bs_f = parse_canonical_q(bp["expected_bs_fcst_q"], "P3_BP_BSF")
    y1_t = (1 - qt) ** 2
    y1_f = (1 - pf) ** 2
    h_def = _req_int(a2["harvey_tenet_early_stop_steps_default"], "P3_HARVEY_INT")
    h_beam = _req_int(a2["harvey_tenet_early_stop_steps_beam"], "P3_HARVEY_INT")

    _audit_ref_mixture(a2["reference_mixture_half"], Fraction(1, 2), "P3_MH")
    _audit_ref_mixture(a2["reference_mixture_pure_ref"], Fraction(0, 1), "P3_M0")
    _audit_ref_mixture(a2["reference_mixture_pure_outcome"], Fraction(1, 1), "P3_M1")

    expected_fail = {
        "ablate_g1_divergent_sleep_loop": "gate1_sleep_loop_contractive",
        "ablate_g2_unbudgeted_forgetting": "gate2_forgetting_budgeted",
        "ablate_g3_unanchored_reference_only": "gate3_outcome_anchored",
        "ablate_g4_unguarded_songe_goodhart": "gate4_anti_goodhart_clean",
        "ablate_g5_vram_spill_violation": "gate5_memory_residency_ok",
    }
    require_ok(frozenset(abls.keys()) == frozenset(expected_fail.keys()), "P3_ABLS_KEYS")

    checks: list[tuple[bool, str]] = [
        (p3["all_verified"] is True, "P3_NOT_VERIFIED"),
        (parse_canonical_q(a1["sleep_n2_token_efficiency_q"], "P3_N2") == Fraction(21, 10), "P3_N2_VAL"),
        (parse_canonical_q(a1["sleep_n4_token_efficiency_q"], "P3_N4") == Fraction(239, 100), "P3_N4_VAL"),
        (parse_canonical_q(a1["arxiv_2504_13171_ttc_reduction_q"], "P3_TTC") == Fraction(5, 1), "P3_TTC_VAL"),
        (parse_canonical_q(a1["arxiv_2504_13171_multiquery_amort_q"], "P3_AMORT") == Fraction(5, 2), "P3_AMORT_VAL"),
        (a1["wake_latency_overhead"] == 0, "P3_ZERO_OVERHEAD"),
        (a1["kv_cache_size_growth"] == 0, "P3_ZERO_OVERHEAD"),
        (parse_canonical_q(a1["weight_forgetting_ratio_q"], "P3_ZERO_F") == Fraction(0, 1), "P3_ZERO_F_VAL"),
        (a1["cross_session_persistence"] is False, "P3_A1_PERSIST"),
        (rho < 1, "P3_RHO_E4"),
        (parse_canonical_q(a1["s76_loop2_err_q"], "P3_E2") == rho ** 2, "P3_RHO_E2"),
        (parse_canonical_q(a1["s76_loop4_err_q"], "P3_E4") == rho ** 4, "P3_RHO_E4"),
        (parse_canonical_q(a1["s79_circularep_loop4_q"], "P3_CEP") == Fraction(81, 256), "P3_CEP_VAL"),
        (parse_canonical_q(a1["s50_within_session_state_frob_sq_q"], "P3_S50F") == Fraction(212, 5), "P3_S50F_VAL"),
        (parse_canonical_q(a1["s50_margin_flip_delta_q"], "P3_S50M") == Fraction(-133, 25), "P3_S50M_VAL"),
        (a2["cross_session_persistence"] is True, "P3_A2_PERSIST"),
        (parse_canonical_q(a2["s78_forgetting_over_learning_q"], "P3_S78_F") == Fraction(1, 1), "P3_S78_F_VAL"),
        (fwer1 == Fraction(39, 400), "P3_S80_1N_VAL"),
        (a2["s80_songe_20night_fwer_dec4"] == dec_str(fwer20, 4), "P3_S80_20N_DEC"),
        (a2["s80_ratchet_clean_outside_accepts"] == 5, "P3_S80_CLEAN"),
        (a2["s80_ratchet_goodhart_accepts"] == 0, "P3_S80_RATCHET"),
        (parse_canonical_q(a2["tm_forecasting_cost_reduction_q"], "P3_TM_COST") == Fraction(15, 1), "P3_TM_COST_VAL"),
        (a2["tm_forecasting_synthetic_questions"] == 45000, "P3_TM_SYNTH"),
        (h_def > 0, "P3_HARVEY_VALS"),
        (h_beam > h_def, "P3_HARVEY_VALS"),
        (bs_t == qt * (1 - qt), "P3_BP_DECOMP"),
        (bs_f == bs_t + (pf - qt) ** 2, "P3_BP_DECOMP"),
        (parse_canonical_q(bp["excess_penalty_q"], "P3_BP_EX") == bs_f - bs_t, "P3_BP_EX_VAL"),
        (parse_canonical_q(bp["single_draw_y1_true_err_q"], "P3_BP_Y1T") == y1_t, "P3_BP_Y1_VAL"),
        (parse_canonical_q(bp["single_draw_y1_fcst_err_q"], "P3_BP_Y1F") == y1_f, "P3_BP_Y1_VAL"),
        (bp["overconfident_wins_on_y1"] is True, "P3_BP_FLAGS"),
        (bp["calibrated_strictly_better_in_expectation"] is True, "P3_BP_FLAGS"),
        (fp["all_five_gates_pass"] is True, "P3_FP_PASS"),
        (parse_canonical_q(fp["error_after_steps_q"], "P3_FP_ERR") == Fraction(1, 256), "P3_FP_ERR_VAL"),
        (p3["all_five_ablations_rejected"] is True, "P3_ABLS_FLAG"),
    ]
    for g_key in expected_fail.values():
        checks.append((fp[g_key] is True, "P3_FP_GATE"))
    for kname, l_len in (("r4_w64_l2048_q", 2048), ("r4_w64_l8192_q", 8192), ("r4_w64_l32768_q", 32768)):
        checks.append((parse_canonical_q(kvr[kname], "P3_KVR_Q") == Fraction(4 * l_len, l_len + 192), "P3_KVR_VAL"))
    for ab_name, fail_key in expected_fail.items():
        ab = _req_exact_dict(abls[ab_name], _P3_GATE_KEYS, "P3_ABL_ROW")
        ab_err = parse_canonical_q(ab["error_after_steps_q"], "P3_ABL_ERR")
        exp_err = Fraction(625, 256) if ab_name == "ablate_g1_divergent_sleep_loop" else Fraction(1, 256)
        checks.append((ab["all_five_gates_pass"] is False, "P3_ABL_NOT_REJECTED"))
        checks.append((ab_err == exp_err, "P3_ABL_ERR_VAL"))
        for g_key in expected_fail.values():
            checks.append((ab[g_key] is (g_key != fail_key), "P3_ABL_GATE_PATTERN"))
    _check_invariants(checks)


def _audit_pillar_4_semantics(p4: dict[str, Any]) -> None:
    p4 = _req_exact_dict(p4, _P4_KEYS, "P4_SCHEMA")
    w6 = _req_list(p4["wave6_snapshot_pins"], "P4_W6_LIST")
    up = _req_list(p4["upstream_cert_pins"], "P4_UP_LIST")
    lc = _req_exact_dict(p4["lean4_companion"], _P4_LEAN_KEYS, "P4_LEAN_SCHEMA")
    nov = _req_exact_dict(p4["novelty_honesty_law4"], _P4_NOV_KEYS, "P4_NOV_SCHEMA")

    checks: list[tuple[bool, str]] = [
        (p4["zero_dataset_copies_in_expedition"] is True, "P4_NO_COPIES"),
        (p4["wave6_snapshot_count"] == len(WAVE6_SNAPSHOT_PINS), "P4_W6_LEN"),
        (len(w6) == len(WAVE6_SNAPSHOT_PINS), "P4_W6_LEN"),
        (p4["upstream_cert_count"] == len(UPSTREAM_CERT_PINS), "P4_UP_LEN"),
        (len(up) == len(UPSTREAM_CERT_PINS), "P4_UP_LEN"),
        (lc["file"] == LEAN_FILE_NAME, "P4_LEAN_META"),
        (lc["toolchain"] == LEAN_TOOLCHAIN, "P4_LEAN_META"),
        (lc["theorem_count"] == len(EXPECTED_LEAN_THEOREMS), "P4_LEAN_COUNT"),
        (lc["all_theorems_universally_quantified"] is True, "P4_LEAN_UNIV"),
        (lc["theorems"] == list(EXPECTED_LEAN_THEOREMS), "P4_LEAN_THMS"),
        (lc["allowed_axioms"] == ["propext"], "P4_LEAN_AXIOMS"),
        (nov["novelty_tier"] == NOVELTY_TIER, "P4_NOV_TIER"),
        (nov["n0_prior_art_anchored"] is True, "P4_NOV_FLAGS"),
        (nov["n1_exact_synthesis_verified"] is True, "P4_NOV_FLAGS"),
        (_req_int(nov["n2_claims"], "P4_NOV_N2") == 0, "P4_NOV_N2"),
    ]
    _check_invariants(checks)
    require_ok(_is_sha256_hex(lc["sha256"]), "P4_LEAN_SHA")
    require_ok(hmac.compare_digest(lc["sha256"], EXPECTED_LEAN_SHA256), "P4_LEAN_SHA")

    for item, exp in zip(w6, WAVE6_SNAPSHOT_PINS):
        d = _req_exact_dict(item, _P4_W6_PIN_KEYS, "P4_W6_ITEM")
        require_ok(_is_sha256_hex(d["sha256"]), "P4_W6_SHA")
        _check_invariants(
            [
                (d["portal"] == exp["portal"], "P4_W6_PIN_MISMATCH"),
                (d["filename"] == exp["filename"], "P4_W6_NAME"),
                (_req_int(d["bytes"], "P4_W6_BYTES") == exp["bytes"], "P4_W6_BYTES_POS"),
                (hmac.compare_digest(d["sha256"], exp["sha256"]), "P4_W6_SHA"),
            ]
        )

    for item, exp in zip(up, UPSTREAM_CERT_PINS):
        d = _req_exact_dict(item, _P4_UP_PIN_KEYS, "P4_UP_ITEM")
        require_ok(_is_sha256_hex(d["sha256"]), "P4_UP_SHA")
        _check_invariants(
            [
                (d["track_id"] == exp["track_id"], "P4_UP_FIELDS"),
                (d["relative_ref"] == exp["relative_ref"], "P4_UP_FIELDS"),
                (_req_int(d["bytes"], "P4_UP_BYTES") == exp["bytes"], "P4_UP_BYTES_POS"),
                (hmac.compare_digest(d["sha256"], exp["sha256"]), "P4_UP_SHA"),
            ]
        )


def audit_payload_semantics(payload: Any) -> dict[str, Any]:
    """Fail-closed in-memory Zone-B secondary semantic auditor for the payload dict."""
    _check_json_tree(payload)
    p = _req_dict(payload, "PAYLOAD_NOT_DICT")
    require_ok(frozenset(p.keys()) == REQUIRED_PAYLOAD_KEYS, "PAYLOAD_KEYS_MISMATCH")
    stack: list[Any] = [p]
    while stack:
        cur = stack.pop()
        if type(cur) is dict:
            for k, v in cur.items():
                if type(v) is bool:
                    require_ok(k in _PAYLOAD_BOOL_KEYS, f"UNEXPECTED_BOOL_FIELD:{k}")
                elif type(v) in (dict, list):
                    stack.append(v)
        else:
            for item in cur:
                require_ok(type(item) is not bool, "UNEXPECTED_BOOL_ITEM")
                if type(item) in (dict, list):
                    stack.append(item)
    require_ok(p["track_id"] == TRACK_ID, "PAYLOAD_TRACK_MISMATCH")
    require_ok(p["oracle_class"] == ORACLE_CLASS, "ORACLE_CLASS_MISMATCH")
    require_ok(p["novelty_tier"] == NOVELTY_TIER, "NOVELTY_TIER_MISMATCH")
    require_ok(p["all_pillars_verified"] is True, "PILLARS_NOT_VERIFIED")
    _audit_pillar_1_semantics(_req_dict(p["pillar_1_privileged_neuron_basis"], "P1_NOT_DICT"))
    _audit_pillar_2_semantics(_req_dict(p["pillar_2_bonsai_magnitude_roofline"], "P2_NOT_DICT"))
    _audit_pillar_3_semantics(_req_dict(p["pillar_3_sleep_trilogy_consolidation"], "P3_NOT_DICT"))
    _audit_pillar_4_semantics(_req_dict(p["pillar_4_provenance_and_lean4"], "P4_NOT_DICT"))
    return p


def secondary_audit_payload(payload: Any) -> dict[str, Any]:
    """Direct SEC entrypoint for v2.1 Zone-B fuzzer and library callers."""
    return audit_payload_semantics(payload)


def verify_certificate_dict(cert: Any, *, full_replay: bool = True) -> dict[str, Any]:
    """Fail-closed Zone-B certificate verifier supporting FR1 (full_replay=True) and FR0 (full_replay=False)."""
    require_ok(type(full_replay) is bool, "INVALID_FULL_REPLAY_FLAG")
    _check_json_tree(cert)
    c = _req_dict(cert, "CERT_NOT_DICT")
    require_ok(frozenset(c.keys()) == REQUIRED_CERT_KEYS, "CERT_KEYS_MISMATCH")
    require_ok(c["schema_version"] == SCHEMA_VERSION, "SCHEMA_VERSION_MISMATCH")
    require_ok(c["track_id"] == TRACK_ID, "TRACK_ID_MISMATCH")
    require_ok(_is_sha256_hex(c["payload_sha256"]), "INVALID_PAYLOAD_SHA256")
    require_ok(_is_sha256_hex(c["certificate_sha256"]), "INVALID_CERT_SHA256")
    payload = _req_dict(c["payload"], "PAYLOAD_NOT_DICT")

    calc_p = hashlib.sha256(canonical_json_bytes(payload)).hexdigest()
    require_ok(hmac.compare_digest(c["payload_sha256"], calc_p), "PAYLOAD_SHA256_TAMPERED")
    body = {
        "schema_version": c["schema_version"],
        "track_id": c["track_id"],
        "payload_sha256": c["payload_sha256"],
        "payload": payload,
    }
    calc_c = hashlib.sha256(canonical_json_bytes(body)).hexdigest()
    require_ok(hmac.compare_digest(c["certificate_sha256"], calc_c), "CERTIFICATE_SHA256_TAMPERED")

    audit_payload_semantics(payload)

    if full_replay:
        expected = build_certificate_envelope()
        require_ok(exact_typed_equal(payload, expected["payload"]), "ORACLE_PAYLOAD_DRIFT")
        require_ok(hmac.compare_digest(c["certificate_sha256"], expected["certificate_sha256"]), "ORACLE_CERT_DRIFT")
    return {
        "status": "PASS",
        "track_id": TRACK_ID,
        "full_replay": full_replay,
        "secondary_audit_passed": True,
        "payload_sha256": c["payload_sha256"],
        "certificate_sha256": c["certificate_sha256"],
    }


def check_certificate_file(path: Path, *, full_replay: bool = True) -> dict[str, Any]:
    raw = read_regular_file_bytes(path, max_bytes=MAX_JSON_BYTES)
    parsed = parse_strict_json_bytes(raw)
    return verify_certificate_dict(parsed, full_replay=full_replay)


# ---------------------------------------------------------------------------
# Read-Only On-Disk Pin Verification (10 Upstream Certs + 12 Wave-6 Snapshots)
# ---------------------------------------------------------------------------

def verify_pins_on_disk(
    *,
    expedition_root: Path | None = None,
    wave6_root: Path | None = None,
) -> dict[str, Any]:
    require_ok(expedition_root is not None or wave6_root is not None, "NO_PIN_ROOT_SPECIFIED")
    result: dict[str, Any] = {"status": "PINS_VERIFIED"}
    if expedition_root is not None:
        _validate_path(expedition_root)
        require_ok(expedition_root.is_dir(), "EXPEDITION_ROOT_INVALID")
        for pin in UPSTREAM_CERT_PINS:
            raw = read_regular_file_bytes(expedition_root / pin["relative_ref"], max_bytes=MAX_JSON_BYTES)
            require_ok(len(raw) == pin["bytes"], f"UPSTREAM_BYTES_MISMATCH:{pin['track_id']}")
            got_sha = hashlib.sha256(raw).hexdigest()
            require_ok(hmac.compare_digest(got_sha, pin["sha256"]), f"UPSTREAM_SHA_MISMATCH:{pin['track_id']}")
        result["upstream_certs_verified"] = len(UPSTREAM_CERT_PINS)
    if wave6_root is not None:
        _validate_path(wave6_root)
        require_ok(wave6_root.is_dir(), "WAVE6_ROOT_INVALID")
        for pin in WAVE6_SNAPSHOT_PINS:
            raw = read_regular_file_bytes(wave6_root / pin["filename"], max_bytes=MAX_JSON_BYTES)
            require_ok(len(raw) == pin["bytes"], f"WAVE6_BYTES_MISMATCH:{pin['filename']}")
            got_sha = hashlib.sha256(raw).hexdigest()
            require_ok(hmac.compare_digest(got_sha, pin["sha256"]), f"WAVE6_SHA_MISMATCH:{pin['filename']}")
        result["wave6_snapshots_verified"] = len(WAVE6_SNAPSHOT_PINS)
    return result


# ---------------------------------------------------------------------------
# R10+ Static & Live Lean 4.36.0 Verification (Zero-TOCTOU --stdin + $HOME CI)
# ---------------------------------------------------------------------------

def strip_lean_comments_only(source: str) -> tuple[str, list[str]]:
    """Strip Lean line (--) and nested block (/- ... -/) comments only; never swallows quotes."""
    out: list[str] = []
    errors: list[str] = []
    i = 0
    n = len(source)
    depth = 0
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
        if ch == "/" and nxt == "-":
            depth = 1
            out.append("  ")
            i += 2
            continue
        if ch == "-" and nxt == "-":
            i += 2
            out.append("  ")
            while i < n and source[i] != "\n":
                out.append(" ")
                i += 1
            continue
        out.append(ch)
        i += 1
    if depth > 0:
        errors.append("LEAN_UNTERMINATED_BLOCK_COMMENT")
    return "".join(out), errors


def audit_lean_source_static(source: str) -> dict[str, Any]:
    """R10+ fail-closed static Lean 4 scanner (end-anchored decide native + quote/guillemet ban)."""
    require_ok(type(source) is str, "LEAN_SOURCE_NOT_STR")
    cleaned, findings = strip_lean_comments_only(source)
    if _LEAN_QUOTE_OR_GUILLEMET_RE.search(cleaned) is not None:
        findings.append("LEAN_QUOTE_OR_GUILLEMET_FORBIDDEN")
    norm = cleaned.replace("«", "").replace("»", "")
    m_forb = _LEAN_FORBIDDEN_RE.search(norm)
    if m_forb is not None:
        findings.append(f"LEAN_FORBIDDEN_KEYWORD:{m_forb.group(0)}")
    if _LEAN_PARTIAL_RE.search(norm) is not None:
        findings.append("LEAN_PARTIAL_DECL")
    if _LEAN_DECIDE_NATIVE_RE.search(norm) is not None:
        findings.append("LEAN_DECIDE_NATIVE")
    if _LEAN_SKIP_TC_RE.search(norm) is not None:
        findings.append("LEAN_SKIP_KERNEL_TC")
    if _LEAN_EVAL_SPOOF_RE.search(norm) is not None:
        findings.append("LEAN_EVAL_OR_PRINT_SPOOF")
    if _LEAN_ATTR_ESCAPE_RE.search(norm) is not None:
        findings.append("LEAN_ATTR_TRUST_ESCAPE")
    imports = [m.group(1) for m in _LEAN_IMPORT_RE.finditer(norm)]
    if imports:
        findings.append(f"LEAN_NON_ZERO_IMPORTS:{','.join(imports)}")
    return {"clean": len(findings) == 0, "findings": findings, "imports": imports}


def resolve_lean_binary() -> str:
    """Resolve lean binary via ALETHEIA_LEAN_BIN, PATH, or $HOME env (never /etc/passwd)."""
    env_bin = os.environ.get("ALETHEIA_LEAN_BIN")
    if env_bin:
        p = Path(env_bin)
        require_ok(p.is_file() and os.access(p, os.X_OK), "LEAN_BINARY_UNAVAILABLE")
        return str(p)
    found = shutil.which("lean")
    if found is not None:
        return found
    home_env = os.environ.get("HOME")
    if home_env:
        for rel in (".local/bin/lean", ".elan/bin/lean"):
            cand = Path(home_env) / rel
            if cand.is_file() and os.access(cand, os.X_OK):
                return str(cand)
    raise ValueError("LEAN_BINARY_UNAVAILABLE")


def verify_lean_proof(path: Path, *, enforce_sha256: bool = True) -> dict[str, Any]:
    """Run R10+ static scan + zero-TOCTOU live `lean --stdin` kernel axiom verification."""
    require_ok(type(enforce_sha256) is bool, "INVALID_ENFORCE_SHA256_FLAG")
    raw = read_regular_file_bytes(path, max_bytes=MAX_JSON_BYTES)
    require_ok(b"\r" not in raw, "CRLF_FORBIDDEN")
    try:
        source = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValueError("LEAN_INVALID_UTF8") from exc
    sha = hashlib.sha256(raw).hexdigest()
    if enforce_sha256:
        require_ok(hmac.compare_digest(sha, EXPECTED_LEAN_SHA256), "LEAN_SHA256_MISMATCH")
    static_res = audit_lean_source_static(source)
    require_ok(static_res["clean"], f"LEAN_STATIC_AUDIT_FAILED:{static_res['findings']}")

    lean_bin = resolve_lean_binary()
    proc = subprocess.run(
        [lean_bin, "--stdin"],
        input=source,
        capture_output=True,
        text=True,
        timeout=120,
        check=False,
    )
    require_ok(proc.returncode == 0, f"LEAN_COMPILE_FAILED:{proc.stderr.strip()}")
    require_ok(proc.stderr == "", f"LEAN_NONEMPTY_STDERR:{proc.stderr.strip()}")

    coalesced: list[str] = []
    for raw_ln in proc.stdout.splitlines():
        if raw_ln.startswith("  ") and coalesced:
            coalesced[-1] = coalesced[-1] + " " + raw_ln.strip()
        else:
            coalesced.append(raw_ln.strip())

    seen: dict[str, list[str]] = {}
    zero_ax_count = 0
    axioms_used: set[str] = set()
    for line in coalesced:
        m0 = _ZERO_AXIOM_LINE_RE.match(line)
        if m0 is not None:
            thm = m0.group(1)
            require_ok(thm not in seen, f"LEAN_DUPLICATE_THEOREM:{thm}")
            seen[thm] = []
            zero_ax_count += 1
            continue
        m1 = _DEPENDS_AXIOM_LINE_RE.match(line)
        require_ok(m1 is not None, f"LEAN_UNEXPECTED_STDOUT_LINE:{line}")
        thm = m1.group(1)
        require_ok(thm not in seen, f"LEAN_DUPLICATE_THEOREM:{thm}")
        ax_list = [a.strip() for a in m1.group(2).split(",")]
        for ax in ax_list:
            require_ok(ax in _ALLOWED_LEAN_AXIOMS, f"LEAN_FORBIDDEN_AXIOM:{ax}")
            axioms_used.add(ax)
        seen[thm] = ax_list

    require_ok(len(seen) >= 1, "LEAN_NO_THEOREMS_VERIFIED")
    if enforce_sha256:
        require_ok(tuple(seen.keys()) == EXPECTED_LEAN_THEOREMS, "LEAN_THEOREM_LIST_MISMATCH")
    return {
        "lean_file": path.name,
        "lean_sha256": sha,
        "sha256_pinned": enforce_sha256,
        "static_clean": True,
        "theorems_verified": len(seen),
        "zero_axiom_theorems": zero_ax_count,
        "axioms_used": sorted(axioms_used),
        "imports": [],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Track S94 Wave-6 Convergence Hardened Verifier")
    mode = parser.add_mutually_exclusive_group(required=False)
    mode.add_argument("--standalone", action="store_true", help="Emit canonical certificate JSON")
    mode.add_argument("--write", type=Path, help="Atomically write canonical 0o600 certificate JSON")
    mode.add_argument("--check", type=Path, help="Fail-closed Zone-B verification of certificate JSON")
    mode.add_argument("--verify-lean", type=Path, help="R10+ static + live Lean 4.36.0 verification")
    mode.add_argument("--verify-pins", action="store_true", help="Verify pinned upstream certs / Wave-6 snapshots")
    parser.add_argument("--expedition-root", type=Path, default=None, help="Read-only expedition parent root")
    parser.add_argument("--wave6-root", type=Path, default=None, help="Read-only Wave-6 snapshot directory")
    parser.add_argument("--json", action="store_true", help="Emit JSON output")
    args = parser.parse_args(argv)

    try:
        if args.write is not None:
            cert = build_certificate_envelope()
            verify_certificate_dict(cert, full_replay=True)
            atomic_write_0600(args.write, canonical_json_bytes(cert))
            if args.json:
                sys.stdout.buffer.write(
                    canonical_json_bytes({"status": "WRITTEN", "certificate_sha256": cert["certificate_sha256"]})
                )
            return 0
        if args.check is not None:
            res = check_certificate_file(args.check, full_replay=True)
            if args.json:
                sys.stdout.buffer.write(canonical_json_bytes(res))
            return 0
        if args.verify_lean is not None:
            res = verify_lean_proof(args.verify_lean, enforce_sha256=True)
            if args.json:
                sys.stdout.buffer.write(canonical_json_bytes(res))
            return 0
        if args.verify_pins:
            res = verify_pins_on_disk(expedition_root=args.expedition_root, wave6_root=args.wave6_root)
            if args.json:
                sys.stdout.buffer.write(canonical_json_bytes(res))
            return 0
        cert = build_certificate_envelope()
        verify_certificate_dict(cert, full_replay=True)
        sys.stdout.buffer.write(canonical_json_bytes(cert))
        return 0
    except (ValueError, OSError) as exc:
        sys.stderr.write(f"ERROR: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
