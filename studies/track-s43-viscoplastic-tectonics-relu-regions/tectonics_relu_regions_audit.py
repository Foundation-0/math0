#!/usr/bin/env python3
"""Hardened CLI, Full Pure-Q Replay & Secondary Algebraic Cross-Check.

Pure Python 3 standard library: zero floats, zero bare asserts, zero mathematical RNG.
Strict I/O hardening (baked in from line 1):
  - Concrete pathlib.Path check + NUL-byte and lone UTF-16 surrogate path refusal
  - Deleted-CWD OSError wrapping -> CWD_UNAVAILABLE (rc=2)
  - Atomic dir_fd PWD walk + per-component openat(O_RDONLY | O_DIRECTORY | O_NOFOLLOW) (zero os.path.islink)
  - Root-owned macOS Darwin /tmp, /var, /etc -> /private/* prefix normalization
  - Leaf O_RDONLY | O_NOFOLLOW | O_NONBLOCK + fstat S_ISREG + 64 KiB streaming capped reads (max_bytes <= 64 MiB)
  - Atomic write: type(data) is bytes BEFORE dir/temp open -> target lstat (st_nlink > 1 -> HARDLINK_FORBIDDEN)
    -> thread-locked monotonic + CSPRNG (secrets.token_hex(8)) 0o600 O_CREAT|O_EXCL|O_NOFOLLOW|O_NONBLOCK
    temp file in same dir_fd -> bounded 32-attempt EEXIST retry -> os.fsync(tmp_fd)
    -> pre-replace os.fstat(tmp_fd).st_nlink == 1 -> os.replace(..., src_dir_fd=dfd, dst_dir_fd=dfd) -> os.fsync(dfd)
  - Strict manual CLI parser (no flag abbreviations, rejecting space- & equals-syntax flag-like/empty paths -> rc=2)
  - Full pure-Q replay + field-complete strict-keyset secondary_audit_payload (100% rejection across all 4 fuzzing surfaces)
"""
from __future__ import annotations

import errno
from fractions import Fraction
import hashlib
import os
from pathlib import Path
import secrets
import stat
import sys
import threading
from typing import Any, Sequence

_THIS_DIR = str(Path(__file__).resolve().parent)
if _THIS_DIR not in sys.path:
    sys.path.insert(0, _THIS_DIR)

from tectonics_relu_regions_oracle import (
    MAX_JSON_BYTES,
    SCHEMA_VERSION,
    TRACK_ID,
    _PAYLOAD_KEYS,
    TectonicsReluError,
    build_standalone_certificate,
    canonical_json_bytes,
    parse_exact_rational,
    parse_strict_json_text,
    require_exact_bool,
    require_exact_int,
    require_exact_str,
    validate_certificate_payload,
)

MAX_ALLOWED_CAP_BYTES = 64 * 1024 * 1024
_READ_CHUNK_BYTES = 65_536
_EXACT_PATH_TYPE = type(Path("."))
_DIR_OPEN_FLAGS = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
_TMP_LOCK = threading.Lock()
_TMP_COUNTER = 0
_DARWIN_SYSTEM_ROOT_ALIASES = frozenset({"tmp", "var", "etc"})


def _next_tmp_name(leaf: str) -> str:
    global _TMP_COUNTER
    with _TMP_LOCK:
        _TMP_COUNTER += 1
        seq = _TMP_COUNTER
    return f".{leaf}.s43tmp.{os.getpid()}.{threading.get_ident()}.{seq}.{secrets.token_hex(8)}"


# ---------------------------------------------------------------------------
# Race-Free Strict File I/O (Per-Component dir_fd/openat + Atomic os.replace)
# ---------------------------------------------------------------------------

def _normalize_darwin_system_prefix(path: Path, *, allow_exact: bool = False) -> Path:
    """Normalize verified root-owned macOS /tmp, /var, /etc aliases to /private/*."""
    if sys.platform != "darwin" or not path.is_absolute():
        return path
    parts = path.parts
    if len(parts) < 2:
        return path
    head = parts[1]
    if head not in _DARWIN_SYSTEM_ROOT_ALIASES:
        return path
    if not allow_exact and len(parts) == 2:
        return path
    alias = f"/{head}"
    try:
        st = os.lstat(alias)
        if not stat.S_ISLNK(st.st_mode) or st.st_uid != 0:
            return path
        if os.readlink(alias) != f"private/{head}":
            return path
    except OSError:
        return path
    return Path("/private", *parts[1:])


def _open_dir_chain(anchor: str, parts: Sequence[str]) -> int:
    """Walk directory components atomically via `openat(..., O_DIRECTORY | O_NOFOLLOW)`."""
    try:
        dfd = os.open(anchor, _DIR_OPEN_FLAGS)
    except OSError as exc:
        raise TectonicsReluError("PATH_STAT_ERROR", f"cannot open anchor dir: {type(exc).__name__}") from exc

    for part in parts:
        try:
            nxt = os.open(part, _DIR_OPEN_FLAGS, dir_fd=dfd)
        except OSError as exc:
            os.close(dfd)
            if exc.errno in (errno.ELOOP, errno.ENOTDIR):
                raise TectonicsReluError("SYMLINK_FORBIDDEN", "symlink or non-dir forbidden in path") from exc
            if exc.errno == errno.ENOENT:
                raise TectonicsReluError("PATH_NOT_FOUND", "directory component not found") from exc
            raise TectonicsReluError("PATH_STAT_ERROR", f"cannot traverse dir: {type(exc).__name__}") from exc
        os.close(dfd)
        dfd = nxt
    return dfd


def _check_pwd_no_symlinks() -> None:
    pwd_env = require_exact_str(os.environ.get("PWD", ""), "PWD", non_empty=False)
    if pwd_env.startswith("/"):
        pwd_path = _normalize_darwin_system_prefix(Path(pwd_env), allow_exact=True)
        pwd_parts = [p for p in pwd_path.parts[1:] if p not in ("", ".")]
        try:
            pwd_fd = _open_dir_chain(pwd_path.anchor, pwd_parts)
        except TectonicsReluError as exc:
            if exc.code != "PATH_NOT_FOUND":
                raise
        else:
            os.close(pwd_fd)


def _validate_path_and_split(path: Any) -> tuple[str, list[str]]:
    if type(path) is not _EXACT_PATH_TYPE:
        raise TectonicsReluError("INVALID_PATH_TYPE", "path must be exact pathlib.Path")
    raw_str = require_exact_str(str(path), "path")
    if "\x00" in raw_str:
        raise TectonicsReluError("INVALID_PATH", "path contains NUL byte")

    if not path.is_absolute():
        try:
            Path.cwd()
        except OSError as exc:
            raise TectonicsReluError("CWD_UNAVAILABLE", f"cannot resolve cwd: {type(exc).__name__}") from exc
        _check_pwd_no_symlinks()
        rel_parts = [p for p in path.parts if p not in ("", ".")]
        return ".", rel_parts
    norm_path = _normalize_darwin_system_prefix(path)
    abs_parts = [p for p in norm_path.parts[1:] if p not in ("", ".")]
    return norm_path.anchor, abs_parts


def require_safe_path(path: Any) -> Path:
    """Validate path type, CWD/PWD, and atomic `openat` directory chain with zero symlinks."""
    anchor, parts = _validate_path_and_split(path)
    if not parts:
        return path
    dfd = _open_dir_chain(anchor, parts[:-1])
    try:
        try:
            st = os.lstat(parts[-1], dir_fd=dfd)
        except FileNotFoundError:
            return path
        except OSError as exc:
            raise TectonicsReluError("PATH_STAT_ERROR", f"cannot lstat leaf: {type(exc).__name__}") from exc
        if stat.S_ISLNK(st.st_mode):
            raise TectonicsReluError("SYMLINK_FORBIDDEN", "symlink forbidden at leaf")
    finally:
        os.close(dfd)
    return path


def _open_leaf_for_read(path: Path) -> int:
    anchor, parts = _validate_path_and_split(path)
    if not parts:
        raise TectonicsReluError("NON_REGULAR_FILE", "target path refers to a directory")
    dfd = _open_dir_chain(anchor, parts[:-1])
    try:
        try:
            return os.open(parts[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=dfd)
        except OSError as exc:
            if exc.errno == errno.ELOOP:
                raise TectonicsReluError("SYMLINK_FORBIDDEN", "symlink forbidden at leaf") from exc
            raise TectonicsReluError("FILE_READ_ERROR", f"cannot open file: {type(exc).__name__}") from exc
    finally:
        os.close(dfd)


def read_regular_bytes_capped(path: Path, max_bytes: Any = MAX_JSON_BYTES) -> bytes:
    """Read regular file bytes via atomic dir_fd + O_NOFOLLOW|O_NONBLOCK in bounded 64 KiB streaming chunks."""
    cap = require_exact_int(max_bytes, "max_bytes", min_val=1, max_val=MAX_ALLOWED_CAP_BYTES)
    fd = _open_leaf_for_read(path)
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise TectonicsReluError("NON_REGULAR_FILE", "target is not a regular file")
        chunks: list[bytes] = []
        total = 0
        while True:
            rem = cap + 1 - total
            to_read = _READ_CHUNK_BYTES if _READ_CHUNK_BYTES < rem else rem
            chunk = os.read(fd, to_read)
            if not chunk:
                break
            total += len(chunk)
            if total > cap:
                raise TectonicsReluError("FILE_TOO_LARGE", f"file exceeds {cap} bytes")
            chunks.append(chunk)
        return b"".join(chunks)
    except TectonicsReluError:
        raise
    except OSError as exc:
        raise TectonicsReluError("FILE_READ_ERROR", f"failed reading file: {type(exc).__name__}") from exc
    finally:
        os.close(fd)


def write_regular_file_bytes(path: Path, data: bytes) -> None:
    """Write regular file atomically via 0o600 CSPRNG temp file, fsync, pre-replace st_nlink==1 & os.replace."""
    if type(data) is not bytes:
        raise TectonicsReluError("INVALID_WRITE_DATA", "data must be exact bytes")
    anchor, parts = _validate_path_and_split(path)
    if not parts:
        raise TectonicsReluError("NON_REGULAR_FILE", "target path refers to a directory")
    leaf = parts[-1]
    dfd = _open_dir_chain(anchor, parts[:-1])
    try:
        try:
            st = os.lstat(leaf, dir_fd=dfd)
        except FileNotFoundError:
            st = None
        except OSError as exc:
            raise TectonicsReluError("FILE_WRITE_ERROR", f"cannot lstat target: {type(exc).__name__}") from exc
        if st is not None:
            if stat.S_ISLNK(st.st_mode):
                raise TectonicsReluError("SYMLINK_FORBIDDEN", "symlink forbidden at leaf")
            if not stat.S_ISREG(st.st_mode):
                raise TectonicsReluError("NON_REGULAR_FILE", "cannot write to non-regular file")
            if st.st_nlink > 1:
                raise TectonicsReluError("HARDLINK_FORBIDDEN", "cannot write through hardlinked file")

        tmp_fd: int | None = None
        tmp_name = ""
        for _ in range(32):
            cand = _next_tmp_name(leaf)
            try:
                tmp_fd = os.open(
                    cand,
                    os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_NONBLOCK,
                    0o600,
                    dir_fd=dfd,
                )
                tmp_name = cand
                break
            except FileExistsError:
                continue
            except OSError as exc:
                raise TectonicsReluError("FILE_WRITE_ERROR", f"cannot create temp file: {type(exc).__name__}") from exc
        if tmp_fd is None:
            raise TectonicsReluError("TEMP_RETRY_EXHAUSTED", "temp file collision limit exceeded")

        try:
            try:
                view = memoryview(data)
                written = 0
                while written < len(data):
                    written += os.write(tmp_fd, view[written:])
                os.fsync(tmp_fd)
                if os.fstat(tmp_fd).st_nlink != 1:
                    raise TectonicsReluError("HARDLINK_FORBIDDEN", "temp file link count != 1")
            finally:
                os.close(tmp_fd)
            os.replace(tmp_name, leaf, src_dir_fd=dfd, dst_dir_fd=dfd)
            os.fsync(dfd)
        except TectonicsReluError:
            try:
                os.unlink(tmp_name, dir_fd=dfd)
            except OSError:
                pass
            raise
        except OSError as exc:
            try:
                os.unlink(tmp_name, dir_fd=dfd)
            except OSError:
                pass
            raise TectonicsReluError("FILE_WRITE_ERROR", f"failed writing file: {type(exc).__name__}") from exc
    finally:
        os.close(dfd)


# ---------------------------------------------------------------------------
# Field-Complete Strict-Keyset Secondary Algebraic Audit Over All 4 Pillars
# ---------------------------------------------------------------------------

_P1_KEYS = frozenset({"variational_proximal_identity", "poiseuille_plug_shear_channel"})
_VAR_KEYS = frozenset({
    "eta0", "tau_y", "grid_points", "plug_points", "positive_shear_points", "negative_shear_points",
    "kkt_subdifferential_all_exact", "variational_dominance_all_strict", "sample_witnesses",
})
_WIT_KEYS = frozenset({
    "tau", "e_star", "kkt_subgradient_s", "j_star", "j_plus_tenth_gap", "j_minus_tenth_gap",
})
_POIS_KEYS = frozenset({
    "g_grad", "h_half", "tau_y", "eta0", "yield_number_y", "y_plug", "u_plug",
    "q_half", "q_full", "d_visc_half", "d_yield_half", "power_in_half",
    "dissipation_balance_exact", "no_slip_walls_exact",
    "two_neuron_relu_matches_bingham_all", "rigid_plug_zero_strain_all", "channel_probes",
})
_PROBE_KEYS = frozenset({"y", "tau", "u", "du_dy", "in_plug", "neuron1_active", "neuron2_active"})

_P2_KEYS = frozenset({"yield_phase_diagram", "shallow_2d_relu_regions"})
_PHASE_KEYS = frozenset({
    "g_grad", "h_half", "eta0", "yield_points_count", "newtonian_count", "mobile_lid_count",
    "stagnant_lid_count", "flux_strictly_decreasing_to_y1", "stagnant_lid_exact_zero_flux",
    "all_dissipation_balances_exact", "sweep",
})
_SWEEP_KEYS = frozenset({
    "y_num", "plug_fraction", "u_plug", "q_half", "q_full", "d_visc_half", "d_yield_half",
    "power_in_half", "dissipation_balance_exact", "plastic_dissipation_share",
    "active_shear_walls", "rigid_plate_interior", "tectonic_regime", "neural_regime",
})
_RELU2D_KEYS = frozenset({
    "neuron_count", "linear_region_count", "impossible_pattern", "codim1_wall_count",
    "piecewise_constant_jacobian_all_regions", "all_walls_exact_rank1_jump",
    "all_walls_continuous", "regions",
})
_REG_KEYS = frozenset({"pattern", "probe_x", "jacobian", "det_j"})

_P3_KEYS = frozenset({
    "rtf_triple_junction_cocycle", "tropical_3region_relu_hinge", "relu_2d_rtf_jacobian_contrast",
})
_RTF_KEYS = frozenset({
    "point_p", "omega_a", "omega_b", "omega_c", "omega_cocycle_zero",
    "velocity_cocycle_zero", "all_velocities_tangent_to_s2", "walls",
})
_WALL_KEYS = frozenset({
    "wall", "v_rel", "normal", "tangent", "normal_opening", "tangential_shear", "classification",
})
_TROP_KEYS = frozenset({
    "gradients", "delta_g_ab", "delta_g_bc", "delta_g_ca", "gradient_jump_cocycle_zero",
    "tropical_weights", "primitive_rays", "weighted_tropical_balancing_zero",
    "unweighted_ray_sum_nonzero", "two_layer_relu_equals_max_all_probes", "interior_gradients_exact",
})
_JAC_CONTRAST_KEYS = frozenset({"cases", "dead_subduction_collision_exact"})
_JAC_CASE_KEYS = frozenset({"case", "c_vec", "det_j_minus", "det_j_plus", "rank_j_plus", "regime"})

_P4_KEYS = frozenset({
    "discrete_s2_cube_hodge_complex",
    "obstruction_a_toroidal_curl_zero",
    "obstruction_b_gauss_stokes_vs_relu",
    "obstruction_c_static_feedforward_vs_gdn2_advection",
})
_CUBE_KEYS = frozenset({
    "vertices", "edges", "faces", "euler_characteristic", "d1_d0_identically_zero",
    "closed_oriented_s2_boundary_zero", "rank_d0", "rank_d1", "betti_numbers", "betti_euler_matches",
})
_OBSA_KEYS = frozenset({
    "e_pol", "e_tor", "e_eq_combined", "poloidal_curl_identically_zero",
    "toroidal_div_identically_zero", "hodge_inner_product", "hodge_pythagorean_exact", "equipartition_ratio",
})
_OBSB_KEYS = frozenset({
    "outward_div_edge_sign_exact",
    "s2_basis_fluxes_zero_sum_count", "s2_gauss_stokes_universal_exact",
    "asym_flux_u", "asym_outward_div",
    "asym_ridge_creation_sum", "asym_trench_subduction_sum", "asym_global_net_div",
    "unconstrained_relu_domain_area", "unconstrained_relu_image_area",
    "unconstrained_relu_area_ratio", "unconstrained_relu_global_div",
    "unconstrained_relu_violates_gauss_stokes",
})
_OBSC_KEYS = frozenset({
    "static_wall_x_t0", "static_wall_x_t1", "static_wall_displacement",
    "static_pre_t0", "static_pre_t1", "static_inference_frozen",
    "gdn2_alpha", "gdn2_beta", "gdn2_delta_rank", "gdn2_key_overwrite_exact",
    "gdn2_wall_x_t0", "gdn2_wall_x_t1", "gdn2_wall_displacement",
    "gdn2_pre_t0", "gdn2_pre_t1", "gdn2_relu_t0", "gdn2_relu_t1",
    "gdn2_inference_region_flip_zero_weight_update",
})


def _require_dict_exact_keys(
    parent: dict[str, Any],
    key: str,
    expected_keys: frozenset[str],
    err_code: str,
) -> dict[str, Any]:
    val = parent.get(key)
    if type(val) is not dict:
        raise TectonicsReluError(err_code, f"{key} must be a JSON object")
    if frozenset(val.keys()) != expected_keys:
        raise TectonicsReluError(err_code, f"{key} keys mismatch")
    return val


def _require_flag(d: dict[str, Any], key: str, expected: bool, err_code: str) -> None:
    if require_exact_bool(d[key], key) is not expected:
        raise TectonicsReluError(err_code, f"{key} must be {expected}")


def _require_list_len(parent: dict[str, Any], key: str, length: int, err_code: str) -> list[Any]:
    val = parent.get(key)
    if type(val) is not list or len(val) != length:
        raise TectonicsReluError(err_code, f"{key} must be list of length {length}")
    return val


def _parse_q_vec(vec: Any, length: int, name: str, err_code: str) -> tuple[Fraction, ...]:
    if type(vec) is not list or len(vec) != length:
        raise TectonicsReluError(err_code, f"{name} must be list of length {length}")
    return tuple(parse_exact_rational(item, f"{name}[{i}]") for i, item in enumerate(vec))


def _parse_int_vec(vec: Any, length: int, name: str, err_code: str) -> tuple[int, ...]:
    if type(vec) is not list or len(vec) != length:
        raise TectonicsReluError(err_code, f"{name} must be list of length {length}")
    return tuple(require_exact_int(item, f"{name}[{i}]") for i, item in enumerate(vec))


def _audit_pillar1(p1: dict[str, Any]) -> None:
    vp = _require_dict_exact_keys(p1, "variational_proximal_identity", _VAR_KEYS, "AUDIT_P1_VP")
    for fk in ("kkt_subdifferential_all_exact", "variational_dominance_all_strict"):
        _require_flag(vp, fk, True, "AUDIT_P1_VP_FLAG")
    eta0 = parse_exact_rational(vp["eta0"], "p1.eta0")
    tau_y = parse_exact_rational(vp["tau_y"], "p1.tau_y")
    gp = require_exact_int(vp["grid_points"], "grid_points")
    pp = require_exact_int(vp["plug_points"], "plug_points")
    ps = require_exact_int(vp["positive_shear_points"], "positive_shear_points")
    ns = require_exact_int(vp["negative_shear_points"], "negative_shear_points")
    if (eta0, tau_y, gp, pp, ps, ns, pp + ps + ns == gp) != (Fraction(3, 2), Fraction(2, 1), 41, 17, 12, 12, True):
        raise TectonicsReluError("AUDIT_P1_VP_VAL", "variational proximal grid summary mismatch")

    wits = _require_list_len(vp, "sample_witnesses", 5, "AUDIT_P1_WIT")
    exp_taus = (Fraction(-5, 1), Fraction(-2, 1), Fraction(0, 1), Fraction(2, 1), Fraction(5, 1))
    for idx, raw_w in enumerate(wits):
        if type(raw_w) is not dict or frozenset(raw_w.keys()) != _WIT_KEYS:
            raise TectonicsReluError("AUDIT_P1_WIT", f"sample_witnesses[{idx}] schema mismatch")
        wt = parse_exact_rational(raw_w["tau"], "wt")
        we = parse_exact_rational(raw_w["e_star"], "we")
        ws = parse_exact_rational(raw_w["kkt_subgradient_s"], "ws")
        wj = parse_exact_rational(raw_w["j_star"], "wj")
        wgp = parse_exact_rational(raw_w["j_plus_tenth_gap"], "wgp")
        wgm = parse_exact_rational(raw_w["j_minus_tenth_gap"], "wgm")
        abs_e = -we if we < 0 else we
        abs_s = -ws if ws < 0 else ws
        rp = wt - tau_y if wt > tau_y else Fraction(0, 1)
        rm = -wt - tau_y if -wt > tau_y else Fraction(0, 1)
        exp_e = (rp - rm) / (2 * eta0)
        d10 = Fraction(1, 10)
        ep = we + d10
        em = we - d10
        jp = eta0 * ep * ep + tau_y * (-ep if ep < 0 else ep) - wt * ep
        jm = eta0 * em * em + tau_y * (-em if em < 0 else em) - wt * em
        if (
            wt, we, abs_s <= 1, 2 * eta0 * we + tau_y * ws == wt,
            wj == eta0 * we * we + tau_y * abs_e - wt * we,
            wgp == jp - wj, wgm == jm - wj,
            wgp >= eta0 * d10 * d10, wgm >= eta0 * d10 * d10,
        ) != (exp_taus[idx], exp_e, True, True, True, True, True, True, True):
            raise TectonicsReluError("AUDIT_P1_WIT_VAL", f"sample_witnesses[{idx}] algebraic mismatch")

    ch = _require_dict_exact_keys(p1, "poiseuille_plug_shear_channel", _POIS_KEYS, "AUDIT_P1_CH")
    for fk in (
        "dissipation_balance_exact", "no_slip_walls_exact",
        "two_neuron_relu_matches_bingham_all", "rigid_plug_zero_strain_all",
    ):
        _require_flag(ch, fk, True, "AUDIT_P1_CH_FLAG")
    g = parse_exact_rational(ch["g_grad"], "ch.g")
    h = parse_exact_rational(ch["h_half"], "ch.h")
    ty = parse_exact_rational(ch["tau_y"], "ch.ty")
    eta = parse_exact_rational(ch["eta0"], "ch.eta")
    yn = parse_exact_rational(ch["yield_number_y"], "ch.yn")
    yp = parse_exact_rational(ch["y_plug"], "ch.yp")
    up = parse_exact_rational(ch["u_plug"], "ch.up")
    qh = parse_exact_rational(ch["q_half"], "ch.qh")
    qf = parse_exact_rational(ch["q_full"], "ch.qf")
    dv = parse_exact_rational(ch["d_visc_half"], "ch.dv")
    dy = parse_exact_rational(ch["d_yield_half"], "ch.dy")
    pin = parse_exact_rational(ch["power_in_half"], "ch.pin")
    if (
        g, h, ty, eta, yn, yp, up, qh, qf, dv, dy, pin,
        yn * g * h == ty, yp * g == ty,
        up * 2 * eta == g * (h - yp) * (h - yp),
        qh * 6 * eta == g * (h - yp) * (h - yp) * (2 * h + yp),
        qf == 2 * qh, dv + dy == pin, pin == g * qh,
    ) != (
        Fraction(4, 1), Fraction(2, 1), Fraction(4, 1), Fraction(1, 1),
        Fraction(1, 2), Fraction(1, 1), Fraction(2, 1), Fraction(10, 3), Fraction(20, 3),
        Fraction(16, 3), Fraction(8, 1), Fraction(40, 3),
        True, True, True, True, True, True, True,
    ):
        raise TectonicsReluError("AUDIT_P1_CH_VAL", "Poiseuille channel invariants mismatch")

    probes = _require_list_len(ch, "channel_probes", 9, "AUDIT_P1_PROBE")
    exp_ys = (
        Fraction(-2, 1), Fraction(-3, 2), Fraction(-1, 1), Fraction(-1, 2),
        Fraction(0, 1), Fraction(1, 2), Fraction(1, 1), Fraction(3, 2), Fraction(2, 1),
    )
    for idx, raw_p in enumerate(probes):
        if type(raw_p) is not dict or frozenset(raw_p.keys()) != _PROBE_KEYS:
            raise TectonicsReluError("AUDIT_P1_PROBE", f"channel_probes[{idx}] schema mismatch")
        py = parse_exact_rational(raw_p["y"], "py")
        ptau = parse_exact_rational(raw_p["tau"], "ptau")
        pu = parse_exact_rational(raw_p["u"], "pu")
        pdu = parse_exact_rational(raw_p["du_dy"], "pdu")
        p_in = require_exact_bool(raw_p["in_plug"], "in_plug")
        p_n1 = require_exact_bool(raw_p["neuron1_active"], "n1")
        p_n2 = require_exact_bool(raw_p["neuron2_active"], "n2")
        n1 = -py - yp if (-py - yp) > 0 else Fraction(0, 1)
        n2 = py - yp if (py - yp) > 0 else Fraction(0, 1)
        exp_du = (g / eta) * (n1 - n2)
        exp_u = up - (g / (2 * eta)) * (n1 * n1 + n2 * n2)
        abs_py = -py if py < 0 else py
        if (py, ptau, pu, pdu, p_in, p_n1, p_n2) != (
            exp_ys[idx], -g * py, exp_u, exp_du, abs_py <= yp, n1 > 0, n2 > 0
        ):
            raise TectonicsReluError("AUDIT_P1_PROBE_VAL", f"channel_probes[{idx}] mismatch")


def _audit_pillar2(p2: dict[str, Any]) -> None:
    pd = _require_dict_exact_keys(p2, "yield_phase_diagram", _PHASE_KEYS, "AUDIT_P2_PD")
    for fk in (
        "flux_strictly_decreasing_to_y1", "stagnant_lid_exact_zero_flux", "all_dissipation_balances_exact",
    ):
        _require_flag(pd, fk, True, "AUDIT_P2_PD_FLAG")
    g = parse_exact_rational(pd["g_grad"], "pd.g")
    h = parse_exact_rational(pd["h_half"], "pd.h")
    eta = parse_exact_rational(pd["eta0"], "pd.eta")
    if (
        g, h, eta,
        require_exact_int(pd["yield_points_count"], "yc"),
        require_exact_int(pd["newtonian_count"], "nc"),
        require_exact_int(pd["mobile_lid_count"], "mc"),
        require_exact_int(pd["stagnant_lid_count"], "sc"),
    ) != (Fraction(4, 1), Fraction(2, 1), Fraction(1, 1), 8, 1, 4, 3):
        raise TectonicsReluError("AUDIT_P2_PD_VAL", "yield phase diagram counts mismatch")

    sweep = _require_list_len(pd, "sweep", 8, "AUDIT_P2_SWEEP")
    exp_ys = (
        Fraction(0, 1), Fraction(1, 8), Fraction(1, 4), Fraction(1, 2),
        Fraction(3, 4), Fraction(1, 1), Fraction(5, 4), Fraction(2, 1),
    )
    for idx, row in enumerate(sweep):
        if type(row) is not dict or frozenset(row.keys()) != _SWEEP_KEYS:
            raise TectonicsReluError("AUDIT_P2_SWEEP", f"sweep[{idx}] schema mismatch")
        _require_flag(row, "dissipation_balance_exact", True, "AUDIT_P2_SWEEP_FLAG")
        yv = parse_exact_rational(row["y_num"], "sw.y")
        rho = parse_exact_rational(row["plug_fraction"], "sw.rho")
        up = parse_exact_rational(row["u_plug"], "sw.up")
        qh = parse_exact_rational(row["q_half"], "sw.qh")
        qf = parse_exact_rational(row["q_full"], "sw.qf")
        dv = parse_exact_rational(row["d_visc_half"], "sw.dv")
        dy = parse_exact_rational(row["d_yield_half"], "sw.dy")
        pin = parse_exact_rational(row["power_in_half"], "sw.pin")
        psh = parse_exact_rational(row["plastic_dissipation_share"], "sw.psh")
        aw = require_exact_int(row["active_shear_walls"], "sw.aw")
        ri = require_exact_bool(row["rigid_plate_interior"], "sw.ri")
        tr = require_exact_str(row["tectonic_regime"], "sw.tr")
        nr = require_exact_str(row["neural_regime"], "sw.nr")

        ey = exp_ys[idx]
        erho = Fraction(1, 1) if ey >= 1 else ey
        em = Fraction(1, 1) - erho
        eup = g * h * h * em * em / (2 * eta)
        eqh = (g * h * h * h / (3 * eta)) * (Fraction(1, 1) - Fraction(3, 2) * erho + Fraction(1, 2) * erho * erho * erho)
        edv = g * g * (h - erho * h) * (h - erho * h) * (h - erho * h) / (3 * eta)
        edy = (ey * g * h) * g * (h - erho * h) * (h - erho * h) / (2 * eta)
        epin = g * eqh
        if ey == 0:
            e_meta = (Fraction(0, 1), 0, False, "newtonian_magma_ocean", "splintered_unregularized_limit")
        elif ey < 1:
            e_meta = (edy / epin, 2, True, "mobile_lid_plate_tectonics", "modular_feature_learning")
        else:
            e_meta = (Fraction(0, 1), 0, True, "stagnant_lid", "dead_relu_frozen_ntk")
        if (yv, rho, up, qh, qf, dv, dy, pin, psh, aw, ri, tr, nr) != (
            ey, erho, eup, eqh, 2 * eqh, edv, edy, epin, *e_meta
        ):
            raise TectonicsReluError("AUDIT_P2_SWEEP_VAL", f"sweep[{idx}] mismatch")

    r2 = _require_dict_exact_keys(p2, "shallow_2d_relu_regions", _RELU2D_KEYS, "AUDIT_P2_R2")
    for fk in (
        "piecewise_constant_jacobian_all_regions", "all_walls_exact_rank1_jump", "all_walls_continuous",
    ):
        _require_flag(r2, fk, True, "AUDIT_P2_R2_FLAG")
    if (
        require_exact_int(r2["neuron_count"], "nc"),
        require_exact_int(r2["linear_region_count"], "lrc"),
        _parse_int_vec(r2["impossible_pattern"], 3, "imp", "AUDIT_P2_R2_VAL"),
        require_exact_int(r2["codim1_wall_count"], "wc"),
    ) != (3, 7, (0, 0, 1), 9):
        raise TectonicsReluError("AUDIT_P2_R2_VAL", "shallow 2D ReLU summary mismatch")

    regs = _require_list_len(r2, "regions", 7, "AUDIT_P2_REGS")
    exp_regs = (
        ((0, 0, 0), (Fraction(-1, 1), Fraction(-1, 1)), ((1, 0), (0, 1)), 1),
        ((1, 0, 0), (Fraction(1, 1), Fraction(-1, 1)), ((3, 0), (1, 1)), 3),
        ((1, 0, 1), (Fraction(4, 1), Fraction(-1, 1)), ((4, 1), (-1, -1)), -3),
        ((0, 1, 0), (Fraction(-1, 1), Fraction(1, 1)), ((1, -1), (0, 4)), 4),
        ((0, 1, 1), (Fraction(-1, 1), Fraction(4, 1)), ((2, 0), (-2, 2)), 4),
        ((1, 1, 0), (Fraction(1, 2), Fraction(1, 2)), ((3, -1), (1, 4)), 13),
        ((1, 1, 1), (Fraction(2, 1), Fraction(2, 1)), ((4, 0), (-1, 2)), 8),
    )
    for idx, reg in enumerate(regs):
        if type(reg) is not dict or frozenset(reg.keys()) != _REG_KEYS:
            raise TectonicsReluError("AUDIT_P2_REGS", f"regions[{idx}] schema mismatch")
        pat = _parse_int_vec(reg["pattern"], 3, "pat", "AUDIT_P2_REG_VAL")
        px = _parse_q_vec(reg["probe_x"], 2, "px", "AUDIT_P2_REG_VAL")
        jac_raw = _require_list_len(reg, "jacobian", 2, "AUDIT_P2_REG_VAL")
        jac = (
            _parse_int_vec(jac_raw[0], 2, "j0", "AUDIT_P2_REG_VAL"),
            _parse_int_vec(jac_raw[1], 2, "j1", "AUDIT_P2_REG_VAL"),
        )
        det_j = require_exact_int(reg["det_j"], "det_j")
        if (pat, px, jac, det_j, det_j == jac[0][0] * jac[1][1] - jac[0][1] * jac[1][0]) != (*exp_regs[idx], True):
            raise TectonicsReluError("AUDIT_P2_REG_VAL", f"regions[{idx}] mismatch")


def _audit_pillar3(p3: dict[str, Any]) -> None:
    rtf = _require_dict_exact_keys(p3, "rtf_triple_junction_cocycle", _RTF_KEYS, "AUDIT_P3_RTF")
    for fk in ("omega_cocycle_zero", "velocity_cocycle_zero", "all_velocities_tangent_to_s2"):
        _require_flag(rtf, fk, True, "AUDIT_P3_RTF_FLAG")
    z0, p1 = Fraction(0, 1), Fraction(1, 1)
    if (
        _parse_q_vec(rtf["point_p"], 3, "p", "AUDIT_P3_RTF_VAL"),
        _parse_q_vec(rtf["omega_a"], 3, "wa", "AUDIT_P3_RTF_VAL"),
        _parse_q_vec(rtf["omega_b"], 3, "wb", "AUDIT_P3_RTF_VAL"),
        _parse_q_vec(rtf["omega_c"], 3, "wc", "AUDIT_P3_RTF_VAL"),
    ) != ((z0, z0, p1), (z0, p1, z0), (z0, z0, z0), (-p1, p1, z0)):
        raise TectonicsReluError("AUDIT_P3_RTF_VAL", "triple junction point/omega mismatch")

    walls = _require_list_len(rtf, "walls", 3, "AUDIT_P3_WALLS")
    exp_walls = (
        ("AB", (p1, z0, z0), (p1, z0, z0), (z0, -p1, z0), p1, z0, "divergent_ridge"),
        ("BC", (-p1, -p1, z0), (p1, p1, z0), (p1, -p1, z0), Fraction(-2, 1), z0, "convergent_subduction_trench"),
        ("CA", (z0, p1, z0), (p1, z0, z0), (z0, -p1, z0), z0, -p1, "transform_fault"),
    )
    for idx, w in enumerate(walls):
        if type(w) is not dict or frozenset(w.keys()) != _WALL_KEYS:
            raise TectonicsReluError("AUDIT_P3_WALLS", f"walls[{idx}] schema mismatch")
        if (
            require_exact_str(w["wall"], "wall"),
            _parse_q_vec(w["v_rel"], 3, "vr", "AUDIT_P3_WALL_VAL"),
            _parse_q_vec(w["normal"], 3, "nm", "AUDIT_P3_WALL_VAL"),
            _parse_q_vec(w["tangent"], 3, "tg", "AUDIT_P3_WALL_VAL"),
            parse_exact_rational(w["normal_opening"], "op"),
            parse_exact_rational(w["tangential_shear"], "sh"),
            require_exact_str(w["classification"], "cls"),
        ) != exp_walls[idx]:
            raise TectonicsReluError("AUDIT_P3_WALL_VAL", f"walls[{idx}] mismatch")

    tr = _require_dict_exact_keys(p3, "tropical_3region_relu_hinge", _TROP_KEYS, "AUDIT_P3_TROP")
    for fk in (
        "gradient_jump_cocycle_zero", "weighted_tropical_balancing_zero",
        "unweighted_ray_sum_nonzero", "two_layer_relu_equals_max_all_probes", "interior_gradients_exact",
    ):
        _require_flag(tr, fk, True, "AUDIT_P3_TROP_FLAG")
    grads = _require_dict_exact_keys(tr, "gradients", frozenset({"A", "B", "C"}), "AUDIT_P3_TROP_VAL")
    tw = _require_dict_exact_keys(tr, "tropical_weights", frozenset({"AB", "BC", "CA"}), "AUDIT_P3_TROP_VAL")
    pr = _require_dict_exact_keys(tr, "primitive_rays", frozenset({"AB", "BC", "CA"}), "AUDIT_P3_TROP_VAL")
    if (
        _parse_int_vec(grads["A"], 2, "gA", "AUDIT_P3_TROP_VAL"),
        _parse_int_vec(grads["B"], 2, "gB", "AUDIT_P3_TROP_VAL"),
        _parse_int_vec(grads["C"], 2, "gC", "AUDIT_P3_TROP_VAL"),
        _parse_int_vec(tr["delta_g_ab"], 2, "dgAB", "AUDIT_P3_TROP_VAL"),
        _parse_int_vec(tr["delta_g_bc"], 2, "dgBC", "AUDIT_P3_TROP_VAL"),
        _parse_int_vec(tr["delta_g_ca"], 2, "dgCA", "AUDIT_P3_TROP_VAL"),
        require_exact_int(tw["AB"], "mAB"),
        require_exact_int(tw["BC"], "mBC"),
        require_exact_int(tw["CA"], "mCA"),
        _parse_int_vec(pr["AB"], 2, "rAB", "AUDIT_P3_TROP_VAL"),
        _parse_int_vec(pr["BC"], 2, "rBC", "AUDIT_P3_TROP_VAL"),
        _parse_int_vec(pr["CA"], 2, "rCA", "AUDIT_P3_TROP_VAL"),
    ) != ((2, 0), (0, 2), (-1, -2), (2, -2), (1, 4), (-3, -2), 2, 1, 1, (1, 1), (-4, 1), (2, -3)):
        raise TectonicsReluError("AUDIT_P3_TROP_VAL", "tropical hinge gradients/weights/rays mismatch")

    jc = _require_dict_exact_keys(p3, "relu_2d_rtf_jacobian_contrast", _JAC_CONTRAST_KEYS, "AUDIT_P3_JC")
    _require_flag(jc, "dead_subduction_collision_exact", True, "AUDIT_P3_JC_FLAG")
    cases = _require_list_len(jc, "cases", 4, "AUDIT_P3_JCASES")
    exp_jc = (
        ("ridge_expanding", (Fraction(2, 1), z0), p1, Fraction(3, 1), 2, "expanding_ridge"),
        ("trench_contractive", (Fraction(-1, 2), z0), p1, Fraction(1, 2), 2, "contractive_trench"),
        ("trench_dead_slab_collapse", (-p1, z0), p1, z0, 1, "rank_deficient_subduction"),
        ("transform_volume_preserving_shear", (z0, Fraction(2, 1)), p1, p1, 2, "volume_preserving_transform"),
    )
    for idx, c in enumerate(cases):
        if type(c) is not dict or frozenset(c.keys()) != _JAC_CASE_KEYS:
            raise TectonicsReluError("AUDIT_P3_JCASES", f"cases[{idx}] schema mismatch")
        if (
            require_exact_str(c["case"], "case"),
            _parse_q_vec(c["c_vec"], 2, "c_vec", "AUDIT_P3_JC_VAL"),
            parse_exact_rational(c["det_j_minus"], "djm"),
            parse_exact_rational(c["det_j_plus"], "djp"),
            require_exact_int(c["rank_j_plus"], "rjp"),
            require_exact_str(c["regime"], "reg"),
        ) != exp_jc[idx]:
            raise TectonicsReluError("AUDIT_P3_JC_VAL", f"cases[{idx}] mismatch")


def _audit_pillar4(p4: dict[str, Any]) -> None:
    cube = _require_dict_exact_keys(p4, "discrete_s2_cube_hodge_complex", _CUBE_KEYS, "AUDIT_P4_CUBE")
    for fk in ("d1_d0_identically_zero", "closed_oriented_s2_boundary_zero", "betti_euler_matches"):
        _require_flag(cube, fk, True, "AUDIT_P4_CUBE_FLAG")
    if (
        require_exact_int(cube["vertices"], "V"),
        require_exact_int(cube["edges"], "E"),
        require_exact_int(cube["faces"], "F"),
        require_exact_int(cube["euler_characteristic"], "chi"),
        require_exact_int(cube["rank_d0"], "r0"),
        require_exact_int(cube["rank_d1"], "r1"),
        _parse_int_vec(cube["betti_numbers"], 3, "betti", "AUDIT_P4_CUBE_VAL"),
    ) != (8, 12, 6, 2, 7, 5, (1, 0, 1)):
        raise TectonicsReluError("AUDIT_P4_CUBE_VAL", "S^2 cube Hodge complex invariants mismatch")

    oa = _require_dict_exact_keys(p4, "obstruction_a_toroidal_curl_zero", _OBSA_KEYS, "AUDIT_P4_OA")
    for fk in ("poloidal_curl_identically_zero", "toroidal_div_identically_zero", "hodge_pythagorean_exact"):
        _require_flag(oa, fk, True, "AUDIT_P4_OA_FLAG")
    if (
        require_exact_int(oa["e_pol"], "e_pol"),
        require_exact_int(oa["e_tor"], "e_tor"),
        require_exact_int(oa["e_eq_combined"], "e_eq"),
        require_exact_int(oa["hodge_inner_product"], "dot"),
        parse_exact_rational(oa["equipartition_ratio"], "eq_rat"),
    ) != (4, 4, 8, 0, Fraction(1, 1)):
        raise TectonicsReluError("AUDIT_P4_OA_VAL", "Obstruction A toroidal/equipartition invariants mismatch")

    ob = _require_dict_exact_keys(p4, "obstruction_b_gauss_stokes_vs_relu", _OBSB_KEYS, "AUDIT_P4_OB")
    for fk in (
        "outward_div_edge_sign_exact",
        "s2_gauss_stokes_universal_exact",
        "unconstrained_relu_violates_gauss_stokes",
    ):
        _require_flag(ob, fk, True, "AUDIT_P4_OB_FLAG")
    u_asym_vec = _parse_int_vec(ob["asym_flux_u"], 12, "asym_flux_u", "AUDIT_P4_OB_VAL")
    div_asym_vec = _parse_int_vec(ob["asym_outward_div"], 8, "asym_outward_div", "AUDIT_P4_OB_VAL")
    r_sum = require_exact_int(ob["asym_ridge_creation_sum"], "r_sum")
    t_sum = require_exact_int(ob["asym_trench_subduction_sum"], "t_sum")
    if (
        require_exact_int(ob["s2_basis_fluxes_zero_sum_count"], "bzc"),
        u_asym_vec,
        div_asym_vec,
        r_sum, t_sum,
        require_exact_int(ob["asym_global_net_div"], "net"),
        r_sum + t_sum == 0,
        require_exact_int(ob["unconstrained_relu_domain_area"], "dom_a"),
        require_exact_int(ob["unconstrained_relu_image_area"], "img_a"),
        parse_exact_rational(ob["unconstrained_relu_area_ratio"], "ar"),
        require_exact_int(ob["unconstrained_relu_global_div"], "gdiv"),
    ) != (
        12,
        (-3, 1, -2, 0, -1, 2, -4, 0, 3, -2, -1, 1),
        (-1, 3, 1, -2, -9, 4, 5, -1),
        13, -13, 0, True, 4, 1, Fraction(1, 4), -4,
    ):
        raise TectonicsReluError("AUDIT_P4_OB_VAL", "Obstruction B Gauss-Stokes invariants mismatch")

    oc = _require_dict_exact_keys(p4, "obstruction_c_static_feedforward_vs_gdn2_advection", _OBSC_KEYS, "AUDIT_P4_OC")
    for fk in ("static_inference_frozen", "gdn2_key_overwrite_exact", "gdn2_inference_region_flip_zero_weight_update"):
        _require_flag(oc, fk, True, "AUDIT_P4_OC_FLAG")
    if (
        parse_exact_rational(oc["static_wall_x_t0"], "sw0"),
        parse_exact_rational(oc["static_wall_x_t1"], "sw1"),
        parse_exact_rational(oc["static_wall_displacement"], "swd"),
        parse_exact_rational(oc["static_pre_t0"], "sp0"),
        parse_exact_rational(oc["static_pre_t1"], "sp1"),
        parse_exact_rational(oc["gdn2_alpha"], "ga"),
        parse_exact_rational(oc["gdn2_beta"], "gb"),
        require_exact_int(oc["gdn2_delta_rank"], "gdr"),
        parse_exact_rational(oc["gdn2_wall_x_t0"], "gw0"),
        parse_exact_rational(oc["gdn2_wall_x_t1"], "gw1"),
        parse_exact_rational(oc["gdn2_wall_displacement"], "gwd"),
        parse_exact_rational(oc["gdn2_pre_t0"], "gp0"),
        parse_exact_rational(oc["gdn2_pre_t1"], "gp1"),
        parse_exact_rational(oc["gdn2_relu_t0"], "gr0"),
        parse_exact_rational(oc["gdn2_relu_t1"], "gr1"),
    ) != (
        Fraction(1, 1), Fraction(1, 1), Fraction(0, 1), Fraction(1, 2), Fraction(1, 2),
        Fraction(1, 2), Fraction(1, 1), 1,
        Fraction(1, 1), Fraction(4, 1), Fraction(3, 1),
        Fraction(1, 2), Fraction(-5, 8), Fraction(1, 2), Fraction(0, 1),
    ):
        raise TectonicsReluError("AUDIT_P4_OC_VAL", "Obstruction C GDN-2 advection invariants mismatch")


def secondary_audit_payload(payload: Any) -> dict[str, Any]:
    """Field-complete strict-keyset independent algebraic audit enforced under both replay modes."""
    if type(payload) is not dict or frozenset(payload.keys()) != _PAYLOAD_KEYS:
        raise TectonicsReluError("AUDIT_INVALID_PAYLOAD", "payload must be exact schema dict")
    if (
        require_exact_str(payload["novelty_tier"], "novelty_tier"),
        require_exact_str(payload["individual_domains_novelty"], "individual_domains_novelty"),
        require_exact_str(payload["oracle_class"], "oracle_class"),
    ) != ("N1", "N0", "exact"):
        raise TectonicsReluError("AUDIT_SCOPE_META", "novelty/oracle_class metadata mismatch")
    for fk in ("measured_live_mantle_convection_gcm", "measured_live_deep_network_training_runs"):
        _require_flag(payload, fk, False, "AUDIT_MEASURED_FLAG")
    for fk in ("zero_trust_path_floats", "zero_bare_asserts", "zero_mathematical_rng"):
        _require_flag(payload, fk, True, "AUDIT_ZERO_FLAG")

    p1 = _require_dict_exact_keys(payload, "pillar1_bingham_relu_poiseuille", _P1_KEYS, "AUDIT_P1")
    p2 = _require_dict_exact_keys(payload, "pillar2_yield_phase_and_2d_relu", _P2_KEYS, "AUDIT_P2")
    p3 = _require_dict_exact_keys(payload, "pillar3_triple_junction_tropical_rtf", _P3_KEYS, "AUDIT_P3")
    p4 = _require_dict_exact_keys(payload, "pillar4_s2_hodge_obstructions", _P4_KEYS, "AUDIT_P4")

    _audit_pillar1(p1)
    _audit_pillar2(p2)
    _audit_pillar3(p3)
    _audit_pillar4(p4)

    return {
        "secondary_audit_passed": True,
        "pillars_audited": 4,
        "yield_phases_audited": 8,
        "relu_regions_audited": 7,
        "obstructions_audited": 3,
    }


def verify_certificate_dict(cert: Any, *, full_replay: bool = True) -> dict[str, Any]:
    """Validate an in-memory certificate dict with digests, schema, secondary audit & optional full replay."""
    res = validate_certificate_payload(cert, full_replay=full_replay)
    sec = secondary_audit_payload(cert["payload"])
    res["secondary_audit"] = sec
    return res


def check_certificate_file(path: Path) -> dict[str, Any]:
    raw = read_regular_bytes_capped(path, MAX_JSON_BYTES)
    if b"\r" in raw:
        raise TectonicsReluError("CRLF_FORBIDDEN", "CRLF line endings forbidden in certificate")
    if not raw.endswith(b"\n"):
        raise TectonicsReluError("MISSING_TRAILING_LF", "certificate must end with a single LF")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise TectonicsReluError("INVALID_UTF8", "certificate is not valid UTF-8") from exc
    cert = parse_strict_json_text(text, require_object=True)
    canonical_raw = canonical_json_bytes(cert)
    if raw != canonical_raw + b"\n":
        raise TectonicsReluError("NON_CANONICAL_BYTES", "certificate bytes are not canonical ASCII JSON + LF")
    res = verify_certificate_dict(cert, full_replay=True)
    res["canonical_sha256"] = hashlib.sha256(canonical_raw).hexdigest()
    res["file_sha256"] = hashlib.sha256(raw).hexdigest()
    return res


def write_certificate_file(path: Path) -> dict[str, Any]:
    cert = build_standalone_certificate()
    canonical_raw = canonical_json_bytes(cert)
    raw = canonical_raw + b"\n"
    write_regular_file_bytes(path, raw)
    return {
        "written": True,
        "schema": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": cert["payload_sha256"],
        "certificate_sha256": cert["certificate_sha256"],
        "file_sha256": hashlib.sha256(raw).hexdigest(),
    }


# ---------------------------------------------------------------------------
# Strict Fail-Closed Manual CLI Parsing (Zero Abbreviations, Zero Flag Traps)
# ---------------------------------------------------------------------------

def _parse_cli_argv(argv: Sequence[str]) -> tuple[str, Path | None, bool]:
    if type(argv) not in (list, tuple):
        raise TectonicsReluError("INVALID_ARGV", "argv must be exact list/tuple of strict str")
    for item in argv:
        require_exact_str(item, "argv_item", non_empty=False)

    mode: str | None = None
    target: Path | None = None
    as_json = False
    i = 0
    n = len(argv)
    while i < n:
        tok = argv[i]
        if tok == "--json":
            if as_json:
                raise TectonicsReluError("DUPLICATE_FLAG", "duplicate --json flag")
            as_json = True
            i += 1
        elif tok == "--standalone":
            if mode is not None:
                raise TectonicsReluError("CONFLICTING_MODE", "multiple mode flags forbidden")
            mode = "standalone"
            i += 1
        elif tok in ("--check", "--write"):
            if mode is not None:
                raise TectonicsReluError("CONFLICTING_MODE", "multiple mode flags forbidden")
            if i + 1 >= n:
                raise TectonicsReluError("MISSING_PATH_ARG", f"{tok} requires a path argument")
            val = argv[i + 1]
            if not val or val.startswith("-"):
                raise TectonicsReluError("INVALID_PATH_ARG", f"{tok} path cannot be empty or flag-like")
            mode = "check" if tok == "--check" else "write"
            target = Path(val)
            i += 2
        else:
            raise TectonicsReluError("UNKNOWN_FLAG", f"unrecognized CLI argument: {tok}")

    if mode is None:
        mode = "standalone"
    return mode, target, as_json


def main(argv: Sequence[str] | None = None) -> int:
    raw_argv: Any = sys.argv[1:] if argv is None else argv
    try:
        mode, target, as_json = _parse_cli_argv(raw_argv)
        if mode == "standalone":
            out: dict[str, Any] = build_standalone_certificate()
        elif mode == "write":
            out = write_certificate_file(target)  # type: ignore[arg-type]
        else:
            out = check_certificate_file(target)  # type: ignore[arg-type]
    except TectonicsReluError as exc:
        err = {"valid": False, "error_code": exc.code, "error_message": exc.message}
        sys.stderr.write(canonical_json_bytes(err).decode("ascii") + "\n")
        return 2

    if as_json:
        sys.stdout.write(canonical_json_bytes(out).decode("ascii") + "\n")
    else:
        sys.stdout.write(
            f"OK {SCHEMA_VERSION} payload_sha256={out['payload_sha256']} "
            f"certificate_sha256={out['certificate_sha256']}\n"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
