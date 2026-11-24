#!/usr/bin/env python3
"""Fail-Closed CLI, Full Pure-Q Replay & Secondary Algebraic Cross-Check.

Pure Python 3 standard library: zero floats, zero bare asserts, zero mathematical RNG.
Fail-closed I/O & certificate verification invariants:
  - Concrete pathlib.Path check + NUL-byte and lone UTF-16 surrogate path refusal
  - Deleted-CWD OSError wrapping -> CWD_UNAVAILABLE (rc=2)
  - Atomic dir_fd PWD walk + per-component openat(O_RDONLY | O_DIRECTORY | O_NOFOLLOW) (zero os.path.islink)
  - Leaf O_RDONLY | O_NOFOLLOW | O_NONBLOCK + fstat S_ISREG + 64 KiB streaming capped reads (max_bytes <= 64 MiB)
  - Atomic write: type(data) is bytes BEFORE dir/temp open -> target lstat (st_nlink > 1 -> HARDLINK_FORBIDDEN)
    -> thread-locked monotonic + CSPRNG (secrets.token_hex(8)) 0o600 O_CREAT|O_EXCL|O_NOFOLLOW|O_NONBLOCK
    temp file in same dir_fd -> bounded 32-attempt EEXIST retry -> os.fsync(tmp_fd)
    -> pre-replace os.fstat(tmp_fd).st_nlink == 1 -> os.replace(..., src_dir_fd=dfd, dst_dir_fd=dfd) -> os.fsync(dfd)
  - Strict CLI parser rejecting space- and equals-syntax flag-like/empty paths (--write --json -> rc=2, 0 files)
  - Full pure-Q replay + division-free cross-multiplied secondary_audit_payload (CLI, full_replay=True & False)
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

from entropy_bulk_projection_oracle import (
    MAX_JSON_BYTES,
    SCHEMA_VERSION,
    TRACK_ID,
    _PAYLOAD_KEYS,
    EntropyBulkProjectionError,
    build_standalone_certificate,
    canonical_json_bytes,
    parse_exact_rational,
    parse_strict_json_text,
    require_exact_bool,
    require_exact_int,
    require_exact_str,
    validate_certificate_payload,
    validate_json_tree_iterative,
)

MAX_ALLOWED_CAP_BYTES = 64 * 1024 * 1024
_READ_CHUNK_BYTES = 65_536
_EXACT_PATH_TYPE = type(Path("."))
_DIR_OPEN_FLAGS = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
_TMP_LOCK = threading.Lock()
_TMP_COUNTER = 0


def _next_tmp_name(leaf: str) -> str:
    global _TMP_COUNTER
    with _TMP_LOCK:
        _TMP_COUNTER += 1
        seq = _TMP_COUNTER
    return f".{leaf}.s37tmp.{os.getpid()}.{threading.get_ident()}.{seq}.{secrets.token_hex(8)}"


# ---------------------------------------------------------------------------
# Race-Free Fail-Closed File I/O (Per-Component dir_fd/openat + Atomic os.replace)
# ---------------------------------------------------------------------------

_DARWIN_SYSTEM_ROOT_ALIASES: tuple[tuple[str, str], ...] = (
    ("/var", "/private/var"),
    ("/tmp", "/private/tmp"),
    ("/etc", "/private/etc"),
)


def _normalize_darwin_system_prefix(path: Path, *, allow_exact: bool = False) -> Path:
    """Map verified root-owned macOS /var, /tmp, /etc aliases to /private/* without resolving user symlinks."""
    if sys.platform != "darwin" or not path.is_absolute():
        return path
    parts = path.parts
    min_parts = 2 if allow_exact else 3
    if len(parts) < min_parts or ".." in parts:
        return path
    top = "/" + parts[1]
    for alias, canonical in _DARWIN_SYSTEM_ROOT_ALIASES:
        if top != alias:
            continue
        try:
            st = os.lstat(alias)
            if not stat.S_ISLNK(st.st_mode) or st.st_uid != 0:
                return path
            link_target = os.readlink(alias)
            if link_target not in (canonical, canonical.lstrip("/")):
                return path
        except OSError:
            return path
        return Path(canonical, *parts[2:])
    return path


def _open_dir_chain(anchor: str, parts: Sequence[str]) -> int:
    """Walk directory components atomically via `openat(..., O_DIRECTORY | O_NOFOLLOW)`."""
    try:
        dfd = os.open(anchor, _DIR_OPEN_FLAGS)
    except OSError as exc:
        raise EntropyBulkProjectionError("PATH_STAT_ERROR", f"cannot open anchor dir: {type(exc).__name__}") from exc

    for part in parts:
        try:
            nxt = os.open(part, _DIR_OPEN_FLAGS, dir_fd=dfd)
        except OSError as exc:
            os.close(dfd)
            if exc.errno in (errno.ELOOP, errno.ENOTDIR):
                raise EntropyBulkProjectionError("SYMLINK_FORBIDDEN", "symlink or non-dir forbidden in path") from exc
            if exc.errno == errno.ENOENT:
                raise EntropyBulkProjectionError("PATH_NOT_FOUND", "directory component not found") from exc
            raise EntropyBulkProjectionError("PATH_STAT_ERROR", f"cannot traverse dir: {type(exc).__name__}") from exc
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
        except EntropyBulkProjectionError as exc:
            if exc.code != "PATH_NOT_FOUND":
                raise
        else:
            os.close(pwd_fd)


def _validate_path_and_split(path: Any) -> tuple[str, list[str]]:
    if type(path) is not _EXACT_PATH_TYPE:
        raise EntropyBulkProjectionError("INVALID_PATH_TYPE", "path must be exact pathlib.Path")
    raw_str = require_exact_str(str(path), "path")
    if "\x00" in raw_str:
        raise EntropyBulkProjectionError("INVALID_PATH", "path contains NUL byte")

    if not path.is_absolute():
        try:
            Path.cwd()
        except OSError as exc:
            raise EntropyBulkProjectionError("CWD_UNAVAILABLE", f"cannot resolve cwd: {type(exc).__name__}") from exc
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
            raise EntropyBulkProjectionError("PATH_STAT_ERROR", f"cannot lstat leaf: {type(exc).__name__}") from exc
        if stat.S_ISLNK(st.st_mode):
            raise EntropyBulkProjectionError("SYMLINK_FORBIDDEN", "symlink forbidden at leaf")
    finally:
        os.close(dfd)
    return path


def _open_leaf_for_read(path: Path) -> int:
    anchor, parts = _validate_path_and_split(path)
    if not parts:
        raise EntropyBulkProjectionError("NON_REGULAR_FILE", "target path refers to a directory")
    dfd = _open_dir_chain(anchor, parts[:-1])
    try:
        try:
            return os.open(parts[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=dfd)
        except OSError as exc:
            if exc.errno == errno.ELOOP:
                raise EntropyBulkProjectionError("SYMLINK_FORBIDDEN", "symlink forbidden at leaf") from exc
            raise EntropyBulkProjectionError("FILE_READ_ERROR", f"cannot open file: {type(exc).__name__}") from exc
    finally:
        os.close(dfd)


def read_regular_bytes_capped(path: Path, max_bytes: Any = MAX_JSON_BYTES) -> bytes:
    """Read regular file bytes via atomic dir_fd + O_NOFOLLOW|O_NONBLOCK in bounded 64 KiB streaming chunks."""
    cap = require_exact_int(max_bytes, "max_bytes", min_val=1, max_val=MAX_ALLOWED_CAP_BYTES)
    fd = _open_leaf_for_read(path)
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise EntropyBulkProjectionError("NON_REGULAR_FILE", "target is not a regular file")
        chunks: list[bytes] = []
        total = 0
        while True:
            to_read = min(_READ_CHUNK_BYTES, cap + 1 - total)
            chunk = os.read(fd, to_read)
            if not chunk:
                break
            total += len(chunk)
            if total > cap:
                raise EntropyBulkProjectionError("FILE_TOO_LARGE", f"file exceeds {cap} bytes")
            chunks.append(chunk)
        return b"".join(chunks)
    except EntropyBulkProjectionError:
        raise
    except OSError as exc:
        raise EntropyBulkProjectionError("FILE_READ_ERROR", f"failed reading file: {type(exc).__name__}") from exc
    finally:
        os.close(fd)


def write_regular_file_bytes(path: Path, data: bytes) -> None:
    """Write regular file atomically via 0o600 CSPRNG temp file, fsync, pre-replace st_nlink==1 & os.replace."""
    if type(data) is not bytes:
        raise EntropyBulkProjectionError("INVALID_WRITE_DATA", "data must be exact bytes")
    anchor, parts = _validate_path_and_split(path)
    if not parts:
        raise EntropyBulkProjectionError("NON_REGULAR_FILE", "target path refers to a directory")
    leaf = parts[-1]
    dfd = _open_dir_chain(anchor, parts[:-1])
    try:
        try:
            st = os.lstat(leaf, dir_fd=dfd)
        except FileNotFoundError:
            st = None
        except OSError as exc:
            raise EntropyBulkProjectionError("FILE_WRITE_ERROR", f"cannot lstat target: {type(exc).__name__}") from exc
        if st is not None:
            if stat.S_ISLNK(st.st_mode):
                raise EntropyBulkProjectionError("SYMLINK_FORBIDDEN", "symlink forbidden at leaf")
            if not stat.S_ISREG(st.st_mode):
                raise EntropyBulkProjectionError("NON_REGULAR_FILE", "cannot write to non-regular file")
            if st.st_nlink > 1:
                raise EntropyBulkProjectionError("HARDLINK_FORBIDDEN", "cannot write through hardlinked file")

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
                raise EntropyBulkProjectionError("FILE_WRITE_ERROR", f"cannot create temp file: {type(exc).__name__}") from exc
        if tmp_fd is None:
            raise EntropyBulkProjectionError("TEMP_RETRY_EXHAUSTED", "temp file collision limit exceeded")

        try:
            try:
                view = memoryview(data)
                written = 0
                while written < len(data):
                    written += os.write(tmp_fd, view[written:])
                os.fsync(tmp_fd)
                if os.fstat(tmp_fd).st_nlink != 1:
                    raise EntropyBulkProjectionError("HARDLINK_FORBIDDEN", "temp file link count != 1")
            finally:
                os.close(tmp_fd)
            os.replace(tmp_name, leaf, src_dir_fd=dfd, dst_dir_fd=dfd)
            os.fsync(dfd)
        except EntropyBulkProjectionError:
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
            raise EntropyBulkProjectionError("FILE_WRITE_ERROR", f"failed writing file: {type(exc).__name__}") from exc
    finally:
        os.close(dfd)


# ---------------------------------------------------------------------------
# Secondary Algebraic Invariant Cross-Check Over All Four Pillars
# ---------------------------------------------------------------------------

_P1_KEYS = frozenset({
    "q3_jko_diffusion",
    "c8_jko_diffusion",
    "arnold_cat_map_filament_arc",
    "jaynes_maxent_missing_vectors",
})
_DIFF_KEYS = frozenset({
    "graph",
    "vertices",
    "steps",
    "doubly_stochastic",
    "symmetric",
    "probability_conserved_all_steps",
    "collision_energy_t0",
    "collision_energy_t1",
    "collision_energy_t_end",
    "collision_energy_uniform_floor",
    "collision_energy_strictly_decreasing",
    "renyi2_entropy_strictly_increasing",
    "dirichlet_roughness_t0",
    "dirichlet_roughness_t1",
    "dirichlet_roughness_t_end",
    "dirichlet_roughness_strictly_decreasing",
    "spectral_gap_contraction_certified",
})
_CAT_KEYS = frozenset({
    "torus_n",
    "coarse_block_size",
    "occupied_pixels",
    "matrix_det",
    "matrix_trace",
    "hyperbolic_discriminant",
    "integer_inverse_exact",
    "all_12_steps_micro_reversible",
    "poincare_recurrence_period",
    "poincare_recurrence_t12_exact",
    "arc_t0_to_t3",
    "coarse_entropy_strictly_increasing_t0_to_t3",
    "coarse_variance_collapses_to_exact_zero_t3",
    "micro_perimeter_hits_theoretical_max_256_t3",
    "non_monotonic_macro_levels_peak_t2",
    "non_monotonic_macro_edges_peak",
})
_ARC_KEYS = frozenset({
    "t",
    "micro_perimeter",
    "coarse_collision_energy",
    "coarse_block_variance",
    "coarse_dirichlet_energy",
    "active_macro_edges",
    "distinct_macro_levels",
})
_MAXENT_KEYS = frozenset({
    "state_dim",
    "constraint_dim",
    "missing_ker_dim",
    "p_star",
    "constraints_exact",
    "ker_basis_in_nullspace",
    "ker_basis_gram_det",
    "ker_basis_rank_6_certified",
    "all_6_missing_vectors_zero_bias",
    "perturbation_feasible",
    "p_star_collision_energy",
    "delta_norm_sq",
    "p_pert_collision_energy",
    "pythagorean_optimality_exact",
    "shannon_gibbs_exact_coincidence",
    "gibbs_stratum_ratio",
})
_P2_KEYS = frozenset({
    "worthington_incompressible_focusing",
    "unruh_analogue_sonic_horizon",
    "gravitational_negative_heat_capacity_jeans",
})
_WORTH_KEYS = frozenset({
    "alpha",
    "beta_forced_2alpha",
    "divergence_residual",
    "incompressibility_exact",
    "stagnation_point_zero_velocity",
    "cylinder_flux_in_over_2pi",
    "cylinder_flux_out_over_2pi",
    "control_volume_flux_conserved",
    "euler_bernoulli_stagnation_exact",
    "rayleigh_plesset_self_similar_coeff",
    "streamline_k4_focusing_witnesses",
    "streamline_k4_focusing_exact",
})
_FOCUS_KEYS = frozenset({
    "radial_compression_k",
    "r",
    "z",
    "axial_ke_amplification",
    "radial_ke_ratio",
})
_UNRUH_KEYS = frozenset({
    "wave_speed_cw",
    "sonic_horizon_r_h",
    "f_ac_at_horizon",
    "f_ac_supersonic_interior_r1",
    "f_ac_subsonic_exterior_r4",
    "horizon_sign_separation_exact",
    "surface_gravity_kappa",
    "kappa_velocity_gradient_matches",
    "normalized_killing_kappa",
    "normalized_killing_matches_inv_rh",
})
_GRAV_KEYS = frozenset({
    "virial_k",
    "virial_u",
    "virial_e",
    "virial_identity_exact",
    "cv_ideal_gas",
    "cv_grav_virial",
    "heat_capacity_opposite_sign",
    "jeans_c_s",
    "jeans_omega_j_sq",
    "jeans_k_j",
    "jeans_critical_zero_exact",
    "jeans_dispersion_probes",
    "jeans_sign_flip_certified",
})
_JEANS_KEYS = frozenset({"k", "omega_sq", "regime"})
_P3_KEYS = frozenset({
    "offbrane_plummer_core_theorem",
    "schur_dark_gravity_2x2",
    "schur_dark_gravity_4x4",
    "schur_dark_gravity_6x6",
    "all_schur_dark_projections_certified",
})
_PLUM_KEYS = frozenset({
    "pythagorean_triplets",
    "all_triplets_exact",
    "central_density_finite_zero_cusp",
    "central_density_slope_zero_at_r0",
    "peak_condition_r_sq_over_y0_sq",
    "vc_deriv_num_rising_r_eq_y0",
    "vc_deriv_num_falling_r_eq_2y0",
    "vc_peak_sign_change_exact",
    "vc_max_fourth_over_gm_sq_y0_1",
    "asymptotic_mass_sq_deficit_r1000",
    "total_mass_conserved_certified",
})
_TRIP_KEYS = frozenset({
    "r",
    "y0",
    "R",
    "pythagorean_exact",
    "poisson_derivative_identity_exact",
    "m_enc_over_m",
    "four_pi_rho_eff_over_m",
    "four_pi_central_core_density_over_m",
    "vc_sq_over_gm",
})
_SCHUR_KEYS = frozenset({
    "n_total",
    "n_obs",
    "n_hidden",
    "full_pd",
    "m_hh_pd",
    "schur_so_pd",
    "det_m",
    "det_m_hh",
    "det_s_o",
    "schur_det_identity_exact",
    "j_dark",
    "j_dark_all_strictly_positive",
    "phi_o_schur",
    "phi_o_all_strictly_positive",
    "schur_matches_full_solve_exact",
    "full_energy",
    "obs_schur_energy",
    "dark_shadow_energy_deficit",
    "energy_decomposition_exact",
    "dark_shadow_strictly_positive",
})
_P4_KEYS = frozenset({
    "shtanov_sahni_timelike_bounce",
    "dmpr_pell_tidal_charge_shadows",
    "gw170817_cmb_observational_gates",
})
_BOUNCE_KEYS = frozenset({
    "ss_h2_at_rhoc",
    "ss_dh2_dx_at_rhoc",
    "ss_h2_peak_at_half_rhoc",
    "ss_bounce_hdot_radiation",
    "ss_bounce_hdot_dust",
    "ss_regular_bounce_certified",
    "rs2_h2_at_rhoc",
    "rs2_dh2_dx_at_rhoc",
    "rs2_hdot_radiation_at_rhoc",
    "rs2_no_bounce_singular_certified",
})
_DMPR_KEYS = frozenset({
    "pell_rational_parametrization_verified",
    "witness_q_pos1",
    "witness_q_zero_schwarzschild",
    "witness_q_neg_495_289_pell",
    "witness_q_neg2",
    "witness_q_neg35_pell",
    "q_neg1_exact_radicand_17_cubed",
    "q_neg1_b_crit_sq_lo",
    "q_neg1_b_crit_sq_hi",
    "q_neg1_bracket_certified",
    "shadow_chain_strictly_increasing",
    "all_pell_witnesses_valid",
})
_PELL_WIT_KEYS = frozenset({
    "a",
    "b",
    "pell_residual",
    "q_over_m2",
    "r_h_over_m",
    "r_ph_over_m",
    "horizon_root_exact",
    "photon_sphere_root_exact",
    "f_at_r_ph",
    "b_crit_sq_over_m2",
    "b_crit_sq_4dp",
    "envelope_deriv_db2_dq",
    "envelope_deriv_negative",
})
_NEG2_WIT_KEYS = frozenset({
    "q_over_m2",
    "r_ph_over_m",
    "photon_sphere_root_exact",
    "f_at_r_ph",
    "b_crit_sq_over_m2",
    "b_crit_sq_4dp",
})
_OBS_KEYS = frozenset({
    "gw170817_d_lo",
    "gw170817_d_hi",
    "d_4_inside_gw170817",
    "flat_d_5_excluded_by_gw170817",
    "flat_d_5_exclusion_margin",
    "flat5d_amp_ratio_sq_40mpc_rc10",
    "cmb_redshift_z",
    "first_stars_redshift_upper",
    "omega_dm_h2",
    "omega_b_h2",
    "dm_to_baryon_ratio",
    "dm_to_baryon_ratio_4dp",
    "dm_to_baryon_in_5_to_6",
    "post_stellar_only_bh_ruled_out_at_cmb",
})


def _require_dict_exact_keys(
    mapping: dict[str, Any],
    key: str,
    expected_keys: frozenset[str],
    err_code: str,
) -> dict[str, Any]:
    val = mapping.get(key)
    if type(val) is not dict or frozenset(val.keys()) != expected_keys:
        raise EntropyBulkProjectionError(err_code, f"missing or invalid object key set: {key}")
    return val


def _require_flag(mapping: dict[str, Any], key: str, expected: bool, err_code: str) -> None:
    if require_exact_bool(mapping.get(key), key) is not expected:
        raise EntropyBulkProjectionError(err_code, f"invariant {key} must be {expected}")


def _require_rational_list(val: Any, name: str, expected_len: int, err_code: str) -> list[Fraction]:
    if type(val) is not list or len(val) != expected_len:
        raise EntropyBulkProjectionError(err_code, f"{name} must be list of length {expected_len}")
    return [parse_exact_rational(item, f"{name}[{i}]") for i, item in enumerate(val)]


def secondary_audit_payload(payload: Any) -> dict[str, Any]:
    """Fail-closed field-complete division-free secondary algebraic invariant cross-check over all four pillars."""
    if type(payload) is not dict or frozenset(payload.keys()) != _PAYLOAD_KEYS:
        raise EntropyBulkProjectionError("AUDIT_PAYLOAD_TYPE", "payload must be dict with exact required keys")
    validate_json_tree_iterative(payload)
    if (payload["novelty_tier"], payload["oracle_class"]) != ("N1", "exact"):
        raise EntropyBulkProjectionError("AUDIT_META", "unexpected novelty_tier or oracle_class")

    # Honesty & hygiene flags
    for key in (
        "measured_live_cosmological_nbody_fits",
        "measured_eht_shadow_tidal_charge_detection",
        "measured_laboratory_worthington_piv_velocimetry",
    ):
        _require_flag(payload, key, False, "AUDIT_LAW4_FLAG")
    for key in ("zero_trust_path_floats", "zero_bare_asserts", "zero_mathematical_rng"):
        _require_flag(payload, key, True, "AUDIT_HYGIENE_FLAG")

    # Pillar 1: JKO Diffusion, Arnold Cat Map & Jaynes MaxEnt
    p1 = _require_dict_exact_keys(payload, "pillar1_entropy_smoothing_catmap_maxent", _P1_KEYS, "AUDIT_P1_MISSING")
    diff_specs = (
        ("q3_jko_diffusion", "Q_3", Fraction(1, 3), Fraction(3603611, 28697814), Fraction(3, 1), Fraction(1, 2), Fraction(3641, 3188646)),
        ("c8_jko_diffusion", "C_8", Fraction(3, 8), Fraction(4860289, 33554432), Fraction(2, 1), Fraction(1, 4), Fraction(195153, 16777216)),
    )
    for gk, gname, exp_c1, exp_ce, exp_d0, exp_d1, exp_de in diff_specs:
        gd = _require_dict_exact_keys(p1, gk, _DIFF_KEYS, "AUDIT_P1_GRAPH")
        for fk in (
            "doubly_stochastic",
            "symmetric",
            "probability_conserved_all_steps",
            "collision_energy_strictly_decreasing",
            "renyi2_entropy_strictly_increasing",
            "dirichlet_roughness_strictly_decreasing",
            "spectral_gap_contraction_certified",
        ):
            _require_flag(gd, fk, True, "AUDIT_P1_DIFF")
        c0 = parse_exact_rational(gd["collision_energy_t0"], f"{gk}.c0")
        c1 = parse_exact_rational(gd["collision_energy_t1"], f"{gk}.c1")
        ce = parse_exact_rational(gd["collision_energy_t_end"], f"{gk}.ce")
        cf = parse_exact_rational(gd["collision_energy_uniform_floor"], f"{gk}.cf")
        d0 = parse_exact_rational(gd["dirichlet_roughness_t0"], f"{gk}.d0")
        d1 = parse_exact_rational(gd["dirichlet_roughness_t1"], f"{gk}.d1")
        de = parse_exact_rational(gd["dirichlet_roughness_t_end"], f"{gk}.de")
        if (
            require_exact_str(gd["graph"], f"{gk}.graph"),
            require_exact_int(gd["vertices"], f"{gk}.vertices"),
            require_exact_int(gd["steps"], f"{gk}.steps"),
            c0, c1, ce, cf, d0, d1, de,
            c0 > c1 > ce > cf,
            d0 > d1 > de > 0,
        ) != (gname, 8, 8, Fraction(1, 1), exp_c1, exp_ce, Fraction(1, 8), exp_d0, exp_d1, exp_de, True, True):
            raise EntropyBulkProjectionError("AUDIT_P1_DIFF_VAL", f"{gk} exact diffusion invariants mismatch")

    cat = _require_dict_exact_keys(p1, "arnold_cat_map_filament_arc", _CAT_KEYS, "AUDIT_P1_CAT")
    for fk in (
        "integer_inverse_exact",
        "all_12_steps_micro_reversible",
        "poincare_recurrence_t12_exact",
        "coarse_entropy_strictly_increasing_t0_to_t3",
        "coarse_variance_collapses_to_exact_zero_t3",
        "micro_perimeter_hits_theoretical_max_256_t3",
        "non_monotonic_macro_levels_peak_t2",
        "non_monotonic_macro_edges_peak",
    ):
        _require_flag(cat, fk, True, "AUDIT_P1_CAT_FLAG")
    det_m = require_exact_int(cat["matrix_det"], "matrix_det")
    tr_m = require_exact_int(cat["matrix_trace"], "matrix_trace")
    disc_m = require_exact_int(cat["hyperbolic_discriminant"], "hyperbolic_discriminant")
    if (
        require_exact_int(cat["torus_n"], "torus_n"),
        require_exact_int(cat["coarse_block_size"], "coarse_block_size"),
        require_exact_int(cat["occupied_pixels"], "occupied_pixels"),
        det_m, tr_m, disc_m, disc_m == tr_m * tr_m - 4 * det_m,
        require_exact_int(cat["poincare_recurrence_period"], "period"),
    ) != (16, 4, 64, 1, 3, 5, True, 12):
        raise EntropyBulkProjectionError("AUDIT_P1_CAT_VAL", "Arnold Cat Map metadata/algebraic invariants mismatch")
    arc = cat["arc_t0_to_t3"]
    if type(arc) is not list or len(arc) != 4:
        raise EntropyBulkProjectionError("AUDIT_P1_ARC", "arc_t0_to_t3 must have 4 entries")
    arc_expected = (
        (0, 32, Fraction(1, 4), Fraction(48, 1), 2048, 8, 2),
        (1, 74, Fraction(33, 256), Fraction(17, 1), 1088, 28, 6),
        (2, 166, Fraction(19, 256), Fraction(3, 1), 288, 32, 7),
        (3, 256, Fraction(1, 16), Fraction(0, 1), 0, 0, 1),
    )
    for idx, item in enumerate(arc):
        if type(item) is not dict or frozenset(item.keys()) != _ARC_KEYS:
            raise EntropyBulkProjectionError("AUDIT_P1_ARC", "arc item must be dict with exact keys")
        if (
            require_exact_int(item["t"], "arc.t"),
            require_exact_int(item["micro_perimeter"], "arc.micro_perimeter"),
            parse_exact_rational(item["coarse_collision_energy"], "arc.coll"),
            parse_exact_rational(item["coarse_block_variance"], "arc.var"),
            require_exact_int(item["coarse_dirichlet_energy"], "arc.dir"),
            require_exact_int(item["active_macro_edges"], "arc.edges"),
            require_exact_int(item["distinct_macro_levels"], "arc.levels"),
        ) != arc_expected[idx]:
            raise EntropyBulkProjectionError("AUDIT_P1_ARC_VAL", f"arc_t0_to_t3[{idx}] values mismatch")

    me = _require_dict_exact_keys(p1, "jaynes_maxent_missing_vectors", _MAXENT_KEYS, "AUDIT_P1_MAXENT")
    for fk in (
        "constraints_exact",
        "ker_basis_in_nullspace",
        "ker_basis_rank_6_certified",
        "all_6_missing_vectors_zero_bias",
        "perturbation_feasible",
        "pythagorean_optimality_exact",
        "shannon_gibbs_exact_coincidence",
    ):
        _require_flag(me, fk, True, "AUDIT_P1_MAXENT_FLAG")
    p_star = _require_rational_list(me["p_star"], "p_star", 8, "AUDIT_P1_MAXENT_VAL")
    e_star = parse_exact_rational(me["p_star_collision_energy"], "p_star_coll")
    e_delta = parse_exact_rational(me["delta_norm_sq"], "delta_norm_sq")
    e_pert = parse_exact_rational(me["p_pert_collision_energy"], "p_pert_coll")
    if (
        require_exact_int(me["state_dim"], "state_dim"),
        require_exact_int(me["constraint_dim"], "constraint_dim"),
        require_exact_int(me["missing_ker_dim"], "missing_ker_dim"),
        p_star,
        sum(p_star, Fraction(0, 1)),
        sum((x * x for x in p_star), Fraction(0, 1)) == e_star,
        parse_exact_rational(me["ker_basis_gram_det"], "ker_det"),
        e_star, e_delta, e_pert, e_pert == e_star + e_delta,
        parse_exact_rational(me["gibbs_stratum_ratio"], "gibbs_ratio"),
    ) != (
        8, 2, 6,
        [Fraction(5, 32)] * 4 + [Fraction(3, 32)] * 4,
        Fraction(1, 1), True, Fraction(16, 1),
        Fraction(17, 128), Fraction(1, 1024), Fraction(137, 1024), True,
        Fraction(5, 3),
    ):
        raise EntropyBulkProjectionError("AUDIT_P1_MAXENT_VAL", "Jaynes MaxEnt values mismatch")

    # Pillar 2: Worthington, Unruh & Gravity Bifurcation
    p2 = _require_dict_exact_keys(payload, "pillar2_worthington_unruh_gravity_bifurcation", _P2_KEYS, "AUDIT_P2_MISSING")
    worth = _require_dict_exact_keys(p2, "worthington_incompressible_focusing", _WORTH_KEYS, "AUDIT_P2_WORTH")
    for fk in (
        "incompressibility_exact",
        "stagnation_point_zero_velocity",
        "control_volume_flux_conserved",
        "euler_bernoulli_stagnation_exact",
        "streamline_k4_focusing_exact",
    ):
        _require_flag(worth, fk, True, "AUDIT_P2_WORTH_FLAG")
    w_alpha = parse_exact_rational(worth["alpha"], "alpha")
    w_beta = parse_exact_rational(worth["beta_forced_2alpha"], "beta")
    w_div = parse_exact_rational(worth["divergence_residual"], "div_res")
    f_in = parse_exact_rational(worth["cylinder_flux_in_over_2pi"], "flux_in")
    f_out = parse_exact_rational(worth["cylinder_flux_out_over_2pi"], "flux_out")
    if (
        w_alpha, w_beta, w_beta == 2 * w_alpha, w_div, w_div == -2 * w_alpha + w_beta,
        f_in, f_out, f_in == f_out,
        parse_exact_rational(worth["rayleigh_plesset_self_similar_coeff"], "rp"),
    ) != (Fraction(3, 2), Fraction(3, 1), True, Fraction(0, 1), True, Fraction(72, 1), Fraction(72, 1), True, Fraction(1, 8)):
        raise EntropyBulkProjectionError("AUDIT_P2_WORTH_VAL", "Worthington invariants mismatch")
    fw = worth["streamline_k4_focusing_witnesses"]
    if type(fw) is not list or len(fw) != 2:
        raise EntropyBulkProjectionError("AUDIT_P2_FOCUS", "streamline witnesses must have length 2")
    fw_expected = (
        (2, Fraction(1, 1), Fraction(4, 1), Fraction(16, 1), Fraction(1, 4)),
        (3, Fraction(2, 3), Fraction(9, 1), Fraction(81, 1), Fraction(1, 9)),
    )
    for idx, item in enumerate(fw):
        if type(item) is not dict or frozenset(item.keys()) != _FOCUS_KEYS:
            raise EntropyBulkProjectionError("AUDIT_P2_FOCUS", "focus witness must have exact keys")
        if (
            require_exact_int(item["radial_compression_k"], "k"),
            parse_exact_rational(item["r"], "r"),
            parse_exact_rational(item["z"], "z"),
            parse_exact_rational(item["axial_ke_amplification"], "amp"),
            parse_exact_rational(item["radial_ke_ratio"], "rad"),
        ) != fw_expected[idx]:
            raise EntropyBulkProjectionError("AUDIT_P2_FOCUS_VAL", f"focus witness[{idx}] mismatch")

    unruh = _require_dict_exact_keys(p2, "unruh_analogue_sonic_horizon", _UNRUH_KEYS, "AUDIT_P2_UNRUH")
    for fk in ("horizon_sign_separation_exact", "kappa_velocity_gradient_matches", "normalized_killing_matches_inv_rh"):
        _require_flag(unruh, fk, True, "AUDIT_P2_UNRUH_FLAG")
    cw = parse_exact_rational(unruh["wave_speed_cw"], "cw")
    rh = parse_exact_rational(unruh["sonic_horizon_r_h"], "rh")
    kappa = parse_exact_rational(unruh["surface_gravity_kappa"], "kappa")
    knorm = parse_exact_rational(unruh["normalized_killing_kappa"], "knorm")
    if (
        cw, rh,
        parse_exact_rational(unruh["f_ac_at_horizon"], "f_h"),
        parse_exact_rational(unruh["f_ac_supersonic_interior_r1"], "f_in"),
        parse_exact_rational(unruh["f_ac_subsonic_exterior_r4"], "f_ex"),
        kappa, kappa * rh == cw * cw,
        knorm, knorm * rh == Fraction(1, 1),
    ) != (Fraction(3, 1), Fraction(2, 1), Fraction(0, 1), Fraction(-27, 1), Fraction(27, 4), Fraction(9, 2), True, Fraction(1, 2), True):
        raise EntropyBulkProjectionError("AUDIT_P2_UNRUH_VAL", "Unruh sonic horizon invariants mismatch")

    grav = _require_dict_exact_keys(p2, "gravitational_negative_heat_capacity_jeans", _GRAV_KEYS, "AUDIT_P2_GRAV")
    for fk in ("virial_identity_exact", "heat_capacity_opposite_sign", "jeans_critical_zero_exact", "jeans_sign_flip_certified"):
        _require_flag(grav, fk, True, "AUDIT_P2_GRAV_FLAG")
    vk = parse_exact_rational(grav["virial_k"], "vk")
    vu = parse_exact_rational(grav["virial_u"], "vu")
    ve = parse_exact_rational(grav["virial_e"], "ve")
    cv_g = parse_exact_rational(grav["cv_ideal_gas"], "cv_gas")
    cv_v = parse_exact_rational(grav["cv_grav_virial"], "cv_grav")
    cs = parse_exact_rational(grav["jeans_c_s"], "cs")
    oj2 = parse_exact_rational(grav["jeans_omega_j_sq"], "oj2")
    kj = parse_exact_rational(grav["jeans_k_j"], "kj")
    if (
        vk, vu, ve, 2 * vk + vu == 0, ve == vk + vu,
        cv_g, cv_v, cv_v == -cv_g,
        cs, oj2, kj, kj * kj * cs * cs == oj2,
    ) != (Fraction(15, 1), Fraction(-30, 1), Fraction(-15, 1), True, True, Fraction(15, 1), Fraction(-15, 1), True, Fraction(2, 1), Fraction(36, 1), Fraction(3, 1), True):
        raise EntropyBulkProjectionError("AUDIT_P2_GRAV_VAL", "virial/Jeans scalar invariants mismatch")
    jprobes = grav["jeans_dispersion_probes"]
    if type(jprobes) is not list or len(jprobes) != 5:
        raise EntropyBulkProjectionError("AUDIT_P2_JEANS", "jeans_dispersion_probes must have length 5")
    j_expected = (
        (1, Fraction(-32, 1), "clumping_unstable"),
        (2, Fraction(-20, 1), "clumping_unstable"),
        (3, Fraction(0, 1), "jeans_critical"),
        (4, Fraction(28, 1), "acoustic_stable"),
        (5, Fraction(64, 1), "acoustic_stable"),
    )
    for idx, item in enumerate(jprobes):
        if type(item) is not dict or frozenset(item.keys()) != _JEANS_KEYS:
            raise EntropyBulkProjectionError("AUDIT_P2_JEANS", "jeans probe must have exact keys")
        if (
            require_exact_int(item["k"], "jeans.k"),
            parse_exact_rational(item["omega_sq"], "jeans.omega_sq"),
            require_exact_str(item["regime"], "jeans.regime"),
        ) != j_expected[idx]:
            raise EntropyBulkProjectionError("AUDIT_P2_JEANS_VAL", f"jeans probe[{idx}] mismatch")

    # Pillar 3: Off-Brane Plummer Core & Schur Dark-Gravity Source
    p3 = _require_dict_exact_keys(payload, "pillar3_offbrane_plummer_schur_dark_source", _P3_KEYS, "AUDIT_P3_MISSING")
    plum = _require_dict_exact_keys(p3, "offbrane_plummer_core_theorem", _PLUM_KEYS, "AUDIT_P3_PLUM")
    for fk in (
        "all_triplets_exact",
        "central_density_finite_zero_cusp",
        "central_density_slope_zero_at_r0",
        "vc_peak_sign_change_exact",
        "total_mass_conserved_certified",
    ):
        _require_flag(plum, fk, True, "AUDIT_P3_PLUM_FLAG")
    if (
        require_exact_int(plum["peak_condition_r_sq_over_y0_sq"], "peak_cond"),
        parse_exact_rational(plum["vc_deriv_num_rising_r_eq_y0"], "rising"),
        parse_exact_rational(plum["vc_deriv_num_falling_r_eq_2y0"], "falling"),
        parse_exact_rational(plum["vc_max_fourth_over_gm_sq_y0_1"], "vc_max4"),
        parse_exact_rational(plum["asymptotic_mass_sq_deficit_r1000"], "asym"),
    ) != (2, Fraction(1, 1), Fraction(-4, 1), Fraction(4, 27), Fraction(3000003000001, 1000003000003000001)):
        raise EntropyBulkProjectionError("AUDIT_P3_PLUM_VAL", "Plummer core scalar invariants mismatch")
    trips = plum["pythagorean_triplets"]
    if type(trips) is not list or len(trips) != 3:
        raise EntropyBulkProjectionError("AUDIT_P3_TRIPS", "pythagorean_triplets must have length 3")
    trip_expected = (
        (3, 4, 5, Fraction(27, 125), Fraction(48, 3125), Fraction(3, 64), Fraction(9, 125)),
        (5, 12, 13, Fraction(125, 2197), Fraction(432, 371293), Fraction(1, 576), Fraction(25, 2197)),
        (8, 15, 17, Fraction(512, 4913), Fraction(675, 1419857), Fraction(1, 1125), Fraction(64, 4913)),
    )
    for idx, item in enumerate(trips):
        if type(item) is not dict or frozenset(item.keys()) != _TRIP_KEYS:
            raise EntropyBulkProjectionError("AUDIT_P3_TRIPS", "triplet item must be dict with exact keys")
        _require_flag(item, "pythagorean_exact", True, "AUDIT_P3_MENC")
        _require_flag(item, "poisson_derivative_identity_exact", True, "AUDIT_P3_MENC")
        tr_r = require_exact_int(item["r"], "triplet.r")
        tr_y = require_exact_int(item["y0"], "triplet.y0")
        tr_R = require_exact_int(item["R"], "triplet.R")
        if (
            tr_r, tr_y, tr_R, tr_r * tr_r + tr_y * tr_y == tr_R * tr_R,
            parse_exact_rational(item["m_enc_over_m"], "m_enc"),
            parse_exact_rational(item["four_pi_rho_eff_over_m"], "rho"),
            parse_exact_rational(item["four_pi_central_core_density_over_m"], "rho0"),
            parse_exact_rational(item["vc_sq_over_gm"], "vc2"),
        ) != (
            trip_expected[idx][0], trip_expected[idx][1], trip_expected[idx][2], True,
            trip_expected[idx][3], trip_expected[idx][4], trip_expected[idx][5], trip_expected[idx][6],
        ):
            raise EntropyBulkProjectionError("AUDIT_P3_MENC", f"triplet[{idx}] invariants mismatch")

    _require_flag(p3, "all_schur_dark_projections_certified", True, "AUDIT_P3_SCHUR")
    schur_specs = (
        (
            "schur_dark_gravity_2x2", 2, 1, 1,
            Fraction(5, 1), Fraction(2, 1), Fraction(5, 2),
            [Fraction(2, 1)], [Fraction(4, 5)],
            Fraction(48, 5), Fraction(8, 5), Fraction(8, 1),
        ),
        (
            "schur_dark_gravity_4x4", 4, 2, 2,
            Fraction(192, 1), Fraction(15, 1), Fraction(64, 5),
            [Fraction(17, 15), Fraction(23, 15)], [Fraction(11, 24), Fraction(13, 24)],
            Fraction(149, 12), Fraction(27, 20), Fraction(166, 15),
        ),
        (
            "schur_dark_gravity_6x6", 6, 3, 3,
            Fraction(4200, 1), Fraction(72, 1), Fraction(175, 3),
            [Fraction(5, 6), Fraction(4, 3), Fraction(11, 6)], [Fraction(11, 30), Fraction(1, 2), Fraction(19, 30)],
            Fraction(302, 15), Fraction(32, 15), Fraction(18, 1),
        ),
    )
    for sk, exp_n, exp_no, exp_nh, exp_dm, exp_dhh, exp_dso, exp_j, exp_phi, exp_ef, exp_eo, exp_ed in schur_specs:
        sd = _require_dict_exact_keys(p3, sk, _SCHUR_KEYS, "AUDIT_P3_SCHUR_OBJ")
        for fk in (
            "full_pd",
            "m_hh_pd",
            "schur_so_pd",
            "schur_det_identity_exact",
            "j_dark_all_strictly_positive",
            "phi_o_all_strictly_positive",
            "schur_matches_full_solve_exact",
            "energy_decomposition_exact",
            "dark_shadow_strictly_positive",
        ):
            _require_flag(sd, fk, True, "AUDIT_P3_SCHUR_FLAG")
        dm = parse_exact_rational(sd["det_m"], f"{sk}.det_m")
        dhh = parse_exact_rational(sd["det_m_hh"], f"{sk}.det_m_hh")
        dso = parse_exact_rational(sd["det_s_o"], f"{sk}.det_s_o")
        ef = parse_exact_rational(sd["full_energy"], f"{sk}.e_full")
        eo = parse_exact_rational(sd["obs_schur_energy"], f"{sk}.e_obs")
        ed = parse_exact_rational(sd["dark_shadow_energy_deficit"], f"{sk}.deficit")
        j_list = _require_rational_list(sd["j_dark"], f"{sk}.j_dark", exp_no, "AUDIT_P3_SCHUR_VAL")
        phi_list = _require_rational_list(sd["phi_o_schur"], f"{sk}.phi_o_schur", exp_no, "AUDIT_P3_SCHUR_VAL")
        if (
            require_exact_int(sd["n_total"], f"{sk}.n_total"),
            require_exact_int(sd["n_obs"], f"{sk}.n_obs"),
            require_exact_int(sd["n_hidden"], f"{sk}.n_hidden"),
            dm, dhh, dso, dm == dhh * dso,
            j_list, phi_list,
            ef, eo, ed, ef == eo + ed, ed > 0,
        ) != (exp_n, exp_no, exp_nh, exp_dm, exp_dhh, exp_dso, True, exp_j, exp_phi, exp_ef, exp_eo, exp_ed, True, True):
            raise EntropyBulkProjectionError("AUDIT_P3_SCHUR_VAL", f"{sk} algebraic invariants mismatch")

    # Pillar 4: Shtanov-Sahni Bounce, DMPR Pell Shadows & GW170817/CMB Gates
    p4 = _require_dict_exact_keys(payload, "pillar4_bounce_dmpr_pell_observational_gates", _P4_KEYS, "AUDIT_P4_MISSING")
    bnc = _require_dict_exact_keys(p4, "shtanov_sahni_timelike_bounce", _BOUNCE_KEYS, "AUDIT_P4_BOUNCE")
    for fk in ("ss_regular_bounce_certified", "rs2_no_bounce_singular_certified"):
        _require_flag(bnc, fk, True, "AUDIT_P4_BOUNCE_FLAG")
    if (
        parse_exact_rational(bnc["ss_h2_at_rhoc"], "ss_h2"),
        parse_exact_rational(bnc["ss_dh2_dx_at_rhoc"], "ss_dh2"),
        parse_exact_rational(bnc["ss_h2_peak_at_half_rhoc"], "ss_peak"),
        parse_exact_rational(bnc["ss_bounce_hdot_radiation"], "ss_rad"),
        parse_exact_rational(bnc["ss_bounce_hdot_dust"], "ss_dust"),
        parse_exact_rational(bnc["rs2_h2_at_rhoc"], "rs2_h2"),
        parse_exact_rational(bnc["rs2_dh2_dx_at_rhoc"], "rs2_dh2"),
        parse_exact_rational(bnc["rs2_hdot_radiation_at_rhoc"], "rs2_hdot"),
    ) != (Fraction(0, 1), Fraction(-1, 1), Fraction(1, 4), Fraction(2, 1), Fraction(3, 2), Fraction(2, 1), Fraction(3, 1), Fraction(-6, 1)):
        raise EntropyBulkProjectionError("AUDIT_P4_BOUNCE_VAL", "Shtanov-Sahni vs RS-II bounce invariants mismatch")

    dmpr = _require_dict_exact_keys(p4, "dmpr_pell_tidal_charge_shadows", _DMPR_KEYS, "AUDIT_P4_DMPR")
    for fk in ("pell_rational_parametrization_verified", "q_neg1_bracket_certified", "shadow_chain_strictly_increasing", "all_pell_witnesses_valid"):
        _require_flag(dmpr, fk, True, "AUDIT_P4_DMPR_FLAG")
    b2_lo = parse_exact_rational(dmpr["q_neg1_b_crit_sq_lo"], "q_m1_lo")
    b2_hi = parse_exact_rational(dmpr["q_neg1_b_crit_sq_hi"], "q_m1_hi")
    if (
        require_exact_int(dmpr["q_neg1_exact_radicand_17_cubed"], "radicand"),
        b2_lo, b2_hi,
    ) != (4913, Fraction(141, 4), Fraction(71, 2)):
        raise EntropyBulkProjectionError("AUDIT_P4_RAD", "DMPR q=-1 radicand or bracket mismatch")
    pell_specs = (
        ("witness_q_pos1", Fraction(0, 1), Fraction(1, 1), Fraction(16, 1), "16.0000"),
        ("witness_q_zero_schwarzschild", Fraction(1, 1), Fraction(3, 1), Fraction(27, 1), "27.0000"),
        ("witness_q_neg_495_289_pell", Fraction(28, 17), Fraction(81, 17), Fraction(574992, 14161), "40.6039"),
        ("witness_q_neg35_pell", Fraction(6, 1), Fraction(17, 1), Fraction(2000, 9), "222.2222"),
    )
    for wk, exp_a, exp_b, exp_b2, exp_4dp in pell_specs:
        wd = _require_dict_exact_keys(dmpr, wk, _PELL_WIT_KEYS, "AUDIT_P4_WIT")
        for fk in ("horizon_root_exact", "photon_sphere_root_exact", "envelope_deriv_negative"):
            _require_flag(wd, fk, True, "AUDIT_P4_WIT_FLAG")
        wa = parse_exact_rational(wd["a"], f"{wk}.a")
        wb = parse_exact_rational(wd["b"], f"{wk}.b")
        wq = parse_exact_rational(wd["q_over_m2"], f"{wk}.q")
        wrh = parse_exact_rational(wd["r_h_over_m"], f"{wk}.rh")
        wrp = parse_exact_rational(wd["r_ph_over_m"], f"{wk}.rph")
        wfrp = parse_exact_rational(wd["f_at_r_ph"], f"{wk}.frph")
        wb2 = parse_exact_rational(wd["b_crit_sq_over_m2"], f"{wk}.b2")
        wder = parse_exact_rational(wd["envelope_deriv_db2_dq"], f"{wk}.der")
        if (
            wa, wb, wb * wb - 8 * wa * wa == 1,
            parse_exact_rational(wd["pell_residual"], f"{wk}.pres"),
            wq == Fraction(1, 1) - wa * wa,
            wrh == Fraction(1, 1) + wa,
            2 * wrp == Fraction(3, 1) + wb,
            wfrp * wrp * wrp == wrp * wrp - 2 * wrp + wq,
            wb2, wb2 * wfrp == wrp * wrp,
            wder * wfrp * wfrp == Fraction(-1, 1),
            require_exact_str(wd["b_crit_sq_4dp"], f"{wk}.4dp"),
        ) != (exp_a, exp_b, True, Fraction(0, 1), True, True, True, True, exp_b2, True, True, exp_4dp):
            raise EntropyBulkProjectionError("AUDIT_P4_B2", f"{wk} Pell shadow invariants mismatch")
    w2 = _require_dict_exact_keys(dmpr, "witness_q_neg2", _NEG2_WIT_KEYS, "AUDIT_P4_WIT")
    _require_flag(w2, "photon_sphere_root_exact", True, "AUDIT_P4_WIT_FLAG")
    if (
        parse_exact_rational(w2["q_over_m2"], "q_m2"),
        parse_exact_rational(w2["r_ph_over_m"], "rph_m2"),
        parse_exact_rational(w2["f_at_r_ph"], "f_m2"),
        parse_exact_rational(w2["b_crit_sq_over_m2"], "b2_m2"),
        require_exact_str(w2["b_crit_sq_4dp"], "4dp_m2"),
    ) != (Fraction(-2, 1), Fraction(4, 1), Fraction(3, 8), Fraction(128, 3), "42.6666"):
        raise EntropyBulkProjectionError("AUDIT_P4_B2", "witness_q_neg2 invariants mismatch")

    obs = _require_dict_exact_keys(p4, "gw170817_cmb_observational_gates", _OBS_KEYS, "AUDIT_P4_OBS")
    for fk in ("d_4_inside_gw170817", "flat_d_5_excluded_by_gw170817", "dm_to_baryon_in_5_to_6", "post_stellar_only_bh_ruled_out_at_cmb"):
        _require_flag(obs, fk, True, "AUDIT_P4_OBS_FLAG")
    d_lo = parse_exact_rational(obs["gw170817_d_lo"], "d_lo")
    d_hi = parse_exact_rational(obs["gw170817_d_hi"], "d_hi")
    d_mar = parse_exact_rational(obs["flat_d_5_exclusion_margin"], "d_mar")
    odm = parse_exact_rational(obs["omega_dm_h2"], "odm")
    ob = parse_exact_rational(obs["omega_b_h2"], "ob")
    rat = parse_exact_rational(obs["dm_to_baryon_ratio"], "rat")
    if (
        d_lo, d_hi, d_mar, d_mar == Fraction(5, 1) - d_hi,
        parse_exact_rational(obs["flat5d_amp_ratio_sq_40mpc_rc10"], "amp_sq"),
        require_exact_int(obs["cmb_redshift_z"], "cmb_z"),
        require_exact_int(obs["first_stars_redshift_upper"], "stars_z"),
        odm, ob, rat, rat * ob == odm,
        require_exact_str(obs["dm_to_baryon_ratio_4dp"], "rat_4dp"),
    ) != (
        Fraction(98, 25), Fraction(409, 100), Fraction(91, 100), True,
        Fraction(1, 4), 1100, 30,
        Fraction(3, 25), Fraction(2237, 100000), Fraction(12000, 2237), True,
        "5.3643",
    ):
        raise EntropyBulkProjectionError("AUDIT_P4_OBS_VAL", "GW170817/CMB observational gate invariants mismatch")

    return {
        "secondary_audit_passed": True,
        "pillars_audited": 4,
        "schur_graphs_audited": 3,
        "dmpr_shadows_audited": 5,
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
        raise EntropyBulkProjectionError("CRLF_FORBIDDEN", "CRLF line endings forbidden in certificate")
    if not raw.endswith(b"\n"):
        raise EntropyBulkProjectionError("MISSING_TRAILING_LF", "certificate must end with a single LF")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise EntropyBulkProjectionError("INVALID_UTF8", "certificate is not valid UTF-8") from exc
    cert = parse_strict_json_text(text, require_object=True)
    canonical_raw = canonical_json_bytes(cert)
    if raw != canonical_raw + b"\n":
        raise EntropyBulkProjectionError("NON_CANONICAL_BYTES", "certificate bytes are not canonical ASCII JSON + LF")
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
# Strict Fail-Closed Manual CLI Parsing
# ---------------------------------------------------------------------------

def _parse_cli_argv(argv: Sequence[str]) -> tuple[str, Path | None, bool]:
    if type(argv) not in (list, tuple):
        raise EntropyBulkProjectionError("INVALID_ARGV", "argv must be exact list/tuple of strict str")
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
                raise EntropyBulkProjectionError("DUPLICATE_FLAG", "duplicate --json flag")
            as_json = True
            i += 1
        elif tok == "--standalone":
            if mode is not None:
                raise EntropyBulkProjectionError("CONFLICTING_MODE", "multiple mode flags forbidden")
            mode = "standalone"
            i += 1
        elif tok in ("--check", "--write"):
            if mode is not None:
                raise EntropyBulkProjectionError("CONFLICTING_MODE", "multiple mode flags forbidden")
            if i + 1 >= n:
                raise EntropyBulkProjectionError("MISSING_PATH_ARG", f"{tok} requires a path argument")
            val = argv[i + 1]
            if not val or val.startswith("-"):
                raise EntropyBulkProjectionError("INVALID_PATH_ARG", f"{tok} path cannot be empty or flag-like")
            mode = "check" if tok == "--check" else "write"
            target = Path(val)
            i += 2
        else:
            raise EntropyBulkProjectionError("UNKNOWN_FLAG", f"unrecognized CLI argument: {tok}")

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
    except EntropyBulkProjectionError as exc:
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
