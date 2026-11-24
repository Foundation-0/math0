#!/usr/bin/env python3
"""Track S33: Zone-B Hardened CLI, Deterministic Replay & Secondary Algebraic Auditor.

Zero external dependencies, zero floats, zero bare asserts, zero RNG.
Provides full pure-Q deterministic replay and secondary algebraic cross-checking
with atomic per-component `dir_fd` (`openat` + `O_NOFOLLOW | O_DIRECTORY`) path
traversal, atomic `O_CREAT | O_EXCL` + `os.fsync` + `os.replace` + dir `os.fsync`
writes preserving hardlinks and symlinks under concurrent `renameat2(RENAME_EXCHANGE)`
and `os.link`/`os.unlink` races, deleted-CWD fail-closed handling, lone UTF-16
surrogate rejection, and strict zero-abbreviation CLI parsing.
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

from leonardo_codices_oracle import (
    HARD_MAX_BYTES_CAP,
    LeonardoError,
    MAX_JSON_BYTES,
    SCHEMA_VERSION,
    TRACK_ID,
    build_standalone_certificate,
    canonical_json_bytes,
    parse_exact_rational,
    parse_strict_json_text,
    require_int,
    validate_certificate_payload,
)

_EXACT_PATH_TYPE = type(Path("."))
_READ_CHUNK_BYTES = 65536
_TMP_LOCK = threading.Lock()
_TMP_COUNTER = 0
_TMP_MAX_ATTEMPTS = 32


# ---------------------------------------------------------------------------
# Zone-B Hardened Atomic dir_fd File I/O (TOCTOU, PWD, Hardlinks, Surrogates)
# ---------------------------------------------------------------------------

def _require_utf8_str(raw: str, label: str) -> str:
    try:
        raw.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise LeonardoError("INVALID_UTF8_SURROGATE", f"{label} contains lone UTF-16 surrogate") from exc
    return raw


def _step_dir_fd_chain(start_fd: int, components: Sequence[str], label: str) -> int:
    """Atomically traverse directory components via openat(O_RDONLY|O_DIRECTORY|O_NOFOLLOW)."""
    dfd = start_fd
    for comp in components:
        try:
            nxt = os.open(comp, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=dfd)
        except OSError as exc:
            if exc.errno in (errno.ELOOP, errno.ENOTDIR):
                try:
                    is_sym = stat.S_ISLNK(os.lstat(comp, dir_fd=dfd).st_mode)
                except OSError:
                    is_sym = True
                os.close(dfd)
                if is_sym:
                    raise LeonardoError("SYMLINK_FORBIDDEN", f"symlink forbidden at {label}") from exc
                raise LeonardoError("PATH_STAT_ERROR", f"non-directory ancestor at {label}") from exc
            os.close(dfd)
            raise LeonardoError("FILE_IO_ERROR", f"cannot traverse {label}: {type(exc).__name__}") from exc
        os.close(dfd)
        dfd = nxt
    return dfd


def _check_logical_pwd_no_symlinks() -> None:
    pwd_env = os.environ.get("PWD")
    if not pwd_env or not pwd_env.startswith("/"):
        return
    _require_utf8_str(pwd_env, "PWD")
    pwd_parts = [p for p in Path(pwd_env).parts[1:] if p not in ("", ".")]
    try:
        root_fd = os.open("/", os.O_RDONLY | os.O_DIRECTORY)
    except OSError as exc:
        raise LeonardoError("CWD_UNAVAILABLE", f"cannot open root: {type(exc).__name__}") from exc
    end_fd = _step_dir_fd_chain(root_fd, pwd_parts, "pwd_ancestor")
    os.close(end_fd)


def _open_parent_dir_fd(path: Any) -> tuple[int, str]:
    """Validate path and atomically open parent directory fd pinned against TOCTOU swaps."""
    if type(path) is not _EXACT_PATH_TYPE:
        raise LeonardoError("INVALID_PATH_TYPE", "path must be exact pathlib.Path")
    raw_str = str(path)
    if "\x00" in raw_str:
        raise LeonardoError("INVALID_PATH", "path contains NUL byte")
    _require_utf8_str(raw_str, "path")

    if path.is_absolute():
        raw_parts = [p for p in path.parts[1:] if p not in ("", ".")]
        try:
            start_fd = os.open(path.anchor, os.O_RDONLY | os.O_DIRECTORY)
        except OSError as exc:
            raise LeonardoError("FILE_IO_ERROR", f"cannot open root anchor: {type(exc).__name__}") from exc
    else:
        try:
            os.getcwd()
            start_fd = os.open(".", os.O_RDONLY | os.O_DIRECTORY)
        except OSError as exc:
            raise LeonardoError("CWD_UNAVAILABLE", f"current working directory unavailable: {type(exc).__name__}") from exc
        try:
            _check_logical_pwd_no_symlinks()
        except LeonardoError:
            os.close(start_fd)
            raise
        raw_parts = [p for p in path.parts if p not in ("", ".")]

    if not raw_parts or raw_parts[-1] == "..":
        os.close(start_fd)
        raise LeonardoError("NON_REGULAR_FILE", "target path names a directory")

    dfd = _step_dir_fd_chain(start_fd, raw_parts[:-1], "path_component")
    return dfd, raw_parts[-1]


def require_safe_path(path: Any) -> Path:
    """Verify exact Path type, CWD/PWD safety, ancestor traversal, and non-symlink leaf."""
    dfd, leaf = _open_parent_dir_fd(path)
    try:
        try:
            st = os.lstat(leaf, dir_fd=dfd)
        except FileNotFoundError:
            return path
        except OSError as exc:
            raise LeonardoError("PATH_STAT_ERROR", f"cannot lstat target: {type(exc).__name__}") from exc
        if stat.S_ISLNK(st.st_mode):
            raise LeonardoError("SYMLINK_FORBIDDEN", "symlink forbidden at leaf")
        return path
    finally:
        os.close(dfd)


def read_regular_file_bytes(path: Path, max_bytes: int = MAX_JSON_BYTES) -> bytes:
    cap = require_int(max_bytes, "max_bytes", lo=1, hi=HARD_MAX_BYTES_CAP)
    dfd, leaf = _open_parent_dir_fd(path)
    fd = -1
    try:
        try:
            fd = os.open(leaf, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=dfd)
        except OSError as exc:
            if exc.errno == errno.ELOOP:
                raise LeonardoError("SYMLINK_FORBIDDEN", "symlink forbidden at leaf") from exc
            raise LeonardoError("FILE_READ_ERROR", f"cannot open file: {type(exc).__name__}") from exc
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise LeonardoError("NON_REGULAR_FILE", "target is not a regular file")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(fd, _READ_CHUNK_BYTES)
            if not chunk:
                break
            total += len(chunk)
            if total > cap:
                raise LeonardoError("FILE_TOO_LARGE", f"file exceeds {cap} bytes")
            chunks.append(chunk)
        return b"".join(chunks)
    except LeonardoError:
        raise
    except OSError as exc:
        raise LeonardoError("FILE_READ_ERROR", f"failed reading file: {type(exc).__name__}") from exc
    finally:
        if fd >= 0:
            os.close(fd)
        os.close(dfd)


def write_regular_file_bytes(path: Path, payload: bytes) -> None:
    global _TMP_COUNTER
    if type(payload) is not bytes:
        raise LeonardoError("INVALID_WRITE_DATA", "payload must be exact bytes")
    dfd, leaf = _open_parent_dir_fd(path)
    tmp_fd = -1
    created_tmp = False
    tmp_name = ""
    try:
        try:
            st = os.lstat(leaf, dir_fd=dfd)
        except FileNotFoundError:
            st = None
        except OSError as exc:
            raise LeonardoError("FILE_WRITE_ERROR", f"cannot stat target: {type(exc).__name__}") from exc
        if st is not None:
            if stat.S_ISLNK(st.st_mode):
                raise LeonardoError("SYMLINK_FORBIDDEN", "cannot write to symlink target")
            if not stat.S_ISREG(st.st_mode):
                raise LeonardoError("NON_REGULAR_FILE", "cannot write to non-regular file")
            if st.st_nlink > 1:
                raise LeonardoError("HARDLINK_FORBIDDEN", "cannot write through hardlinked file")

        try:
            for _ in range(_TMP_MAX_ATTEMPTS):
                with _TMP_LOCK:
                    _TMP_COUNTER += 1
                    seq = _TMP_COUNTER
                cand = f".s33_leonardo_tmp_{os.getpid()}_{seq}_{secrets.token_hex(8)}"
                try:
                    tmp_fd = os.open(
                        cand,
                        os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_NONBLOCK,
                        0o600,
                        dir_fd=dfd,
                    )
                    tmp_name = cand
                    created_tmp = True
                    break
                except FileExistsError:
                    continue
            if not created_tmp:
                raise LeonardoError("TEMP_RETRY_EXHAUSTED", "exhausted atomic temp file retries")
            view = memoryview(payload)
            written = 0
            while written < len(payload):
                written += os.write(tmp_fd, view[written:])
            os.fsync(tmp_fd)
            if os.fstat(tmp_fd).st_nlink != 1:
                raise LeonardoError("HARDLINK_FORBIDDEN", "temp file hardlinked before replace")
            os.replace(tmp_name, leaf, src_dir_fd=dfd, dst_dir_fd=dfd)
            created_tmp = False
            os.close(tmp_fd)
            tmp_fd = -1
            os.fsync(dfd)
        except LeonardoError:
            raise
        except OSError as exc:
            raise LeonardoError("FILE_WRITE_ERROR", f"failed atomic write: {type(exc).__name__}") from exc
    finally:
        if tmp_fd >= 0:
            os.close(tmp_fd)
        if created_tmp:
            try:
                os.unlink(tmp_name, dir_fd=dfd)
            except OSError:
                pass
        os.close(dfd)


# ---------------------------------------------------------------------------
# Secondary Algebraic Cross-Check over All 5 Pillars
# ---------------------------------------------------------------------------

def secondary_algebraic_audit(payload: Any) -> dict[str, Any]:
    """Independent secondary algebraic cross-checks across all 5 pillars."""
    if type(payload) is not dict:
        raise LeonardoError("AUDIT_PAYLOAD_TYPE", "payload must be strict dict")
    if payload.get("all_verified") is not True:
        raise LeonardoError("AUDIT_ALL_VERIFIED_FALSE", "payload.all_verified must be True")

    try:
        # Pillar 1: Arundel motion (continuous + uniform backward/forward difference)
        p1 = payload["pillar1_arundel_motion"]
        if p1["pitcher_snapshot_45deg"]["is_45_degree_equatione_di_moti"] is not True:
            raise LeonardoError("AUDIT_P1_45DEG", "45-degree Equatione di Moti witness failed")
        if p1["must_fail_cubic_jerk"]["is_straight_hypotenuse"] is not False:
            raise LeonardoError("AUDIT_P1_CUBIC", "cubic jerk must break straight hypotenuse")
        gal_cont = p1["discrete_galileo_continuous_k2"]
        if [require_int(row["N"], "N") for row in gal_cont] != [3, 4, 5, 6] or not all(
            row["all_determinants_zero"] is True for row in gal_cont
        ):
            raise LeonardoError("AUDIT_P1_GALILEO", "continuous Galileo k^2 determinants must vanish")
        bwd = p1["uniform_backward_difference"]
        if [require_int(row["N"], "N") for row in bwd["galileo_k2"]] != [3, 4, 5, 6] or [
            parse_exact_rational(row["first_det"]) for row in bwd["galileo_k2"]
        ] != [Fraction(2, 1)] * 4:
            raise LeonardoError("AUDIT_P1_BWD_GALILEO", "uniform backward-diff Galileo dets must be [2,2,2,2]")
        if [require_int(row["N"], "N") for row in bwd["leonardo_2k"]] != [3, 4, 5, 6] or [
            parse_exact_rational(row["first_det"]) for row in bwd["leonardo_2k"]
        ] != [Fraction(4, 1), Fraction(8, 1), Fraction(16, 1), Fraction(32, 1)]:
            raise LeonardoError("AUDIT_P1_BWD_LEONARDO", "uniform backward-diff Leonardo dets must be [4,8,16,32]")
        fwd = p1["uniform_forward_difference"]
        if [require_int(row["N"], "N") for row in fwd["galileo_k2"]] != [3, 4, 5, 6] or [
            parse_exact_rational(row["first_det"]) for row in fwd["galileo_k2"]
        ] != [Fraction(-2, 1)] * 4:
            raise LeonardoError("AUDIT_P1_FWD_GALILEO", "uniform forward-diff Galileo dets must be [-2,-2,-2,-2]")
        if [require_int(row["N"], "N") for row in fwd["leonardo_2k"]] != [3, 4, 5, 6] or [
            parse_exact_rational(row["first_det"]) for row in fwd["leonardo_2k"]
        ] != [Fraction(-2, 1), Fraction(-4, 1), Fraction(-8, 1), Fraction(-16, 1)]:
            raise LeonardoError("AUDIT_P1_FWD_LEONARDO", "uniform forward-diff Leonardo dets must be [-2,-4,-8,-16]")

        # Pillar 2: Leicester rising bubble
        p2 = payload["pillar2_leicester_bubble"]
        if [require_int(x, "vacuum_l") for x in p2["vacuum_resonance_modes"]] != [7]:
            raise LeonardoError("AUDIT_P2_VACUUM_L7", "unique vacuum resonance must be l=7")
        if p2["sigma_zero_collapse_all_zero"] is not True:
            raise LeonardoError("AUDIT_P2_SIGMA_ZERO", "sigma=0 collapse must vanish identically")
        res_list = p2["positive_rational_resonances_l3_to_l10"]
        if len(res_list) != 6:
            raise LeonardoError("AUDIT_P2_RESONANCE_LEN", "must certify all 6 positive resonances")
        seen_lk: set[tuple[int, int]] = set()
        for res in res_list:
            l_val = require_int(res["l"], "res.l")
            k_val = require_int(res["k"], "res.k")
            seen_lk.add((l_val, k_val))
            if parse_exact_rational(res["tau_lk"]) <= 0:
                raise LeonardoError("AUDIT_P2_TAU_NONPOS", "positive resonance tau must be > 0")
            if parse_exact_rational(res["omega_l_sq"]) != parse_exact_rational(res["k2_omega_2_sq"]):
                raise LeonardoError("AUDIT_P2_RESONANCE_EQ", "resonance frequency equality mismatch")
        if len(seen_lk) != 6:
            raise LeonardoError("AUDIT_P2_RESONANCE_DUP", "positive resonances (l, k) pairs must be distinct")
        hb = p2["hopf_bifurcation_4d"]
        if parse_exact_rational(hb["subcritical_straight_rise"]["hurwitz_d3"]) <= 0:
            raise LeonardoError("AUDIT_P2_HOPF_SUB", "subcritical Hurwitz Delta_3 must be > 0")
        if parse_exact_rational(hb["critical_hopf_threshold"]["hurwitz_d3"]) != 0:
            raise LeonardoError("AUDIT_P2_HOPF_CRIT", "critical Hurwitz Delta_3 must be 0")
        if parse_exact_rational(hb["supercritical_oscillatory"]["hurwitz_d3"]) >= 0:
            raise LeonardoError("AUDIT_P2_HOPF_SUP", "supercritical Hurwitz Delta_3 must be < 0")
        inertias = tuple(
            (
                require_int(hb[key]["hermite_inertia"]["n_pos"], f"{key}.n_pos"),
                require_int(hb[key]["hermite_inertia"]["n_neg"], f"{key}.n_neg"),
                require_int(hb[key]["hermite_inertia"]["n_zero"], f"{key}.n_zero"),
            )
            for key in ("subcritical_straight_rise", "critical_hopf_threshold", "supercritical_oscillatory")
        )
        if inertias != ((4, 0, 0), (2, 0, 2), (2, 2, 0)):
            raise LeonardoError("AUDIT_P2_HOPF_INERTIA", "4D Hopf Hermite inertia transition mismatch")

        # Pillar 3: Atlanticus reciprocal bridge & Da Vinci domes
        p3 = payload["pillar3_atlanticus_bridge_domes"]
        desc = p3["da_vinci_domes_descartes_obstruction"]
        if [require_int(r["degree"], "degree") for r in desc] != [2, 3, 4, 5, 6] or not all(
            parse_exact_rational(r["descartes_defect_half_turns"]) <= 0 for r in desc
        ):
            raise LeonardoError("AUDIT_P3_DESCARTES", "collinear-rod vertex defect must be <= 0")
        torus = p3["euler_torus_tilings_11"]
        if len(torus) != 11:
            raise LeonardoError("AUDIT_P3_TORUS_LEN", "must certify all 11 uniform torus tilings")
        if not all(
            require_int(r["V"], "V") - require_int(r["E"], "E") + require_int(r["F"], "F") == 0
            and require_int(r["chi"], "chi") == 0
            for r in torus
        ):
            raise LeonardoError("AUDIT_P3_TORUS_CHI", "periodic torus tiling chi must be 0")
        spheres = p3["euler_sphere_cages"]
        if len(spheres) != 6 or not all(
            require_int(r["V"], "V") - require_int(r["E"], "E") + require_int(r["F"], "F") == 2
            and require_int(r["chi"], "chi") == 2
            for r in spheres
        ):
            raise LeonardoError("AUDIT_P3_SPHERE_CHI", "spherical cage chi must be 2")
        if p3["reciprocal_bridge_equilibrium_threshold"]["mu_min"] != "1/3":
            raise LeonardoError("AUDIT_P3_BRIDGE_MU", "reciprocal bridge mu_min must be 1/3")
        if p3["reciprocal_bridge_equilibrium_threshold"]["equilibrium_residual_zero"] is not True:
            raise LeonardoError("AUDIT_P3_BRIDGE_EQ", "reciprocal bridge equilibrium residual nonzero")
        if p3["reciprocal_bridge_farkas_collapse_low_mu"]["farkas_vTg_strictly_negative"] is not True:
            raise LeonardoError("AUDIT_P3_FARKAS_MU", "low-mu Farkas dual collapse missing")
        if p3["reciprocal_bridge_central_beam_removal"]["catastrophic_collapse_certified"] is not True:
            raise LeonardoError("AUDIT_P3_BEAM_DEL", "central beam removal collapse missing")

        # Pillar 4: Tree branching & Kirchhoff-Schur vascular pushforward
        p4 = payload["pillar4_trattato_branching_trees"]
        ve = p4["variational_exponents"]
        if (ve["leonardo_p2_q2_m2"], ve["murray_p4_q2_m2"], ve["turbulent_p5_q2_m3"]) != ("2", "3", "7/3"):
            raise LeonardoError("AUDIT_P4_EXPONENTS", "variational branching exponents mismatch")
        dom = p4["symmetric_split_poiseuille_dominance"]
        if parse_exact_rational(dom["C_murray_cubed"]) >= parse_exact_rational(dom["C_leonardo_cubed"]):
            raise LeonardoError("AUDIT_P4_DOMINANCE", "Murray cubed cost must be strictly less than Leonardo")
        ks = p4["kirchhoff_schur_4level_vascular"]
        ks_dims = tuple(
            (
                require_int(ks[k]["n_levels"], f"{k}.n_levels"),
                require_int(ks[k]["n_edges"], f"{k}.n_edges"),
                require_int(ks[k]["n_internal_schur_nodes"], f"{k}.n_internal"),
            )
            for k in ("naive_alpha2_uniform_pipe", "sopp_valbuena_widened_conduit")
        )
        if ks_dims != ((4, 15, 7), (4, 15, 7)) or parse_exact_rational(ks["conductance_gain_ratio"]) != Fraction(15, 4):
            raise LeonardoError("AUDIT_P4_SCHUR_GAIN", "Kirchhoff-Schur conductance gain must be 15/4")

        # Pillar 5: Lunes, aerial screw & CS-13 myth audit
        p5 = payload["pillar5_lunes_aerial_screw_myth"]
        lunes = p5["squarable_lunes_5"]
        if len(lunes) != 5:
            raise LeonardoError("AUDIT_P5_LUNES_LEN", "must certify all 5 squarable lunes")
        if not all(
            require_int(r["deg_in_y"], "deg_in_y") >= 1
            and require_int(r["ratio_m_n"][0], "m") > require_int(r["ratio_m_n"][1], "n")
            and r["ruler_compass_constructible"] is True
            for r in lunes
        ):
            raise LeonardoError("AUDIT_P5_LUNES_CONSTRUCT", "all 5 squarable lunes must be constructible")
        if p5["zero_pi_dissections"]["hippocrates_2_1_lune"]["pi_coeff"] != "0":
            raise LeonardoError("AUDIT_P5_HIPP_PI", "Hippocrates lune pi_coeff must be 0")
        if p5["zero_pi_dissections"]["leonardo_atlanticus_4_lunes"]["pi_coeff"] != "0":
            raise LeonardoError("AUDIT_P5_ROSETTE_PI", "Leonardo rosette pi_coeff must be 0")
        if require_int(p5["galois_obstruction_4_1"]["degree"], "deg41") != 3 or p5["galois_obstruction_4_1"]["ruler_compass_impossible"] is not True:
            raise LeonardoError("AUDIT_P5_GALOIS_41", "4:1 lune Galois obstruction missing")
        if require_int(p5["galois_obstruction_7_1"]["degree"], "deg71") != 6 or p5["galois_obstruction_7_1"]["ruler_compass_impossible"] is not True:
            raise LeonardoError("AUDIT_P5_GALOIS_71", "7:1 lune Galois obstruction missing")
        if p5["aerial_screw_isolift_2506_10223"]["jhu_power_drop_in_42_to_43_pct_band"] is not True:
            raise LeonardoError("AUDIT_P5_SCREW", "aerial screw power reduction bracket failed")
        if p5["cs13_myth_audit"]["attributed_to_leonardo_in_authentic_codices"] is not False:
            raise LeonardoError("AUDIT_P5_MYTH", "Mayer 1772 proof must not be attributed to Leonardo")
    except LeonardoError:
        raise
    except (KeyError, TypeError, AttributeError) as exc:
        raise LeonardoError("AUDIT_SCHEMA_ERROR", f"malformed payload structure: {type(exc).__name__}") from exc

    return {
        "secondary_audit_passed": True,
        "pillars_checked": 5,
        "positive_resonances_checked": len(res_list),
        "torus_tilings_checked": len(torus),
        "squarable_lunes_checked": len(lunes),
    }


def check_certificate_file(path: Path) -> dict[str, Any]:
    raw = read_regular_file_bytes(path)
    if b"\r" in raw:
        raise LeonardoError("CRLF_FORBIDDEN", "CRLF line endings forbidden in certificate")
    if not raw.endswith(b"\n"):
        raise LeonardoError("MISSING_TRAILING_LF", "certificate must end with a single LF")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise LeonardoError("INVALID_UTF8", "certificate is not valid UTF-8") from exc
    cert = parse_strict_json_text(text, require_object=True)
    canonical_raw = canonical_json_bytes(cert)
    if raw != canonical_raw + b"\n":
        raise LeonardoError("NON_CANONICAL_BYTES", "certificate bytes are not canonical ASCII JSON + LF")
    res = validate_certificate_payload(cert, full_replay=True)
    sec = secondary_algebraic_audit(cert["payload"])
    res["canonical_sha256"] = hashlib.sha256(canonical_raw).hexdigest()
    res["file_sha256"] = hashlib.sha256(raw).hexdigest()
    res["secondary_audit"] = sec
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
# Strict Zero-Abbreviation Fail-Closed CLI Parsing
# ---------------------------------------------------------------------------

def _validate_cli_path_value(flag: str, val: str) -> Path:
    _require_utf8_str(val, f"{flag}.path")
    if not val or val.startswith("-"):
        raise LeonardoError("INVALID_PATH_ARG", f"{flag} path cannot be empty or flag-like")
    return Path(val)


def _parse_cli_argv(argv: Sequence[str]) -> tuple[str, Path | None, bool]:
    if type(argv) not in (list, tuple) or any(type(item) is not str for item in argv):
        raise LeonardoError("INVALID_ARGV", "argv must be exact list/tuple of strict str")

    mode: str | None = None
    target: Path | None = None
    as_json = False
    i = 0
    n = len(argv)
    while i < n:
        tok = _require_utf8_str(argv[i], "argv")
        if tok == "--json":
            if as_json:
                raise LeonardoError("DUPLICATE_FLAG", "duplicate --json flag")
            as_json = True
            i += 1
        elif tok == "--standalone":
            if mode is not None:
                raise LeonardoError("CONFLICTING_MODE", "multiple mode flags forbidden")
            mode = "standalone"
            i += 1
        elif tok in ("--check", "--write"):
            if mode is not None:
                raise LeonardoError("CONFLICTING_MODE", "multiple mode flags forbidden")
            if i + 1 >= n:
                raise LeonardoError("MISSING_PATH_ARG", f"{tok} requires a path argument")
            mode = "check" if tok == "--check" else "write"
            target = _validate_cli_path_value(tok, argv[i + 1])
            i += 2
        elif tok.startswith("--check=") or tok.startswith("--write="):
            if mode is not None:
                raise LeonardoError("CONFLICTING_MODE", "multiple mode flags forbidden")
            flag_name, raw_val = tok.split("=", 1)
            mode = "check" if flag_name == "--check" else "write"
            target = _validate_cli_path_value(flag_name, raw_val)
            i += 1
        else:
            raise LeonardoError("UNKNOWN_FLAG", f"unrecognized CLI argument: {tok}")

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
    except LeonardoError as exc:
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
