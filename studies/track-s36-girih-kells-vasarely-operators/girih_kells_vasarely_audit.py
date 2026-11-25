#!/usr/bin/env python3
"""
Track S36: Zone-B Hardened Atomic dir_fd CLI & Secondary Algebraic Auditor.

Zero external dependencies, zero AST floats, zero bare asserts, zero .isdigit(),
zero mathematical RNG (`secrets.token_hex(8)` used strictly for atomic temp
filename collision resistance).
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

from girih_kells_vasarely_oracle import (  # noqa: E402
    GirihKellsVasarelyError,
    HARD_MAX_BYTES_CAP,
    MAX_JSON_BYTES,
    SCHEMA_VERSION,
    TRACK_ID,
    build_standalone_certificate,
    canonical_json_bytes,
    parse_exact_rational,
    parse_strict_json_text,
    pin_payload_exact,
    require_int,
    validate_certificate_payload,
    validate_json_tree_iterative,
)

_EXACT_PATH_TYPE = type(Path("."))
_READ_CHUNK_BYTES = 65536
_TMP_LOCK = threading.Lock()
_TMP_COUNTER = 0
_TMP_MAX_ATTEMPTS = 32
_DARWIN_SYSTEM_ALIASES: dict[str, str] = {
    "var": "/private/var",
    "tmp": "/private/tmp",
    "etc": "/private/etc",
}


# ---------------------------------------------------------------------------
# Zone-B Hardened Atomic dir_fd File I/O (TOCTOU, PWD, Hardlinks, Surrogates)
# ---------------------------------------------------------------------------

def _normalize_darwin_system_prefix(path: Path, allow_exact: bool = False) -> Path:
    """On macOS only, rewrite verified root-owned /var, /tmp, /etc system aliases to /private/*."""
    if sys.platform != "darwin":
        return path
    if not path.is_absolute():
        return path
    parts = path.parts
    if parts[0] != "/":
        return path
    if ".." in parts:
        return path
    min_parts = 2 if allow_exact else 3
    if len(parts) < min_parts:
        return path
    alias_name = parts[1]
    canonical = _DARWIN_SYSTEM_ALIASES.get(alias_name)
    if canonical is None:
        return path
    alias_path = f"/{alias_name}"
    try:
        st = os.lstat(alias_path)
        target = os.readlink(alias_path)
    except OSError:
        return path
    if not stat.S_ISLNK(st.st_mode):
        return path
    if st.st_uid != 0:
        return path
    if target not in (canonical, canonical.lstrip("/")):
        return path
    return Path(canonical, *parts[2:])


def _require_utf8_str(raw: str, label: str) -> str:
    try:
        raw.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise GirihKellsVasarelyError("INVALID_UTF8_SURROGATE", f"{label} contains lone UTF-16 surrogate") from exc
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
                    raise GirihKellsVasarelyError("SYMLINK_FORBIDDEN", f"symlink forbidden at {label}") from exc
                raise GirihKellsVasarelyError("PATH_STAT_ERROR", f"non-directory ancestor at {label}") from exc
            os.close(dfd)
            raise GirihKellsVasarelyError("FILE_IO_ERROR", f"cannot traverse {label}: {type(exc).__name__}") from exc
        os.close(dfd)
        dfd = nxt
    return dfd


def _check_pwd_no_symlinks() -> None:
    """Verify logical PWD ancestors contain zero symlinks via dir_fd chain (zero islink)."""
    pwd_env = os.environ.get("PWD", "")
    if not pwd_env.startswith("/"):
        return
    _require_utf8_str(pwd_env, "PWD")
    pwd_path = _normalize_darwin_system_prefix(Path(pwd_env), allow_exact=True)
    pwd_parts = [p for p in pwd_path.parts[1:] if p not in ("", ".")]
    try:
        root_fd = os.open("/", os.O_RDONLY | os.O_DIRECTORY)
    except OSError as exc:
        raise GirihKellsVasarelyError("CWD_UNAVAILABLE", f"cannot open root: {type(exc).__name__}") from exc
    end_fd = _step_dir_fd_chain(root_fd, pwd_parts, "pwd_ancestor")
    os.close(end_fd)


def _open_parent_dir_fd(path: Any) -> tuple[int, str]:
    """Validate exact Path type and atomically pin parent dir_fd against TOCTOU swaps."""
    if type(path) is not _EXACT_PATH_TYPE:
        raise GirihKellsVasarelyError("INVALID_PATH_TYPE", "path must be exact pathlib.Path")
    raw_str = str(path)
    if "\x00" in raw_str:
        raise GirihKellsVasarelyError("INVALID_PATH", "path contains NUL byte")
    _require_utf8_str(raw_str, "path")

    if path.is_absolute():
        norm_path = _normalize_darwin_system_prefix(path, allow_exact=False)
        raw_parts = [p for p in norm_path.parts[1:] if p not in ("", ".")]
        try:
            start_fd = os.open(norm_path.anchor, os.O_RDONLY | os.O_DIRECTORY)
        except OSError as exc:
            raise GirihKellsVasarelyError("FILE_IO_ERROR", f"cannot open root anchor: {type(exc).__name__}") from exc
    else:
        try:
            os.getcwd()
            start_fd = os.open(".", os.O_RDONLY | os.O_DIRECTORY)
        except OSError as exc:
            raise GirihKellsVasarelyError("CWD_UNAVAILABLE", f"CWD unavailable: {type(exc).__name__}") from exc
        try:
            _check_pwd_no_symlinks()
        except GirihKellsVasarelyError:
            os.close(start_fd)
            raise
        raw_parts = [p for p in path.parts if p not in ("", ".")]

    if not raw_parts or raw_parts[-1] == "..":
        os.close(start_fd)
        raise GirihKellsVasarelyError("NON_REGULAR_FILE", "target path names a directory")

    dfd = _step_dir_fd_chain(start_fd, raw_parts[:-1], "path_component")
    return dfd, raw_parts[-1]


def read_regular_bytes_capped(path: Path, max_bytes: int = MAX_JSON_BYTES) -> bytes:
    """Streaming 65536-byte capped regular-file reader pinned to parent dir_fd."""
    cap = require_int(max_bytes, "max_bytes", lo=1, hi=HARD_MAX_BYTES_CAP)
    dfd, leaf = _open_parent_dir_fd(path)
    fd = -1
    try:
        try:
            fd = os.open(leaf, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=dfd)
        except OSError as exc:
            if exc.errno == errno.ELOOP:
                raise GirihKellsVasarelyError("SYMLINK_FORBIDDEN", "symlink forbidden at leaf") from exc
            raise GirihKellsVasarelyError("FILE_READ_ERROR", f"cannot open file: {type(exc).__name__}") from exc
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise GirihKellsVasarelyError("NON_REGULAR_FILE", "target is not a regular file")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(fd, _READ_CHUNK_BYTES)
            if not chunk:
                break
            total += len(chunk)
            if total > cap:
                raise GirihKellsVasarelyError("FILE_TOO_LARGE", f"file exceeds {cap} bytes")
            chunks.append(chunk)
        return b"".join(chunks)
    except GirihKellsVasarelyError:
        raise
    except OSError as exc:
        raise GirihKellsVasarelyError("FILE_READ_ERROR", f"failed reading file: {type(exc).__name__}") from exc
    finally:
        if fd >= 0:
            os.close(fd)
        os.close(dfd)


def write_regular_file_bytes(path: Path, payload: bytes) -> None:
    """Atomic 0o600 dir_fd writer with Lock, EEXIST retry, fsync, pre-replace nlink==1, and dir fsync."""
    global _TMP_COUNTER
    if type(payload) is not bytes:
        raise GirihKellsVasarelyError("INVALID_WRITE_DATA", "payload must be exact bytes")
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
            raise GirihKellsVasarelyError("FILE_WRITE_ERROR", f"cannot stat target: {type(exc).__name__}") from exc
        if st is not None:
            if stat.S_ISLNK(st.st_mode):
                raise GirihKellsVasarelyError("SYMLINK_FORBIDDEN", "cannot write to symlink target")
            if not stat.S_ISREG(st.st_mode):
                raise GirihKellsVasarelyError("NON_REGULAR_FILE", "cannot write to non-regular file")
            if st.st_nlink > 1:
                raise GirihKellsVasarelyError("HARDLINK_FORBIDDEN", "cannot write through hardlinked file")

        try:
            for _ in range(_TMP_MAX_ATTEMPTS):
                with _TMP_LOCK:
                    _TMP_COUNTER += 1
                    seq = _TMP_COUNTER
                cand = f".s36_gkv_tmp_{os.getpid()}_{seq}_{secrets.token_hex(8)}"
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
                raise GirihKellsVasarelyError("TEMP_RETRY_EXHAUSTED", "exhausted atomic temp file retries")
            view = memoryview(payload)
            written = 0
            while written < len(payload):
                written += os.write(tmp_fd, view[written:])
            os.fsync(tmp_fd)
            if os.fstat(tmp_fd).st_nlink != 1:
                raise GirihKellsVasarelyError("HARDLINK_FORBIDDEN", "temp file hardlinked before replace")
            os.replace(tmp_name, leaf, src_dir_fd=dfd, dst_dir_fd=dfd)
            created_tmp = False
            os.close(tmp_fd)
            tmp_fd = -1
            os.fsync(dfd)
        except GirihKellsVasarelyError:
            raise
        except OSError as exc:
            raise GirihKellsVasarelyError("FILE_WRITE_ERROR", f"failed atomic write: {type(exc).__name__}") from exc
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
# Independent Secondary Algebraic Audit Across All 4 Pillars
# ---------------------------------------------------------------------------

def secondary_audit_payload(payload: Any) -> dict[str, Any]:
    """Independent secondary exact-int/exact-Q audit over all 4 mathematical pillars."""
    # Entry-point Zone-B gate: reject runtime floats, cycles, depth blowups, oversized
    # ints and any dict/list/str/int subclass before a single algebraic re-derivation runs.
    validate_json_tree_iterative(payload)
    if type(payload) is not dict:
        raise GirihKellsVasarelyError("AUDIT_PAYLOAD_TYPE", "payload must be strict dict")
    if payload.get("all_verified") is not True:
        raise GirihKellsVasarelyError("AUDIT_ALL_VERIFIED_FALSE", "payload.all_verified must be True")

    try:
        # Pillar 1: Girih Q(phi) areas, additive dissections, inflation & E8 icosians
        p1 = payload["pillar1_girih_qphi_e8"]
        tiles = p1["girih_tiles"]
        exp_areas = {
            "rhombus": (Fraction(0, 1), Fraction(1, 1)),
            "pentagon": (Fraction(1, 2), Fraction(3, 2)),
            "bowtie": (Fraction(-1, 1), Fraction(2, 1)),
            "elongated_hexagon": (Fraction(2, 1), Fraction(1, 1)),
            "decagon": (Fraction(5, 1), Fraction(5, 1)),
        }
        if frozenset(tiles.keys()) != frozenset(exp_areas.keys()):
            raise GirihKellsVasarelyError("AUDIT_P1_TILES", "Girih tile set mismatch")
        for tname, (ea, eb) in exp_areas.items():
            tinfo = tiles[tname]
            require_int(tinfo["n_edges"], f"{tname}.n_edges", lo=4, hi=10)
            a_val = parse_exact_rational(tinfo["area_over_sin36"]["a"], f"{tname}.a")
            b_val = parse_exact_rational(tinfo["area_over_sin36"]["b_phi"], f"{tname}.b")
            if a_val != ea or b_val != eb:
                raise GirihKellsVasarelyError("AUDIT_P1_AREA", f"Girih area mismatch for {tname}")
        es = p1["elser_sloane_e8_icosian_bridge"]
        if (
            require_int(es["inner_600cell_vertices"], "es.inner") != 120
            or require_int(es["outer_600cell_vertices"], "es.outer") != 120
            or require_int(es["total_e8_roots"], "es.total") != 240
            or require_int(es["simple_root_count"], "es.simple") != 8
        ):
            raise GirihKellsVasarelyError("AUDIT_P1_E8_COUNTS", "Elser-Sloane E8 vertex/root counts mismatch")
        if parse_exact_rational(es["e8_gram_det"], "es.det") != Fraction(1, 1):
            raise GirihKellsVasarelyError("AUDIT_P1_E8_DET", "E8 icosian Gram det must equal 1")

        # Pillar 2: Book of Kells plait gcd(m,n), breaklines & dual Tait Kirchhoff
        p2 = payload["pillar2_kells_plait_kirchhoff"]
        sw = p2["plait_grid_sweep_1_to_12"]
        if (
            require_int(sw["total_pairs_traced"], "p2.total") != 144
            or require_int(sw["mismatches"], "p2.mismatches") != 0
            or require_int(sw["single_strand_knot_pairs"], "p2.single") != 91
        ):
            raise GirihKellsVasarelyError("AUDIT_P2_SWEEP", "12x12 Celtic plait sweep invariant mismatch")
        kt = p2["kirchhoff_tait_determinants"]
        ck = kt["classic_knots_V_neg1"]
        if (
            require_int(ck["trefoil_3_1"], "ck.trefoil") != 3
            or require_int(ck["figure_eight_4_1"], "ck.fig8") != 5
            or require_int(ck["cinquefoil_5_1"], "ck.cinq") != 5
        ):
            raise GirihKellsVasarelyError("AUDIT_P2_CLASSIC", "classic knot Kirchhoff determinants mismatch")
        cd = kt["celtic_plaits_dual_tait"]
        for key, exp_tau in (("2x2", 4), ("2x3", 15), ("3x3", 192), ("3x4", 2415)):
            row = cd[key]
            tw = require_int(row["tau_white"], f"cd.{key}.tw")
            tb = require_int(row["tau_black"], f"cd.{key}.tb")
            require_int(row["crossings"], f"cd.{key}.crossings", lo=1)
            if tw != exp_tau or tb != exp_tau:
                raise GirihKellsVasarelyError("AUDIT_P2_DUAL_TAIT", f"Celtic dual Tait det mismatch at {key}")

        # Pillar 3: Vasarely Beltrami metric & D4 Plastic Alphabet Burnside
        p3 = payload["pillar3_vasarely_vega_alphabet"]
        samples = p3["vega_orthographic_beltrami"]["pythagorean_samples"]
        if len(samples) != 5:
            raise GirihKellsVasarelyError("AUDIT_P3_SAMPLES_LEN", "must certify 5 Pythagorean Vasarely samples")
        exp_k2 = [Fraction(1, 1), Fraction(169, 144), Fraction(25, 16), Fraction(25, 9), Fraction(169, 25)]
        got_k2 = [parse_exact_rational(s["K_sq_det_g"], "s.K2") for s in samples]
        if got_k2 != exp_k2:
            raise GirihKellsVasarelyError("AUDIT_P3_K2", "Vasarely Beltrami K^2 values mismatch")
        pa = p3["plastic_alphabet_d4_burnside"]
        if (
            require_int(pa["d4_group_order"], "pa.d4") != 8
            or require_int(pa["single_tile_oriented_states"], "pa.states") != 11
            or require_int(pa["single_tile_shape_orbits"], "pa.orbits") != 6
        ):
            raise GirihKellsVasarelyError("AUDIT_P3_SINGLE", "Plastic Alphabet single-tile orbit mismatch")
        qo = pa["quad_2x2_burnside_orbits"]
        if (
            require_int(qo["k_2"], "qo.2") != 6
            or require_int(qo["k_3"], "qo.3") != 21
            or require_int(qo["k_6"], "qo.6") != 231
        ):
            raise GirihKellsVasarelyError("AUDIT_P3_QUAD", "Plastic Alphabet 2x2 Burnside orbits mismatch")

        # Pillar 4: Cross-domain unification
        p4 = payload["pillar4_cross_domain_unification"]
        if require_int(p4["shared_exact_operators"]["bareiss_determinant_bridges"]["p2_kells_3x4_kirchhoff_det"], "p4.det") != 2415:
            raise GirihKellsVasarelyError("AUDIT_P4_BRIDGE", "Pillar 4 bridge determinant mismatch")
    except GirihKellsVasarelyError:
        raise
    except (KeyError, TypeError, AttributeError) as exc:
        raise GirihKellsVasarelyError("AUDIT_SCHEMA_ERROR", f"malformed payload structure: {type(exc).__name__}") from exc

    # Final exact gate: 42 dict key sets, 30 list lengths, 211 type-identical pinned leaves.
    pin_payload_exact(payload)

    return {
        "secondary_audit_passed": True,
        "pillars_checked": 4,
        "girih_tiles_checked": len(exp_areas),
        "pythagorean_samples_checked": len(samples),
    }


def check_certificate_file(path: Path) -> dict[str, Any]:
    raw = read_regular_bytes_capped(path)
    if b"\r" in raw:
        raise GirihKellsVasarelyError("CRLF_FORBIDDEN", "CRLF line endings forbidden in certificate")
    if not raw.endswith(b"\n"):
        raise GirihKellsVasarelyError("MISSING_TRAILING_LF", "certificate must end with a single LF")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise GirihKellsVasarelyError("INVALID_UTF8", "certificate is not valid UTF-8") from exc
    cert = parse_strict_json_text(text, require_object=True)
    canonical_raw = canonical_json_bytes(cert)
    if raw != canonical_raw + b"\n":
        raise GirihKellsVasarelyError("NON_CANONICAL_BYTES", "certificate bytes are not canonical ASCII JSON + LF")
    res = validate_certificate_payload(cert, full_replay=True)
    sec = secondary_audit_payload(cert["payload"])
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
# Strict Zero-Abbreviation Fail-Closed CLI
# ---------------------------------------------------------------------------

def _validate_cli_path_value(flag: str, val: str) -> Path:
    _require_utf8_str(val, f"{flag}.path")
    if not val or val.startswith("-"):
        raise GirihKellsVasarelyError("INVALID_PATH_ARG", f"{flag} path cannot be empty or flag-like")
    return Path(val)


def _parse_cli_argv(argv: Sequence[str]) -> tuple[str, Path | None, bool]:
    if type(argv) not in (list, tuple) or any(type(item) is not str for item in argv):
        raise GirihKellsVasarelyError("INVALID_ARGV", "argv must be exact list/tuple of strict str")

    mode: str | None = None
    target: Path | None = None
    as_json = False
    i = 0
    n = len(argv)
    while i < n:
        tok = _require_utf8_str(argv[i], "argv")
        if tok == "--json":
            if as_json:
                raise GirihKellsVasarelyError("DUPLICATE_FLAG", "duplicate --json flag")
            as_json = True
            i += 1
        elif tok == "--standalone":
            if mode is not None:
                raise GirihKellsVasarelyError("CONFLICTING_MODE", "multiple mode flags forbidden")
            mode = "standalone"
            i += 1
        elif tok in ("--check", "--write"):
            if mode is not None:
                raise GirihKellsVasarelyError("CONFLICTING_MODE", "multiple mode flags forbidden")
            if i + 1 >= n:
                raise GirihKellsVasarelyError("MISSING_PATH_ARG", f"{tok} requires a path argument")
            mode = "check" if tok == "--check" else "write"
            target = _validate_cli_path_value(tok, argv[i + 1])
            i += 2
        elif tok.startswith("--check=") or tok.startswith("--write="):
            if mode is not None:
                raise GirihKellsVasarelyError("CONFLICTING_MODE", "multiple mode flags forbidden")
            flag_name, raw_val = tok.split("=", 1)
            mode = "check" if flag_name == "--check" else "write"
            target = _validate_cli_path_value(flag_name, raw_val)
            i += 1
        else:
            raise GirihKellsVasarelyError("UNKNOWN_FLAG", f"unrecognized CLI argument: {tok}")

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
    except GirihKellsVasarelyError as exc:
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
