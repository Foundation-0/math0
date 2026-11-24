#!/usr/bin/env python3
"""
SU(2)_k Chern-Simons Levels, Exact Jones Polynomials, Poincare-Disk
SL(2,Z) Modularity, and Exact NTT+CRT Divisor-Sigma Convolutions.

Pure Python 3 standard library (errno, int, Fraction, hashlib, hmac, json, math,
os, pathlib, stat, sys) with ZERO floating-point operations, ZERO bare `assert`s,
and ZERO RNG.

Three exact-operator pillars:
  1. Exact PD-code Kauffman bracket state sum, Reidemeister I/II/III invariance,
     Jones polynomials (unknot, unlinks, Hopf link, T(2,3) & mirror, T(2,5),
     T(3,4), figure-eight 4_1, Borromean rings L6a4 with exact zero pairwise
     linking numbers proving Abelian-vs-non-Abelian separation), Rosso-Jones
     torus closed form, and exact cyclotomic Chern-Simons level k=1..4 evaluations.
  2. Exact cyclotomic Q(zeta_N) Kac-Peterson modular matrices (S, T) for SU(2)_k
     (k=1..4): S^T = S, S^* = S, S^2 = I, S^dag S = I, (ST)^3 = I, and all
     (k+1)^3 Verlinde fusion coefficients matching truncated Clebsch-Gordan;
     plus exact Q[i] / Q(zeta_12) Cayley Mobius isomorphism C: H -> D for
     SL(2,Z) -> PSU(1,1), metric invariance, and elliptic fixed points i and e^{i*pi/3}.
  3. Exact divisor-sigma_k Hecke multiplicativity (1 <= m,n <= 40, k in {1,3,5})
     and radix-2 Cooley-Tukey Number-Theoretic Transform (NTT) + multi-prime CRT
     zero-float exact integer convolutions matching naive O(N^2) bit-for-bit on
     Ramanujan E2<->E4 (N=128), E4^2=E8 (N=128), and Delta=(E4^3-E6^2)/1728 +
     Ramanujan tau(n) multiplicativity & prime-power Hecke recurrence (N=64).
"""
from __future__ import annotations

import errno
from fractions import Fraction
import hashlib
import hmac
import json
import math
import os
from pathlib import Path
import stat
import sys
from typing import Any

_DIR_OPEN_FLAGS = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
_DARWIN_SYSTEM_ROOT_ALIASES: tuple[tuple[str, str], ...] = (
    ("/var", "/private/var"),
    ("/tmp", "/private/tmp"),
    ("/etc", "/private/etc"),
)

SCHEMA_VERSION = "s23b-jones-cs-poincare-ntt-cert/v1"
TRACK_ID = "TRACK-S23B"
MAX_JSON_DEPTH = 64
MAX_JSON_BYTES = 2_000_000
MAX_INT_BITS = 2048
MAX_INT_DIGITS = 620
MAX_SEQ_LEN = 4096
NTT_PRIME_1 = 998244353   # 119 * 2^23 + 1, primitive root 3
NTT_PRIME_2 = 469762049   # 7 * 2^26 + 1, primitive root 3
NTT_PRIME_3 = 1004535809  # 479 * 2^21 + 1, primitive root 3
NTT_PRIMITIVE_ROOTS: dict[int, int] = {
    NTT_PRIME_1: 3,
    NTT_PRIME_2: 3,
    NTT_PRIME_3: 3,
}
_HEX_LOWER = frozenset("0123456789abcdef")
_ASCII_DIGITS = frozenset("0123456789")
_CS_LEVELS = (1, 2, 3, 4)
_SU2_CYCLOTOMIC_N: dict[int, int] = {1: 24, 2: 16, 3: 40, 4: 24}


class JonesPoincareNTTError(ValueError):
    """Fail-closed typed error (never stripped under `python3 -O`)."""

    def __init__(self, code: str, message: str) -> None:
        self.code = code
        self.message = message
        super().__init__(f"{code}: {message}")


# ---------------------------------------------------------------------------
# Zone-B strict primitives, canonical JSON, and atomic dir_fd I/O (zero floats)
# ---------------------------------------------------------------------------


def _require_valid_utf8_str(s: str, label: str = "str") -> str:
    try:
        s.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise JonesPoincareNTTError("INVALID_UTF8", f"{label} contains unpaired UTF-16 surrogate") from exc
    return s


def require_int(
    val: Any,
    label: str = "int",
    *,
    lo: int | None = None,
    hi: int | None = None,
) -> int:
    if type(val) is not int:
        raise JonesPoincareNTTError("INVALID_INT_TYPE", f"{label} must be strict int, got {type(val).__name__}")
    blen = val.bit_length()
    if blen > MAX_INT_BITS:
        raise JonesPoincareNTTError("INT_BIT_LIMIT", f"{label} bit_length={blen} exceeds {MAX_INT_BITS}")
    if lo is not None:
        if type(lo) is not int:
            raise JonesPoincareNTTError("INVALID_INT_BOUND", f"{label} lo must be strict int")
        if val < lo:
            raise JonesPoincareNTTError("INT_BELOW_MIN", f"{label} bit_length={blen} below min_bits={lo.bit_length()}")
    if hi is not None:
        if type(hi) is not int:
            raise JonesPoincareNTTError("INVALID_INT_BOUND", f"{label} hi must be strict int")
        if val > hi:
            raise JonesPoincareNTTError("INT_ABOVE_MAX", f"{label} bit_length={blen} above max_bits={hi.bit_length()}")
    return val


def require_bool(val: Any, label: str = "bool") -> bool:
    if type(val) is not bool:
        raise JonesPoincareNTTError("INVALID_BOOL_TYPE", f"{label} must be strict bool, got {type(val).__name__}")
    return val


def require_str(val: Any, label: str = "str", *, min_len: int = 1, max_len: int = 1024) -> str:
    if type(val) is not str:
        raise JonesPoincareNTTError("INVALID_STR_TYPE", f"{label} must be strict str, got {type(val).__name__}")
    _require_valid_utf8_str(val, label)
    n = len(val)
    if n < min_len:
        raise JonesPoincareNTTError("STR_TOO_SHORT", f"{label} length {n} < min_bits={min_len.bit_length()}")
    if n > max_len:
        raise JonesPoincareNTTError("STR_TOO_LONG", f"{label} length {n} > max_bits={max_len.bit_length()}")
    return val


def require_seq(
    val: Any,
    label: str = "seq",
    *,
    min_len: int = 1,
    max_len: int = MAX_SEQ_LEN,
) -> tuple[Any, ...]:
    if type(val) not in (list, tuple):
        raise JonesPoincareNTTError("INVALID_SEQ_TYPE", f"{label} must be strict list or tuple")
    n = len(val)
    if n < min_len:
        raise JonesPoincareNTTError("SEQ_TOO_SHORT", f"{label} length {n} < min_bits={min_len.bit_length()}")
    if n > max_len:
        raise JonesPoincareNTTError("SEQ_TOO_LONG", f"{label} length {n} > max_bits={max_len.bit_length()}")
    return tuple(val)


def require_mapping(val: Any, label: str = "mapping") -> dict[str, Any]:
    if type(val) is not dict:
        raise JonesPoincareNTTError("INVALID_MAPPING_TYPE", f"{label} must be strict dict")
    for k in val:
        if type(k) is not str:
            raise JonesPoincareNTTError("NON_STR_KEY", f"{label} keys must be strict str")
        _require_valid_utf8_str(k, f"{label}.key")
    return val


def require_hex64_ascii(val: Any, label: str = "sha256") -> str:
    if type(val) is not str:
        raise JonesPoincareNTTError("INVALID_DIGEST_TYPE", f"{label} must be strict str")
    if len(val) != 64:
        raise JonesPoincareNTTError("INVALID_DIGEST_LEN", f"{label} must have length 64")
    for ch in val:
        if ch not in _HEX_LOWER:
            raise JonesPoincareNTTError("INVALID_DIGEST_HEX", f"{label} must be lowercase ASCII hex")
    return val


def constant_time_hex64_equal(left: Any, right: Any, label: str = "sha256") -> bool:
    a = require_hex64_ascii(left, f"{label}.left")
    b = require_hex64_ascii(right, f"{label}.right")
    return hmac.compare_digest(a, b)


def _reject_float_token(tok: str) -> Any:
    raise JonesPoincareNTTError("JSON_FLOAT_FORBIDDEN", f"float literal forbidden: {tok!r}")


def _reject_constant_token(tok: str) -> Any:
    raise JonesPoincareNTTError("JSON_CONSTANT_FORBIDDEN", f"non-RFC8259 constant forbidden: {tok!r}")


def _parse_capped_int_token(tok: str) -> int:
    digits = tok[1:] if tok.startswith("-") else tok
    if not digits or any(ch not in _ASCII_DIGITS for ch in digits):
        raise JonesPoincareNTTError("INVALID_INT_TOKEN", "integer token must be ASCII digits")
    if len(digits) > MAX_INT_DIGITS:
        raise JonesPoincareNTTError("INT_DIGIT_LIMIT", f"integer token exceeds {MAX_INT_DIGITS} digits")
    val = int(tok)
    blen = val.bit_length()
    if blen > MAX_INT_BITS:
        raise JonesPoincareNTTError("INT_BIT_LIMIT", f"integer token bit_length={blen} exceeds {MAX_INT_BITS}")
    return val


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise JonesPoincareNTTError("JSON_DUPLICATE_KEY", f"duplicate JSON key: {k!r}")
        out[k] = v
    return out


def fmt_q(q: Fraction) -> str:
    if type(q) is not Fraction:
        raise JonesPoincareNTTError("INVALID_FRACTION_TYPE", "q must be strict Fraction")
    nb = q.numerator.bit_length()
    db = q.denominator.bit_length()
    if nb > MAX_INT_BITS or db > MAX_INT_BITS:
        raise JonesPoincareNTTError("FRACTION_BIT_LIMIT", f"fraction bit_lengths=({nb},{db}) exceed {MAX_INT_BITS}")
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"


def validate_json_value(obj: Any, *, max_depth: int = MAX_JSON_DEPTH) -> None:
    limit = require_int(max_depth, "max_depth", lo=1, hi=128)
    stack: list[tuple[Any, int]] = [(obj, 0)]
    while stack:
        cur, depth = stack.pop()
        if depth > limit:
            raise JonesPoincareNTTError("MAX_DEPTH_EXCEEDED", f"JSON nesting exceeds {limit}")
        t = type(cur)
        if t is dict:
            for k, v in cur.items():
                if type(k) is not str:
                    raise JonesPoincareNTTError("NON_STR_KEY", "JSON object keys must be strict str")
                _require_valid_utf8_str(k, "json_key")
                stack.append((v, depth + 1))
        elif t is list:
            for item in cur:
                stack.append((item, depth + 1))
        elif t is int:
            blen = cur.bit_length()
            if blen > MAX_INT_BITS:
                raise JonesPoincareNTTError("INT_BIT_LIMIT", f"JSON int bit_length={blen} exceeds {MAX_INT_BITS}")
        elif t is str:
            _require_valid_utf8_str(cur, "json_str")
        elif t is bool or cur is None:
            continue
        elif t is float:
            raise JonesPoincareNTTError("FLOAT_FORBIDDEN", "float values are forbidden in exact JSON")
        else:
            raise JonesPoincareNTTError("UNSUPPORTED_JSON_TYPE", f"unsupported JSON type {t.__name__}")


def parse_strict_json_text(raw_text: str, *, require_object: bool = True) -> Any:
    req_obj = require_bool(require_object, "require_object")
    if type(raw_text) is not str:
        raise JonesPoincareNTTError("INVALID_JSON_INPUT", "JSON text must be strict str")
    encoded = _require_valid_utf8_str(raw_text, "json_text").encode("utf-8")
    if len(encoded) > MAX_JSON_BYTES:
        raise JonesPoincareNTTError("JSON_TOO_LARGE", f"JSON exceeds {MAX_JSON_BYTES} bytes")
    if not raw_text.strip():
        raise JonesPoincareNTTError("EMPTY_JSON_INPUT", "JSON text must be non-empty")
    try:
        obj = json.loads(
            raw_text,
            parse_float=_reject_float_token,
            parse_constant=_reject_constant_token,
            parse_int=_parse_capped_int_token,
            object_pairs_hook=_reject_duplicate_keys,
        )
    except JonesPoincareNTTError:
        raise
    except (json.JSONDecodeError, ValueError, RecursionError) as exc:
        raise JonesPoincareNTTError("JSON_PARSE_ERROR", f"invalid JSON: {type(exc).__name__}") from exc
    if req_obj and type(obj) is not dict:
        raise JonesPoincareNTTError("JSON_ROOT_NOT_OBJECT", "JSON root must be a strict object")
    validate_json_value(obj)
    return obj


def canonical_json_bytes(obj: Any) -> bytes:
    validate_json_value(obj)
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False).encode("ascii")


def sha256_canonical(obj: Any) -> str:
    return hashlib.sha256(canonical_json_bytes(obj)).hexdigest()


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
            target = os.readlink(alias)
            if target not in (canonical, canonical.lstrip("/")):
                return path
        except OSError:
            return path
        return Path(canonical, *parts[2:])
    return path


def _open_dir_chain(anchor: str, parts: tuple[str, ...], err_code: str, label: str) -> int:
    """Atomically walk directory components via openat(..., O_DIRECTORY | O_NOFOLLOW)."""
    try:
        dfd = os.open(anchor, _DIR_OPEN_FLAGS)
    except OSError as exc:
        raise JonesPoincareNTTError("CWD_UNAVAILABLE", f"{label} anchor open failed: {exc.strerror}") from exc
    try:
        for part in parts:
            try:
                nxt = os.open(part, _DIR_OPEN_FLAGS, dir_fd=dfd)
            except OSError as exc:
                if exc.errno in (errno.ELOOP, errno.ENOTDIR):
                    raise JonesPoincareNTTError(
                        "SYMLINK_FORBIDDEN", f"{label} symlink or non-directory ancestor forbidden"
                    ) from exc
                raise JonesPoincareNTTError(err_code, f"{label} directory open failed: {exc.strerror}") from exc
            os.close(dfd)
            dfd = nxt
    except BaseException:
        os.close(dfd)
        raise
    return dfd


def _validate_path_and_split(path: Path, label: str = "path", err_code: str = "FILE_READ_ERROR") -> tuple[str, tuple[str, ...]]:
    if type(path) is not type(Path()):
        raise JonesPoincareNTTError("INVALID_PATH_TYPE", f"{label} must be a strict Path")
    raw_str = str(path)
    if "\x00" in raw_str:
        raise JonesPoincareNTTError("INVALID_PATH_NUL", f"{label} contains embedded NUL byte")
    _require_valid_utf8_str(raw_str, label)
    if not path.is_absolute():
        try:
            cwd_real = os.path.realpath(os.getcwd())
        except OSError as exc:
            raise JonesPoincareNTTError("CWD_UNAVAILABLE", f"{label} cwd unavailable: {exc.strerror}") from exc
        pwd_env = os.environ.get("PWD", "")
        if pwd_env.startswith("/") and os.path.realpath(pwd_env) == cwd_real:
            pwd_path = _normalize_darwin_system_prefix(Path(pwd_env), allow_exact=True)
            pwd_fd = _open_dir_chain(
                pwd_path.anchor, pwd_path.relative_to(pwd_path.anchor).parts, err_code, label
            )
            os.close(pwd_fd)
        return ".", path.parts
    norm_path = _normalize_darwin_system_prefix(path)
    return norm_path.anchor, norm_path.relative_to(norm_path.anchor).parts


def require_safe_path(path: Path, label: str = "path", err_code: str = "FILE_READ_ERROR") -> Path:
    anchor, parts = _validate_path_and_split(path, label, err_code)
    if not parts:
        return path
    *dir_parts, leaf = parts
    dfd = _open_dir_chain(anchor, tuple(dir_parts), err_code, label)
    try:
        try:
            st = os.lstat(leaf, dir_fd=dfd)
        except FileNotFoundError:
            return path
        except OSError as exc:
            raise JonesPoincareNTTError(err_code, f"{label} stat failed: {exc.strerror}") from exc
        if stat.S_ISLNK(st.st_mode):
            raise JonesPoincareNTTError("SYMLINK_FORBIDDEN", f"{label} must not be a symlink")
    finally:
        os.close(dfd)
    return path


def _open_read_fd_no_toctou(path: Path, label: str) -> int:
    anchor, parts = _validate_path_and_split(path, label, "FILE_READ_ERROR")
    if not parts:
        raise JonesPoincareNTTError("NON_REGULAR_FILE", f"{label} must be a regular file")
    *dir_parts, leaf = parts
    dfd = _open_dir_chain(anchor, tuple(dir_parts), "FILE_READ_ERROR", label)
    leaf_flags = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK
    try:
        try:
            return os.open(leaf, leaf_flags, dir_fd=dfd)
        except OSError as exc:
            if exc.errno == errno.ELOOP:
                raise JonesPoincareNTTError("SYMLINK_FORBIDDEN", f"{label} must not be a symlink") from exc
            raise JonesPoincareNTTError("FILE_READ_ERROR", f"{label} open failed: {exc.strerror}") from exc
    finally:
        os.close(dfd)


def _open_unique_temp_in_dir(dfd: int, label: str) -> tuple[str, int]:
    """Deterministically create an exclusive regular temp file inside pinned dir_fd (zero RNG)."""
    pid = os.getpid()
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_NONBLOCK
    for attempt in range(64):
        tmp_name = f".s23b.{pid}.{attempt}.tmp"
        try:
            fd = os.open(tmp_name, flags, 0o600, dir_fd=dfd)
            return tmp_name, fd
        except FileExistsError:
            continue
        except OSError as exc:
            raise JonesPoincareNTTError("FILE_WRITE_ERROR", f"{label} temp open failed: {exc.strerror}") from exc
    raise JonesPoincareNTTError("FILE_WRITE_ERROR", f"{label} temp name collisions exhausted")


def load_safe_bytes(path: Path, label: str = "file") -> bytes:
    fd = _open_read_fd_no_toctou(path, label)
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise JonesPoincareNTTError("NON_REGULAR_FILE", f"{label} must be a regular file")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(fd, min(65536, MAX_JSON_BYTES + 1 - total))
            if not chunk:
                break
            total += len(chunk)
            if total > MAX_JSON_BYTES:
                raise JonesPoincareNTTError("FILE_TOO_LARGE", f"{label} exceeds {MAX_JSON_BYTES} bytes")
            chunks.append(chunk)
        return b"".join(chunks)
    except OSError as exc:
        raise JonesPoincareNTTError("FILE_READ_ERROR", f"{label} read failed: {exc.strerror}") from exc
    finally:
        os.close(fd)


def safe_write_bytes(path: Path, data: bytes, label: str = "out") -> None:
    if type(data) is not bytes:
        raise JonesPoincareNTTError("INVALID_BYTES_TYPE", f"{label} data must be strict bytes")
    anchor, parts = _validate_path_and_split(path, label, "FILE_WRITE_ERROR")
    if not parts:
        raise JonesPoincareNTTError("NON_REGULAR_FILE", f"{label} must be a regular file")
    *dir_parts, leaf = parts
    dfd = _open_dir_chain(anchor, tuple(dir_parts), "FILE_WRITE_ERROR", label)
    tmp_name: str | None = None
    tmp_fd: int | None = None
    try:
        try:
            st = os.lstat(leaf, dir_fd=dfd)
        except FileNotFoundError:
            st = None
        except OSError as exc:
            raise JonesPoincareNTTError("FILE_WRITE_ERROR", f"{label} stat failed: {exc.strerror}") from exc
        if st is not None:
            if stat.S_ISLNK(st.st_mode):
                raise JonesPoincareNTTError("SYMLINK_FORBIDDEN", f"{label} must not be a symlink")
            if not stat.S_ISREG(st.st_mode):
                raise JonesPoincareNTTError("NON_REGULAR_FILE", f"{label} must be a regular file")
            if st.st_nlink > 1:
                raise JonesPoincareNTTError("HARDLINK_FORBIDDEN", f"{label} must not be a hardlink")
        tmp_name, tmp_fd = _open_unique_temp_in_dir(dfd, label)
        view = memoryview(data)
        written = 0
        while written < len(data):
            written += os.write(tmp_fd, view[written:])
        os.close(tmp_fd)
        tmp_fd = None
        os.replace(tmp_name, leaf, src_dir_fd=dfd, dst_dir_fd=dfd)
        tmp_name = None
    except OSError as exc:
        raise JonesPoincareNTTError("FILE_WRITE_ERROR", f"{label} write failed: {exc.strerror}") from exc
    finally:
        if tmp_fd is not None:
            os.close(tmp_fd)
        if tmp_name is not None:
            try:
                os.unlink(tmp_name, dir_fd=dfd)
            except OSError:
                pass
        os.close(dfd)


# ---------------------------------------------------------------------------
# Exact Cyclotomic Field Arithmetic Q(zeta_N) = Q[x] / (Phi_N(x))
# ---------------------------------------------------------------------------


def _poly_trim_q(p: list[Fraction]) -> list[Fraction]:
    out = list(p)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def _poly_add_q(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    n = max(len(a), len(b))
    out = [Fraction(0)] * n
    for i, x in enumerate(a):
        out[i] += x
    for i, y in enumerate(b):
        out[i] += y
    return _poly_trim_q(out)


def _poly_sub_q(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    return _poly_add_q(a, [-x for x in b])


def _poly_mul_q(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x != 0:
            for j, y in enumerate(b):
                if y != 0:
                    out[i + j] += x * y
    return _poly_trim_q(out)


def _poly_divmod_q(a: list[Fraction], b: list[Fraction]) -> tuple[list[Fraction], list[Fraction]]:
    a_t = _poly_trim_q(a)
    b_t = _poly_trim_q(b)
    if len(b_t) == 1 and b_t[0] == 0:
        raise JonesPoincareNTTError("POLY_ZERO_DIV", "polynomial division by zero")
    db = len(b_t) - 1
    lb = b_t[-1]
    q = [Fraction(0)] * max(1, len(a_t) - db)
    rem = list(a_t)
    while len(rem) - 1 >= db and not (len(rem) == 1 and rem[0] == 0):
        shift = len(rem) - 1 - db
        c = rem[-1] / lb
        q[shift] = c
        for i in range(db + 1):
            rem[shift + i] -= c * b_t[i]
        rem = _poly_trim_q(rem)
    return _poly_trim_q(q), _poly_trim_q(rem)


def _poly_mod_q(a: list[Fraction], m: list[Fraction]) -> list[Fraction]:
    _, r = _poly_divmod_q(a, m)
    return r


def poly_inv_mod_q(a: list[Fraction], m: list[Fraction]) -> list[Fraction]:
    """Exact modular inverse in Q[x]/(m(x)) via extended Euclidean algorithm."""
    r0 = _poly_trim_q(m)
    r1 = _poly_mod_q(a, m)
    t0 = [Fraction(0)]
    t1 = [Fraction(1)]
    while not (len(r1) == 1 and r1[0] == 0):
        q, r2 = _poly_divmod_q(r0, r1)
        t2 = _poly_sub_q(t0, _poly_mul_q(q, t1))
        r0, r1 = r1, r2
        t0, t1 = t1, t2
    if len(r0) != 1 or r0[0] == 0:
        raise JonesPoincareNTTError("POLY_NOT_INVERTIBLE", "element is not invertible modulo polynomial")
    inv_c = Fraction(1) / r0[0]
    return _poly_mod_q([x * inv_c for x in t0], m)


def cyclotomic_poly_q(n: int) -> list[Fraction]:
    """Exact n-th cyclotomic polynomial Phi_n(x) in Q[x] via exact divisor quotient."""
    n_val = require_int(n, "n", lo=1, hi=120)
    memo: dict[int, list[Fraction]] = {}

    def _phi(d: int) -> list[Fraction]:
        if d in memo:
            return memo[d]
        res = [Fraction(0)] * (d + 1)
        res[0] = Fraction(-1)
        res[d] = Fraction(1)
        for k in range(1, d):
            if d % k == 0:
                res, _rem = _poly_divmod_q(res, _phi(k))
        memo[d] = res
        return res

    return _phi(n_val)


def zeta_pow_q(exp: int, n_order: int, phi_n: list[Fraction]) -> list[Fraction]:
    e = exp % n_order
    p = [Fraction(0)] * (e + 1)
    p[e] = Fraction(1)
    return _poly_mod_q(p, phi_n)


def cyc_conj_q(elem: list[Fraction], n_order: int, phi_n: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)]
    for i, c in enumerate(elem):
        if c != 0:
            zp = zeta_pow_q(-i, n_order, phi_n)
            out = _poly_add_q(out, [c * v for v in zp])
    return _poly_mod_q(out, phi_n)


def _pad_cyc_int(elem: list[Fraction], deg: int) -> list[int]:
    out = [0] * deg
    for i, c in enumerate(elem):
        if c.denominator != 1:
            raise JonesPoincareNTTError("NON_INTEGRAL_CYCLOTOMIC", "expected algebraic integer in Z[zeta]")
        out[i] = int(c.numerator)
    return out


# ---------------------------------------------------------------------------
# Theorem 1: Exact Kauffman Bracket, Jones Polynomials, Reidemeister & CS(k)
# ---------------------------------------------------------------------------


def _laurent_add(a: dict[int, int], b: dict[int, int]) -> dict[int, int]:
    out = dict(a)
    for k, v in b.items():
        nv = out.get(k, 0) + v
        if nv == 0:
            out.pop(k, None)
        else:
            out[k] = nv
    return out


def _laurent_mul(a: dict[int, int], b: dict[int, int]) -> dict[int, int]:
    out: dict[int, int] = {}
    for k1, v1 in a.items():
        for k2, v2 in b.items():
            k = k1 + k2
            out[k] = out.get(k, 0) + v1 * v2
    return {k: v for k, v in out.items() if v != 0}


def _laurent_pow(p: dict[int, int], exp: int) -> dict[int, int]:
    out: dict[int, int] = {0: 1}
    base = dict(p)
    e = exp
    while e > 0:
        if e & 1:
            out = _laurent_mul(out, base)
        base = _laurent_mul(base, base)
        e >>= 1
    return out


def _laurent_mirror(p: dict[int, int]) -> dict[int, int]:
    return {-k: v for k, v in sorted(p.items())}


def _laurent_to_str_dict(p: dict[int, int]) -> dict[str, int]:
    return {str(k): v for k, v in sorted(p.items())}


def braid_to_pd(n_strands: int, word: list[tuple[int, int]]) -> tuple[list[tuple[int, int, int, int]], list[int]]:
    """Convert an oriented n-strand braid word [(gen_1based, +1|-1), ...] into a closed PD code + signs."""
    ns = require_int(n_strands, "n_strands", lo=2, hi=8)
    w_seq = require_seq(word, "word", min_len=1, max_len=14)
    cur = list(range(1, ns + 1))
    nxt_id = ns + 1
    raw_crossings: list[tuple[int, int, int, int, int]] = []
    for idx, step in enumerate(w_seq):
        pair = require_seq(step, f"word[{idx}]", min_len=2, max_len=2)
        gen = require_int(pair[0], f"word[{idx}].gen", lo=1, hi=ns - 1)
        sgn = require_int(pair[1], f"word[{idx}].sign", lo=-1, hi=1)
        if sgn == 0:
            raise JonesPoincareNTTError("INVALID_CROSSING_SIGN", "braid generator sign must be +1 or -1")
        i = gen - 1
        in_l, in_r = cur[i], cur[i + 1]
        out_l, out_r = nxt_id, nxt_id + 1
        nxt_id += 2
        cur[i], cur[i + 1] = out_l, out_r
        raw_crossings.append((sgn, in_l, in_r, out_l, out_r))

    remap = {cur[s]: s + 1 for s in range(ns)}
    pd: list[tuple[int, int, int, int]] = []
    signs: list[int] = []
    for sgn, in_l, in_r, out_l, out_r in raw_crossings:
        a, b, c, d = (
            (in_r, out_r, out_l, in_l) if sgn == 1 else (in_l, in_r, out_r, out_l)
        )
        pd.append((remap.get(a, a), remap.get(b, b), remap.get(c, c), remap.get(d, d)))
        signs.append(sgn)
    return pd, signs


def compute_linking_matrix(
    pd: list[tuple[int, int, int, int]],
    signs: list[int],
) -> tuple[int, list[list[int]]]:
    """Trace oriented link components from PD code and compute exact pairwise linking numbers Lk_{ij}."""
    pd_seq = require_seq(pd, "pd", min_len=1, max_len=14)
    s_seq = require_seq(signs, "signs", min_len=1, max_len=14)
    if len(pd_seq) != len(s_seq):
        raise JonesPoincareNTTError("PD_SIGN_LEN_MISMATCH", "pd and signs lengths differ")
    next_edge: dict[int, int] = {}
    all_edges: set[int] = set()
    parsed: list[tuple[tuple[int, int, int, int], int]] = []
    for idx, (cr, sgn) in enumerate(zip(pd_seq, s_seq)):
        tup = require_seq(cr, f"pd[{idx}]", min_len=4, max_len=4)
        a, b, c, d = (require_int(tup[k], f"pd[{idx}][{k}]", lo=1, hi=1000) for k in range(4))
        s_val = require_int(sgn, f"signs[{idx}]", lo=-1, hi=1)
        if s_val == 0:
            raise JonesPoincareNTTError("INVALID_CROSSING_SIGN", "crossing sign must be +1 or -1")
        all_edges.update((a, b, c, d))
        # Under-strand is always a -> c; over-strand is d -> b (+1) or b -> d (-1)
        next_edge[a] = c
        if s_val == 1:
            next_edge[d] = b
        else:
            next_edge[b] = d
        parsed.append(((a, b, c, d), s_val))

    edge_comp: dict[int, int] = {}
    comp_count = 0
    for e in sorted(all_edges):
        if e not in edge_comp:
            cur = e
            while cur not in edge_comp:
                edge_comp[cur] = comp_count
                cur = next_edge[cur]
            comp_count += 1

    twice_lk = [[0] * comp_count for _ in range(comp_count)]
    for (a, b, _c, _d), s_val in parsed:
        cu = edge_comp[a]
        co = edge_comp[b]
        if cu != co:
            twice_lk[cu][co] += s_val
            twice_lk[co][cu] += s_val

    lk_mat = [[twice_lk[i][j] // 2 for j in range(comp_count)] for i in range(comp_count)]
    return comp_count, lk_mat


def kauffman_jones_from_pd(
    pd: list[tuple[int, int, int, int]],
    signs: list[int],
    *,
    free_loops: int = 0,
) -> dict[int, int]:
    """Exact state-sum Kauffman bracket & writhe-normalized Jones polynomial V_L(t) in Z[t^{+/-1/2}].

    Keys are integer exponents of t^(1/2) (e.g. key 2 is t^1, key -4 is t^-2).
    """
    pd_seq = require_seq(pd, "pd", min_len=0, max_len=12)
    s_seq = require_seq(signs, "signs", min_len=0, max_len=12)
    fl = require_int(free_loops, "free_loops", lo=0, hi=8)
    if len(pd_seq) != len(s_seq):
        raise JonesPoincareNTTError("PD_SIGN_LEN_MISMATCH", "pd and signs lengths differ")
    m = len(pd_seq)
    if m == 0 and fl == 0:
        raise JonesPoincareNTTError("EMPTY_LINK_DIAGRAM", "diagram must have crossings or free_loops >= 1")

    parsed_pd: list[tuple[int, int, int, int]] = []
    parsed_signs: list[int] = []
    for idx, (cr, sgn) in enumerate(zip(pd_seq, s_seq)):
        tup = require_seq(cr, f"pd[{idx}]", min_len=4, max_len=4)
        parsed_pd.append(
            (
                require_int(tup[0], f"pd[{idx}][0]", lo=1, hi=1000),
                require_int(tup[1], f"pd[{idx}][1]", lo=1, hi=1000),
                require_int(tup[2], f"pd[{idx}][2]", lo=1, hi=1000),
                require_int(tup[3], f"pd[{idx}][3]", lo=1, hi=1000),
            )
        )
        s_val = require_int(sgn, f"signs[{idx}]", lo=-1, hi=1)
        if s_val == 0:
            raise JonesPoincareNTTError("INVALID_CROSSING_SIGN", "crossing sign must be +1 or -1")
        parsed_signs.append(s_val)

    d_poly: dict[int, int] = {2: -1, -2: -1}
    if m == 0:
        bracket = _laurent_pow(d_poly, fl - 1)
    else:
        bracket = {}
        for mask in range(1 << m):
            adj: dict[int, list[int]] = {}
            a_cnt = 0
            for i, (a, b, c, d) in enumerate(parsed_pd):
                if ((mask >> i) & 1) == 0:
                    a_cnt += 1
                    pairs = ((a, b), (c, d))
                else:
                    pairs = ((a, d), (b, c))
                for u, v in pairs:
                    adj.setdefault(u, []).append(v)
                    adj.setdefault(v, []).append(u)
            visited: set[int] = set()
            loops = fl
            for node in adj:
                if node not in visited:
                    loops += 1
                    stack = [node]
                    visited.add(node)
                    while stack:
                        cur = stack.pop()
                        for nxt in adj[cur]:
                            if nxt not in visited:
                                visited.add(nxt)
                                stack.append(nxt)
            exp_a = 2 * a_cnt - m
            term = _laurent_mul({exp_a: 1}, _laurent_pow(d_poly, loops - 1))
            bracket = _laurent_add(bracket, term)

    writhe = sum(parsed_signs)
    norm_sign = -1 if (writhe & 1) else 1
    jones_a = _laurent_mul({-3 * writhe: norm_sign}, bracket)
    # Substitute A = t^(-1/4): A^k = t^(-k/4) = (t^(1/2))^(-k/2)
    out: dict[int, int] = {}
    for k, v in sorted(jones_a.items()):
        if k % 2 != 0:
            raise JonesPoincareNTTError("ODD_KAUFFMAN_POWER", "Kauffman exponent not even in A")
        out[-(k // 2)] = v
    return dict(sorted(out.items()))


def torus_knot_jones_closed_form(p: int, q: int) -> dict[int, int]:
    """Exact Rosso-Jones / Jones closed form V_{T(p,q)}(t) = t^((p-1)(q-1)/2)*(1 - t^(p+1) - t^(q+1) + t^(p+q))/(1 - t^2)."""
    pv = require_int(p, "p", lo=2, hi=25)
    qv = require_int(q, "q", lo=2, hi=25)
    if math.gcd(pv, qv) != 1:
        raise JonesPoincareNTTError("NON_COPRIME_TORUS", "p and q must be coprime for a torus knot")
    # Exact polynomial division of (1 - t^(p+1) - t^(q+1) + t^(p+q)) by (1 - t^2)
    deg = pv + qv
    num = [0] * (deg + 1)
    num[0] += 1
    num[pv + 1] -= 1
    num[qv + 1] -= 1
    num[pv + qv] += 1
    quot = [0] * (deg - 1)
    for k in range(deg, 1, -1):
        c = num[k]
        if c != 0:
            quot[k - 2] = -c
            num[k] -= c
            num[k - 2] += c
    if any((num[0], num[1])):
        raise JonesPoincareNTTError("TORUS_DIVISION_REMAINDER", "torus numerator not divisible by (1 - t^2)")
    shift = ((pv - 1) * (qv - 1)) // 2
    # Express in t^(1/2) exponents (multiply t-power by 2)
    out: dict[int, int] = {}
    for idx, coeff in enumerate(quot):
        if coeff != 0:
            out[2 * (idx + shift)] = coeff
    return dict(sorted(out.items()))


def eval_jones_at_cs_level(jones_half_t: dict[int, int], level_k: int) -> dict[str, Any]:
    """Evaluate V_L(t) at t^(1/2) = zeta_{2(k+2)} in exact Z[x]/(Phi_{2(k+2)}(x)) + exact |V_L|^2."""
    k = require_int(level_k, "level_k", lo=1, hi=4)
    m = 2 * (k + 2)
    phi = cyclotomic_poly_q(m)
    deg = len(phi) - 1
    acc = [Fraction(0)]
    for exp_half, coeff in jones_half_t.items():
        zp = zeta_pow_q(exp_half, m, phi)
        acc = _poly_add_q(acc, [Fraction(coeff) * v for v in zp])
    val = _poly_mod_q(acc, phi)
    conj = cyc_conj_q(val, m, phi)
    norm_sq = _poly_mod_q(_poly_mul_q(val, conj), phi)
    return {
        "level_k": k,
        "cyclotomic_order": m,
        "phi_degree": deg,
        "value_coeffs_z": _pad_cyc_int(val, deg),
        "norm_sq_coeffs_z": _pad_cyc_int(norm_sq, deg),
    }


def certify_theorem1_jones_and_cs() -> dict[str, Any]:
    """Certify Pillar 1: PD Kauffman bracket, Reidemeister I/II/III, Rosso-Jones, Borromean obstruction, CS levels."""
    # 1. Exact PD codes for canonical knots & links
    v_unknot = kauffman_jones_from_pd([], [], free_loops=1)
    v_2unlink = kauffman_jones_from_pd([], [], free_loops=2)
    v_3unlink = kauffman_jones_from_pd([], [], free_loops=3)
    hopf_pd, hopf_s = braid_to_pd(2, [(1, 1), (1, 1)])
    v_hopf = kauffman_jones_from_pd(hopf_pd, hopf_s)
    _hopf_c, hopf_lk = compute_linking_matrix(hopf_pd, hopf_s)

    tref_r_pd, tref_r_s = [(1, 5, 2, 4), (3, 1, 4, 6), (5, 3, 6, 2)], [1, 1, 1]
    tref_l_pd, tref_l_s = [(1, 4, 2, 5), (3, 6, 4, 1), (5, 2, 6, 3)], [-1, -1, -1]
    v_tref_r = kauffman_jones_from_pd(tref_r_pd, tref_r_s)
    v_tref_l = kauffman_jones_from_pd(tref_l_pd, tref_l_s)

    t25_pd, t25_s = braid_to_pd(2, [(1, 1)] * 5)
    v_t25 = kauffman_jones_from_pd(t25_pd, t25_s)

    t34_pd, t34_s = braid_to_pd(3, [(1, 1), (2, 1)] * 4)
    v_t34 = kauffman_jones_from_pd(t34_pd, t34_s)

    fig8_pd, fig8_s = [(4, 2, 5, 1), (8, 6, 1, 5), (6, 3, 7, 4), (2, 7, 3, 8)], [-1, -1, 1, 1]
    v_fig8 = kauffman_jones_from_pd(fig8_pd, fig8_s)

    # Borromean rings L6a4 as exact 3-strand braid closure (sigma_1 * sigma_2^-1)^3
    borr_pd, borr_s = braid_to_pd(3, [(1, 1), (2, -1)] * 3)
    v_borr = kauffman_jones_from_pd(borr_pd, borr_s)
    borr_comps, borr_lk = compute_linking_matrix(borr_pd, borr_s)

    # 2. Explicit Reidemeister I, II, III invariance witnesses
    # R1: unknot with positive kink (braid sigma_1 on 2 strands) and negative kink (sigma_1^-1)
    r1_pos_pd, r1_pos_s = braid_to_pd(2, [(1, 1)])
    r1_neg_pd, r1_neg_s = braid_to_pd(2, [(1, -1)])
    r1_ok = all(
        (
            kauffman_jones_from_pd(r1_pos_pd, r1_pos_s) == v_unknot,
            kauffman_jones_from_pd(r1_neg_pd, r1_neg_s) == v_unknot,
        )
    )
    # R2: canceling pair sigma_1 * sigma_1^-1 on 2 strands (2-unlink) and on trefoil sigma_1^4 * sigma_1^-1
    r2_unlink_pd, r2_unlink_s = braid_to_pd(2, [(1, 1), (1, -1)])
    r2_tref_pd, r2_tref_s = braid_to_pd(2, [(1, 1), (1, 1), (1, 1), (1, 1), (1, -1)])
    r2_ok = all(
        (
            kauffman_jones_from_pd(r2_unlink_pd, r2_unlink_s) == v_2unlink,
            kauffman_jones_from_pd(r2_tref_pd, r2_tref_s) == v_tref_r,
        )
    )
    # R3: braid relation (s1 s2 s1) vs (s2 s1 s2) appended to (s1 s2) on 3 strands (both give T(2,3) + R1 = trefoil!)
    r3_lhs_pd, r3_lhs_s = braid_to_pd(3, [(1, 1), (2, 1), (1, 1), (1, 1), (2, 1)])
    r3_rhs_pd, r3_rhs_s = braid_to_pd(3, [(2, 1), (1, 1), (2, 1), (1, 1), (2, 1)])
    r3_ok = kauffman_jones_from_pd(r3_lhs_pd, r3_lhs_s) == kauffman_jones_from_pd(r3_rhs_pd, r3_rhs_s)

    # 3. Rosso-Jones closed-form cross-checks for torus knots T(2,3), T(2,5), T(3,4)
    rj_t23_ok = v_tref_r == torus_knot_jones_closed_form(2, 3)
    rj_t25_ok = v_t25 == torus_knot_jones_closed_form(2, 5)
    rj_t34_ok = v_t34 == torus_knot_jones_closed_form(3, 4)

    # 4. Chirality, amphichirality, and Borromean Abelian-vs-non-Abelian separation
    trefoil_chiral_ok = all((v_tref_l == _laurent_mirror(v_tref_r), v_tref_r != v_tref_l))
    fig8_amphichiral_ok = v_fig8 == _laurent_mirror(v_fig8)
    borr_zero_lk = all((borr_comps == 3, borr_lk == [[0, 0, 0], [0, 0, 0], [0, 0, 0]]))
    borr_non_abelian_sep = all((borr_zero_lk, v_borr != v_3unlink))

    # 5. Exact Chern-Simons level k=1..4 evaluations in Z[x]/(Phi_{2(k+2)}(x))
    knot_table = {
        "unknot": v_unknot,
        "2_unlink": v_2unlink,
        "3_unlink": v_3unlink,
        "hopf_pos": v_hopf,
        "trefoil_right_T23": v_tref_r,
        "trefoil_left_mirror": v_tref_l,
        "cinquefoil_T25": v_t25,
        "torus_T34_8_19": v_t34,
        "figure_eight_4_1": v_fig8,
        "borromean_L6a4": v_borr,
    }
    cs_evals: dict[str, dict[str, Any]] = {}
    for kname in ("unknot", "trefoil_right_T23", "figure_eight_4_1", "cinquefoil_T25", "torus_T34_8_19", "borromean_L6a4"):
        cs_evals[kname] = {
            f"k{lvl}": eval_jones_at_cs_level(knot_table[kname], lvl)
            for lvl in _CS_LEVELS
        }

    # Exact verification of k=1 Abelian collapse on knots (|V_K(e^{2pi i/3})|^2 == 1 for all knots!)
    k1_abelian_unit = all(
        cs_evals[kname]["k1"]["norm_sq_coeffs_z"] == [1, 0]
        for kname in ("unknot", "trefoil_right_T23", "figure_eight_4_1", "cinquefoil_T25", "torus_T34_8_19")
    )
    # Exact verification of k=1 Abelian Borromean collapse vs k in {2, 3, 4} non-Abelian separation
    unlink3_cs = {lvl: eval_jones_at_cs_level(v_3unlink, lvl) for lvl in _CS_LEVELS}
    borr_k1_collapse = cs_evals["borromean_L6a4"]["k1"]["value_coeffs_z"] == unlink3_cs[1]["value_coeffs_z"]
    borr_cs_sep_k234 = all(
        cs_evals["borromean_L6a4"][f"k{lvl}"]["value_coeffs_z"] != unlink3_cs[lvl]["value_coeffs_z"]
        for lvl in (2, 3, 4)
    )

    all_passed = all(
        (
            v_unknot == {0: 1},
            v_2unlink == {-1: -1, 1: -1},
            v_3unlink == {-2: 1, 0: 2, 2: 1},
            v_hopf == {1: -1, 5: -1},
            hopf_lk == [[0, 1], [1, 0]],
            v_tref_r == {2: 1, 6: 1, 8: -1},
            v_tref_l == {-8: -1, -6: 1, -2: 1},
            v_t25 == {4: 1, 8: 1, 10: -1, 12: 1, 14: -1},
            v_t34 == {6: 1, 10: 1, 16: -1},
            v_fig8 == {-4: 1, -2: -1, 0: 1, 2: -1, 4: 1},
            v_borr == {-6: -1, -4: 3, -2: -2, 0: 4, 2: -2, 4: 3, 6: -1},
            r1_ok,
            r2_ok,
            r3_ok,
            rj_t23_ok,
            rj_t25_ok,
            rj_t34_ok,
            trefoil_chiral_ok,
            fig8_amphichiral_ok,
            borr_non_abelian_sep,
            k1_abelian_unit,
            borr_k1_collapse,
            borr_cs_sep_k234,
        )
    )
    return {
        "jones_polynomials_half_t": {k: _laurent_to_str_dict(v) for k, v in knot_table.items()},
        "reidemeister_checks": {"R1": r1_ok, "R2": r2_ok, "R3": r3_ok},
        "rosso_jones_torus_matches": {"T23": rj_t23_ok, "T25": rj_t25_ok, "T34": rj_t34_ok},
        "symmetry_and_obstruction_checks": {
            "trefoil_chiral_proven": trefoil_chiral_ok,
            "figure_eight_amphichiral_proven": fig8_amphichiral_ok,
            "hopf_linking_matrix": hopf_lk,
            "borromean_components": borr_comps,
            "borromean_linking_matrix": borr_lk,
            "borromean_zero_abelian_helicity_nonzero_jones": borr_non_abelian_sep,
            "cs_k1_abelian_unit_norm_knots": k1_abelian_unit,
        },
        "cs_level_evaluations": cs_evals,
        "all_passed": all_passed,
    }


# ---------------------------------------------------------------------------
# Theorem 2: Exact SU(2)_k Kac-Peterson Modularity + Cayley Poincare Disk
# ---------------------------------------------------------------------------


def certify_su2_k_modular(level_k: int) -> dict[str, Any]:
    """Certify exact SU(2)_k Kac-Peterson S, T, S^2=I, S^dag S=I, (ST)^3=I, and Verlinde fusion in Q(zeta_N)."""
    k = require_int(level_k, "level_k", lo=1, hi=4)
    r = k + 2
    n_ord = _SU2_CYCLOTOMIC_N[k]
    phi = cyclotomic_poly_q(n_ord)
    i_el = zeta_pow_q(n_ord // 4, n_ord, phi)
    sq2 = _poly_add_q(zeta_pow_q(n_ord // 8, n_ord, phi), zeta_pow_q(-n_ord // 8, n_ord, phi))

    if r == 3:
        sq3 = _poly_mod_q(
            _poly_mul_q([-x for x in i_el], _poly_sub_q(zeta_pow_q(n_ord // 3, n_ord, phi), zeta_pow_q(-n_ord // 3, n_ord, phi))),
            phi,
        )
        pref = _poly_mod_q(_poly_mul_q(sq2, poly_inv_mod_q(sq3, phi)), phi)
    elif r == 4:
        pref = [x * Fraction(1, 2) for x in sq2]
    elif r == 5:
        s5 = _poly_sub_q(
            _poly_add_q(zeta_pow_q(n_ord // 5, n_ord, phi), zeta_pow_q(4 * n_ord // 5, n_ord, phi)),
            _poly_add_q(zeta_pow_q(2 * n_ord // 5, n_ord, phi), zeta_pow_q(3 * n_ord // 5, n_ord, phi)),
        )
        pref = _poly_mod_q(_poly_mul_q(sq2, poly_inv_mod_q(s5, phi)), phi)
    else:
        sq3 = _poly_mod_q(
            _poly_mul_q([-x for x in i_el], _poly_sub_q(zeta_pow_q(n_ord // 3, n_ord, phi), zeta_pow_q(-n_ord // 3, n_ord, phi))),
            phi,
        )
        pref = poly_inv_mod_q(sq3, phi)

    pref_sq_ok = _poly_mod_q(_poly_mul_q(pref, pref), phi) == [Fraction(2, r)]
    inv_2i = poly_inv_mod_q([Fraction(2) * x for x in i_el], phi)
    dim = k + 1
    step = n_ord // (2 * r)

    s_mat: list[list[list[Fraction]]] = []
    s_real_sym = True
    for a in range(dim):
        row: list[list[Fraction]] = []
        for b in range(dim):
            m = (a + 1) * (b + 1)
            sin_ab = _poly_mod_q(
                _poly_mul_q(_poly_sub_q(zeta_pow_q(m * step, n_ord, phi), zeta_pow_q(-m * step, n_ord, phi)), inv_2i),
                phi,
            )
            entry = _poly_mod_q(_poly_mul_q(pref, sin_ab), phi)
            if cyc_conj_q(entry, n_ord, phi) != entry:
                s_real_sym = False
            row.append(entry)
        s_mat.append(row)

    for a in range(dim):
        for b in range(dim):
            if s_mat[a][b] != s_mat[b][a]:
                s_real_sym = False

    t_mat: list[list[list[Fraction]]] = [[[Fraction(0)] for _ in range(dim)] for _ in range(dim)]
    conformal_weights: list[str] = []
    for a in range(dim):
        h_a = Fraction(a * (a + 2), 4 * r)
        conformal_weights.append(fmt_q(h_a))
        q_exp = h_a - Fraction(k, 8 * r)
        n_exp = int(q_exp * n_ord)
        t_mat[a][a] = zeta_pow_q(n_exp, n_ord, phi)

    def _mat_mul_cyc(m1: list[list[list[Fraction]]], m2: list[list[list[Fraction]]]) -> list[list[list[Fraction]]]:
        out: list[list[list[Fraction]]] = [[[Fraction(0)] for _ in range(dim)] for _ in range(dim)]
        for i in range(dim):
            for j in range(dim):
                acc = [Fraction(0)]
                for l in range(dim):
                    acc = _poly_add_q(acc, _poly_mod_q(_poly_mul_q(m1[i][l], m2[l][j]), phi))
                out[i][j] = _poly_mod_q(acc, phi)
        return out

    eye = [[[Fraction(1 if i == j else 0)] for j in range(dim)] for i in range(dim)]
    s_dag = [[cyc_conj_q(s_mat[j][i], n_ord, phi) for j in range(dim)] for i in range(dim)]
    s2_ok = _mat_mul_cyc(s_mat, s_mat) == eye
    unitary_ok = _mat_mul_cyc(s_dag, s_mat) == eye
    st = _mat_mul_cyc(s_mat, t_mat)
    st3_ok = _mat_mul_cyc(_mat_mul_cyc(st, st), st) == eye

    inv_s0 = [poly_inv_mod_q(s_mat[0][d], phi) for d in range(dim)]
    verlinde_ok = True
    nonzero_fusions = 0
    for a in range(dim):
        for b in range(dim):
            for c in range(dim):
                acc = [Fraction(0)]
                for d in range(dim):
                    term = _poly_mod_q(_poly_mul_q(s_mat[a][d], s_mat[b][d]), phi)
                    term = _poly_mod_q(_poly_mul_q(term, cyc_conj_q(s_mat[c][d], n_ord, phi)), phi)
                    term = _poly_mod_q(_poly_mul_q(term, inv_s0[d]), phi)
                    acc = _poly_add_q(acc, term)
                acc = _poly_mod_q(acc, phi)
                expected = 1 if (abs(a - b) <= c <= min(a + b, 2 * k - a - b) and (a + b + c) % 2 == 0) else 0
                if acc != [Fraction(expected)]:
                    verlinde_ok = False
                nonzero_fusions += expected

    return {
        "level_k": k,
        "central_charge_q": fmt_q(Fraction(3 * k, r)),
        "cyclotomic_order": n_ord,
        "cyclotomic_degree": len(phi) - 1,
        "conformal_weights_q": conformal_weights,
        "prefactor_sq_exact": pref_sq_ok,
        "s_real_symmetric": s_real_sym,
        "s_sq_equals_I": s2_ok,
        "s_unitary": unitary_ok,
        "st_cubed_equals_I": st3_ok,
        "verlinde_triples_checked": dim * dim * dim,
        "verlinde_nonzero_fusions": nonzero_fusions,
        "verlinde_matches_clebsch_gordan": verlinde_ok,
        "all_passed": all((pref_sq_ok, s_real_sym, s2_ok, unitary_ok, st3_ok, verlinde_ok)),
    }


# Exact Q[i] Gaussian-rational arithmetic (re, im)
Qi = tuple[Fraction, Fraction]


def _qi_add(a: Qi, b: Qi) -> Qi:
    return (a[0] + b[0], a[1] + b[1])


def _qi_sub(a: Qi, b: Qi) -> Qi:
    return (a[0] - b[0], a[1] - b[1])


def _qi_mul(a: Qi, b: Qi) -> Qi:
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def _qi_conj(a: Qi) -> Qi:
    return (a[0], -a[1])


def _qi_norm2(a: Qi) -> Fraction:
    return a[0] * a[0] + a[1] * a[1]


def _qi_div(a: Qi, b: Qi) -> Qi:
    n2 = _qi_norm2(b)
    if n2 == 0:
        raise JonesPoincareNTTError("QI_ZERO_DIV", "division by zero in Q[i]")
    num = _qi_mul(a, _qi_conj(b))
    return (num[0] / n2, num[1] / n2)


def _qi_mobius(mat: tuple[tuple[Qi, Qi], tuple[Qi, Qi]], z: Qi) -> Qi:
    num = _qi_add(_qi_mul(mat[0][0], z), mat[0][1])
    den = _qi_add(_qi_mul(mat[1][0], z), mat[1][1])
    return _qi_div(num, den)


def _qi_mat2_mul(
    m1: tuple[tuple[Qi, Qi], tuple[Qi, Qi]],
    m2: tuple[tuple[Qi, Qi], tuple[Qi, Qi]],
) -> tuple[tuple[Qi, Qi], tuple[Qi, Qi]]:
    return (
        (
            _qi_add(_qi_mul(m1[0][0], m2[0][0]), _qi_mul(m1[0][1], m2[1][0])),
            _qi_add(_qi_mul(m1[0][0], m2[0][1]), _qi_mul(m1[0][1], m2[1][1])),
        ),
        (
            _qi_add(_qi_mul(m1[1][0], m2[0][0]), _qi_mul(m1[1][1], m2[1][0])),
            _qi_add(_qi_mul(m1[1][0], m2[0][1]), _qi_mul(m1[1][1], m2[1][1])),
        ),
    )


def _qi_mat2_su11_check(m: tuple[tuple[Qi, Qi], tuple[Qi, Qi]]) -> bool:
    """Verify M^dag J M == J with J = diag(1, -1) and det(M) == 1 in Q[i]."""
    z0: Qi = (Fraction(0), Fraction(0))
    one: Qi = (Fraction(1), Fraction(0))
    neg1: Qi = (Fraction(-1), Fraction(0))
    j_mat = ((one, z0), (z0, neg1))
    m_dag = ((_qi_conj(m[0][0]), _qi_conj(m[1][0])), (_qi_conj(m[0][1]), _qi_conj(m[1][1])))
    prod = _qi_mat2_mul(_qi_mat2_mul(m_dag, j_mat), m)
    det = _qi_sub(_qi_mul(m[0][0], m[1][1]), _qi_mul(m[0][1], m[1][0]))
    return all((prod == j_mat, det == one))


def certify_cayley_poincare_disk() -> dict[str, Any]:
    """Certify exact Cayley isomorphism H -> D over Q[i] and elliptic fixed points in Q(zeta_12)."""
    z0: Qi = (Fraction(0), Fraction(0))
    one: Qi = (Fraction(1), Fraction(0))
    neg1: Qi = (Fraction(-1), Fraction(0))
    im: Qi = (Fraction(0), Fraction(1))
    neg_im: Qi = (Fraction(0), Fraction(-1))
    half: Qi = (Fraction(1, 2), Fraction(0))
    half_i: Qi = (Fraction(0), Fraction(1, 2))
    neg_half_i: Qi = (Fraction(0), Fraction(-1, 2))

    c_mat = ((one, neg_im), (one, im))
    c_inv = ((half, half), (half_i, neg_half_i))
    s_sl2 = ((z0, neg1), (one, z0))
    t_sl2 = ((one, one), (z0, one))

    # Exact Cayley conjugates: S_D = C S C^-1, T_D = C T C^-1
    s_d = _qi_mat2_mul(_qi_mat2_mul(c_mat, s_sl2), c_inv)
    t_d = _qi_mat2_mul(_qi_mat2_mul(c_mat, t_sl2), c_inv)

    expected_s_d = ((neg_im, z0), (z0, im))
    expected_t_d = (((Fraction(1), Fraction(1, 2)), neg_half_i), (half_i, (Fraction(1), Fraction(-1, 2))))
    conjugation_exact = all((s_d == expected_s_d, t_d == expected_t_d))
    su11_exact = all((_qi_mat2_su11_check(s_d), _qi_mat2_su11_check(t_d)))

    neg_eye = ((neg1, z0), (z0, neg1))
    st_d = _qi_mat2_mul(s_d, t_d)
    modular_rel_d = all(
        (
            _qi_mat2_mul(s_d, s_d) == neg_eye,
            _qi_mat2_mul(_qi_mat2_mul(st_d, st_d), st_d) == neg_eye,
        )
    )

    # Verify exact Cayley bijection, disk interior 1 - |w|^2 > 0, and pseudo-hyperbolic distance^2 invariance
    sample_taus: list[Qi] = [
        (Fraction(0), Fraction(1)),
        (Fraction(1, 2), Fraction(3, 2)),
        (Fraction(-2, 3), Fraction(5, 4)),
        (Fraction(3, 5), Fraction(2, 7)),
    ]
    sample_ws = [_qi_mobius(c_mat, tau) for tau in sample_taus]
    bijection_ok = all(_qi_mobius(c_inv, w) == tau for tau, w in zip(sample_taus, sample_ws))
    interior_ok = all(_qi_norm2(w) < 1 for w in sample_ws)

    def _pseudo_hyp_dist2(w1: Qi, w2: Qi) -> Fraction:
        num = _qi_norm2(_qi_sub(w1, w2))
        den = _qi_norm2(_qi_sub(one, _qi_mul(_qi_conj(w1), w2)))
        return num / den

    metric_inv_ok = True
    for g_mat in (s_d, t_d, st_d):
        mapped = [_qi_mobius(g_mat, w) for w in sample_ws]
        for w in mapped:
            if _qi_norm2(w) >= 1:
                metric_inv_ok = False
        for a_i in range(len(sample_ws)):
            for b_i in range(a_i + 1, len(sample_ws)):
                if _pseudo_hyp_dist2(sample_ws[a_i], sample_ws[b_i]) != _pseudo_hyp_dist2(mapped[a_i], mapped[b_i]):
                    metric_inv_ok = False

    # Elliptic fixed point 1: tau = i -> w = 0, fixed by S_D
    tau_i_w = _qi_mobius(c_mat, im)
    elliptic_i_ok = all((tau_i_w == z0, _qi_mobius(s_d, tau_i_w) == z0))

    # Elliptic fixed point 2: tau = e^(i*pi/3) = (1 + i*sqrt(3))/2 in Q(zeta_12)
    phi12 = cyclotomic_poly_q(12)
    i12 = zeta_pow_q(3, 12, phi12)
    tau_rho = zeta_pow_q(2, 12, phi12)  # zeta_12^2 = e^(i*pi/3)
    w_rho = _poly_mod_q(
        _poly_mul_q(_poly_sub_q(tau_rho, i12), poly_inv_mod_q(_poly_add_q(tau_rho, i12), phi12)),
        phi12,
    )
    # Exact expected value: -i * (2 - sqrt(3)), where sqrt(3) = -i*(zeta_3 - zeta_3^-1) = zeta_12 + zeta_12^-1
    sq3_12 = _poly_add_q(zeta_pow_q(1, 12, phi12), zeta_pow_q(-1, 12, phi12))
    two_minus_sq3 = _poly_sub_q([Fraction(2)], sq3_12)
    expected_w_rho = _poly_mod_q(_poly_mul_q([-x for x in i12], two_minus_sq3), phi12)
    # Verify |w_rho|^2 = 7 - 4*sqrt(3) and (T_D * S_D)(w_rho) == w_rho in Q(zeta_12)!
    w_rho_norm2 = _poly_mod_q(_poly_mul_q(w_rho, cyc_conj_q(w_rho, 12, phi12)), phi12)
    expected_norm2 = _poly_sub_q([Fraction(7)], [Fraction(4) * x for x in sq3_12])
    # Apply S_D (w -> -w), then T_D (u -> ((1 + i/2)u - i/2) / ((i/2)u + (1 - i/2)))
    u_neg = [-x for x in w_rho]
    half_i12 = [Fraction(1, 2) * x for x in i12]
    t_num = _poly_sub_q(_poly_mul_q(_poly_add_q([Fraction(1)], half_i12), u_neg), half_i12)
    t_den = _poly_add_q(_poly_mul_q(half_i12, u_neg), _poly_sub_q([Fraction(1)], half_i12))
    ts_w_rho = _poly_mod_q(_poly_mul_q(t_num, poly_inv_mod_q(t_den, phi12)), phi12)
    elliptic_rho_ok = all(
        (
            _poly_mod_q(_poly_mul_q(sq3_12, sq3_12), phi12) == [Fraction(3)],
            w_rho == expected_w_rho,
            w_rho_norm2 == expected_norm2,
            ts_w_rho == w_rho,
        )
    )

    return {
        "cayley_S_D_equals_neg_w": conjugation_exact,
        "cayley_T_D_formula": "((1 + i/2)*w - i/2) / ((i/2)*w + (1 - i/2))",
        "su11_metric_preserved": su11_exact,
        "modular_relations_on_disk": modular_rel_d,
        "bijection_and_interior_preserved": all((bijection_ok, interior_ok)),
        "pseudo_hyperbolic_distance_sq_invariant": metric_inv_ok,
        "elliptic_i_maps_to_origin": elliptic_i_ok,
        "elliptic_rho_maps_to_neg_i_2_minus_sqrt3": elliptic_rho_ok,
        "elliptic_rho_w_coeffs_q_zeta12": [fmt_q(c) for c in w_rho],
        "all_passed": all(
            (
                conjugation_exact,
                su11_exact,
                modular_rel_d,
                bijection_ok,
                interior_ok,
                metric_inv_ok,
                elliptic_i_ok,
                elliptic_rho_ok,
            )
        ),
    }


def certify_theorem2_modular_and_poincare() -> dict[str, Any]:
    """Certify Pillar 2: SU(2)_k (k=1..4) exact modular representation & Cayley Poincare-disk isomorphism."""
    su2_levels = {f"k{k}": certify_su2_k_modular(k) for k in _CS_LEVELS}
    cayley = certify_cayley_poincare_disk()
    all_passed = all((all(v["all_passed"] for v in su2_levels.values()), cayley["all_passed"]))
    return {
        "su2_k_modular": su2_levels,
        "cayley_poincare_disk": cayley,
        "all_passed": all_passed,
    }


# ---------------------------------------------------------------------------
# Theorem 3: Divisor-sigma_k Hecke Multiplicativity & Exact NTT + CRT FFT
# ---------------------------------------------------------------------------


def divisor_sigma(k: int, n: int) -> int:
    """Exact integer divisor power sum sigma_k(n) = sum_{d|n} d^k."""
    kv = require_int(k, "k", lo=0, hi=12)
    nv = require_int(n, "n", lo=1, hi=4096)
    total = 0
    limit = math.isqrt(nv)
    for d in range(1, limit + 1):
        if nv % d == 0:
            total += d**kv
            other = nv // d
            if other != d:
                total += other**kv
    return total


def ntt_transform(vec: list[int], mod: int, prim_root: int, *, invert: bool = False) -> list[int]:
    """Exact iterative radix-2 Cooley-Tukey Number-Theoretic Transform over Z/mod Z (zero floats)."""
    vals = require_seq(vec, "vec", min_len=2, max_len=MAX_SEQ_LEN)
    n = len(vals)
    if (n & (n - 1)) != 0:
        raise JonesPoincareNTTError("INVALID_NTT_LEN", "NTT length must be a power of two >= 2")
    p = require_int(mod, "mod", lo=3, hi=(1 << 62))
    g = require_int(prim_root, "prim_root", lo=2, hi=p - 1)
    inv_flag = require_bool(invert, "invert")
    if (p - 1) % n != 0:
        raise JonesPoincareNTTError("NTT_MOD_NOT_FRIENDLY", "mod - 1 must be divisible by NTT length")

    a = [require_int(x, "vec_item") % p for x in vals]
    # Bit-reversal permutation
    j = 0
    for i in range(1, n):
        bit = n >> 1
        while j & bit:
            j ^= bit
            bit >>= 1
        j ^= bit
        if i < j:
            a[i], a[j] = a[j], a[i]

    step = 2
    while step <= n:
        half = step >> 1
        wlen = pow(g, (p - 1) // step, p)
        if inv_flag:
            wlen = pow(wlen, p - 2, p)
        for base in range(0, n, step):
            w = 1
            for off in range(half):
                u = a[base + off]
                v = (a[base + off + half] * w) % p
                a[base + off] = (u + v) % p
                a[base + off + half] = (u - v) % p
                w = (w * wlen) % p
        step <<= 1

    if inv_flag:
        inv_n = pow(n, p - 2, p)
        a = [(x * inv_n) % p for x in a]
    return a


def ntt_convolve_mod(a: list[int], b: list[int], mod: int, prim_root: int) -> list[int]:
    """Exact linear polynomial convolution modulo an NTT-friendly prime."""
    sa = require_seq(a, "a", min_len=1, max_len=2048)
    sb = require_seq(b, "b", min_len=1, max_len=2048)
    out_len = len(sa) + len(sb) - 1
    size = 2
    while size < out_len:
        size <<= 1
    fa = [require_int(x, "a_i") for x in sa] + [0] * (size - len(sa))
    fb = [require_int(x, "b_i") for x in sb] + [0] * (size - len(sb))
    ta = ntt_transform(fa, mod, prim_root, invert=False)
    tb = ntt_transform(fb, mod, prim_root, invert=False)
    prod = [(ta[i] * tb[i]) % mod for i in range(size)]
    inv = ntt_transform(prod, mod, prim_root, invert=True)
    return inv[:out_len]


def ntt_convolve_crt(
    a: list[int],
    b: list[int],
    *,
    primes: tuple[int, ...] = (NTT_PRIME_1, NTT_PRIME_2),
) -> list[int]:
    """Exact signed integer convolution via multi-prime NTT + Garner/CRT reconstruction (zero floats)."""
    sa = [require_int(x, "a_i") for x in require_seq(a, "a", min_len=1, max_len=2048)]
    sb = [require_int(x, "b_i") for x in require_seq(b, "b", min_len=1, max_len=2048)]
    p_seq = require_seq(primes, "primes", min_len=2, max_len=3)
    p_list: list[int] = []
    for p_val in p_seq:
        pi = require_int(p_val, "prime", lo=3)
        if pi not in NTT_PRIMITIVE_ROOTS:
            raise JonesPoincareNTTError("UNSUPPORTED_NTT_PRIME", "prime not in certified NTT prime table")
        if pi in p_list:
            raise JonesPoincareNTTError("DUPLICATE_NTT_PRIME", "CRT primes must be distinct")
        p_list.append(pi)

    modulus_prod = 1
    for pi in p_list:
        modulus_prod *= pi
    half_m = modulus_prod // 2
    # Worst-case L1*Linf bound guarantees exact signed reconstruction in [-half_m, half_m]
    max_bound = sum(abs(x) for x in sa) * max(abs(y) for y in sb)
    if max_bound > half_m:
        raise JonesPoincareNTTError("CRT_DYNAMIC_RANGE_EXCEEDED", "convolution bound exceeds CRT modulus/2")

    residues = [ntt_convolve_mod(sa, sb, pi, NTT_PRIMITIVE_ROOTS[pi]) for pi in p_list]
    out_len = len(sa) + len(sb) - 1
    out: list[int] = []
    for idx in range(out_len):
        cur_val = residues[0][idx]
        cur_mod = p_list[0]
        for k_i in range(1, len(p_list)):
            pk = p_list[k_i]
            rk = residues[k_i][idx]
            inv_m = pow(cur_mod, pk - 2, pk)
            t = ((rk - cur_val) % pk * inv_m) % pk
            cur_val += t * cur_mod
            cur_mod *= pk
        if cur_val > half_m:
            cur_val -= modulus_prod
        out.append(cur_val)
    return out


def naive_convolve_exact(a: list[int], b: list[int], limit: int) -> list[int]:
    """Independent O(N^2) exact integer convolution reference up to index `limit` inclusive."""
    out = [0] * (limit + 1)
    for i in range(min(len(a), limit + 1)):
        ai = a[i]
        if ai != 0:
            for j in range(min(len(b), limit + 1 - i)):
                out[i + j] += ai * b[j]
    return out


def certify_theorem3_hecke_and_ntt_convolutions() -> dict[str, Any]:
    """Certify Pillar 3: Hecke multiplicativity + exact NTT+CRT modular-form convolutions."""
    # 1. Exact Hecke multiplicativity for 1 <= m,n <= 40, k in {1, 3, 5}
    hecke_checks = 0
    hecke_ok = True
    for k in (1, 3, 5):
        s_cache = [0] + [divisor_sigma(k, n) for n in range(1, 1601)]
        for m in range(1, 41):
            for n in range(1, 41):
                g = math.gcd(m, n)
                rhs = 0
                for d in range(1, g + 1):
                    if g % d == 0:
                        rhs += (d**k) * s_cache[(m * n) // (d * d)]
                if s_cache[m] * s_cache[n] != rhs:
                    hecke_ok = False
                hecke_checks += 1

    # 2. (a) Ramanujan E2 <-> E4 identity up to N=128 via 2-prime NTT + CRT
    lim128 = 128
    sig1 = [0] + [divisor_sigma(1, n) for n in range(1, lim128 + 1)]
    sig3 = [0] + [divisor_sigma(3, n) for n in range(1, lim128 + 1)]
    sig7 = [0] + [divisor_sigma(7, n) for n in range(1, lim128 + 1)]

    conv_s1_ntt = ntt_convolve_crt(sig1, sig1, primes=(NTT_PRIME_1, NTT_PRIME_2))[: lim128 + 1]
    conv_s1_naive = naive_convolve_exact(sig1, sig1, lim128)
    e2_e4_ntt_eq_naive = conv_s1_ntt == conv_s1_naive
    e2_e4_identity_ok = all(
        5 * sig3[n] + (1 - 6 * n) * sig1[n] == 12 * conv_s1_ntt[n]
        for n in range(1, lim128 + 1)
    )

    # 3. (b) E4^2 = E8 up to N=128 via 2-prime signed NTT + CRT on sigma_3 * sigma_3:
    #        (1 + 240*sum sigma_3 q^n)^2 = 1 + sum (480*sigma_3(n) + 57600*(sigma_3*sigma_3)[n]) q^n = 1 + 480*sum sigma_7(n) q^n
    conv_s3_ntt = ntt_convolve_crt(sig3, sig3, primes=(NTT_PRIME_1, NTT_PRIME_2))[: lim128 + 1]
    conv_s3_naive = naive_convolve_exact(sig3, sig3, lim128)
    e4_sq_ntt_eq_naive = conv_s3_ntt == conv_s3_naive
    e4_sq_128 = [1] + [480 * sig3[n] + 57600 * conv_s3_ntt[n] for n in range(1, lim128 + 1)]
    e4_sq_eq_e8_ok = all(e4_sq_128[n] == 480 * sig7[n] for n in range(1, lim128 + 1))

    # 4. (c) Delta = (E4^3 - E6^2) / 1728 up to N=64 via 3-prime NTT + CRT & Ramanujan tau(n) multiplicativity
    lim64 = 64
    e4_64 = [1] + [240 * sig3[n] for n in range(1, lim64 + 1)]
    e4_sq_64 = e4_sq_128[: lim64 + 1]
    e6_64 = [1] + [-504 * divisor_sigma(5, n) for n in range(1, lim64 + 1)]
    e4_cu_ntt = ntt_convolve_crt(e4_sq_64, e4_64, primes=(NTT_PRIME_1, NTT_PRIME_2, NTT_PRIME_3))[: lim64 + 1]
    e4_cu_naive = naive_convolve_exact(e4_sq_64, e4_64, lim64)
    e6_sq_ntt = ntt_convolve_crt(e6_64, e6_64, primes=(NTT_PRIME_1, NTT_PRIME_2, NTT_PRIME_3))[: lim64 + 1]
    e6_sq_naive = naive_convolve_exact(e6_64, e6_64, lim64)
    delta_ntt_eq_naive = all((e4_cu_ntt == e4_cu_naive, e6_sq_ntt == e6_sq_naive))

    delta_div_ok = all((e4_cu_ntt[n] - e6_sq_ntt[n]) % 1728 == 0 for n in range(lim64 + 1))
    tau = [(e4_cu_ntt[n] - e6_sq_ntt[n]) // 1728 for n in range(lim64 + 1)]
    tau_first12_ok = tau[:13] == [0, 1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370944]

    tau_coprime_pairs = 0
    tau_mult_ok = True
    for m in range(1, lim64 + 1):
        for n in range(m, lim64 // m + 1):
            if math.gcd(m, n) == 1:
                if tau[m * n] != tau[m] * tau[n]:
                    tau_mult_ok = False
                tau_coprime_pairs += 1

    tau_hecke_prime_powers = 0
    tau_hecke_pp_ok = True
    for p in (2, 3, 5, 7):
        pr = p * p
        prev = tau[p]
        prev2 = 1
        while pr <= lim64:
            if tau[pr] != tau[p] * prev - (p**11) * prev2:
                tau_hecke_pp_ok = False
            prev2 = prev
            prev = tau[pr]
            pr *= p
            tau_hecke_prime_powers += 1

    all_passed = all(
        (
            hecke_ok,
            e2_e4_ntt_eq_naive,
            e2_e4_identity_ok,
            e4_sq_ntt_eq_naive,
            e4_sq_eq_e8_ok,
            delta_ntt_eq_naive,
            delta_div_ok,
            tau_first12_ok,
            tau_mult_ok,
            tau_hecke_pp_ok,
        )
    )
    return {
        "hecke_multiplicativity": {
            "limit": 40,
            "ks": [1, 3, 5],
            "pairs_checked": hecke_checks,
            "all_exact": hecke_ok,
        },
        "ntt_primes": [NTT_PRIME_1, NTT_PRIME_2, NTT_PRIME_3],
        "e2_e4_ramanujan_N128": {
            "n_max": lim128,
            "crt_primes_used": [NTT_PRIME_1, NTT_PRIME_2],
            "ntt_equals_naive": e2_e4_ntt_eq_naive,
            "identity_exact": e2_e4_identity_ok,
            "conv_sample_n128": conv_s1_ntt[128],
        },
        "e4_sq_equals_e8_N128": {
            "n_max": lim128,
            "crt_primes_used": [NTT_PRIME_1, NTT_PRIME_2],
            "ntt_equals_naive": e4_sq_ntt_eq_naive,
            "identity_exact": e4_sq_eq_e8_ok,
            "e8_coeff_n128": e4_sq_128[128],
        },
        "delta_ramanujan_tau_N64": {
            "n_max": lim64,
            "crt_primes_used": [NTT_PRIME_1, NTT_PRIME_2, NTT_PRIME_3],
            "ntt_equals_naive": delta_ntt_eq_naive,
            "divisible_by_1728": delta_div_ok,
            "tau_1_to_12": tau[1:13],
            "tau_64": tau[64],
            "tau_coprime_pairs_checked": tau_coprime_pairs,
            "tau_multiplicative": tau_mult_ok,
            "tau_prime_power_checks": tau_hecke_prime_powers,
            "tau_hecke_prime_power_exact": tau_hecke_pp_ok,
        },
        "all_passed": all_passed,
    }


# ---------------------------------------------------------------------------
# Self-Signed Certificate Generation & Fail-Closed Validation
# ---------------------------------------------------------------------------


def build_certificate() -> dict[str, Any]:
    """Build the canonical self-signed pure-Z/Q/Q[zeta] certificate."""
    th1 = certify_theorem1_jones_and_cs()
    th2 = certify_theorem2_modular_and_poincare()
    th3 = certify_theorem3_hecke_and_ntt_convolutions()
    all_passed = all((th1["all_passed"], th2["all_passed"], th3["all_passed"]))

    payload: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "arithmetic_mode": "pure_Z_Q_cyclotomic_ntt_crt_zero_float",
        "novelty_classification": "N0_N1_exact_unified_pure_stdlib_certification",
        "theorem1_jones_and_cs": th1,
        "theorem2_modular_and_poincare": th2,
        "theorem3_hecke_and_ntt": th3,
        "all_theorems_passed": all_passed,
    }
    payload_sha = sha256_canonical(payload)
    cert_sha = sha256_canonical(
        {
            "schema_version": SCHEMA_VERSION,
            "track_id": TRACK_ID,
            "payload_sha256": payload_sha,
        }
    )
    return {
        "schema_version": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": payload_sha,
        "certificate_sha256": cert_sha,
        "payload": payload,
    }


def validate_certificate_payload(
    cert: Any,
    *,
    full_replay: bool = True,
) -> dict[str, Any]:
    """Fail-closed Zone-B validation of a certificate (full replay by default)."""
    do_full = require_bool(full_replay, "full_replay")
    root = require_mapping(cert, "certificate")
    validate_json_value(root)
    if set(root.keys()) != {"schema_version", "track_id", "payload_sha256", "certificate_sha256", "payload"}:
        raise JonesPoincareNTTError("INVALID_CERT_KEYS", "certificate top-level keys mismatch")
    if require_str(root["schema_version"], "schema_version") != SCHEMA_VERSION:
        raise JonesPoincareNTTError("INVALID_SCHEMA_VERSION", "unexpected schema_version")
    if require_str(root["track_id"], "track_id") != TRACK_ID:
        raise JonesPoincareNTTError("INVALID_TRACK_ID", "unexpected track_id")

    payload = require_mapping(root["payload"], "payload")
    computed_payload_sha = sha256_canonical(payload)
    if not constant_time_hex64_equal(root["payload_sha256"], computed_payload_sha, "payload_sha256"):
        raise JonesPoincareNTTError("PAYLOAD_SHA_MISMATCH", "payload_sha256 does not match canonical payload")
    computed_cert_sha = sha256_canonical(
        {
            "schema_version": SCHEMA_VERSION,
            "track_id": TRACK_ID,
            "payload_sha256": computed_payload_sha,
        }
    )
    if not constant_time_hex64_equal(root["certificate_sha256"], computed_cert_sha, "certificate_sha256"):
        raise JonesPoincareNTTError("CERT_SHA_MISMATCH", "certificate_sha256 does not match envelope")

    expected_payload_keys = {
        "schema_version",
        "track_id",
        "arithmetic_mode",
        "novelty_classification",
        "theorem1_jones_and_cs",
        "theorem2_modular_and_poincare",
        "theorem3_hecke_and_ntt",
        "all_theorems_passed",
    }
    if set(payload.keys()) != expected_payload_keys:
        raise JonesPoincareNTTError("INVALID_PAYLOAD_KEYS", "payload keys mismatch")
    if require_str(payload["schema_version"], "payload.schema_version") != SCHEMA_VERSION:
        raise JonesPoincareNTTError("INVALID_PAYLOAD_SCHEMA", "payload schema_version mismatch")
    if require_str(payload["track_id"], "payload.track_id") != TRACK_ID:
        raise JonesPoincareNTTError("INVALID_PAYLOAD_TRACK", "payload track_id mismatch")
    if require_str(payload["arithmetic_mode"], "arithmetic_mode") != "pure_Z_Q_cyclotomic_ntt_crt_zero_float":
        raise JonesPoincareNTTError("INVALID_ARITHMETIC_MODE", "unexpected arithmetic_mode")
    if require_str(payload["novelty_classification"], "novelty_classification") != "N0_N1_exact_unified_pure_stdlib_certification":
        raise JonesPoincareNTTError("INVALID_NOVELTY_CLASS", "unexpected novelty_classification")

    th1 = require_mapping(payload["theorem1_jones_and_cs"], "theorem1_jones_and_cs")
    th2 = require_mapping(payload["theorem2_modular_and_poincare"], "theorem2_modular_and_poincare")
    th3 = require_mapping(payload["theorem3_hecke_and_ntt"], "theorem3_hecke_and_ntt")
    if not require_bool(th1.get("all_passed"), "theorem1.all_passed"):
        raise JonesPoincareNTTError("THEOREM_FAILED", "theorem1_jones_and_cs.all_passed is False")
    if not require_bool(th2.get("all_passed"), "theorem2.all_passed"):
        raise JonesPoincareNTTError("THEOREM_FAILED", "theorem2_modular_and_poincare.all_passed is False")
    if not require_bool(th3.get("all_passed"), "theorem3.all_passed"):
        raise JonesPoincareNTTError("THEOREM_FAILED", "theorem3_hecke_and_ntt.all_passed is False")
    if not require_bool(payload["all_theorems_passed"], "all_theorems_passed"):
        raise JonesPoincareNTTError("THEOREM_FAILED", "all_theorems_passed is False")

    if do_full:
        expected_cert = build_certificate()
        if canonical_json_bytes(expected_cert) != canonical_json_bytes(root):
            raise JonesPoincareNTTError("CANONICAL_REPLAY_MISMATCH", "certificate does not match canonical replay")

    return {
        "valid": True,
        "track_id": TRACK_ID,
        "payload_sha256": computed_payload_sha,
        "certificate_sha256": computed_cert_sha,
        "all_theorems_passed": True,
        "full_replay": do_full,
    }
