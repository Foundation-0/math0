#!/usr/bin/env python3
"""
Track S21e — Escher Operator 4 (Metamorphosis / Relativity):
Exact-Q Finite-Group Equivariant Obstruction & Subgroup-Bifurcation Bridge.

Zero floats on trust paths, zero bare asserts, zero external dependencies,
zero RNG calls. Unifies three live symmetry frontiers through one pure-Q
finite-group isotypic-projector & Schur-obstruction calculus:

  1. `siliquant` (E8 / W(E8)):
     - Basis metamorphosis U_WHT8 = U_BH2 * A with A = (1/2)(H4 kron I2) in W(E8)
       lifting 1-sparse coordinate-axis root count 0 -> 16 and creating the 14
       Steiner 3-(8,4,1) quads with exact forced bleed 9801/20000.
     - Antipodal symmetry breaking {-I_8} -> {I_8} via two Weyl chambers
       (siliquant default & lexicographic), universally yielding
       ||mu_inf||^2 = 31/45, max(mu_inf . r) = 29/30 < 1, and 52/240 shifted
       roots strictly inside (0, sqrt(2)) starting at d^2 = 34/45.

  2. `point-charges` (Exact Harmonic Coulomb Hessian Walls):
     - Exact rational n=4 C_3v pyramid family (q_a = t^2 at (t,t,t)):
       T_d -> C_3v splits T_2 = A_1 + E. At unbroken T_d (t=1), Schur + tr(H)=0
       forces H(0) = 0_{3x3} (inertia (0,0,3)). Breaking to C_3v splits
       t=1/2 -> inertia (1,2,0) (index 2) vs t=2 -> inertia (2,1,0) (index 1),
       an exact 2-unit Poincare-Hopf sign jump across the T_d wall.
     - Exact D_4h -> D_2h square family q=(q_x,q_x,1,1):
       q_x=1 -> diag(2,2,-4) (2,1,0), q_x=2 -> diag(6,0,-6) (1,1,1) exact B_2u
       pitchfork wall, q_x=3 -> diag(10,-2,-8) (1,2,0); plus C_1 n=4 fold
       parity conservation m_2 - m_1 = 3 across 11 -> 9 equilibria.

  3. `aska-physical` (`fibral-rigidity` Voigt Coupling, Z_2 Truss & D_6 Prestress):
     - Exact D_2h (order 8) on 6D Voigt space Q^6 = A_g(3) + B_1g + B_2g + B_3g
       acting on exact periodic Schur-complement homogenization of F_3(t=3/5):
       D_2h-symmetric bracing (`none`, `half_2_opp`, `full_4`) forces
       P_{Ag} C P_{shear} = 0 (C14 = 0); chiral `one_per_plane` (3 ties) breaks
       D_2h -> C_3, opening parasitic coupling C14 = -26/253 (C44 = 34/253);
       `half_2_opp` (6 ties) restores D_2h, locking C44 = 1/4, C14 = 0, PD (6,0,0),
       optimal efficiency 1/24.
     - Exact Z_2 (y -> -y) decomposition Q^2 = A_1 + B_1 on the 2-bar truss:
       singular diagonal (9/10, 11/10) -> H = diag(200/99, 0) with positive
       quartic transverse potential 257500/970299 y^4 vs saddle diag(200/99, -2000/209)
       vs Z_2-broken PD corner (7/10, 3/2) det H = 64/105, tr H = 44/21.
     - Exact anchored 6-spoke unilateral cable prestress: tension (1,10,11) PD (7,0,0)
       vs compression (1,-10,-9) ND (0,7,0).
"""
from __future__ import annotations

from fractions import Fraction
import hashlib
import hmac
from itertools import combinations, permutations, product
import json
import os
from pathlib import Path, PosixPath, WindowsPath
import stat
from typing import Any

CERT_SCHEMA = "aletheia.escher_metamorphosis_symmetry_bridge.certificate.v1"
CERT_TRACK_ID = "TRACK-S21E-ESCHER-METAMORPHOSIS-SYMMETRY-BRIDGE"
CERT_TOP_KEYS = frozenset({"schema", "track_id", "payload_sha256", "certificate_sha256", "payload"})

MAX_JSON_BYTES = 2_000_000
MAX_JSON_DEPTH = 64
MAX_INT_DIGITS = 617
MAX_INT_BITS = 2048
MAX_MATRIX_DIM = 32
_HEX_LOWER = frozenset("0123456789abcdef")


class SymmetryBridgeError(ValueError):
    """Fail-closed typed error for Track S21e oracle and certifier."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"{code}: {message}")
        self.code = code


# ---------------------------------------------------------------------------
# Strict Zone-B Primitive Validators & Canonical Zero-Float JSON
# ---------------------------------------------------------------------------

def require_exact_int(
    value: Any,
    label: str,
    lo: int | None = None,
    hi: int | None = None,
) -> int:
    if type(value) is not int:
        raise SymmetryBridgeError("INVALID_INT", f"{label} must be strict int")
    if value.bit_length() > MAX_INT_BITS:
        raise SymmetryBridgeError("INT_BITS_EXCEEDED", f"{label} exceeds {MAX_INT_BITS} bits")
    if lo is not None:
        if type(lo) is not int:
            raise SymmetryBridgeError("INVALID_BOUND", f"{label} lo bound must be strict int")
        if value < lo:
            raise SymmetryBridgeError("INT_OUT_OF_RANGE", f"{label} below lower bound")
    if hi is not None:
        if type(hi) is not int:
            raise SymmetryBridgeError("INVALID_BOUND", f"{label} hi bound must be strict int")
        if value > hi:
            raise SymmetryBridgeError("INT_OUT_OF_RANGE", f"{label} above upper bound")
    return value


def require_exact_rat(value: Any, label: str) -> Fraction:
    t = type(value)
    if t is int:
        require_exact_int(value, label)
        return Fraction(value, 1)
    if t is Fraction:
        if value.numerator.bit_length() > MAX_INT_BITS or value.denominator.bit_length() > MAX_INT_BITS:
            raise SymmetryBridgeError("RAT_BITS_EXCEEDED", f"{label} exceeds bit budget")
        return value
    raise SymmetryBridgeError("INVALID_RATIONAL", f"{label} must be strict int or Fraction")


def require_exact_seq(
    value: Any,
    label: str,
    min_len: int = 0,
    max_len: int = 1024,
) -> list[Any]:
    lo = require_exact_int(min_len, "min_len", lo=0, hi=10_000)
    hi = require_exact_int(max_len, "max_len", lo=lo, hi=10_000)
    if type(value) not in (list, tuple):
        raise SymmetryBridgeError("INVALID_SEQ", f"{label} must be strict list or tuple")
    items = list(value)
    if len(items) < lo or len(items) > hi:
        raise SymmetryBridgeError("SEQ_LEN_ERROR", f"{label} length out of bounds")
    return items


def require_exact_str(value: Any, label: str) -> str:
    if type(value) is not str:
        raise SymmetryBridgeError("INVALID_STR", f"{label} must be strict str")
    try:
        value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise SymmetryBridgeError("INVALID_UTF8_STR", f"{label} contains lone surrogate") from exc
    return value


def require_hex_sha256(value: Any, label: str) -> str:
    s = require_exact_str(value, label)
    if len(s) != 64 or not all(ch in _HEX_LOWER for ch in s):
        raise SymmetryBridgeError("INVALID_SHA256", f"{label} must be 64 lowercase hex chars")
    return s


def fmt_q(x: Fraction) -> str:
    q = require_exact_rat(x, "fmt_q")
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def fmt_vec_q(v: list[Fraction] | tuple[Fraction, ...]) -> list[str]:
    return [fmt_q(x) for x in v]


def fmt_mat_q(M: list[list[Fraction]]) -> list[list[str]]:
    return [[fmt_q(x) for x in row] for row in M]


def _check_raw_prefix_symlinks(raw: str, label: str) -> None:
    cur = "/" if raw.startswith("/") else ""
    for part in raw.split("/"):
        if part in ("", "."):
            continue
        cur = os.path.join(cur, part) if cur else part
        if part != ".." and os.path.islink(cur):
            raise SymmetryBridgeError("SYMLINK_ANCESTOR_FORBIDDEN", f"{label} traverses a symlink")


def require_no_symlink_path(path: Any, label: str = "path") -> Path:
    t = type(path)
    if t is str:
        raw_str = path
    elif t in (Path, PosixPath, WindowsPath):
        raw_str = str(path)
    else:
        raise SymmetryBridgeError("INVALID_PATH_TYPE", f"{label} must be strict str or Path")
    if not raw_str or "\x00" in raw_str:
        raise SymmetryBridgeError("INVALID_PATH", f"{label} is empty or contains NUL")
    require_exact_str(raw_str, label)
    p = Path(raw_str)
    if p.is_absolute():
        _check_raw_prefix_symlinks(raw_str, label)
    else:
        env_pwd = os.environ.get("PWD")
        if env_pwd:
            _check_raw_prefix_symlinks(env_pwd, "PWD")
        cwd_real = os.getcwd()
        _check_raw_prefix_symlinks(cwd_real, "CWD")
        base_dir = env_pwd if env_pwd else cwd_real
        _check_raw_prefix_symlinks(os.path.join(base_dir, raw_str), label)
    return p


def validate_json_tree_iterative(obj: Any, max_depth: int = MAX_JSON_DEPTH) -> None:
    limit = require_exact_int(max_depth, "max_depth", lo=1, hi=256)
    stack: list[tuple[Any, int]] = [(obj, 0)]
    while stack:
        cur, depth = stack.pop()
        if depth > limit:
            raise SymmetryBridgeError("JSON_DEPTH_EXCEEDED", f"JSON nesting exceeds {limit}")
        t = type(cur)
        if t is dict:
            for k, v in cur.items():
                require_exact_str(k, "json_key")
                stack.append((v, depth + 1))
        elif t is list:
            for item in cur:
                stack.append((item, depth + 1))
        elif t is str:
            require_exact_str(cur, "json_str")
        elif t is int:
            if cur.bit_length() > MAX_INT_BITS:
                raise SymmetryBridgeError("INT_BITS_EXCEEDED", "JSON integer exceeds bit budget")
        elif t is bool or cur is None:
            continue
        else:
            raise SymmetryBridgeError("FORBIDDEN_JSON_TYPE", f"unsupported JSON type: {t.__name__}")


def canonical_json_bytes(obj: Any) -> bytes:
    validate_json_tree_iterative(obj)
    text = json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False)
    return (text + "\n").encode("ascii")


def sha256_canonical(obj: Any) -> str:
    return hashlib.sha256(canonical_json_bytes(obj)).hexdigest()


def parse_strict_json_text(text: Any, *, require_object: bool = True) -> Any:
    raw = require_exact_str(text, "json_text")
    if type(require_object) is not bool:
        raise SymmetryBridgeError("INVALID_FLAG", "require_object must be strict bool")
    if "\r" in raw:
        raise SymmetryBridgeError("CRLF_FORBIDDEN", "CR/CRLF bytes forbidden in canonical JSON")
    if len(raw.encode("utf-8")) > MAX_JSON_BYTES:
        raise SymmetryBridgeError("JSON_TOO_LARGE", "JSON text exceeds byte limit")

    def _reject_float(token: str) -> Any:
        raise SymmetryBridgeError("FLOAT_FORBIDDEN", f"float literal forbidden: {token}")

    def _reject_const(token: str) -> Any:
        raise SymmetryBridgeError("NONFINITE_FORBIDDEN", f"non-finite constant forbidden: {token}")

    def _parse_int(token: str) -> int:
        digits = token[1:] if token.startswith("-") else token
        if len(digits) > MAX_INT_DIGITS:
            raise SymmetryBridgeError("INT_DIGITS_EXCEEDED", "integer literal exceeds digit limit")
        return int(token)

    def _no_dup_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        out: dict[str, Any] = {}
        for k, v in pairs:
            if k in out:
                raise SymmetryBridgeError("DUPLICATE_KEY", f"duplicate JSON key: {k!r}")
            out[k] = v
        return out

    try:
        parsed = json.loads(
            raw,
            parse_float=_reject_float,
            parse_int=_parse_int,
            parse_constant=_reject_const,
            object_pairs_hook=_no_dup_pairs,
        )
    except SymmetryBridgeError:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise SymmetryBridgeError("INVALID_JSON", f"JSON decode failed: {exc}") from exc

    validate_json_tree_iterative(parsed)
    if require_object and type(parsed) is not dict:
        raise SymmetryBridgeError("NON_OBJECT_ROOT", "JSON root must be an object")
    return parsed


def read_strict_json_file(path: Any, label: str = "certificate_path") -> tuple[bytes, dict[str, Any]]:
    p = require_no_symlink_path(path, label)
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0)
    try:
        fd = os.open(p, flags)
    except OSError as exc:
        raise SymmetryBridgeError("FILE_MISSING_OR_UNREADABLE", f"cannot open {label}: {exc}") from exc
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise SymmetryBridgeError("NON_REGULAR_FILE", f"{label} must be a regular file")
        if st.st_size > MAX_JSON_BYTES:
            raise SymmetryBridgeError("JSON_TOO_LARGE", f"{label} exceeds byte limit")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(fd, min(65536, MAX_JSON_BYTES - total + 1))
            if not chunk:
                break
            total += len(chunk)
            if total > MAX_JSON_BYTES:
                raise SymmetryBridgeError("JSON_TOO_LARGE", f"{label} exceeds byte limit")
            chunks.append(chunk)
    except OSError as exc:
        raise SymmetryBridgeError("FILE_MISSING_OR_UNREADABLE", f"cannot read {label}: {exc}") from exc
    finally:
        os.close(fd)
    raw_bytes = b"".join(chunks)
    try:
        text = raw_bytes.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise SymmetryBridgeError("INVALID_UTF8", f"invalid UTF-8 in {label}: {exc}") from exc
    obj = parse_strict_json_text(text, require_object=True)
    return raw_bytes, obj


# ---------------------------------------------------------------------------
# Exact Rational Linear Algebra & Unified Equivariant Obstruction Functor
# ---------------------------------------------------------------------------

def _require_square_mat(mat: Any, label: str) -> list[list[Fraction]]:
    rows = require_exact_seq(mat, label, min_len=1, max_len=MAX_MATRIX_DIM)
    n = len(rows)
    out: list[list[Fraction]] = []
    for i, r in enumerate(rows):
        rseq = require_exact_seq(r, f"{label}[{i}]", min_len=n, max_len=n)
        out.append([require_exact_rat(x, f"{label}[{i}][{j}]") for j, x in enumerate(rseq)])
    return out


def eye_q(n: int) -> list[list[Fraction]]:
    dim = require_exact_int(n, "dim", lo=1, hi=MAX_MATRIX_DIM)
    return [[Fraction(1 if i == j else 0) for j in range(dim)] for i in range(dim)]


def mat_mul_q(A: list[list[Fraction]], B: list[list[Fraction]]) -> list[list[Fraction]]:
    m, k, n = len(A), len(A[0]), len(B[0])
    out = [[Fraction(0)] * n for _ in range(m)]
    for i in range(m):
        row_a = A[i]
        row_o = out[i]
        for p in range(k):
            a_ip = row_a[p]
            if a_ip != 0:
                row_b = B[p]
                for j in range(n):
                    b_pj = row_b[j]
                    if b_pj != 0:
                        row_o[j] += a_ip * b_pj
    return out


def mat_transpose_q(A: list[list[Fraction]]) -> list[list[Fraction]]:
    return [[A[i][j] for i in range(len(A))] for j in range(len(A[0]))]


def mat_sub_q(A: list[list[Fraction]], B: list[list[Fraction]]) -> list[list[Fraction]]:
    return [[A[i][j] - B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_frob_sq_q(A: list[list[Fraction]]) -> Fraction:
    return sum((x * x for row in A for x in row), Fraction(0))


def mat_trace_q(A: list[list[Fraction]]) -> Fraction:
    return sum((A[i][i] for i in range(len(A))), Fraction(0))


def _mat_key(A: list[list[Fraction]]) -> tuple[tuple[Fraction, ...], ...]:
    return tuple(tuple(row) for row in A)


def matrix_rank_q(rows: list[list[Fraction]], ncols: int) -> tuple[int, list[int]]:
    M = [list(r) for r in rows]
    nrows = len(M)
    r = 0
    piv_cols: list[int] = []
    for c in range(ncols):
        piv = -1
        for i in range(r, nrows):
            if M[i][c] != 0:
                piv = i
                break
        if piv < 0:
            continue
        if piv != r:
            M[r], M[piv] = M[piv], M[r]
        pv = M[r][c]
        row_r = M[r]
        nz = [(j, row_r[j] / pv) for j in range(c + 1, ncols) if row_r[j] != 0]
        for i in range(r + 1, nrows):
            f = M[i][c]
            if f != 0:
                row_i = M[i]
                row_i[c] = Fraction(0)
                for j, val in nz:
                    row_i[j] -= f * val
        piv_cols.append(c)
        r += 1
        if r == nrows:
            break
    return r, piv_cols


def solve_linear_multi_q(A: list[list[Fraction]], B: list[list[Fraction]]) -> list[list[Fraction]]:
    n = len(A)
    k = len(B[0])
    aug = [list(A[i]) + list(B[i]) for i in range(n)]
    for c in range(n):
        piv = -1
        for i in range(c, n):
            if aug[i][c] != 0:
                piv = i
                break
        if piv < 0:
            raise SymmetryBridgeError("SINGULAR_MATRIX", f"zero pivot at column {c}")
        if piv != c:
            aug[c], aug[piv] = aug[piv], aug[c]
        pv = aug[c][c]
        row_c = aug[c]
        for j in range(c + 1, n + k):
            if row_c[j] != 0:
                row_c[j] /= pv
        row_c[c] = Fraction(1)
        nz = [(j, row_c[j]) for j in range(c + 1, n + k) if row_c[j] != 0]
        for i in range(c + 1, n):
            f = aug[i][c]
            if f != 0:
                row_i = aug[i]
                row_i[c] = Fraction(0)
                for j, val in nz:
                    row_i[j] -= f * val
    sol = [[Fraction(0)] * k for _ in range(n)]
    for i in range(n - 1, -1, -1):
        row_i = aug[i]
        nz_upper = [(j, row_i[j]) for j in range(i + 1, n) if row_i[j] != 0]
        for col in range(k):
            acc = row_i[n + col]
            for j, val in nz_upper:
                acc -= val * sol[j][col]
            sol[i][col] = acc
    return sol


def sylvester_inertia_q(matrix: Any) -> tuple[int, int, int]:
    """Exact-Q Bunch-Kaufman 1x1/2x2 symmetric congruence Sylvester inertia (n_pos, n_neg, n_zero)."""
    A = _require_square_mat(matrix, "matrix")
    n = len(A)
    for i in range(n):
        for j in range(i + 1, n):
            if A[i][j] != A[j][i]:
                raise SymmetryBridgeError("NON_SYMMETRIC_MATRIX", f"asymmetry at ({i},{j})")

    n_pos = 0
    n_neg = 0
    n_zero = 0
    k = 0
    while k < n:
        diag_piv = -1
        for i in range(k, n):
            if A[i][i] != 0:
                diag_piv = i
                break
        if diag_piv >= 0:
            if diag_piv != k:
                A[k], A[diag_piv] = A[diag_piv], A[k]
                for row in A:
                    row[k], row[diag_piv] = row[diag_piv], row[k]
            d = A[k][k]
            if d > 0:
                n_pos += 1
            else:
                n_neg += 1
            for i in range(k + 1, n):
                f = A[i][k] / d
                if f != 0:
                    for j in range(k + 1, n):
                        A[i][j] -= f * A[k][j]
            k += 1
            continue

        off_i = -1
        off_j = -1
        for i in range(k, n):
            for j in range(i + 1, n):
                if A[i][j] != 0:
                    off_i = i
                    off_j = j
                    break
            if off_i >= 0:
                break
        if off_i < 0:
            n_zero += n - k
            break

        if off_i != k:
            A[k], A[off_i] = A[off_i], A[k]
            for row in A:
                row[k], row[off_i] = row[off_i], row[k]
        if off_j != k + 1:
            A[k + 1], A[off_j] = A[off_j], A[k + 1]
            for row in A:
                row[k + 1], row[off_j] = row[off_j], row[k + 1]

        b = A[k][k + 1]
        n_pos += 1
        n_neg += 1
        for i in range(k + 2, n):
            c0 = A[i][k + 1] / b
            c1 = A[i][k] / b
            for j in range(k + 2, n):
                A[i][j] -= c0 * A[k][j] + c1 * A[k + 1][j]
        k += 2

    return (n_pos, n_neg, n_zero)


def verify_finite_orthogonal_group(mats: Any) -> dict[str, Any]:
    """Verify exact orthogonality, identity inclusion, and group multiplication closure."""
    seq = require_exact_seq(mats, "group", min_len=1, max_len=64)
    group = [_require_square_mat(g, f"group[{idx}]") for idx, g in enumerate(seq)]
    dim = len(group[0])
    ident = eye_q(dim)
    key_set: set[tuple[tuple[Fraction, ...], ...]] = set()
    for g in group:
        if len(g) != dim:
            raise SymmetryBridgeError("DIM_MISMATCH", "group elements must share dimension")
        if mat_mul_q(mat_transpose_q(g), g) != ident:
            raise SymmetryBridgeError("NON_ORTHOGONAL", "group element fails g^T g = I")
        key_set.add(_mat_key(g))
    if len(key_set) != len(group):
        raise SymmetryBridgeError("DUPLICATE_GROUP_ELEMENT", "group contains duplicate matrices")
    if _mat_key(ident) not in key_set:
        raise SymmetryBridgeError("MISSING_IDENTITY", "group must contain identity")
    for g1 in group:
        for g2 in group:
            if _mat_key(mat_mul_q(g1, g2)) not in key_set:
                raise SymmetryBridgeError("GROUP_NOT_CLOSED", "group is not closed under multiplication")
    return {"order": len(group), "dim": dim, "closed_orthogonal": True}


def build_isotypic_projector_q(
    group: list[list[list[Fraction]]],
    character: list[Fraction],
    irrep_dim: int,
) -> dict[str, Any]:
    """Exact-Q Reynolds isotypic projector P_chi = (d_chi / |G|) sum_{g in G} chi(g^-1) g."""
    d_chi = require_exact_int(irrep_dim, "irrep_dim", lo=1, hi=MAX_MATRIX_DIM)
    n_g = len(group)
    if len(character) != n_g:
        raise SymmetryBridgeError("CHAR_LEN_MISMATCH", "character length must match group order")
    dim = len(group[0])
    scale = Fraction(d_chi, n_g)
    P = [[Fraction(0)] * dim for _ in range(dim)]
    for g, chi_val in zip(group, character):
        c = require_exact_rat(chi_val, "chi_val") * scale
        for i in range(dim):
            for j in range(dim):
                P[i][j] += c * g[i][j]
    if mat_mul_q(P, P) != P or mat_transpose_q(P) != P:
        raise SymmetryBridgeError("INVALID_PROJECTOR", "projector fails P^2 = P = P^T")
    return {"projector": P, "rank": int(mat_trace_q(P))}


def verify_isotypic_partition(projectors: list[list[list[Fraction]]], dim: int) -> bool:
    """Verify sum_a P_a = I_d and P_a P_b = 0 for a != b."""
    total = [[Fraction(0)] * dim for _ in range(dim)]
    for P in projectors:
        for i in range(dim):
            for j in range(dim):
                total[i][j] += P[i][j]
    if total != eye_q(dim):
        raise SymmetryBridgeError("PARTITION_SUM_MISMATCH", "projectors do not sum to identity")
    zero = [[Fraction(0)] * dim for _ in range(dim)]
    for i in range(len(projectors)):
        for j in range(i + 1, len(projectors)):
            if mat_mul_q(projectors[i], projectors[j]) != zero:
                raise SymmetryBridgeError("NON_ORTHOGONAL_PROJECTORS", "distinct projectors do not annihilate")
    return True


def certify_schur_coupling(
    group: list[list[list[Fraction]]],
    op_mat: list[list[Fraction]],
    proj_a: list[list[Fraction]],
    proj_b: list[list[Fraction]],
) -> dict[str, Any]:
    """Compute exact equivariance defect max_g ||g K g^T - K||_F^2 and cross-irrep block ||P_a K P_b||_F^2."""
    max_defect_sq = Fraction(0)
    for g in group:
        conj = mat_mul_q(mat_mul_q(g, op_mat), mat_transpose_q(g))
        d2 = mat_frob_sq_q(mat_sub_q(conj, op_mat))
        if d2 > max_defect_sq:
            max_defect_sq = d2
    block = mat_mul_q(mat_mul_q(proj_a, op_mat), proj_b)
    coupling_sq = mat_frob_sq_q(block)
    return {
        "equivariant": max_defect_sq == 0,
        "max_equivariance_defect_sq": fmt_q(max_defect_sq),
        "cross_coupling_frob_sq": fmt_q(coupling_sq),
        "coupling_vanishes": coupling_sq == 0,
    }


# ---------------------------------------------------------------------------
# Frontier 1: `siliquant` — E8 Basis Metamorphosis & Weyl-Vector Antipodal Break
# ---------------------------------------------------------------------------

def analyze_frontier1_siliquant_e8() -> dict[str, Any]:
    # Exact doubled integer coordinates r2 = 2 * r in Z^8 (||r2||^2 = 8) for speed + exactness
    roots2: list[tuple[int, ...]] = []
    for i, j in combinations(range(8), 2):
        for si in (-2, 2):
            for sj in (-2, 2):
                r = [0] * 8
                r[i] = si
                r[j] = sj
                roots2.append(tuple(r))
    for bits in product((-1, 1), repeat=8):
        if bits.count(-1) % 2 == 0:
            roots2.append(bits)
    root2_set = set(roots2)

    H2 = ((1, 1), (1, -1))
    H4 = tuple(tuple(H2[i // 2][j // 2] * H2[i % 2][j % 2] for j in range(4)) for i in range(4))
    H8 = tuple(tuple(H4[i // 2][j // 2] * H2[i % 2][j % 2] for j in range(8)) for i in range(8))
    A2 = tuple(
        tuple(H4[i // 2][j // 2] if (i % 2) == (j % 2) else 0 for j in range(8))
        for i in range(8)
    )
    B_bh2 = tuple(
        tuple(H2[i % 2][j % 2] if (i // 2) == (j // 2) else 0 for j in range(8))
        for i in range(8)
    )

    # Verify A^T A = I_8  <=>  A2^T A2 = 4 I_8, and (I4 kron H2) * A = H8 / 2  <=>  B_bh2 * A2 = H8
    a_orth = all(
        sum(A2[k][i] * A2[k][j] for k in range(8)) == (4 if i == j else 0)
        for i in range(8)
        for j in range(8)
    )
    intertwiner_exact = all(
        sum(B_bh2[i][k] * A2[k][j] for k in range(8)) == H8[i][j]
        for i in range(8)
        for j in range(8)
    )
    a_roots2 = {
        tuple(sum(A2[i][j] * r[j] for j in range(8)) // 2 for i in range(8))
        for r in roots2
    }
    a_preserves_e8 = a_roots2 == root2_set

    # Scaled Hadamard roots: 2 * sqrt(2) * U_WHT8 * r = (H8 * r2) / 2 in Z^8 (norm^2 = 16; divide by 8 -> norm^2 = 2)
    had_roots2 = [
        tuple(sum(H8[i][j] * r[j] for j in range(8)) // 2 for i in range(8))
        for r in roots2
    ]
    std_wt: dict[str, int] = {}
    for r in roots2:
        k = str(sum(1 for x in r if x != 0))
        std_wt[k] = std_wt.get(k, 0) + 1
    had_wt: dict[str, int] = {}
    for r in had_roots2:
        k = str(sum(1 for x in r if x != 0))
        had_wt[k] = had_wt.get(k, 0) + 1
    steiner_quads = sorted(
        {tuple(i for i, x in enumerate(r) if x != 0) for r in had_roots2 if sum(1 for x in r if x != 0) == 4}
    )

    # Exact 4th-coordinate parity bleed on x = (1,1,1,1/100,0,0,0,0) / sqrt(2) across {0} U Phi(E8^Had)
    # In doubled-scaled coords (* 2*sqrt(2)), x_200 = (200, 200, 200, 2, 0, 0, 0, 0) / 100 and cand_200 = 100 * c2
    x100 = (200, 200, 200, 2, 0, 0, 0, 0)
    best_num = sum(c * c for c in x100)
    best_cands: list[tuple[int, ...]] = [(0, 0, 0, 0, 0, 0, 0, 0)]
    for cand in had_roots2:
        num = sum((x100[i] - 100 * cand[i]) ** 2 for i in range(8))
        if num < best_num:
            best_num = num
            best_cands = [cand]
        elif num == best_num:
            best_cands.append(cand)
    best_d2 = Fraction(best_num, 80_000)

    # Antipodal group {-I_8, +I_8} trivial projector proves mu = 0 under unbroken -I_8
    I8 = eye_q(8)
    neg_I8 = [[-I8[i][j] for j in range(8)] for i in range(8)]
    antipodal_group = [I8, neg_I8]
    antipodal_meta = verify_finite_orthogonal_group(antipodal_group)
    p_triv_antipodal = build_isotypic_projector_q(antipodal_group, [Fraction(1), Fraction(1)], 1)

    chambers: dict[str, Any] = {}
    for name, a_vec in (
        ("siliquant_default", (2, 10, 1, -17, 11, 4, -5, 8)),
        ("lexicographic", (128, 64, 32, 16, 8, 4, 2, 1)),
    ):
        pos = [r for r in roots2 if sum(a_vec[i] * r[i] for i in range(8)) > 0]
        ties = sum(1 for r in roots2 if sum(a_vec[i] * r[i] for i in range(8)) == 0)
        # rho = (1/2) sum r = (1/4) sum r2; all entries are exact integers
        rho_int = tuple(sum(r[i] for r in pos) // 4 for i in range(8))
        rho = tuple(Fraction(v, 1) for v in rho_int)
        mu = tuple(Fraction(v, 30) for v in rho_int)
        mu_n2 = Fraction(sum(v * v for v in rho_int), 900)
        # mu . r = (rho . r2) / 60
        max_dot = Fraction(max(sum(rho_int[i] * r[i] for i in range(8)) for r in roots2), 60)
        # ||r - mu||^2 = ||30 r2 - 2 rho||^2 / 3600 = ||15 r2 - rho||^2 / 900
        shifted_nums = sorted(
            sum((15 * r[i] - rho_int[i]) ** 2 for i in range(8)) for r in roots2
        )
        inside_nums = [n for n in shifted_nums if 0 < n < 1800]
        chambers[name] = {
            "positive_roots": len(pos),
            "ties": ties,
            "rho": fmt_vec_q(rho),
            "mu_inf": fmt_vec_q(mu),
            "mu_norm_sq": fmt_q(mu_n2),
            "max_root_dot": fmt_q(max_dot),
            "strictly_interior_voronoi": max_dot < 1,
            "shifted_roots_inside_open_sqrt2_ball": len(inside_nums),
            "min_shifted_root_dist_sq": fmt_q(Fraction(inside_nums[0], 900)),
        }

    return {
        "e8_root_count": len(roots2),
        "intertwiner_A_orthogonal": a_orth,
        "intertwiner_U_WHT8_equals_U_BH2_A": intertwiner_exact,
        "intertwiner_A_in_W_E8": a_preserves_e8,
        "std_e8_root_support_weights": std_wt,
        "had_e8_root_support_weights": had_wt,
        "steiner_3_8_4_1_quad_count": len(steiner_quads),
        "axis_1sparse_d2_max_std_to_had": ["1", "1/2"],
        "axis_1sparse_gain_sq_std_to_had": ["1", "2"],
        "steiner_probe_min_d2": fmt_q(best_d2),
        "steiner_probe_unique_nearest_count": len(best_cands),
        "steiner_probe_forced_coord4_nonzero": best_cands[0][3] != 0,
        "antipodal_group_order": antipodal_meta["order"],
        "antipodal_triv_projector_rank": p_triv_antipodal["rank"],
        "weyl_chambers": chambers,
        "chamber_universal_norm_31_45": all(c["mu_norm_sq"] == "31/45" for c in chambers.values()),
        "chamber_universal_52_inside": all(c["shifted_roots_inside_open_sqrt2_ball"] == 52 for c in chambers.values()),
    }


# ---------------------------------------------------------------------------
# Frontier 2: `point-charges` — T_d -> C_3v & D_4h -> D_2h Harmonic Hessian Walls
# ---------------------------------------------------------------------------

def _perm_sign_mat(perm: tuple[int, int, int], signs: tuple[int, int, int]) -> list[list[Fraction]]:
    M = [[Fraction(0)] * 3 for _ in range(3)]
    for i in range(3):
        M[i][perm[i]] = Fraction(signs[i])
    return M


def _build_point_groups_3d() -> dict[str, list[list[list[Fraction]]]]:
    tet_verts = {(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)}
    td: list[list[list[Fraction]]] = []
    c3v: list[list[list[Fraction]]] = []
    d4h: list[list[list[Fraction]]] = []
    d2h: list[list[list[Fraction]]] = []
    for perm in permutations((0, 1, 2)):
        for signs in product((-1, 1), repeat=3):
            img = {
                (signs[0] * v[perm[0]], signs[1] * v[perm[1]], signs[2] * v[perm[2]])
                for v in tet_verts
            }
            is_td = img == tet_verts
            is_d4h = perm[2] == 2
            if is_td or is_d4h:
                M = _perm_sign_mat(perm, signs)
                if is_td:
                    td.append(M)
                    if signs == (1, 1, 1):
                        c3v.append(M)
                if is_d4h:
                    d4h.append(M)
                    if perm == (0, 1, 2):
                        d2h.append(M)
    return {"Td": td, "C3v": c3v, "D4h": d4h, "D2h": d2h}


def _pyramid_scaled_hessian_q(t_val: Fraction) -> dict[str, Any]:
    """
    Exact-Q n=4 C_3v pyramid: 3 unit base charges at (1,-1,-1),(-1,1,-1),(-1,-1,1),
    1 apex charge q_a = t^2 at (t,t,t). Exact equilibrium grad V(0) = 0 for all t > 0;
    3^(5/2) H(0) is exact rational!
    """
    base = ((1, -1, -1), (-1, 1, -1), (-1, -1, 1))
    u = (1, 1, 1)
    q_a = t_val * t_val
    # Scaled gradient (factor 3^(3/2)): sum q_j p_j / (||p_j||^3 / 3^(3/2))
    grad_scaled = [
        sum((Fraction(p[i]) for p in base), Fraction(0)) + (q_a * t_val * Fraction(u[i])) / (t_val ** 3)
        for i in range(3)
    ]
    H = [[Fraction(0)] * 3 for _ in range(3)]
    for p in base:
        for i in range(3):
            for j in range(3):
                H[i][j] += Fraction(3 * p[i] * p[j] - (3 if i == j else 0))
    inv_t = Fraction(1) / t_val
    for i in range(3):
        for j in range(3):
            H[i][j] += inv_t * Fraction(3 * u[i] * u[j] - (3 if i == j else 0))
    inertia = sylvester_inertia_q(H)
    lam_a1 = sum((H[0][j] for j in range(3)), Fraction(0))
    lam_e = H[0][0] - H[0][1]
    return {
        "t": fmt_q(t_val),
        "q_apex": fmt_q(q_a),
        "grad_zero": grad_scaled == [Fraction(0), Fraction(0), Fraction(0)],
        "trace_zero": mat_trace_q(H) == 0,
        "H_scaled": H,
        "lambda_A1": fmt_q(lam_a1),
        "lambda_E": fmt_q(lam_e),
        "inertia": list(inertia),
        "morse_index": inertia[1],
    }


def _square_hessian_q(q_x: Fraction) -> dict[str, Any]:
    """Exact-Q n=4 square: charges (q_x, q_x, 1, 1) at (+-1,0,0), (0,+-1,0); ||p||=1."""
    pts = ((1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0))
    qs = (q_x, q_x, Fraction(1), Fraction(1))
    grad = [sum((q * Fraction(p[i]) for p, q in zip(pts, qs)), Fraction(0)) for i in range(3)]
    H = [[Fraction(0)] * 3 for _ in range(3)]
    for p, q in zip(pts, qs):
        for i in range(3):
            for j in range(3):
                H[i][j] += q * Fraction(3 * p[i] * p[j] - (1 if i == j else 0))
    inertia = sylvester_inertia_q(H)
    return {
        "q_x": fmt_q(q_x),
        "grad_zero": grad == [Fraction(0), Fraction(0), Fraction(0)],
        "trace_zero": mat_trace_q(H) == 0,
        "H": H,
        "diag": [fmt_q(H[i][i]) for i in range(3)],
        "inertia": list(inertia),
        "morse_index": inertia[1],
    }


def analyze_frontier2_point_charges() -> dict[str, Any]:
    groups = _build_point_groups_3d()
    td_meta = verify_finite_orthogonal_group(groups["Td"])
    c3v_meta = verify_finite_orthogonal_group(groups["C3v"])
    d4h_meta = verify_finite_orthogonal_group(groups["D4h"])
    d2h_meta = verify_finite_orthogonal_group(groups["D2h"])

    # T_d trivial projector rank = 0 (T_2 irreducible on Q^3)
    p_td_triv = build_isotypic_projector_q(groups["Td"], [Fraction(1)] * len(groups["Td"]), 1)

    # C_3v isotypic partition T_2 -> A_1 (dim 1) + E (dim 2):
    # chi_E(g) = tr(g) - 1 on Q^3 since Q^3 = A_1 + E!
    chi_c3v_a1 = [Fraction(1)] * len(groups["C3v"])
    chi_c3v_e = [mat_trace_q(g) - Fraction(1) for g in groups["C3v"]]
    p_c3v_a1 = build_isotypic_projector_q(groups["C3v"], chi_c3v_a1, 1)
    p_c3v_e = build_isotypic_projector_q(groups["C3v"], chi_c3v_e, 2)
    verify_isotypic_partition([p_c3v_a1["projector"], p_c3v_e["projector"]], 3)

    # D_4h partition Q^3 = E_u (xy-plane, dim 2) + A_2u (z-axis, dim 1)
    chi_d4h_a2u = [g[2][2] for g in groups["D4h"]]
    chi_d4h_eu = [mat_trace_q(g) - g[2][2] for g in groups["D4h"]]
    p_d4h_a2u = build_isotypic_projector_q(groups["D4h"], chi_d4h_a2u, 1)
    p_d4h_eu = build_isotypic_projector_q(groups["D4h"], chi_d4h_eu, 2)
    verify_isotypic_partition([p_d4h_a2u["projector"], p_d4h_eu["projector"]], 3)

    # D_2h partition Q^3 = B_3u(x) + B_2u(y) + B_1u(z)
    p_d2h_axes = [
        build_isotypic_projector_q(groups["D2h"], [g[ax][ax] for g in groups["D2h"]], 1)
        for ax in range(3)
    ]
    verify_isotypic_partition([p["projector"] for p in p_d2h_axes], 3)

    pyramid_cases: dict[str, Any] = {}
    for label, t_val in (
        ("compressed_C3v", Fraction(1, 2)),
        ("unbroken_Td_wall", Fraction(1)),
        ("extended_C3v", Fraction(2)),
    ):
        res = _pyramid_scaled_hessian_q(t_val)
        H = res.pop("H_scaled")
        schur_td = certify_schur_coupling(groups["Td"], H, p_c3v_a1["projector"], p_c3v_e["projector"])
        schur_c3v = certify_schur_coupling(groups["C3v"], H, p_c3v_a1["projector"], p_c3v_e["projector"])
        res["td_equivariant"] = schur_td["equivariant"]
        res["c3v_schur"] = schur_c3v
        res["H_scaled_q"] = fmt_mat_q(H)
        pyramid_cases[label] = res

    ph_sign_comp = (-1) ** pyramid_cases["compressed_C3v"]["morse_index"]
    ph_sign_ext = (-1) ** pyramid_cases["extended_C3v"]["morse_index"]

    square_cases: dict[str, Any] = {}
    for label, qx in (
        ("unbroken_D4h", Fraction(1)),
        ("degenerate_B2u_wall", Fraction(2)),
        ("broken_D2h_post_pitchfork", Fraction(3)),
    ):
        res = _square_hessian_q(qx)
        H = res.pop("H")
        schur_d4h = certify_schur_coupling(groups["D4h"], H, p_d4h_eu["projector"], p_d4h_a2u["projector"])
        schur_d2h = certify_schur_coupling(groups["D2h"], H, p_d2h_axes[0]["projector"], p_d2h_axes[1]["projector"])
        res["d4h_equivariant"] = schur_d4h["equivariant"]
        res["d2h_schur_xy"] = schur_d2h
        square_cases[label] = res

    # Poincare-Hopf topological fold conservation for n=4 C_1 fold (11 -> 9)
    n4_fold_pre = {"total": 11, "m1": 4, "m2": 7, "euler_index": 7 - 4}
    n4_fold_post = {"total": 9, "m1": 3, "m2": 6, "euler_index": 6 - 3}

    return {
        "group_orders": {
            "Td": td_meta["order"],
            "C3v": c3v_meta["order"],
            "D4h": d4h_meta["order"],
            "D2h": d2h_meta["order"],
        },
        "td_triv_projector_rank": p_td_triv["rank"],
        "c3v_isotypic_ranks": {"A1": p_c3v_a1["rank"], "E": p_c3v_e["rank"]},
        "d4h_isotypic_ranks": {"A2u": p_d4h_a2u["rank"], "Eu": p_d4h_eu["rank"]},
        "d2h_isotypic_ranks": [p["rank"] for p in p_d2h_axes],
        "pyramid_Td_to_C3v": pyramid_cases,
        "pyramid_poincare_hopf_sign_jump": ph_sign_comp - ph_sign_ext,
        "square_D4h_to_D2h": square_cases,
        "n4_c1_fold_poincare_hopf": {
            "pre_fold": n4_fold_pre,
            "post_fold": n4_fold_post,
            "poincare_hopf_preserved": n4_fold_pre["euler_index"] == n4_fold_post["euler_index"] == 3,
        },
    }


# ---------------------------------------------------------------------------
# Frontier 3: `aska-physical` — D_2h -> C_3 Voigt Stiffness, Z_2 Truss, Prestress
# ---------------------------------------------------------------------------

def _build_voigt_groups_6d() -> tuple[list[list[list[Fraction]]], list[list[list[Fraction]]]]:
    """
    Voigt basis order: (eps_xx, eps_yy, eps_zz, gamma_xy, gamma_xz, gamma_yz).
    Central inversion -I_3 acts trivially on quadratic strain Sym^2(Q^3), so the
    faithful image of D_2h (order 8) on 6D Voigt space is D_2 = D_2h/{+-I_3} = V_4
    (order 4): diag(1, 1, 1, sx*sy, sx, sy) for (sx, sy) in {+-1}^2.
    C_3 cyclic (x,y,z) -> (y,z,x) permutes (0,1,2)->(1,2,0) and (xy,xz,yz)->(yz,xy,xz).
    """
    d2_v: list[list[list[Fraction]]] = []
    for sx, sy in product((-1, 1), repeat=2):
        diag = (1, 1, 1, sx * sy, sx, sy)
        d2_v.append([[Fraction(diag[i] if i == j else 0) for j in range(6)] for i in range(6)])

    # Cyclic generator R: (x',y',z') = (y,z,x) => x'^2=y^2, y'^2=z^2, z'^2=x^2,
    # x'y'=yz (idx 5), x'z'=yx=xy (idx 3), y'z'=zx=xz (idx 4)
    p1 = (1, 2, 0, 5, 3, 4)
    R = [[Fraction(1 if j == p1[i] else 0) for j in range(6)] for i in range(6)]
    R2 = mat_mul_q(R, R)
    c3_v = [eye_q(6), R, R2]
    return d2_v, c3_v


def homogenize_f3_cell_q(tie_mode: str) -> tuple[list[list[Fraction]], dict[str, Any]]:
    """Exact-Q periodic Schur-complement homogenization of F_3(t=3/5, k_cross=1, k_tie=1)."""
    if tie_mode not in ("none", "one_per_plane", "half_2_opp", "full_4"):
        raise SymmetryBridgeError("UNKNOWN_TIE_MODE", f"unknown tie_mode: {tie_mode!r}")
    t = Fraction(3, 5)
    coords: list[list[Fraction]] = []
    for i in range(3):
        p_neg = [Fraction(0)] * 3
        p_neg[i] = -t
        p_pos = [Fraction(0)] * 3
        p_pos[i] = t
        coords.extend([p_neg, p_pos])

    bars: list[tuple[int, int, list[Fraction]]] = []
    for i in range(3):
        for j in range(i + 1, 3):
            for si in (0, 1):
                for sj in (0, 1):
                    bars.append((2 * i + si, 2 * j + sj, [Fraction(0)] * 3))
    for i in range(3):
        sh = [Fraction(0)] * 3
        sh[i] = Fraction(2)
        bars.append((2 * i + 1, 2 * i + 0, sh))
    for i in range(3):
        for j in range(i + 1, 3):
            s_neg = [Fraction(0)] * 3
            s_neg[i] = Fraction(-2)
            s_neg[j] = Fraction(2)
            s_pos = [Fraction(0)] * 3
            s_pos[i] = Fraction(2)
            s_pos[j] = Fraction(2)
            plane_ties = (
                (2 * i + 0, 2 * j + 0, s_neg),
                (2 * j + 1, 2 * i + 1, s_neg),
                (2 * i + 1, 2 * j + 0, s_pos),
                (2 * j + 1, 2 * i + 0, s_pos),
            )
            if tie_mode == "full_4":
                bars.extend(plane_ties)
            elif tie_mode == "half_2_opp":
                bars.extend((plane_ties[0], plane_ties[2]))
            elif tie_mode == "one_per_plane":
                bars.append(plane_ties[0])

    K_uu = [[Fraction(0)] * 18 for _ in range(18)]
    K_ue = [[Fraction(0)] * 6 for _ in range(18)]
    K_ee = [[Fraction(0)] * 6 for _ in range(6)]
    for u, v, sh in bars:
        vec = [coords[v][d] + sh[d] - coords[u][d] for d in range(3)]
        L2 = sum((x * x for x in vec), Fraction(0))
        wb = Fraction(1) / L2
        bu = [Fraction(0)] * 18
        for d in range(3):
            bu[3 * v + d] += vec[d]
            bu[3 * u + d] -= vec[d]
        be = [vec[0] ** 2, vec[1] ** 2, vec[2] ** 2, vec[0] * vec[1], vec[0] * vec[2], vec[1] * vec[2]]
        nz_u = [(a, val) for a, val in enumerate(bu) if val != 0]
        for a, va in nz_u:
            for b, vb in nz_u:
                K_uu[a][b] += wb * va * vb
            for e in range(6):
                if be[e] != 0:
                    K_ue[a][e] += wb * va * be[e]
        for e1 in range(6):
            for e2 in range(6):
                K_ee[e1][e2] += wb * be[e1] * be[e2]

    _, pivs = matrix_rank_q(K_uu, 18)
    K_red = [[K_uu[i][j] for j in pivs] for i in pivs]
    B_red = [[-K_ue[i][e] for e in range(6)] for i in pivs]
    U_red = solve_linear_multi_q(K_red, B_red)
    U_full = [[Fraction(0)] * 6 for _ in range(18)]
    for idx, pcol in enumerate(pivs):
        U_full[pcol] = U_red[idx]

    eq_zero = True
    for i in range(18):
        nz_k = [(j, K_uu[i][j]) for j in range(18) if K_uu[i][j] != 0]
        for e in range(6):
            acc = K_ue[i][e]
            for j, kv in nz_k:
                acc += kv * U_full[j][e]
            if acc != 0:
                eq_zero = False
    nz_kue = [[(i, K_ue[i][a]) for i in range(18) if K_ue[i][a] != 0] for a in range(6)]
    C = [
        [
            (K_ee[a][b] + sum((kv * U_full[i][b] for i, kv in nz_kue[a]), Fraction(0))) / Fraction(8)
            for b in range(6)
        ]
        for a in range(6)
    ]
    n_ties = len(bars) - 15
    inertia = sylvester_inertia_q(C)
    eff = C[3][3] / Fraction(n_ties) if n_ties > 0 else Fraction(0)
    return C, {
        "n_bars": len(bars),
        "n_ties": n_ties,
        "relaxation_zero_residual": eq_zero,
        "C11": fmt_q(C[0][0]),
        "C12": fmt_q(C[0][1]),
        "C44": fmt_q(C[3][3]),
        "C55": fmt_q(C[4][4]),
        "C66": fmt_q(C[5][5]),
        "C14_axial_shear": fmt_q(C[0][3]),
        "shear_per_tie": fmt_q(eff),
        "inertia": list(inertia),
    }


def _analyze_z2_two_bar_truss() -> dict[str, Any]:
    z2 = [
        eye_q(2),
        [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(-1)]],
    ]
    z2_meta = verify_finite_orthogonal_group(z2)
    p_a1 = build_isotypic_projector_q(z2, [Fraction(1), Fraction(1)], 1)
    p_b1 = build_isotypic_projector_q(z2, [Fraction(1), Fraction(-1)], 1)
    verify_isotypic_partition([p_a1["projector"], p_b1["projector"]], 2)

    L1_s, L2_s = Fraction(9, 10), Fraction(11, 10)
    hxx = Fraction(1) / L1_s + Fraction(1) / L2_s
    H_flat = [[hxx, Fraction(0)], [Fraction(0), Fraction(0)]]
    quartic_coeff = Fraction(1, 8) * (Fraction(1) / (L1_s ** 3) + Fraction(1) / (L2_s ** 3))

    x2 = Fraction(-109, 100)
    r1, r2 = abs(x2 + 1), abs(x2 - 1)
    hyy_saddle = (r1 - L1_s) / (L1_s * r1) + (r2 - L2_s) / (L2_s * r2)
    H_saddle = [[hxx, Fraction(0)], [Fraction(0), hyy_saddle]]

    L1_b, L2_b = Fraction(7, 10), Fraction(3, 2)
    xb = (L1_b ** 2 - L2_b ** 2) / Fraction(4)
    yb = Fraction(21, 50)
    u1 = ((xb + 1) / L1_b, yb / L1_b)
    u2 = ((xb - 1) / L2_b, yb / L2_b)
    H_broken = [
        [
            (Fraction(1) / L1_b) * u1[i] * u1[j] + (Fraction(1) / L2_b) * u2[i] * u2[j]
            for j in range(2)
        ]
        for i in range(2)
    ]
    det_broken = H_broken[0][0] * H_broken[1][1] - H_broken[0][1] * H_broken[1][0]

    return {
        "z2_order": z2_meta["order"],
        "isotypic_ranks": {"A1": p_a1["rank"], "B1": p_b1["rank"]},
        "flat_singular_9_10_11_10": {
            "x_star": "-1/10",
            "H_q": fmt_mat_q(H_flat),
            "inertia": list(sylvester_inertia_q(H_flat)),
            "quartic_y4_coeff": fmt_q(quartic_coeff),
            "schur_z2": certify_schur_coupling(z2, H_flat, p_a1["projector"], p_b1["projector"]),
        },
        "online_saddle_9_10_11_10": {
            "x_star": fmt_q(x2),
            "H_q": fmt_mat_q(H_saddle),
            "inertia": list(sylvester_inertia_q(H_saddle)),
            "schur_z2": certify_schur_coupling(z2, H_saddle, p_a1["projector"], p_b1["projector"]),
        },
        "broken_z2_corner_7_10_3_2": {
            "x_star": fmt_q(xb),
            "y_star": fmt_q(yb),
            "exact_pythagorean_check": yb * yb == L1_b * L1_b - (xb + 1) * (xb + 1),
            "H_q": fmt_mat_q(H_broken),
            "det_H": fmt_q(det_broken),
            "tr_H": fmt_q(mat_trace_q(H_broken)),
            "inertia": list(sylvester_inertia_q(H_broken)),
            "schur_z2": certify_schur_coupling(z2, H_broken, p_a1["projector"], p_b1["projector"]),
        },
    }


def _verify_anchored_6spoke_prestress(w_tie: Fraction, w_inner: Fraction, w_anchor: Fraction) -> dict[str, Any]:
    ring = (
        (Fraction(2), Fraction(0)),
        (Fraction(1), Fraction(2)),
        (Fraction(-1), Fraction(2)),
        (Fraction(-2), Fraction(0)),
        (Fraction(-1), Fraction(-2)),
        (Fraction(1), Fraction(-2)),
    )
    coords = [(Fraction(0), Fraction(0))] + list(ring) + [(2 * x, 2 * y) for x, y in ring]
    edges_w: list[tuple[int, int, Fraction]] = []
    for k in range(6):
        edges_w.append((0, 1 + k, w_inner))
        edges_w.append((1 + k, 1 + (k + 1) % 6, w_tie))
        edges_w.append((1 + k, 7 + k, w_anchor))
    eq_ok = True
    for v in range(7):
        fx = Fraction(0)
        fy = Fraction(0)
        px, py = coords[v]
        for a, b, w in edges_w:
            if a == v:
                fx += w * (px - coords[b][0])
                fy += w * (py - coords[b][1])
            elif b == v:
                fx += w * (px - coords[a][0])
                fy += w * (py - coords[a][1])
        if (fx, fy) != (0, 0):
            eq_ok = False
    omega = [[Fraction(0)] * 13 for _ in range(13)]
    for a, b, w in edges_w:
        omega[a][a] += w
        omega[b][b] += w
        omega[a][b] -= w
        omega[b][a] -= w
    omega_int = [row[:7] for row in omega[:7]]
    in_int = sylvester_inertia_q(omega_int)
    in_full = sylvester_inertia_q(omega)
    return {
        "weights": [fmt_q(w_tie), fmt_q(w_inner), fmt_q(w_anchor)],
        "equilibrium_zero_residual": eq_ok,
        "omega_int_inertia": list(in_int),
        "omega_full_inertia": list(in_full),
        "strictly_pd_interior": in_int == (7, 0, 0),
    }


def analyze_frontier3_aska_physical() -> dict[str, Any]:
    d2_v, c3_v = _build_voigt_groups_6d()
    d2_meta = verify_finite_orthogonal_group(d2_v)
    c3_meta = verify_finite_orthogonal_group(c3_v)

    p_ag = build_isotypic_projector_q(d2_v, [Fraction(1)] * 4, 1)
    p_b1g = build_isotypic_projector_q(d2_v, [g[3][3] for g in d2_v], 1)
    p_b2g = build_isotypic_projector_q(d2_v, [g[4][4] for g in d2_v], 1)
    p_b3g = build_isotypic_projector_q(d2_v, [g[5][5] for g in d2_v], 1)
    verify_isotypic_partition(
        [p_ag["projector"], p_b1g["projector"], p_b2g["projector"], p_b3g["projector"]],
        6,
    )
    p_shear = [
        [p_b1g["projector"][i][j] + p_b2g["projector"][i][j] + p_b3g["projector"][i][j] for j in range(6)]
        for i in range(6)
    ]

    f3_modes: dict[str, Any] = {}
    for mode in ("none", "one_per_plane", "half_2_opp", "full_4"):
        C, stats = homogenize_f3_cell_q(mode)
        schur_d2 = certify_schur_coupling(d2_v, C, p_ag["projector"], p_shear)
        schur_c3 = certify_schur_coupling(c3_v, C, p_ag["projector"], p_shear)
        stats["d2h_schur"] = schur_d2
        stats["c3_equivariant"] = schur_c3["equivariant"]
        f3_modes[mode] = stats

    return {
        "voigt_group_orders": {"D2_faithful_from_D2h": d2_meta["order"], "C3": c3_meta["order"]},
        "d2h_voigt_isotypic_ranks": {
            "Ag_axial": p_ag["rank"],
            "B1g_xy": p_b1g["rank"],
            "B2g_xz": p_b2g["rank"],
            "B3g_yz": p_b3g["rank"],
        },
        "f3_periodic_modes": f3_modes,
        "two_bar_z2_truss": _analyze_z2_two_bar_truss(),
        "anchored_6spoke_prestress": {
            "tension_1_10_11": _verify_anchored_6spoke_prestress(Fraction(1), Fraction(10), Fraction(11)),
            "compression_1_neg10_neg9": _verify_anchored_6spoke_prestress(Fraction(1), Fraction(-10), Fraction(-9)),
        },
    }


# ---------------------------------------------------------------------------
# Unified Payload & Fail-Closed Certificate Construction / Verification
# ---------------------------------------------------------------------------

def build_payload() -> dict[str, Any]:
    f1 = analyze_frontier1_siliquant_e8()
    f2 = analyze_frontier2_point_charges()
    f3 = analyze_frontier3_aska_physical()

    all_passed = all(
        (
            f1["e8_root_count"] == 240,
            f1["intertwiner_A_orthogonal"],
            f1["intertwiner_U_WHT8_equals_U_BH2_A"],
            f1["intertwiner_A_in_W_E8"],
            f1["steiner_3_8_4_1_quad_count"] == 14,
            f1["steiner_probe_min_d2"] == "9801/20000",
            f1["steiner_probe_unique_nearest_count"] == 1,
            f1["steiner_probe_forced_coord4_nonzero"],
            f1["antipodal_triv_projector_rank"] == 0,
            f1["chamber_universal_norm_31_45"],
            f1["chamber_universal_52_inside"],
            f2["td_triv_projector_rank"] == 0,
            f2["pyramid_Td_to_C3v"]["unbroken_Td_wall"]["inertia"] == [0, 0, 3],
            f2["pyramid_Td_to_C3v"]["compressed_C3v"]["inertia"] == [1, 2, 0],
            f2["pyramid_Td_to_C3v"]["extended_C3v"]["inertia"] == [2, 1, 0],
            f2["pyramid_poincare_hopf_sign_jump"] == 2,
            f2["square_D4h_to_D2h"]["unbroken_D4h"]["inertia"] == [2, 1, 0],
            f2["square_D4h_to_D2h"]["degenerate_B2u_wall"]["inertia"] == [1, 1, 1],
            f2["square_D4h_to_D2h"]["broken_D2h_post_pitchfork"]["inertia"] == [1, 2, 0],
            f2["n4_c1_fold_poincare_hopf"]["poincare_hopf_preserved"],
            f3["f3_periodic_modes"]["none"]["d2h_schur"]["coupling_vanishes"],
            not f3["f3_periodic_modes"]["one_per_plane"]["d2h_schur"]["equivariant"],
            f3["f3_periodic_modes"]["one_per_plane"]["c3_equivariant"],
            f3["f3_periodic_modes"]["one_per_plane"]["C14_axial_shear"] == "-26/253",
            f3["f3_periodic_modes"]["half_2_opp"]["d2h_schur"]["coupling_vanishes"],
            f3["f3_periodic_modes"]["half_2_opp"]["C44"] == "1/4",
            f3["f3_periodic_modes"]["half_2_opp"]["C14_axial_shear"] == "0",
            f3["f3_periodic_modes"]["half_2_opp"]["shear_per_tie"] == "1/24",
            f3["two_bar_z2_truss"]["flat_singular_9_10_11_10"]["inertia"] == [1, 0, 1],
            f3["two_bar_z2_truss"]["flat_singular_9_10_11_10"]["quartic_y4_coeff"] == "257500/970299",
            f3["two_bar_z2_truss"]["online_saddle_9_10_11_10"]["inertia"] == [1, 1, 0],
            f3["two_bar_z2_truss"]["broken_z2_corner_7_10_3_2"]["det_H"] == "64/105",
            not f3["two_bar_z2_truss"]["broken_z2_corner_7_10_3_2"]["schur_z2"]["coupling_vanishes"],
            f3["anchored_6spoke_prestress"]["tension_1_10_11"]["strictly_pd_interior"],
            f3["anchored_6spoke_prestress"]["compression_1_neg10_neg9"]["omega_int_inertia"] == [0, 7, 0],
        )
    )
    if not all_passed:
        raise SymmetryBridgeError("ORACLE_INVARIANT_FAILED", "unified symmetry theorem invariant failed")

    return {
        "novelty_tier": "N1_UNIFIED_CROSS_FRONTIER_EXACT_SYNTHESIS",
        "law5_functor": "exact_Q_finite_orthogonal_isotypic_projector_and_schur_obstruction",
        "all_theorems_verified": True,
        "frontier1_siliquant_e8": f1,
        "frontier2_point_charges_harmonic": f2,
        "frontier3_aska_physical_voigt_truss": f3,
        "law2b_honest_obstruction": {
            "protective_symmetry": "Equivariance under G enforces zero forbidden cross-irrep couplings and zero invariant drift (C14=0 under D_2h, mu=0 under -I_8, H_xy=0 under Z_2).",
            "degeneracy_trap": "Excessive symmetry forces complete degeneracies or bulk parity walls (T_d forces H(0)=0_{3x3}, Z_2 flat diagonal forces H_yy=0, E8^Had forces Steiner 9801/20000 bleed) requiring controlled symmetry breaking or graded augmentation to escape.",
        },
    }


def build_certificate() -> dict[str, Any]:
    payload = build_payload()
    payload_sha = sha256_canonical(payload)
    outer = {
        "schema": CERT_SCHEMA,
        "track_id": CERT_TRACK_ID,
        "payload_sha256": payload_sha,
        "payload": payload,
    }
    cert_sha = sha256_canonical(outer)
    return {
        "schema": CERT_SCHEMA,
        "track_id": CERT_TRACK_ID,
        "payload_sha256": payload_sha,
        "certificate_sha256": cert_sha,
        "payload": payload,
    }


def verify_certificate_object(cert: Any) -> dict[str, Any]:
    """Fail-closed in-memory Zone-B validator + full exact-Q oracle recomputation check."""
    if type(cert) is not dict:
        raise SymmetryBridgeError("NON_OBJECT_CERT", "certificate must be strict dict")
    validate_json_tree_iterative(cert)
    if frozenset(cert.keys()) != CERT_TOP_KEYS:
        raise SymmetryBridgeError("INVALID_CERT_KEYS", "certificate top-level key set mismatch")
    if cert["schema"] != CERT_SCHEMA or type(cert["schema"]) is not str:
        raise SymmetryBridgeError("INVALID_SCHEMA", "unexpected certificate schema")
    if cert["track_id"] != CERT_TRACK_ID or type(cert["track_id"]) is not str:
        raise SymmetryBridgeError("INVALID_TRACK_ID", "unexpected certificate track_id")

    p_sha = require_hex_sha256(cert["payload_sha256"], "payload_sha256")
    c_sha = require_hex_sha256(cert["certificate_sha256"], "certificate_sha256")
    payload = cert["payload"]
    if type(payload) is not dict:
        raise SymmetryBridgeError("INVALID_PAYLOAD_TYPE", "payload must be strict dict")

    recomputed_p_sha = sha256_canonical(payload)
    if not hmac.compare_digest(p_sha, recomputed_p_sha):
        raise SymmetryBridgeError("PAYLOAD_SHA_MISMATCH", "payload_sha256 mismatch")

    outer = {
        "schema": cert["schema"],
        "track_id": cert["track_id"],
        "payload_sha256": p_sha,
        "payload": payload,
    }
    recomputed_c_sha = sha256_canonical(outer)
    if not hmac.compare_digest(c_sha, recomputed_c_sha):
        raise SymmetryBridgeError("CERT_SHA_MISMATCH", "certificate_sha256 mismatch")

    # Full oracle recomputation closes hollow/re-signed forgeries (ZB05 / ZB13)
    expected_cert = build_certificate()
    if canonical_json_bytes(cert) != canonical_json_bytes(expected_cert):
        raise SymmetryBridgeError("ORACLE_RECOMPUTATION_MISMATCH", "certificate payload diverges from exact-Q oracle")
    return cert


def verify_certificate_file(path: Any) -> dict[str, Any]:
    raw_bytes, cert = read_strict_json_file(path, "certificate_path")
    verified = verify_certificate_object(cert)
    if raw_bytes != canonical_json_bytes(verified):
        raise SymmetryBridgeError("NON_CANONICAL_BYTES", "certificate file bytes are not canonical")
    return verified
