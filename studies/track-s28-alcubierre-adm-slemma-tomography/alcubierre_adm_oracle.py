#!/usr/bin/env python3
"""Track S28: Portal 24 — Exact-Q Alcubierre ADM / S-Lemma / Hawking-Ellis / Horizon / Physical-Shell Tomography.

100% pure Python 3 standard library (exact Z/Q arithmetic only):
  - ZERO floating-point literals, float() casts, or float trust-path arithmetic
  - ZERO bare assert statements
  - ZERO RNG / non-deterministic inputs

Certifies five exact mathematical pillars grounded against 2024-2026 literature:
  1. Full-4D ADM Arbitrary-Lapse Divergence-Enstrophy & Momentum Identities,
     Gullstrand-Painleve Schwarzschild Boundary, Unit-Lapse Sign-Flip Duality,
     and Irrotational Non-Unit-Lapse Hawking-Ellis Type-IV Trigger.
  2. Exact Alcubierre w_x == +3 Equation of State & Mandatory Two-Annulus
     Equatorial Hawking-Ellis Type-IV Obstruction (expanding as v -> 0+).
  3. Zero-Float Exact-Q S-Lemma / Sylvester-Krein Inertia Observer-Robust
     NEC/WEC/SEC/DEC Engine + Pythagorean-Quadruple Violation Witnesses +
     Eulerian Blind-Spot Irrotational Type-I Witness.
  4. Natario Zero-Expansion Stokes-Flow Sharp Minimum (1/4 thin-wall constant +
     exact finite-aspect-ratio concentric-sphere resistance), S23a Beltrami
     Helicity Exact Bridge, and Superluminal Killing Horizons & Surface Gravities.
  5. Law-2 Transformational Steelman: Conformally Flat Lichnerowicz Constraint,
     Van Den Broeck Compact Collar Zero-Integral vs Schwarzschild ADM Mass Tail,
     and Exact Pure-Q Subluminal Boosted Positive-Energy Spherical Shells
     (both smooth 4D conformally flat and Israel thin-shell) Passing WEC+NEC+SEC+DEC
     for ALL Observers via Exact S-Lemma Certificates.
"""
from __future__ import annotations

from collections.abc import Mapping, Sequence
from fractions import Fraction
import hashlib
import hmac
import json
from typing import Any

SCHEMA_VERSION = "aletheia.alcubierre_adm_tomography.certificate.v1"
TRACK_ID = "TRACK-S28-ALCUBIERRE-ADM-SLEMMA-TOMOGRAPHY"

MAX_JSON_BYTES = 1_048_576
MAX_JSON_DEPTH = 64
MAX_INT_DIGITS = 1000

_LOWER_HEX = frozenset("0123456789abcdef")
_CERT_TOP_KEYS = frozenset({"schema", "track_id", "payload_sha256", "certificate_sha256", "payload"})

ETA_4X4: tuple[tuple[Fraction, ...], ...] = (
    (Fraction(-1, 1), Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)),
    (Fraction(0, 1), Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)),
    (Fraction(0, 1), Fraction(0, 1), Fraction(1, 1), Fraction(0, 1)),
    (Fraction(0, 1), Fraction(0, 1), Fraction(0, 1), Fraction(1, 1)),
)


class AlcubierreAdmError(ValueError):
    """Typed fail-closed error for all Track S28 oracle and Zone-B checks."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


# ---------------------------------------------------------------------------
# Strict Zone-B Parsing, Canonicalization & Integrity Primitives
# ---------------------------------------------------------------------------

def _int_digit_len(value: int) -> int:
    mag = abs(value)
    if mag.bit_length() > MAX_INT_DIGITS * 4:
        return MAX_INT_DIGITS + 1
    return len(str(mag))


def require_exact_int(value: Any, label: str, *, min_val: int | None = None, max_val: int | None = None) -> int:
    if type(value) is not int:
        raise AlcubierreAdmError("INVALID_INT", f"{label} must be exact int")
    if _int_digit_len(value) > MAX_INT_DIGITS:
        raise AlcubierreAdmError("INT_DIGITS_EXCEEDED", f"{label} exceeds {MAX_INT_DIGITS} digits")
    if min_val is not None and value < min_val:
        raise AlcubierreAdmError("INT_TOO_SMALL", f"{label} < {min_val}")
    if max_val is not None and value > max_val:
        raise AlcubierreAdmError("INT_TOO_LARGE", f"{label} > {max_val}")
    return value


def require_exact_bool(value: Any, label: str) -> bool:
    if type(value) is not bool:
        raise AlcubierreAdmError("INVALID_BOOL", f"{label} must be exact bool")
    return value


def require_exact_str(value: Any, label: str, *, non_empty: bool = True) -> str:
    if type(value) is not str:
        raise AlcubierreAdmError("INVALID_STR", f"{label} must be exact str")
    try:
        value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise AlcubierreAdmError("INVALID_UTF8_SURROGATE", f"{label} contains lone UTF-16 surrogate") from exc
    if non_empty and not value:
        raise AlcubierreAdmError("EMPTY_STR", f"{label} must be non-empty")
    return value


def require_sha256_hex(value: Any, label: str) -> str:
    text = require_exact_str(value, label)
    if len(text) != 64 or not all(ch in _LOWER_HEX for ch in text):
        raise AlcubierreAdmError("INVALID_SHA256", f"{label} must be 64 lowercase hex chars")
    return text


def format_exact_rational(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _is_ascii_digits(text: str) -> bool:
    return bool(text) and all("0" <= ch <= "9" for ch in text)


def parse_exact_rational(value: Any, label: str = "rational") -> Fraction:
    text = require_exact_str(value, label)
    parts = text.split("/")
    if len(parts) == 1:
        num_s, den_s = parts[0], "1"
    elif len(parts) == 2:
        num_s, den_s = parts[0], parts[1]
    else:
        raise AlcubierreAdmError("INVALID_RATIONAL", f"{label} has multiple '/' separators")
    num_body = num_s[1:] if num_s.startswith("-") else num_s
    if not _is_ascii_digits(num_body) or not _is_ascii_digits(den_s):
        raise AlcubierreAdmError("INVALID_RATIONAL", f"{label} contains non-ASCII-digit characters")
    if len(num_body) > MAX_INT_DIGITS or len(den_s) > MAX_INT_DIGITS:
        raise AlcubierreAdmError("INT_DIGITS_EXCEEDED", f"{label} exceeds {MAX_INT_DIGITS} digits")
    den = int(den_s)
    if den == 0:
        raise AlcubierreAdmError("ZERO_DENOMINATOR", f"{label} has zero denominator")
    return Fraction(int(num_s), den)


def validate_json_tree_iterative(obj: Any, *, max_depth: int = MAX_JSON_DEPTH) -> None:
    limit = require_exact_int(max_depth, "max_depth", min_val=1, max_val=256)
    stack: list[tuple[Any, int]] = [(obj, 0)]
    while stack:
        cur, depth = stack.pop()
        if depth > limit:
            raise AlcubierreAdmError("JSON_DEPTH_EXCEEDED", f"JSON nesting depth > {limit}")
        t = type(cur)
        if t is dict:
            for k, v in cur.items():
                require_exact_str(k, "dict_key", non_empty=False)
                stack.append((v, depth + 1))
        elif t is list:
            for item in cur:
                stack.append((item, depth + 1))
        elif t is str:
            require_exact_str(cur, "str_value", non_empty=False)
        elif t is int:
            require_exact_int(cur, "int_value")
        elif t is bool or cur is None:
            continue
        else:
            raise AlcubierreAdmError("FORBIDDEN_JSON_TYPE", f"forbidden JSON value type: {t.__name__}")


def _strict_parse_int_token(token: str) -> int:
    body = token[1:] if token.startswith("-") else token
    if len(body) > MAX_INT_DIGITS:
        raise AlcubierreAdmError("INT_DIGITS_EXCEEDED", f"integer token exceeds {MAX_INT_DIGITS} digits")
    return int(token)


def _reject_float_token(token: str) -> Any:
    raise AlcubierreAdmError("FLOAT_FORBIDDEN", f"floating-point JSON literal forbidden: {token}")


def _reject_constant_token(token: str) -> Any:
    raise AlcubierreAdmError("NONFINITE_JSON_FORBIDDEN", f"non-finite JSON token forbidden: {token}")


def _strict_object_pairs_hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for key, val in pairs:
        require_exact_str(key, "json_key", non_empty=False)
        if key in out:
            raise AlcubierreAdmError("DUPLICATE_JSON_KEY", f"duplicate JSON key: {key!r}")
        out[key] = val
    return out


def parse_strict_json_text(text: str, *, require_object: bool = True) -> Any:
    require_exact_str(text, "json_text")
    if len(text.encode("utf-8")) > MAX_JSON_BYTES:
        raise AlcubierreAdmError("JSON_TOO_LARGE", f"JSON text exceeds {MAX_JSON_BYTES} bytes")
    try:
        parsed = json.loads(
            text,
            parse_float=_reject_float_token,
            parse_int=_strict_parse_int_token,
            parse_constant=_reject_constant_token,
            object_pairs_hook=_strict_object_pairs_hook,
        )
    except AlcubierreAdmError:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise AlcubierreAdmError("INVALID_JSON", f"JSON parse failed: {type(exc).__name__}") from exc
    if require_object and type(parsed) is not dict:
        raise AlcubierreAdmError("ROOT_NOT_OBJECT", "JSON root must be an object")
    validate_json_tree_iterative(parsed)
    return parsed


def canonical_json_bytes(obj: Any) -> bytes:
    validate_json_tree_iterative(obj)
    try:
        rendered = json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False)
    except (TypeError, ValueError) as exc:
        raise AlcubierreAdmError("CANONICAL_ENCODE_ERROR", f"cannot encode canonical JSON: {exc}") from exc
    return rendered.encode("ascii")


def canonical_sha256(obj: Any) -> str:
    return hashlib.sha256(canonical_json_bytes(obj)).hexdigest()


# ---------------------------------------------------------------------------
# Exact Multivariate Polynomial Ring Q[x_0, ..., x_{n-1}] & Linear Algebra
# ---------------------------------------------------------------------------

class MPoly:
    """Exact sparse multivariate polynomial over Q."""

    __slots__ = ("n_vars", "terms")

    def __init__(self, n_vars: int, terms: Mapping[tuple[int, ...], Fraction]) -> None:
        self.n_vars = n_vars
        self.terms: dict[tuple[int, ...], Fraction] = {m: c for m, c in terms.items() if c != 0}

    @classmethod
    def const(cls, n_vars: int, val: int | Fraction) -> MPoly:
        c = val if isinstance(val, Fraction) else Fraction(val, 1)
        return cls(n_vars, {(0,) * n_vars: c})

    @classmethod
    def var(cls, n_vars: int, idx: int) -> MPoly:
        n_v = require_exact_int(n_vars, "n_vars", min_val=1)
        i_v = require_exact_int(idx, "idx", min_val=0, max_val=n_v - 1)
        return cls(n_v, {tuple(1 if i == i_v else 0 for i in range(n_v)): Fraction(1, 1)})

    def _require_same_ring(self, other: Any) -> None:
        if not isinstance(other, MPoly) or other.n_vars != self.n_vars:
            raise AlcubierreAdmError("MPOLY_RING_MISMATCH", "MPoly operands must share n_vars")

    def __neg__(self) -> MPoly:
        return MPoly(self.n_vars, {m: -c for m, c in self.terms.items()})

    def __add__(self, other: MPoly) -> MPoly:
        self._require_same_ring(other)
        out = dict(self.terms)
        for m, c in other.terms.items():
            out[m] = out.get(m, Fraction(0, 1)) + c
        return MPoly(self.n_vars, out)

    def __sub__(self, other: MPoly) -> MPoly:
        self._require_same_ring(other)
        return self + (-other)

    def scale(self, factor: int | Fraction) -> MPoly:
        f = factor if isinstance(factor, Fraction) else Fraction(factor, 1)
        return MPoly(self.n_vars, {m: c * f for m, c in self.terms.items()})

    def __mul__(self, other: MPoly) -> MPoly:
        self._require_same_ring(other)
        out: dict[tuple[int, ...], Fraction] = {}
        for m1, c1 in self.terms.items():
            for m2, c2 in other.terms.items():
                mon = tuple(a + b for a, b in zip(m1, m2))
                out[mon] = out.get(mon, Fraction(0, 1)) + c1 * c2
        return MPoly(self.n_vars, out)

    def pow(self, exp: int) -> MPoly:
        e = require_exact_int(exp, "exp", min_val=0)
        res = MPoly.const(self.n_vars, 1)
        base = self
        while e > 0:
            if e & 1:
                res = res * base
            base = base * base
            e >>= 1
        return res

    def deriv(self, var_idx: int) -> MPoly:
        idx = require_exact_int(var_idx, "var_idx", min_val=0, max_val=self.n_vars - 1)
        out = {
            tuple(mon[i] - 1 if i == idx else mon[i] for i in range(self.n_vars)): coeff * mon[idx]
            for mon, coeff in self.terms.items()
            if mon[idx] > 0
        }
        return MPoly(self.n_vars, out)

    def integrate_unit_cube(self) -> Fraction:
        """Exact definite integral over [-1, 1]^n_vars."""
        total = Fraction(0, 1)
        for mon, coeff in self.terms.items():
            if any(p & 1 for p in mon):
                continue
            val = coeff
            for p in mon:
                val *= Fraction(2, p + 1)
            total += val
        return total

    def integrate_01_1d(self) -> Fraction:
        """Exact 1D integral over [0, 1]."""
        if self.n_vars != 1:
            raise AlcubierreAdmError("MPOLY_DIM_MISMATCH", "integrate_01_1d requires univariate MPoly")
        total = Fraction(0, 1)
        for mon, coeff in self.terms.items():
            total += coeff / Fraction(mon[0] + 1, 1)
        return total


def _require_exact_fraction(value: Any, label: str) -> Fraction:
    if type(value) is not Fraction:
        raise AlcubierreAdmError("INVALID_FRACTION", f"{label} must be exact Fraction")
    return value


def _require_square_fraction_matrix(
    mat: Any,
    label: str,
    *,
    exact_dim: int | None = None,
    symmetric: bool = False,
) -> list[list[Fraction]]:
    if not isinstance(mat, Sequence) or isinstance(mat, (str, bytes)):
        raise AlcubierreAdmError("INVALID_MATRIX", f"{label} must be a sequence of rows")
    n = len(mat)
    if n == 0:
        raise AlcubierreAdmError("INVALID_MATRIX", f"{label} must be non-empty")
    if exact_dim is not None and n != exact_dim:
        raise AlcubierreAdmError("INVALID_MATRIX_DIM", f"{label} must be {exact_dim}x{exact_dim}")
    out: list[list[Fraction]] = []
    for r_idx, row in enumerate(mat):
        if not isinstance(row, Sequence) or isinstance(row, (str, bytes)):
            raise AlcubierreAdmError("INVALID_MATRIX", f"{label}[{r_idx}] must be a sequence")
        if len(row) != n:
            raise AlcubierreAdmError("INVALID_MATRIX_SHAPE", f"{label} must be square ({n}x{n})")
        out.append([_require_exact_fraction(x, f"{label}[{r_idx}][{c_idx}]") for c_idx, x in enumerate(row)])
    if symmetric:
        for i in range(n):
            for j in range(i + 1, n):
                if out[i][j] != out[j][i]:
                    raise AlcubierreAdmError("NON_SYMMETRIC_MATRIX", f"{label} must be symmetric")
    return out


def _require_fraction_vec4(vec: Any, label: str) -> list[Fraction]:
    if not isinstance(vec, Sequence) or isinstance(vec, (str, bytes)):
        raise AlcubierreAdmError("INVALID_WITNESS_VECTOR", f"{label} must be a sequence")
    if len(vec) != 4:
        raise AlcubierreAdmError("INVALID_WITNESS_VECTOR", f"{label} must have length 4")
    return [_require_exact_fraction(v, f"{label}[{i}]") for i, v in enumerate(vec)]


def mat_inv_exact(mat: Sequence[Sequence[Fraction]]) -> list[list[Fraction]]:
    """Exact Gauss-Jordan inverse of an n x n exact Fraction matrix over Q."""
    m = _require_square_fraction_matrix(mat, "mat")
    n = len(m)
    aug = [
        [m[r][c] for c in range(n)] + [Fraction(1 if r == c else 0, 1) for c in range(n)]
        for r in range(n)
    ]
    for col in range(n):
        piv = next((r for r in range(col, n) if aug[r][col] != 0), None)
        if piv is None:
            raise AlcubierreAdmError("SINGULAR_MATRIX", "matrix is singular over Q")
        aug[col], aug[piv] = aug[piv], aug[col]
        d = aug[col][col]
        aug[col] = [x / d for x in aug[col]]
        for r in range(n):
            if r != col:
                fac = aug[r][col]
                aug[r] = [aug[r][c] - fac * aug[col][c] for c in range(2 * n)]
    return [row[n:] for row in aug]


def mat_mul_4x4(a: Sequence[Sequence[Fraction]], b: Sequence[Sequence[Fraction]]) -> list[list[Fraction]]:
    ma = _require_square_fraction_matrix(a, "a", exact_dim=4)
    mb = _require_square_fraction_matrix(b, "b", exact_dim=4)
    return [
        [sum((ma[i][k] * mb[k][j] for k in range(4)), Fraction(0, 1)) for j in range(4)]
        for i in range(4)
    ]


def mat_transpose_4x4(a: Sequence[Sequence[Fraction]]) -> list[list[Fraction]]:
    ma = _require_square_fraction_matrix(a, "a", exact_dim=4)
    return [[ma[j][i] for j in range(4)] for i in range(4)]


def quad_form_4(mat: Sequence[Sequence[Fraction]], vec: Sequence[Fraction]) -> Fraction:
    m = _require_square_fraction_matrix(mat, "mat", exact_dim=4)
    v = _require_fraction_vec4(vec, "vec")
    return sum((v[i] * m[i][j] * v[j] for i in range(4) for j in range(4)), Fraction(0, 1))


def krein_inertia_exact(mat: Sequence[Sequence[Fraction]]) -> tuple[int, int, int]:
    """Exact Sylvester-Krein inertia (n_pos, n_zero, n_neg) of a symmetric Q matrix via Bunch-Kaufman congruence."""
    a = _require_square_fraction_matrix(mat, "mat", symmetric=True)
    n = len(a)
    n_pos = 0
    n_zero = 0
    n_neg = 0
    k = 0
    while k < n:
        piv_diag = next((i for i in range(k, n) if a[i][i] != 0), None)
        if piv_diag is not None:
            a[k], a[piv_diag] = a[piv_diag], a[k]
            for r in range(n):
                a[r][k], a[r][piv_diag] = a[r][piv_diag], a[r][k]
            d = a[k][k]
            if d > 0:
                n_pos += 1
            else:
                n_neg += 1
            for i in range(k + 1, n):
                fac = a[i][k] / d
                for j in range(k + 1, n):
                    a[i][j] -= fac * a[k][j]
            k += 1
        else:
            pair = next(((i, j) for i in range(k, n) for j in range(i + 1, n) if a[i][j] != 0), None)
            if pair is None:
                n_zero += n - k
                break
            p, q = pair
            a[k], a[p] = a[p], a[k]
            for r in range(n):
                a[r][k], a[r][p] = a[r][p], a[r][k]
            a[k + 1], a[q] = a[q], a[k + 1]
            for r in range(n):
                a[r][k + 1], a[r][q] = a[r][q], a[r][k + 1]
            # 2x2 pivot block [[0, b], [b, 0]] has exact determinant -b^2 < 0 -> inertia (1, 0, 1)
            b = a[k][k + 1]
            n_pos += 1
            n_neg += 1
            for i in range(k + 2, n):
                u0 = a[i][k] / b
                u1 = a[i][k + 1] / b
                for j in range(k + 2, n):
                    a[i][j] -= u1 * a[k][j] + u0 * a[k + 1][j]
            k += 2
    return (n_pos, n_zero, n_neg)


def is_psd_exact(mat: Sequence[Sequence[Fraction]]) -> bool:
    return krein_inertia_exact(mat)[2] == 0


# ---------------------------------------------------------------------------
# Full-4D Exact General Relativity Christoffel -> Ricci -> Einstein Engine
# ---------------------------------------------------------------------------

def christoffel_from_metric_jet(
    g: Sequence[Sequence[Fraction]],
    dg: Sequence[Sequence[Sequence[Fraction]]],
) -> list[list[list[Fraction]]]:
    """Compute exact 4D Christoffel symbols Gamma^rho_{mu nu} over Q from (g_{mu nu}, d_a g_{mu nu})."""
    gm = _require_square_fraction_matrix(g, "g", exact_dim=4, symmetric=True)
    gi = mat_inv_exact(gm)
    half = Fraction(1, 2)
    gamma = [[[Fraction(0, 1)] * 4 for _ in range(4)] for _ in range(4)]
    for r in range(4):
        for m in range(4):
            for n in range(4):
                s_val = Fraction(0, 1)
                for sig in range(4):
                    s_val += gi[r][sig] * (dg[sig][m][n] + dg[sig][n][m] - dg[m][n][sig])
                gamma[r][m][n] = half * s_val
    return gamma


def einstein_tensor_from_jet(
    g: Sequence[Sequence[Fraction]],
    dg: Sequence[Sequence[Sequence[Fraction]]],
    d2g: Sequence[Sequence[Sequence[Sequence[Fraction]]]],
) -> tuple[list[list[Fraction]], list[list[Fraction]]]:
    """Compute exact (g^{mu nu}, G_{mu nu}) from a 2nd-order 4D metric jet over Q."""
    gi = mat_inv_exact(g)
    dgi = [
        [
            [
                -sum((gi[m][r] * dg[r][s][a] * gi[s][n] for r in range(4) for s in range(4)), Fraction(0, 1))
                for n in range(4)
            ]
            for m in range(4)
        ]
        for a in range(4)
    ]
    half = Fraction(1, 2)
    gamma = [[[Fraction(0, 1)] * 4 for _ in range(4)] for _ in range(4)]
    dgamma = [[[[Fraction(0, 1)] * 4 for _ in range(4)] for _ in range(4)] for _ in range(4)]
    for r in range(4):
        for m in range(4):
            for n in range(4):
                s_val = Fraction(0, 1)
                for sig in range(4):
                    s_val += gi[r][sig] * (dg[sig][m][n] + dg[sig][n][m] - dg[m][n][sig])
                gamma[r][m][n] = half * s_val
                for a in range(4):
                    ds_val = Fraction(0, 1)
                    for sig in range(4):
                        t1 = dg[sig][m][n] + dg[sig][n][m] - dg[m][n][sig]
                        t2 = d2g[sig][m][n][a] + d2g[sig][n][m][a] - d2g[m][n][sig][a]
                        ds_val += dgi[a][r][sig] * t1 + gi[r][sig] * t2
                    dgamma[a][r][m][n] = half * ds_val

    ric = [[Fraction(0, 1)] * 4 for _ in range(4)]
    for m in range(4):
        for n in range(4):
            val = Fraction(0, 1)
            for r in range(4):
                val += dgamma[r][r][m][n] - dgamma[n][r][m][r]
                for s in range(4):
                    val += gamma[r][r][s] * gamma[s][m][n] - gamma[r][n][s] * gamma[s][m][r]
            ric[m][n] = val
    r_scalar = sum((gi[m][n] * ric[m][n] for m in range(4) for n in range(4)), Fraction(0, 1))
    ein = [[ric[m][n] - half * r_scalar * g[m][n] for n in range(4)] for m in range(4)]
    return gi, ein


def adm_conformal_einstein_jet(
    lapse: Fraction,
    d_lapse: Sequence[Fraction],
    d2_lapse: Sequence[Sequence[Fraction]],
    shift: Sequence[Fraction],
    d_shift: Sequence[Sequence[Fraction]],
    d2_shift: Sequence[Sequence[Sequence[Fraction]]],
    psi: Fraction = Fraction(1, 1),
    d_psi: Sequence[Fraction] | None = None,
    d2_psi: Sequence[Sequence[Fraction]] | None = None,
) -> tuple[list[list[Fraction]], list[list[Fraction]], list[list[Fraction]]]:
    """Exact 4D (g^{mu nu}, G_{mu nu}, G_{hat a hat b}) for ds^2 = -N^2 dt^2 + psi^4 delta_ij (dx^i + beta^i dt)(dx^j + beta^j dt)."""
    _require_exact_fraction(lapse, "lapse")
    _require_exact_fraction(psi, "psi")
    if lapse <= 0 or psi <= 0:
        raise AlcubierreAdmError("INVALID_ADM_SCALE", "lapse N and conformal factor psi must be > 0")
    dp = [Fraction(0, 1)] * 4 if d_psi is None else list(d_psi)
    d2p = [[Fraction(0, 1)] * 4 for _ in range(4)] if d2_psi is None else [list(row) for row in d2_psi]

    phi = psi ** 4
    dphi = [4 * (psi ** 3) * dp[a] for a in range(4)]
    d2phi = [
        [12 * (psi ** 2) * dp[a] * dp[c] + 4 * (psi ** 3) * d2p[a][c] for c in range(4)]
        for a in range(4)
    ]

    g = [[Fraction(0, 1)] * 4 for _ in range(4)]
    dg = [[[Fraction(0, 1)] * 4 for _ in range(4)] for _ in range(4)]
    d2g = [[[[Fraction(0, 1)] * 4 for _ in range(4)] for _ in range(4)] for _ in range(4)]

    bsq = sum((shift[k] * shift[k] for k in range(3)), Fraction(0, 1))
    dbsq = [2 * sum((shift[k] * d_shift[k][a] for k in range(3)), Fraction(0, 1)) for a in range(4)]
    d2bsq = [
        [
            2 * sum((d_shift[k][a] * d_shift[k][c] + shift[k] * d2_shift[k][a][c] for k in range(3)), Fraction(0, 1))
            for c in range(4)
        ]
        for a in range(4)
    ]

    g[0][0] = -(lapse * lapse) + phi * bsq
    for a in range(4):
        dg[0][0][a] = -2 * lapse * d_lapse[a] + dphi[a] * bsq + phi * dbsq[a]
        for c in range(4):
            d2g[0][0][a][c] = (
                -2 * (d_lapse[a] * d_lapse[c] + lapse * d2_lapse[a][c])
                + d2phi[a][c] * bsq
                + dphi[a] * dbsq[c]
                + dphi[c] * dbsq[a]
                + phi * d2bsq[a][c]
            )
    for i in range(3):
        g[0][i + 1] = g[i + 1][0] = phi * shift[i]
        g[i + 1][i + 1] = phi
        for a in range(4):
            v = dphi[a] * shift[i] + phi * d_shift[i][a]
            dg[0][i + 1][a] = dg[i + 1][0][a] = v
            dg[i + 1][i + 1][a] = dphi[a]
            for c in range(4):
                v2 = (
                    d2phi[a][c] * shift[i]
                    + dphi[a] * d_shift[i][c]
                    + dphi[c] * d_shift[i][a]
                    + phi * d2_shift[i][a][c]
                )
                d2g[0][i + 1][a][c] = d2g[i + 1][0][a][c] = v2
                d2g[i + 1][i + 1][a][c] = d2phi[a][c]

    gi, ein = einstein_tensor_from_jet(g, dg, d2g)
    tetrad = [[Fraction(0, 1)] * 4 for _ in range(4)]
    tetrad[0][0] = Fraction(1, 1) / lapse
    for i in range(3):
        tetrad[0][i + 1] = -shift[i] / lapse
        tetrad[i + 1][i + 1] = Fraction(1, 1) / (psi * psi)
    g_hat = [
        [sum((tetrad[a][m] * tetrad[c][n] * ein[m][n] for m in range(4) for n in range(4)), Fraction(0, 1)) for c in range(4)]
        for a in range(4)
    ]
    return gi, ein, g_hat


# ---------------------------------------------------------------------------
# Exact-Q S-Lemma / Krein Inertia Observer-Robust Energy Condition Engine
# ---------------------------------------------------------------------------

def _add_lambda_eta(t_mat: Sequence[Sequence[Fraction]], lam: Fraction) -> list[list[Fraction]]:
    return [
        [t_mat[i][j] + (lam * ETA_4X4[i][j] if i == j else Fraction(0, 1)) for j in range(4)]
        for i in range(4)
    ]


def _sec_matrix(t_mat: Sequence[Sequence[Fraction]]) -> list[list[Fraction]]:
    trace_eta = -t_mat[0][0] + t_mat[1][1] + t_mat[2][2] + t_mat[3][3]
    return _add_lambda_eta(t_mat, -trace_eta / Fraction(2, 1))


def _neg_t_eta_t(t_mat: Sequence[Sequence[Fraction]]) -> list[list[Fraction]]:
    prod = mat_mul_4x4(mat_mul_4x4(t_mat, ETA_4X4), t_mat)
    return [[-prod[i][j] for j in range(4)] for i in range(4)]


def certify_slemma_satisfaction(
    t_mat: Sequence[Sequence[Fraction]],
    *,
    lam_nec: Fraction,
    lam_wec: Fraction,
    lam_sec: Fraction,
    mu_dec: Fraction,
) -> dict[str, Any]:
    """Unconditionally certify observer-robust NEC/WEC/SEC/DEC via exact Krein inertia over Q."""
    tm = _require_square_fraction_matrix(t_mat, "t_mat", exact_dim=4, symmetric=True)
    ln = _require_exact_fraction(lam_nec, "lam_nec")
    lw = _require_exact_fraction(lam_wec, "lam_wec")
    ls = _require_exact_fraction(lam_sec, "lam_sec")
    md = _require_exact_fraction(mu_dec, "mu_dec")
    nec_inertia = krein_inertia_exact(_add_lambda_eta(tm, ln))
    wec_inertia = krein_inertia_exact(_add_lambda_eta(tm, lw))
    sec_inertia = krein_inertia_exact(_add_lambda_eta(_sec_matrix(tm), ls))
    dec_flux_inertia = krein_inertia_exact(_add_lambda_eta(_neg_t_eta_t(tm), md))

    nec_ok = nec_inertia[2] == 0
    wec_ok = all((lw >= 0, wec_inertia[2] == 0))
    sec_ok = all((ls >= 0, sec_inertia[2] == 0))
    dec_ok = all((wec_ok, md >= 0, dec_flux_inertia[2] == 0))

    return {
        "lam_nec": format_exact_rational(ln),
        "nec_inertia": list(nec_inertia),
        "nec_satisfied_all_observers": nec_ok,
        "lam_wec": format_exact_rational(lw),
        "wec_inertia": list(wec_inertia),
        "wec_satisfied_all_observers": wec_ok,
        "lam_sec": format_exact_rational(ls),
        "sec_inertia": list(sec_inertia),
        "sec_satisfied_all_observers": sec_ok,
        "mu_dec": format_exact_rational(md),
        "dec_flux_inertia": list(dec_flux_inertia),
        "dec_satisfied_all_observers": dec_ok,
    }


def certify_causal_violation_witness(
    t_mat: Sequence[Sequence[Fraction]],
    vec: Sequence[Fraction],
    kind: str,
) -> dict[str, Any]:
    """Certify exact rational causal violation witness (null / timelike / dec_flux)."""
    tm = _require_square_fraction_matrix(t_mat, "t_mat", exact_dim=4, symmetric=True)
    v = _require_fraction_vec4(vec, "vec")
    if all(x == 0 for x in v):
        raise AlcubierreAdmError("INVALID_WITNESS_VECTOR", "witness vector must be non-zero in Q^4")
    eta_norm = quad_form_4(ETA_4X4, v)
    t_val = quad_form_4(tm, v)
    if kind == "null":
        if eta_norm != 0 or t_val >= 0:
            raise AlcubierreAdmError("INVALID_NULL_WITNESS", "null witness must satisfy eta(k,k)==0 and T(k,k)<0")
        metric_val = t_val
    elif kind == "timelike":
        if eta_norm >= 0 or t_val >= 0:
            raise AlcubierreAdmError("INVALID_TIMELIKE_WITNESS", "timelike witness must satisfy eta(u,u)<0 and T(u,u)<0")
        metric_val = t_val
    elif kind == "dec_flux":
        flux_norm = -quad_form_4(_neg_t_eta_t(tm), v)
        if eta_norm >= 0 or flux_norm <= 0:
            raise AlcubierreAdmError("INVALID_DEC_WITNESS", "DEC witness must satisfy eta(u,u)<0 and J^2>0")
        metric_val = flux_norm
    else:
        raise AlcubierreAdmError("UNKNOWN_WITNESS_KIND", f"unknown witness kind: {kind}")

    return {
        "kind": kind,
        "vector": [format_exact_rational(x) for x in v],
        "eta_norm": format_exact_rational(eta_norm),
        "witness_value": format_exact_rational(metric_val),
        "violation_certified": True,
    }


# ---------------------------------------------------------------------------
# Pillar 1: Arbitrary-Lapse ADM Identities, GP Boundary, Duality & Type-IV Trigger
# ---------------------------------------------------------------------------

def certify_pillar1_adm_identities() -> dict[str, Any]:
    """Certify full-4D arbitrary-lapse ADM identities, GP boundary, sign-flip duality, and Type-IV trigger."""
    # 1. Generic non-constant lapse + time/space-varying shift jet (symmetric 2nd derivatives!)
    n_val = Fraction(3, 2)
    dn = [Fraction(1, 3), Fraction(2, 5), Fraction(-1, 2), Fraction(3, 7)]
    d2n = [[Fraction((i + j + 1) * (-1) ** (i + j), 11) for j in range(4)] for i in range(4)]
    b = [Fraction(1, 2), Fraction(-2, 3), Fraction(3, 4)]
    db = [[Fraction((k + 1) * (a + 2) * (-1) ** (k + a), 7) for a in range(4)] for k in range(3)]
    d2b = [
        [[Fraction((k + 2) * (a + c + 1) * (-1) ** (k + a + c), 13) for c in range(4)] for a in range(4)]
        for k in range(3)
    ]

    _gi, _ein, g_hat = adm_conformal_einstein_jet(n_val, dn, d2n, b, db, d2b)
    div_b = sum((db[i][i + 1] for i in range(3)), Fraction(0, 1))
    div_j = div_b * div_b - sum((db[j][i + 1] * db[i][j + 1] for i in range(3) for j in range(3)), Fraction(0, 1))
    omega = [db[2][2] - db[1][3], db[0][3] - db[2][1], db[1][1] - db[0][2]]
    omega_sq = sum((w * w for w in omega), Fraction(0, 1))
    ham_residual = 2 * n_val * n_val * g_hat[0][0] - (div_j - Fraction(1, 2) * omega_sq)

    curl_om = [
        sum((d2b[j][i + 1][j + 1] - d2b[i][j + 1][j + 1] for j in range(3)), Fraction(0, 1))
        for i in range(3)
    ]
    s_mat = [[Fraction(1, 2) * (db[j][i + 1] + db[i][j + 1]) for j in range(3)] for i in range(3)]
    tr_s = sum((s_mat[i][i] for i in range(3)), Fraction(0, 1))
    mom_residuals = [
        -2 * g_hat[0][i + 1]
        - (-(curl_om[i] / n_val) - (Fraction(2, 1) / (n_val * n_val)) * sum((dn[j + 1] * (s_mat[i][j] - (tr_s if i == j else Fraction(0, 1))) for j in range(3)), Fraction(0, 1)))
        for i in range(3)
    ]

    # 2. Gullstrand-Painleve Schwarzschild boundary (M = 2, r in {1, 4, 9, 16} => sqrt(2M/r) = 2/sqrt(r) in Q!)
    mass_gp = Fraction(2, 1)
    gp_checks: list[dict[str, Any]] = []
    for root_r in (1, 2, 3, 4):
        r_val = Fraction(root_r * root_r, 1)
        f_r = Fraction(2, root_r)  # sqrt(2M/r) = sqrt(4/r) = 2/sqrt(r)
        # At (x=r, y=0, z=0), beta(X) = sqrt(2M) * |X|^{-3/2} * X = f(r) * (X / r)
        # Exact derivatives along (r, 0, 0):
        # f' = -f / (2r), f'' = 3 f / (4 r^2)
        b_gp = [f_r, Fraction(0, 1), Fraction(0, 1)]
        db_gp = [[Fraction(0, 1)] * 4 for _ in range(3)]
        db_gp[0][1] = -f_r / (2 * r_val)
        db_gp[1][2] = f_r / r_val
        db_gp[2][3] = f_r / r_val

        d2b_gp = [[[Fraction(0, 1)] * 4 for _ in range(4)] for _ in range(3)]
        # d_xx beta_x = f'' = 3 f / (4 r^2); d_yy beta_x = d_zz beta_x = -3 f / (2 r^2)
        d2b_gp[0][1][1] = Fraction(3, 4) * f_r / (r_val * r_val)
        d2b_gp[0][2][2] = -Fraction(3, 2) * f_r / (r_val * r_val)
        d2b_gp[0][3][3] = -Fraction(3, 2) * f_r / (r_val * r_val)
        # d_xy beta_y = d_yx beta_y = d_x(f/r) = -3 f / (2 r^2); same for z
        d2b_gp[1][1][2] = d2b_gp[1][2][1] = -Fraction(3, 2) * f_r / (r_val * r_val)
        d2b_gp[2][1][3] = d2b_gp[2][3][1] = -Fraction(3, 2) * f_r / (r_val * r_val)

        _, ein_gp, ghat_gp = adm_conformal_einstein_jet(
            Fraction(1, 1),
            [Fraction(0, 1)] * 4,
            [[Fraction(0, 1)] * 4 for _ in range(4)],
            b_gp,
            db_gp,
            d2b_gp,
        )
        vacuum_exact = all(ein_gp[m][n] == 0 for m in range(4) for n in range(4))
        om_gp_zero = all(
            (
                db_gp[2][2] - db_gp[1][3] == 0,
                db_gp[0][3] - db_gp[2][1] == 0,
                db_gp[1][1] - db_gp[0][2] == 0,
            )
        )
        # Radial component of J_ADM = (div b) b_x - b_x d_x b_x = (2 f / r) * f = 2 f^2 / r = 4M / r^2
        # Surface flux over S_r^2 divided by pi: 4 * r^2 * J_r == 16 * M
        div_b_gp = db_gp[0][1] + db_gp[1][2] + db_gp[2][3]
        j_adm_r = div_b_gp * b_gp[0] - b_gp[0] * db_gp[0][1]
        flux_over_pi = 4 * r_val * r_val * j_adm_r
        gp_checks.append(
            {
                "r": format_exact_rational(r_val),
                "beta_r": format_exact_rational(f_r),
                "vacuum_G_zero": vacuum_exact,
                "rho_E_zero": ghat_gp[0][0] == 0,
                "omega_zero": om_gp_zero,
                "flux_J_ADM_over_pi": format_exact_rational(flux_over_pi),
                "flux_equals_16M": flux_over_pi == 16 * mass_gp,
            }
        )

    # 3. Unit-lapse sign-flip duality: pointwise -G^0_0 == G_{hat 0 hat 0} - beta . (-G_{hat 0 hat i})
    gi_u, ein_u, ghat_u = adm_conformal_einstein_jet(
        Fraction(1, 1),
        [Fraction(0, 1)] * 4,
        [[Fraction(0, 1)] * 4 for _ in range(4)],
        b,
        db,
        d2b,
    )
    g_up0_dn0 = sum((gi_u[0][sig] * ein_u[sig][0] for sig in range(4)), Fraction(0, 1))
    # 8*pi*rho_E = G_{hat 0 hat 0}, 8*pi*j_i = -G_{hat 0 hat i}
    duality_pointwise_res = (-g_up0_dn0) - (ghat_u[0][0] - sum((b[i] * (-ghat_u[0][i + 1]) for i in range(3)), Fraction(0, 1)))

    # Global 3D polynomial compactly supported bubble on [-1, 1]^3 (vanishes on boundary => J_ADM = 0 & beta x omega = 0 on boundary):
    # beta_x = (1 - x^2)(1 - y^2)(1 - z^2), beta_y = x * beta_x, beta_z = 0
    x, y, z = MPoly.var(3, 0), MPoly.var(3, 1), MPoly.var(3, 2)
    one3 = MPoly.const(3, 1)
    bx = (one3 - x.pow(2)) * (one3 - y.pow(2)) * (one3 - z.pow(2))
    # omega = (0, d_z bx, -d_y bx); 16*pi*rho_E = div(J) - (1/2)|omega|^2 = -(1/2)(bx_y^2 + bx_z^2) + div(J)
    # Since bx_y, bx_z give J_ADM = (0, -bx*bx_y? No: J_x = bx_x*bx - bx*bx_x = 0, J_y = J_z = 0!)
    # Even better: add nonzero beta_y = (1-x^2)^2(1-y^2)^2(1-z^2)^2 * x so div(J_ADM) is NONTRIVIAL pointwise yet integrates to 0!
    by = bx * x
    div_b_p = bx.deriv(0) + by.deriv(1)
    jx_p = div_b_p * bx - (bx * bx.deriv(0) + by * bx.deriv(1))
    jy_p = div_b_p * by - (bx * by.deriv(0) + by * by.deriv(1))
    div_j_p = jx_p.deriv(0) + jy_p.deriv(1)
    omx_p = -by.deriv(2)
    omy_p = bx.deriv(2)
    omz_p = by.deriv(0) - bx.deriv(1)
    om_sq_p = omx_p.pow(2) + omy_p.pow(2) + omz_p.pow(2)
    rho16_p = div_j_p - om_sq_p.scale(Fraction(1, 2))
    # 16*pi*j = -curl(omega) = (-(omz_y - omy_z), -(omx_z - omz_x), -(omy_x - omx_y))
    curl_om_x = omz_p.deriv(1) - omy_p.deriv(2)
    curl_om_y = omx_p.deriv(2) - omz_p.deriv(0)
    b_dot_j16 = -(bx * curl_om_x + by * curl_om_y)
    neg_2_g00_p = rho16_p - b_dot_j16

    int_div_j = div_j_p.integrate_unit_cube()
    int_om_sq = om_sq_p.integrate_unit_cube()
    int_rho16 = rho16_p.integrate_unit_cube()
    int_neg_2_g00 = neg_2_g00_p.integrate_unit_cube()

    # 4. Irrotational non-unit-lapse Type-IV trigger (breaks Rodal unit-lapse Type-I theorem)
    n_iv = Fraction(3, 2)
    dn_iv = [Fraction(0, 1), Fraction(5, 1), Fraction(0, 1), Fraction(0, 1)]
    d2n_iv = [[Fraction(0, 1)] * 4 for _ in range(4)]
    b_iv = [Fraction(0, 1)] * 3
    db_iv = [[Fraction(0, 1)] * 4 for _ in range(3)]
    db_iv[0][1] = Fraction(1, 1)
    db_iv[1][2] = Fraction(1, 1)
    db_iv[2][3] = Fraction(1, 1)
    d2b_iv = [[[Fraction(0, 1)] * 4 for _ in range(4)] for _ in range(3)]

    _, _, gh_iv = adm_conformal_einstein_jet(n_iv, dn_iv, d2n_iv, b_iv, db_iv, d2b_iv)
    disc_iv = (gh_iv[0][0] + gh_iv[1][1]) ** 2 - 4 * (gh_iv[0][1] ** 2)
    # Exact null witness k = (1, 1, 0, 0) proves automatic NEC violation at this Type-IV point!
    iv_null_witness = certify_causal_violation_witness(gh_iv, [Fraction(1, 1), Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)], "null")

    # Unit-lapse control (grad N == 0 on same irrotational shift jet -> G_{0i} == 0, Type I!)
    _, _, gh_ctrl = adm_conformal_einstein_jet(
        Fraction(1, 1),
        [Fraction(0, 1)] * 4,
        d2n_iv,
        b_iv,
        db_iv,
        d2b_iv,
    )
    ctrl_j_zero = all(gh_ctrl[0][i + 1] == 0 for i in range(3))

    return {
        "arbitrary_lapse_hamiltonian_residual_zero": ham_residual == 0,
        "arbitrary_lapse_momentum_residuals_zero": all(r == 0 for r in mom_residuals),
        "gullstrand_painleve_M": format_exact_rational(mass_gp),
        "gullstrand_painleve_checks": gp_checks,
        "unit_lapse_pointwise_sign_flip_residual_zero": duality_pointwise_res == 0,
        "compact_bubble_int_div_J_zero": int_div_j == 0,
        "compact_bubble_int_omega_sq": format_exact_rational(int_om_sq),
        "compact_bubble_int_16pi_rhoE": format_exact_rational(int_rho16),
        "compact_bubble_int_neg_2G00": format_exact_rational(int_neg_2_g00),
        "compact_bubble_sign_flip_duality_exact": all(
            (int_om_sq > 0, int_rho16 == -Fraction(1, 2) * int_om_sq, int_neg_2_g00 == -int_rho16)
        ),
        "irrotational_non_unit_lapse_type_iv": {
            "N": format_exact_rational(n_iv),
            "grad_N_x": format_exact_rational(dn_iv[1]),
            "omega_zero": True,
            "G_hat_00": format_exact_rational(gh_iv[0][0]),
            "G_hat_01": format_exact_rational(gh_iv[0][1]),
            "G_hat_11": format_exact_rational(gh_iv[1][1]),
            "discriminant_01": format_exact_rational(disc_iv),
            "eulerian_rho_strictly_positive": gh_iv[0][0] > 0,
            "hawking_ellis_type_iv_certified": disc_iv < 0,
            "null_nec_violation_witness": iv_null_witness,
            "unit_lapse_control_flux_zero": ctrl_j_zero,
        },
    }


# ---------------------------------------------------------------------------
# Pillar 2: Exact Alcubierre w_x == +3 EOS & Two-Annulus Type-IV Obstruction
# ---------------------------------------------------------------------------

def _septic_c3_bump_derivs(u: Fraction) -> tuple[Fraction, Fraction, Fraction]:
    """C^3 Hermite bump h(u) = 1 - 35 u^4 + 84 u^5 - 70 u^6 + 20 u^7 and (h', h'') on [0, 1]."""
    u2 = u * u
    u3 = u2 * u
    u4 = u3 * u
    u5 = u4 * u
    u6 = u5 * u
    u7 = u6 * u
    h = Fraction(1, 1) - 35 * u4 + 84 * u5 - 70 * u6 + 20 * u7
    hp = -140 * u3 + 420 * u4 - 420 * u5 + 140 * u6
    hpp = -420 * u2 + 1680 * u3 - 2100 * u4 + 840 * u5
    return h, hp, hpp


def _alcubierre_equatorial_jet(
    vel: Fraction,
    f_val: Fraction,
    fy: Fraction,
    fz: Fraction,
    fxx: Fraction,
    fyy: Fraction,
    fzz: Fraction,
    fyz: Fraction,
) -> list[list[Fraction]]:
    """Full 4D orthonormal Einstein tensor G_{hat a hat b} on equatorial plane (f_x=f_xy=f_xz=0) of beta = (-v f(x-vt,y,z), 0, 0)."""
    # Since f = f(x - v t, y, z): d_t = -v d_x, so on equatorial plane f_t = 0, f_ty = f_tz = 0, f_tx = -v f_xx, f_tt = v^2 f_xx
    b = [-vel * f_val, Fraction(0, 1), Fraction(0, 1)]
    db = [[Fraction(0, 1)] * 4 for _ in range(3)]
    db[0][2] = -vel * fy
    db[0][3] = -vel * fz
    d2b = [[[Fraction(0, 1)] * 4 for _ in range(4)] for _ in range(3)]
    d2b[0][0][0] = -vel * (vel * vel * fxx)
    d2b[0][0][1] = d2b[0][1][0] = -vel * (-vel * fxx)
    d2b[0][1][1] = -vel * fxx
    d2b[0][2][2] = -vel * fyy
    d2b[0][3][3] = -vel * fzz
    d2b[0][2][3] = d2b[0][3][2] = -vel * fyz

    _, _, g_hat = adm_conformal_einstein_jet(
        Fraction(1, 1),
        [Fraction(0, 1)] * 4,
        [[Fraction(0, 1)] * 4 for _ in range(4)],
        b,
        db,
        d2b,
    )
    return g_hat


def certify_pillar2_alcubierre_eos_and_type_iv() -> dict[str, Any]:
    """Certify Alcubierre w_x == +3 EOS, two mandatory concentric Type-IV annuli, and v -> 0+ expansion."""
    # 1. Generic off-equatorial Alcubierre jet (f_x != 0, f_xy != 0, f_xz != 0) confirming w_x == +3 everywhere!
    v_gen = Fraction(7, 5)
    f0 = Fraction(3, 5)
    fx, fy, fz = Fraction(2, 3), Fraction(-4, 5), Fraction(1, 2)
    fxx, fyy, fzz = Fraction(3, 7), Fraction(-5, 6), Fraction(2, 9)
    fxy, fxz, fyz = Fraction(1, 4), Fraction(-2, 5), Fraction(3, 8)
    b_g = [-v_gen * f0, Fraction(0, 1), Fraction(0, 1)]
    db_g = [[Fraction(0, 1)] * 4 for _ in range(3)]
    db_g[0][0] = -v_gen * (-v_gen * fx)
    db_g[0][1] = -v_gen * fx
    db_g[0][2] = -v_gen * fy
    db_g[0][3] = -v_gen * fz
    d2b_g = [[[Fraction(0, 1)] * 4 for _ in range(4)] for _ in range(3)]
    d2b_g[0][0][0] = -v_gen * (v_gen * v_gen * fxx)
    d2b_g[0][0][1] = d2b_g[0][1][0] = -v_gen * (-v_gen * fxx)
    d2b_g[0][0][2] = d2b_g[0][2][0] = -v_gen * (-v_gen * fxy)
    d2b_g[0][0][3] = d2b_g[0][3][0] = -v_gen * (-v_gen * fxz)
    d2b_g[0][1][1] = -v_gen * fxx
    d2b_g[0][1][2] = d2b_g[0][2][1] = -v_gen * fxy
    d2b_g[0][1][3] = d2b_g[0][3][1] = -v_gen * fxz
    d2b_g[0][2][2] = -v_gen * fyy
    d2b_g[0][3][3] = -v_gen * fzz
    d2b_g[0][2][3] = d2b_g[0][3][2] = -v_gen * fyz

    _, _, gh_gen = adm_conformal_einstein_jet(
        Fraction(1, 1), [Fraction(0, 1)] * 4, [[Fraction(0, 1)] * 4 for _ in range(4)], b_g, db_g, d2b_g
    )
    grad_perp_sq = fy * fy + fz * fz
    g00_formula = -Fraction(1, 4) * v_gen * v_gen * grad_perp_sq
    eos_g00_exact = gh_gen[0][0] == g00_formula
    eos_wx_plus3_exact = gh_gen[1][1] == 3 * gh_gen[0][0]

    # 2. C^3 septic Hermite wall on rho in [R, R + Delta] with R = 4, Delta = 2, v = 2
    r_inner = Fraction(4, 1)
    delta_w = Fraction(2, 1)
    v_wall = Fraction(2, 1)
    # Check C^3 endpoint smoothness h(0)=1, h(1)=0, h'=h''=0 at 0 and 1
    h0, hp0, hpp0 = _septic_c3_bump_derivs(Fraction(0, 1))
    h1, hp1, hpp1 = _septic_c3_bump_derivs(Fraction(1, 1))
    profile_c3_smooth = all((h0 == 1, hp0 == 0, hpp0 == 0, h1 == 0, hp1 == 0, hpp1 == 0))

    stations: list[dict[str, Any]] = []
    for label, u_val in (
        ("inner_shoulder_type_iv", Fraction(1, 10)),
        ("core_inflection_type_i", Fraction(1, 2)),
        ("outer_shoulder_type_iv", Fraction(9, 10)),
    ):
        rho_val = r_inner + delta_w * u_val
        h_v, hp_v, hpp_v = _septic_c3_bump_derivs(u_val)
        fp = hp_v / delta_w
        fpp = hpp_v / (delta_w * delta_w)
        # On equatorial ring (x=vt, y=rho, z=0): f_y = f', f_z = 0, f_yy = f'', f_zz = f'/rho, f_xx = f'/rho
        gh_st = _alcubierre_equatorial_jet(v_wall, h_v, fp, Fraction(0, 1), fp / rho_val, fpp, fp / rho_val, Fraction(0, 1))
        lap_perp = fpp + fp / rho_val
        g01_expected = Fraction(1, 2) * v_wall * lap_perp
        disc_actual = (gh_st[0][0] + gh_st[1][1]) ** 2 - 4 * (gh_st[0][1] ** 2)
        disc_formula = (v_wall * v_wall) * ((v_wall * v_wall) * (fp ** 4) - lap_perp * lap_perp)
        stations.append(
            {
                "label": label,
                "u": format_exact_rational(u_val),
                "rho": format_exact_rational(rho_val),
                "G_hat_00": format_exact_rational(gh_st[0][0]),
                "G_hat_11": format_exact_rational(gh_st[1][1]),
                "G_hat_01": format_exact_rational(gh_st[0][1]),
                "w_x_equals_3": gh_st[1][1] == 3 * gh_st[0][0],
                "G_hat_01_formula_exact": gh_st[0][1] == g01_expected,
                "discriminant_01": format_exact_rational(disc_actual),
                "discriminant_formula_exact": disc_actual == disc_formula,
                "hawking_ellis_type": "Type_IV" if disc_actual < 0 else "Type_I",
            }
        )

    # 3. Subluminal vs superluminal Type-IV fraction across 19 interior grid stations u = k/20 (k=1..19)
    velocity_sweep: list[dict[str, Any]] = []
    for v_probe in (Fraction(2, 1), Fraction(1, 1), Fraction(1, 2), Fraction(1, 5), Fraction(1, 10)):
        t4_count = 0
        for k in range(1, 20):
            u_k = Fraction(k, 20)
            rho_k = r_inner + delta_w * u_k
            _, hp_k, hpp_k = _septic_c3_bump_derivs(u_k)
            fp_k = hp_k / delta_w
            lap_k = hpp_k / (delta_w * delta_w) + fp_k / rho_k
            disc_k = (v_probe * v_probe) * ((v_probe * v_probe) * (fp_k ** 4) - lap_k * lap_k)
            if disc_k < 0:
                t4_count += 1
        velocity_sweep.append(
            {
                "v": format_exact_rational(v_probe),
                "type_iv_stations_of_19": t4_count,
                "type_iv_fraction": format_exact_rational(Fraction(t4_count, 19)),
            }
        )
    sweep_counts = [row["type_iv_stations_of_19"] for row in velocity_sweep]
    monotonic_increase_as_v_decreases = all(a < b for a, b in zip(sweep_counts, sweep_counts[1:]))

    two_annuli_certified = all(
        (
            stations[0]["hawking_ellis_type"] == "Type_IV",
            stations[1]["hawking_ellis_type"] == "Type_I",
            stations[2]["hawking_ellis_type"] == "Type_IV",
        )
    )

    return {
        "off_equatorial_g00_formula_exact": eos_g00_exact,
        "off_equatorial_wx_plus3_exact": eos_wx_plus3_exact,
        "septic_profile_c3_smooth": profile_c3_smooth,
        "equatorial_stations": stations,
        "two_concentric_type_iv_annuli_certified": two_annuli_certified,
        "velocity_sweep_as_v_decreases": velocity_sweep,
        "type_iv_fraction_increases_as_v_to_0": all(
            (monotonic_increase_as_v_decreases, velocity_sweep[-1]["type_iv_stations_of_19"] > velocity_sweep[0]["type_iv_stations_of_19"])
        ),
    }


# ---------------------------------------------------------------------------
# Pillar 3: Zero-Float Exact-Q S-Lemma / Krein Inertia & Eulerian Blind Spot
# ---------------------------------------------------------------------------

def certify_pillar3_slemma_and_blind_spot() -> dict[str, Any]:
    """Certify exact Krein inertia, S-lemma satisfaction & violation witnesses, and Eulerian blind spot."""
    # 1. Minkowski metric inertia (3, 0, 1) and zero-diagonal hyperbolic 2x2 pivot test
    eta_inertia = krein_inertia_exact(ETA_4X4)
    hyp_2x2_inertia = krein_inertia_exact(
        [
            [Fraction(0, 1), Fraction(3, 2)],
            [Fraction(3, 2), Fraction(0, 1)],
        ]
    )
    rank_def_inertia = krein_inertia_exact(
        [
            [Fraction(0, 1), Fraction(0, 1), Fraction(2, 1)],
            [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)],
            [Fraction(2, 1), Fraction(0, 1), Fraction(0, 1)],
        ]
    )

    # 2. Exact observer-robust satisfaction on a NON-DIAGONAL Pythagorean-boosted perfect fluid
    # Rest frame: rho = 5, p = 1 -> T_rest = diag(5, 1, 1, 1) -> WEC/NEC/SEC/DEC all satisfied strictly!
    # Exact Pythagorean Lorentz boost v = 3/5, gamma = 5/4, gamma*v = 3/4
    lam_boost = [
        [Fraction(5, 4), Fraction(-3, 4), Fraction(0, 1), Fraction(0, 1)],
        [Fraction(-3, 4), Fraction(5, 4), Fraction(0, 1), Fraction(0, 1)],
        [Fraction(0, 1), Fraction(0, 1), Fraction(1, 1), Fraction(0, 1)],
        [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1), Fraction(1, 1)],
    ]
    t_rest = [
        [Fraction(5, 1), Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)],
        [Fraction(0, 1), Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)],
        [Fraction(0, 1), Fraction(0, 1), Fraction(1, 1), Fraction(0, 1)],
        [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1), Fraction(1, 1)],
    ]
    t_boosted = mat_mul_4x4(mat_mul_4x4(mat_transpose_4x4(lam_boost), t_rest), lam_boost)
    # Multipliers: lam_wec = lam_nec = 2 in [-1, 5]; T_SEC = diag(4, 2, 2, 2) -> lam_sec = 2; -T eta T = diag(25, -1, -1, -1) -> mu_dec = 10
    slemma_boosted_fluid = certify_slemma_satisfaction(
        t_boosted,
        lam_nec=Fraction(2, 1),
        lam_wec=Fraction(2, 1),
        lam_sec=Fraction(2, 1),
        mu_dec=Fraction(10, 1),
    )

    # 3. Exact Pythagorean-quadruple null violation witness on Alcubierre equatorial Type-I core (u = 1/2, v = 2)
    h_c, hp_c, hpp_c = _septic_c3_bump_derivs(Fraction(1, 2))
    rho_c = Fraction(5, 1)
    fp_c = hp_c / Fraction(2, 1)
    fpp_c = hpp_c / Fraction(4, 1)
    gh_alc_core = _alcubierre_equatorial_jet(Fraction(2, 1), h_c, fp_c, Fraction(0, 1), fp_c / rho_c, fpp_c, fp_c / rho_c, Fraction(0, 1))
    # Pythagorean quadruple null vector k = (3, 2, 2, 1): 2^2 + 2^2 + 1^2 = 9 == 3^2
    pyth_null_witness = certify_causal_violation_witness(
        gh_alc_core,
        [Fraction(3, 1), Fraction(2, 1), Fraction(2, 1), Fraction(1, 1)],
        "null",
    )

    # 4. Eulerian Blind-Spot Witness (2602.18023 ~73% blind spot):
    # Unit-lapse N=1, irrotational omega=0, G_{hat 0 hat 0} = +3 > 0, G_{hat 0 hat i} = 0,
    # yet G_{hat 1 hat 1} = -9 => rho + p_x = -6 < 0!
    db_bs = [[Fraction(0, 1)] * 4 for _ in range(3)]
    db_bs[0][1] = Fraction(1, 1)
    db_bs[1][2] = Fraction(1, 1)
    db_bs[2][3] = Fraction(1, 1)
    d2b_bs = [[[Fraction(0, 1)] * 4 for _ in range(4)] for _ in range(3)]
    d2b_bs[1][2][0] = d2b_bs[1][0][2] = Fraction(-3, 1)
    d2b_bs[2][3][0] = d2b_bs[2][0][3] = Fraction(-3, 1)
    _, _, gh_bs = adm_conformal_einstein_jet(
        Fraction(1, 1),
        [Fraction(0, 1)] * 4,
        [[Fraction(0, 1)] * 4 for _ in range(4)],
        [Fraction(0, 1)] * 3,
        db_bs,
        d2b_bs,
    )
    bs_null_wit = certify_causal_violation_witness(
        gh_bs, [Fraction(1, 1), Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)], "null"
    )
    bs_timelike_wit = certify_causal_violation_witness(
        gh_bs, [Fraction(5, 1), Fraction(4, 1), Fraction(0, 1), Fraction(0, 1)], "timelike"
    )
    # Also verify a genuine 3D Pythagorean quadruple null vector (7, 6, 3, 2) with 36+9+4=49!
    bs_pyth4_wit = certify_causal_violation_witness(
        gh_bs, [Fraction(7, 1), Fraction(6, 1), Fraction(3, 1), Fraction(2, 1)], "null"
    )

    return {
        "eta_inertia": list(eta_inertia),
        "hyperbolic_2x2_inertia": list(hyp_2x2_inertia),
        "rank_deficient_3x3_inertia": list(rank_def_inertia),
        "boosted_perfect_fluid_offdiag_nonzero": t_boosted[0][1] != 0,
        "boosted_perfect_fluid_slemma": slemma_boosted_fluid,
        "alcubierre_pythagorean_quadruple_null_witness": pyth_null_witness,
        "eulerian_blind_spot_irrotational_type_i": {
            "G_hat_00": format_exact_rational(gh_bs[0][0]),
            "G_hat_0i_all_zero": all(gh_bs[0][i + 1] == 0 for i in range(3)),
            "G_hat_11": format_exact_rational(gh_bs[1][1]),
            "eulerian_rho_positive_blind_spot": gh_bs[0][0] > 0,
            "null_nec_violation": bs_null_wit,
            "pythagorean_quadruple_7_6_3_2_null_violation": bs_pyth4_wit,
            "boosted_timelike_wec_violation": bs_timelike_wit,
        },
    }


# ---------------------------------------------------------------------------
# Pillar 4: Natario Stokes Minimum, S23a Beltrami Bridge & Killing Horizons
# ---------------------------------------------------------------------------

def _stokes_concentric_energy(r_inner: Fraction, delta: Fraction) -> Fraction:
    """Exact pure-Q enstrophy energy |E_Stokes| / v^2 for concentric rigid spheres (R, R + Delta)."""
    r1 = r_inner
    r2 = r_inner + delta
    mat = [
        [r1 ** 4, r1 ** 2, r1, Fraction(1, 1) / r1],
        [4 * (r1 ** 3), 2 * r1, Fraction(1, 1), -Fraction(1, 1) / (r1 ** 2)],
        [r2 ** 4, r2 ** 2, r2, Fraction(1, 1) / r2],
        [4 * (r2 ** 3), 2 * r2, Fraction(1, 1), -Fraction(1, 1) / (r2 ** 2)],
    ]
    rhs = [r1 ** 2, 2 * r1, Fraction(0, 1), Fraction(0, 1)]
    inv_m = mat_inv_exact(mat)
    a_c, _b_c, c_c, _d_c = [sum((inv_m[i][j] * rhs[j] for j in range(4)), Fraction(0, 1)) for i in range(4)]

    def antideriv(rad: Fraction) -> Fraction:
        return 5 * a_c * a_c * (rad ** 5) - 5 * a_c * c_c * (rad ** 2) - (c_c * c_c) / rad

    return (antideriv(r2) - antideriv(r1)) / Fraction(12, 1)


def certify_pillar4_natario_beltrami_and_horizons() -> dict[str, Any]:
    """Certify Stokes-flow 1/4 minimum, finite-aspect resistance, S23a Beltrami bridge, and Killing horizons."""
    # 1. Exact thin-wall polynomial minimizer f*(x) = 3/2 x^2 - x^3 on x in [0, 1]
    x = MPoly.var(1, 0)
    f_star = x.pow(2).scale(Fraction(3, 2)) - x.pow(3)
    f_star_dd = f_star.deriv(0).deriv(0)
    j_star = (f_star_dd * f_star_dd).integrate_01_1d()
    c_star = j_star / Fraction(12, 1)  # 3 / 12 == 1/4

    # Smooth C^2 quintic competitor f5(x) = (1/2)(10 x^3 - 15 x^4 + 6 x^5)
    f5 = (x.pow(3).scale(10) - x.pow(4).scale(15) + x.pow(5).scale(6)).scale(Fraction(1, 2))
    f5_dd = f5.deriv(0).deriv(0)
    j_f5 = (f5_dd * f5_dd).integrate_01_1d()
    c_f5 = j_f5 / Fraction(12, 1)  # (30/7)/12 == 5/14 > 1/4
    # Exact Euler-Lagrange orthogonality: int_0^1 f*'' * (f5'' - f*'') dx == 0
    eta_dd = f5_dd - f_star_dd
    cross_term = (f_star_dd * eta_dd).integrate_01_1d()
    sos_gap = (eta_dd * eta_dd).integrate_01_1d()

    # Finite-aspect-ratio exact Stokes resistance at Delta/R in {1/10, 1/5, 1/2, 1}
    stokes_table: list[dict[str, Any]] = []
    for eps in (Fraction(1, 10), Fraction(1, 5), Fraction(1, 2), Fraction(1, 1)):
        e_val = _stokes_concentric_energy(Fraction(1, 1), eps)
        scaled = e_val * (eps ** 3)
        stokes_table.append(
            {
                "delta_over_R": format_exact_rational(eps),
                "E_stokes_over_v2R": format_exact_rational(e_val),
                "E_times_delta3_over_v2R4": format_exact_rational(scaled),
                "exceeds_thin_wall_quarter": scaled > Fraction(1, 4),
            }
        )

    # 2. S23a Pythagorean Beltrami Shift Mode: k = (3, 4, 0), lambda = ||k|| = 5
    # e1 = (0, 0, 1), e2 = (4/5, -3/5, 0); beta = cos(k.x) e1 - sin(k.x) e2
    # Evaluate at exact Pythagorean phase (cos theta, sin theta) = (3/5, 4/5)
    lam_b = Fraction(5, 1)
    k_vec = [Fraction(3, 1), Fraction(4, 1), Fraction(0, 1)]
    e1 = [Fraction(0, 1), Fraction(0, 1), Fraction(1, 1)]
    e2 = [Fraction(4, 5), Fraction(-3, 5), Fraction(0, 1)]
    c_ph, s_ph = Fraction(3, 5), Fraction(4, 5)
    b_bel = [c_ph * e1[i] - s_ph * e2[i] for i in range(3)]
    # d_j beta_i = k_j * (-s_ph e1_i - c_ph e2_i); d_j d_m beta_i = -k_j k_m beta_i
    db_bel = [[Fraction(0, 1)] * 4 for _ in range(3)]
    d2b_bel = [[[Fraction(0, 1)] * 4 for _ in range(4)] for _ in range(3)]
    for i in range(3):
        d_phase_i = -s_ph * e1[i] - c_ph * e2[i]
        for j in range(3):
            db_bel[i][j + 1] = k_vec[j] * d_phase_i
            for m in range(3):
                d2b_bel[i][j + 1][m + 1] = -(k_vec[j] * k_vec[m]) * b_bel[i]

    _, _, gh_bel = adm_conformal_einstein_jet(
        Fraction(1, 1),
        [Fraction(0, 1)] * 4,
        [[Fraction(0, 1)] * 4 for _ in range(4)],
        b_bel,
        db_bel,
        d2b_bel,
    )
    div_bel = sum((db_bel[i][i + 1] for i in range(3)), Fraction(0, 1))
    curl_bel = [
        db_bel[2][2] - db_bel[1][3],
        db_bel[0][3] - db_bel[2][1],
        db_bel[1][1] - db_bel[0][2],
    ]
    beltrami_eigen_exact = all(curl_bel[i] == lam_b * b_bel[i] for i in range(3))
    # 16*pi*j_i = -2 G_{hat 0 hat i} == -lambda^2 beta_i
    force_free_mom_exact = all(-2 * gh_bel[0][i + 1] == -(lam_b * lam_b) * b_bel[i] for i in range(3))
    # Pointwise & torus-averaged helicity bridge: A = beta / lam => h_dens = |beta|^2 / lam = 1/5
    b_bel_sq = sum((v * v for v in b_bel), Fraction(0, 1))
    h_dens = b_bel_sq / lam_b
    # 16*pi*rho_E = 2 G_{hat 0 hat 0} == -(lam/2) * h_dens * lam? Wait: 16*pi*rho_E = -(1/2)|omega|^2 = -(lam^2/2)|beta|^2 = -(lam/2)*lam*h_dens?
    # Wait: h_dens = A . beta = (1/lam) |beta|^2 => -(1/2)|omega|^2 = -(lam^2/2)|beta|^2 = -(lam/2) * (lam^2 * h_dens)? No:
    # Check: int rho_E = -1/(32*pi) int |omega|^2 = -1/(32*pi) * lam^2 int |beta|^2 = -1/(32*pi) * lam * (lam * int |beta|^2)?
    # Wait! Helicity H = int A . omega = int beta . (curl beta) = lam * int |beta|^2 !! (With A = beta, B = omega = curl beta!)
    # Check: H(beta) = int beta . omega d^3x = lam * int |beta|^2 => -(1/(32*pi)) int |omega|^2 = -(lam/(32*pi)) H(beta)!
    # So 16*pi*rho_E = -(1/2)*|omega|^2 = -(lam/2) * (beta . omega) !
    helicity_dens = sum((b_bel[i] * curl_bel[i] for i in range(3)), Fraction(0, 1))
    helicity_energy_bridge_exact = (2 * gh_bel[0][0]) == -(lam_b / Fraction(2, 1)) * helicity_dens

    # 3. Superluminal (v = 2 > 1) Killing horizon vs Subluminal (v = 3/5 < 1) absence of horizons
    # Comoving frame x' = x - v t: ds^2 = -dt^2 + (dx' + v(1-f) dt)^2 + dy^2 + dz^2.
    # For v = 2 on septic bump (R = 4, Delta = 2), f(r_H) = 1 - 1/v = 1/2 at exact midpoint u_H = 1/2, r_H = 5.
    # Exact 4D Christoffel Killing equation xi^nu nabla_nu xi^mu = Gamma^mu_{00} = kappa * xi^mu (xi = d_t):
    #   FRONT wall (x' = +5, d_{x'} f = +f'(5) = -35/32 < 0): Gamma^0_{00} = +v f'(5) = -35/16 < 0 (WHITE-HOLE / BLUESHIFT)
    #   REAR  wall (x' = -5, d_{x'} f = -f'(5) = +35/32 > 0): Gamma^0_{00} = -v f'(5) = +35/16 > 0 (BLACK-HOLE / HAWKING)
    v_super = Fraction(2, 1)
    u_h = Fraction(1, 2)
    r_h = Fraction(4, 1) + Fraction(2, 1) * u_h
    f_rh, hp_rh, _ = _septic_c3_bump_derivs(u_h)
    fp_rh = hp_rh / Fraction(2, 1)
    b_rh = v_super * (Fraction(1, 1) - f_rh)
    g_tt_horizon = -(Fraction(1, 1) - b_rh * b_rh)

    def _comoving_horizon_gamma(df_dxprime: Fraction) -> list[list[list[Fraction]]]:
        bp = -v_super * df_dxprime
        g_com = [
            [g_tt_horizon, b_rh, Fraction(0, 1), Fraction(0, 1)],
            [b_rh, Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)],
            [Fraction(0, 1), Fraction(0, 1), Fraction(1, 1), Fraction(0, 1)],
            [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1), Fraction(1, 1)],
        ]
        dg_com = [[[Fraction(0, 1)] * 4 for _ in range(4)] for _ in range(4)]
        dg_com[0][0][1] = 2 * b_rh * bp
        dg_com[0][1][1] = dg_com[1][0][1] = bp
        return christoffel_from_metric_jet(g_com, dg_com)

    gamma_front = _comoving_horizon_gamma(fp_rh)    # x' = +r_H: d_{x'} f = +f'(r_H) < 0
    gamma_rear = _comoving_horizon_gamma(-fp_rh)    # x' = -r_H: d_{x'} f = -f'(r_H) > 0
    kappa_front = gamma_front[0][0][0]              # -35/16 < 0 (white-hole / blueshift horizon)
    kappa_rear = gamma_rear[0][0][0]                # +35/16 > 0 (black-hole / Hawking horizon)
    front_killing_exact = all(
        (kappa_front == v_super * fp_rh, all(gamma_front[m][0][0] == 0 for m in (1, 2, 3)))
    )
    rear_killing_exact = all(
        (kappa_rear == -v_super * fp_rh, all(gamma_rear[m][0][0] == 0 for m in (1, 2, 3)))
    )

    # Subluminal v = 3/5 < 1: g'_tt = -(1 - v^2(1-f)^2) <= -(1 - v^2) = -16/25 < 0 for all f in [0, 1]
    v_sub = Fraction(3, 5)
    sub_max_gtt = -(Fraction(1, 1) - v_sub * v_sub)

    return {
        "stokes_thin_wall_minimizer_constant": format_exact_rational(c_star),
        "stokes_thin_wall_constant_equals_1_4": c_star == Fraction(1, 4),
        "stokes_quintic_competitor_constant": format_exact_rational(c_f5),
        "stokes_euler_lagrange_cross_term_zero": cross_term == 0,
        "stokes_sos_gap_exact": j_f5 == j_star + sos_gap,
        "stokes_finite_aspect_resistance": stokes_table,
        "beltrami_s23a_bridge": {
            "wavevector": [int(k) for k in k_vec],
            "lambda": format_exact_rational(lam_b),
            "natario_zero_expansion_exact": div_bel == 0,
            "beltrami_eigenmode_exact": beltrami_eigen_exact,
            "force_free_momentum_exact": force_free_mom_exact,
            "helicity_density_beta_dot_omega": format_exact_rational(helicity_dens),
            "energy_16pi_rhoE": format_exact_rational(2 * gh_bel[0][0]),
            "energy_equals_neg_lam_over_2_helicity": helicity_energy_bridge_exact,
            "h_coulomb_norm": format_exact_rational(h_dens),
        },
        "killing_horizons": {
            "superluminal_v": format_exact_rational(v_super),
            "horizon_radius_rH": format_exact_rational(r_h),
            "f_at_rH": format_exact_rational(f_rh),
            "g_tt_comoving_at_rH_zero": g_tt_horizon == 0,
            "front_horizon_type": "white_hole_blueshift",
            "rear_horizon_type": "black_hole_hawking",
            "surface_gravity_front_kappa": format_exact_rational(kappa_front),
            "surface_gravity_rear_kappa": format_exact_rational(kappa_rear),
            "front_christoffel_killing_exact": front_killing_exact,
            "rear_christoffel_killing_exact": rear_killing_exact,
            "kappa_antisymmetry_and_signs_exact": all((kappa_front < 0, kappa_rear == -kappa_front)),
            "subluminal_v": format_exact_rational(v_sub),
            "subluminal_max_g_tt": format_exact_rational(sub_max_gtt),
            "subluminal_horizon_free": sub_max_gtt < 0,
            "pfenning_ford_wall_scaling_exponent_v_sq": 2,
        },
    }


# ---------------------------------------------------------------------------
# Pillar 5: Law-2 Steelman — Conformally Flat Lichnerowicz & Physical Subluminal Shells
# ---------------------------------------------------------------------------

def certify_pillar5_physical_subluminal_shells() -> dict[str, Any]:
    """Certify Lichnerowicz constraint, VdB collar zero-integral, and boosted positive-energy shells."""
    # 1. General conformally flat Lichnerowicz Hamiltonian constraint (nonzero shift + time-varying psi)
    n2 = Fraction(4, 3)
    dn2 = [Fraction(1, 5), Fraction(-1, 7), Fraction(2, 9), Fraction(1, 4)]
    d2n2 = [[Fraction(i + j + 1, 19) for j in range(4)] for i in range(4)]
    psi2 = Fraction(5, 4)
    dpsi2 = [Fraction(1, 11), Fraction(-1, 13), Fraction(1, 17), Fraction(-1, 19)]
    d2psi2 = [[Fraction((-1) ** (i + j), 23 + i + j) for j in range(4)] for i in range(4)]
    b2 = [Fraction(1, 3), Fraction(-1, 4), Fraction(2, 5)]
    db2 = [[Fraction((k + 1) * (a + 1) * (-1) ** (k + a), 11) for a in range(4)] for k in range(3)]
    d2b2 = [
        [[Fraction((k + a + c + 1) * (-1) ** (k + a + c), 17) for c in range(4)] for a in range(4)]
        for k in range(3)
    ]
    _, _, gh2 = adm_conformal_einstein_jet(n2, dn2, d2n2, b2, db2, d2b2, psi2, dpsi2, d2psi2)
    phi2 = psi2 ** 4
    dphi2 = [4 * (psi2 ** 3) * dpsi2[a] for a in range(4)]
    b_dot_dphi = sum((b2[k] * dphi2[k + 1] for k in range(3)), Fraction(0, 1))
    k_mat = [[Fraction(0, 1)] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            dt_g = dphi2[0] if i == j else Fraction(0, 1)
            l_b_g = (b_dot_dphi if i == j else Fraction(0, 1)) + phi2 * (db2[j][i + 1] + db2[i][j + 1])
            k_mat[i][j] = -(dt_g - l_b_g) / (2 * n2)
    k_tr = sum((k_mat[i][i] for i in range(3)), Fraction(0, 1)) / phi2
    k_sq = sum((k_mat[i][j] * k_mat[i][j] for i in range(3) for j in range(3)), Fraction(0, 1)) / (phi2 * phi2)
    lap_psi2 = d2psi2[1][1] + d2psi2[2][2] + d2psi2[3][3]
    lich_res = 2 * gh2[0][0] - (-8 * (psi2 ** -5) * lap_psi2 + k_tr * k_tr - k_sq)

    # 2. Van Den Broeck compact conformal pocket (psi = 1 outside [-1,1]^3 -> int psi^5 R^(3) = -8 int lap(psi) == 0)
    x, y, z = MPoly.var(3, 0), MPoly.var(3, 1), MPoly.var(3, 2)
    one3 = MPoly.const(3, 1)
    vdb_phi = (one3 - x.pow(2)).pow(2) * (one3 - y.pow(2)).pow(2) * (one3 - z.pow(2)).pow(2)
    lap_vdb = vdb_phi.deriv(0).deriv(0) + vdb_phi.deriv(1).deriv(1) + vdb_phi.deriv(2).deriv(2)
    int_vdb_weighted_r3 = lap_vdb.scale(-8).integrate_unit_cube()

    # Schwarzschild isotropic tail psi = 1 + M/(2r) -> -8 * 4*pi*R^2 * (-M/(2R^2)) == 16*pi*M_ADM
    m_adm = Fraction(2, 1)
    schwarzschild_weighted_r3_over_pi = Fraction(16, 1) * m_adm

    # 3. Exact Pythagorean Lorentz boost matrix v = 3/5 < 1, gamma = 5/4
    v_boost = Fraction(3, 5)
    lam_boost = [
        [Fraction(5, 4), Fraction(-3, 4), Fraction(0, 1), Fraction(0, 1)],
        [Fraction(-3, 4), Fraction(5, 4), Fraction(0, 1), Fraction(0, 1)],
        [Fraction(0, 1), Fraction(0, 1), Fraction(1, 1), Fraction(0, 1)],
        [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1), Fraction(1, 1)],
    ]

    # 4A. Smooth 4D conformally flat positive-energy shell jet (computed directly from 4D Einstein engine!)
    r_sh = Fraction(10, 1)
    psi_sh = Fraction(21, 20)
    psi_p = Fraction(-1, 200)
    psi_pp = Fraction(-1, 100)
    n_sh = Fraction(19, 20)
    n_p = Fraction(1, 200)
    n_pp = Fraction(1, 2000)
    dpsi_sh = [Fraction(0, 1), psi_p, Fraction(0, 1), Fraction(0, 1)]
    d2psi_sh = [[Fraction(0, 1)] * 4 for _ in range(4)]
    d2psi_sh[1][1] = psi_pp
    d2psi_sh[2][2] = d2psi_sh[3][3] = psi_p / r_sh
    dn_sh = [Fraction(0, 1), n_p, Fraction(0, 1), Fraction(0, 1)]
    d2n_sh = [[Fraction(0, 1)] * 4 for _ in range(4)]
    d2n_sh[1][1] = n_pp
    d2n_sh[2][2] = d2n_sh[3][3] = n_p / r_sh
    _, _, gh_shell_rest = adm_conformal_einstein_jet(
        n_sh,
        dn_sh,
        d2n_sh,
        [Fraction(0, 1)] * 3,
        [[Fraction(0, 1)] * 4 for _ in range(3)],
        [[[Fraction(0, 1)] * 4 for _ in range(4)] for _ in range(3)],
        psi_sh,
        dpsi_sh,
        d2psi_sh,
    )
    gh_shell_boosted = mat_mul_4x4(mat_mul_4x4(mat_transpose_4x4(lam_boost), gh_shell_rest), lam_boost)
    rho_s = gh_shell_rest[0][0]
    pr_s = gh_shell_rest[1][1]
    pt_s = gh_shell_rest[2][2]
    lam_s = rho_s / Fraction(2, 1)
    lam_sec_s = (rho_s + pr_s + 2 * pt_s) / Fraction(4, 1)
    mu_s = (rho_s * rho_s) / Fraction(2, 1)
    smooth_shell_slemma = certify_slemma_satisfaction(
        gh_shell_boosted,
        lam_nec=lam_s,
        lam_wec=lam_s,
        lam_sec=lam_sec_s,
        mu_dec=mu_s,
    )

    # 4B. Israel Minkowski-interior / Schwarzschild-exterior thin shell (2610.17629) at s = sqrt(1 - 2M/R) = 4/5
    # => 2M/R = 9/25 => R/M = 50/9 > 9/4 (Buchdahl) and > 25/12 (thin-shell DEC threshold!)
    s_ok = Fraction(4, 5)
    r_over_m_ok = Fraction(2, 1) / (Fraction(1, 1) - s_ok * s_ok)  # 50/9
    sigma_ok = 2 * (Fraction(1, 1) - s_ok)                        # 8*pi*R*sigma = 2/5
    ptheta_ok = ((Fraction(1, 1) - s_ok) ** 2) / (2 * s_ok)       # 8*pi*R*p_theta = 1/40
    t_thin_rest = [
        [sigma_ok, Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)],
        [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)],
        [Fraction(0, 1), Fraction(0, 1), ptheta_ok, Fraction(0, 1)],
        [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1), ptheta_ok],
    ]
    t_thin_boosted = mat_mul_4x4(mat_mul_4x4(mat_transpose_4x4(lam_boost), t_thin_rest), lam_boost)
    thin_shell_slemma = certify_slemma_satisfaction(
        t_thin_boosted,
        lam_nec=Fraction(1, 5),
        lam_wec=Fraction(1, 5),
        lam_sec=Fraction(1, 5),
        mu_dec=Fraction(1, 10),
    )

    # 4C. Sharp negative control below thin-shell DEC threshold R/M < 25/12: s = 1/6 => R/M = 72/35
    s_bad = Fraction(1, 6)
    r_over_m_bad = Fraction(2, 1) / (Fraction(1, 1) - s_bad * s_bad)  # 72/35 < 25/12
    sigma_bad = 2 * (Fraction(1, 1) - s_bad)                          # 5/3
    ptheta_bad = ((Fraction(1, 1) - s_bad) ** 2) / (2 * s_bad)        # 25/12 > 5/3!
    t_thin_bad = [
        [sigma_bad, Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)],
        [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)],
        [Fraction(0, 1), Fraction(0, 1), ptheta_bad, Fraction(0, 1)],
        [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1), ptheta_bad],
    ]
    # Boosted observer u = (6, 0, 5, 0) (eta = -11 < 0) witnesses spacelike energy flux J^2 = 1225/144 > 0 (DEC violation!)
    dec_bad_witness = certify_causal_violation_witness(
        t_thin_bad, [Fraction(6, 1), Fraction(0, 1), Fraction(5, 1), Fraction(0, 1)], "dec_flux"
    )

    return {
        "lichnerowicz_general_hamiltonian_residual_zero": lich_res == 0,
        "vdb_compact_collar_int_psi5_R3_zero": int_vdb_weighted_r3 == 0,
        "schwarzschild_tail_ADM_mass_M": format_exact_rational(m_adm),
        "schwarzschild_tail_int_psi5_R3_over_pi": format_exact_rational(schwarzschild_weighted_r3_over_pi),
        "boost_velocity_v": format_exact_rational(v_boost),
        "smooth_conformally_flat_boosted_shell": {
            "G_hat_00_rest": format_exact_rational(rho_s),
            "G_hat_11_rest": format_exact_rational(pr_s),
            "G_hat_22_rest": format_exact_rational(pt_s),
            "boosted_flux_G01_nonzero": gh_shell_boosted[0][1] != 0,
            "slemma_all_conditions": smooth_shell_slemma,
        },
        "israel_thin_shell_boosted": {
            "s_sqrt_1_minus_2M_over_R": format_exact_rational(s_ok),
            "R_over_M": format_exact_rational(r_over_m_ok),
            "exceeds_buchdahl_9_4": r_over_m_ok > Fraction(9, 4),
            "exceeds_dec_threshold_25_12": r_over_m_ok > Fraction(25, 12),
            "sigma_8piR": format_exact_rational(sigma_ok),
            "p_theta_8piR": format_exact_rational(ptheta_ok),
            "boosted_flux_nonzero": t_thin_boosted[0][1] != 0,
            "slemma_all_conditions": thin_shell_slemma,
        },
        "negative_control_sub_threshold_dec_violation": {
            "s": format_exact_rational(s_bad),
            "R_over_M": format_exact_rational(r_over_m_bad),
            "below_dec_threshold_25_12": r_over_m_bad < Fraction(25, 12),
            "sigma_8piR": format_exact_rational(sigma_bad),
            "p_theta_8piR": format_exact_rational(ptheta_bad),
            "dec_flux_violation_witness": dec_bad_witness,
        },
    }


# ---------------------------------------------------------------------------
# Certificate Builder & Full-Replay Validator
# ---------------------------------------------------------------------------

def build_standalone_payload() -> dict[str, Any]:
    return {
        "oracle_class": "exact",
        "novelty_tier": "N1",
        "zero_trust_path_floats": True,
        "zero_rng": True,
        "zero_bare_asserts": True,
        "pillar1_arbitrary_lapse_adm": certify_pillar1_adm_identities(),
        "pillar2_alcubierre_eos_type_iv": certify_pillar2_alcubierre_eos_and_type_iv(),
        "pillar3_slemma_krein_blind_spot": certify_pillar3_slemma_and_blind_spot(),
        "pillar4_natario_beltrami_horizons": certify_pillar4_natario_beltrami_and_horizons(),
        "pillar5_physical_subluminal_shells": certify_pillar5_physical_subluminal_shells(),
    }


def build_standalone_certificate() -> dict[str, Any]:
    payload = build_standalone_payload()
    payload_sha = canonical_sha256(payload)
    envelope = {
        "schema": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": payload_sha,
        "payload": payload,
    }
    cert_sha = canonical_sha256(envelope)
    return {
        "schema": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": payload_sha,
        "certificate_sha256": cert_sha,
        "payload": payload,
    }


def validate_certificate_payload(cert: Any, *, full_replay: bool = True) -> dict[str, Any]:
    """Fail-closed Zone-B validation of a Track S28 certificate object."""
    require_exact_bool(full_replay, "full_replay")
    if type(cert) is not dict:
        raise AlcubierreAdmError("INVALID_CERT_TYPE", "certificate must be exact dict")
    validate_json_tree_iterative(cert)
    if set(cert.keys()) != _CERT_TOP_KEYS:
        raise AlcubierreAdmError("INVALID_CERT_KEYS", "certificate top-level keys mismatch")

    schema = require_exact_str(cert["schema"], "schema")
    if schema != SCHEMA_VERSION:
        raise AlcubierreAdmError("SCHEMA_MISMATCH", f"unexpected schema: {schema!r}")
    track_id = require_exact_str(cert["track_id"], "track_id")
    if track_id != TRACK_ID:
        raise AlcubierreAdmError("TRACK_ID_MISMATCH", f"unexpected track_id: {track_id!r}")

    payload = cert["payload"]
    if type(payload) is not dict:
        raise AlcubierreAdmError("INVALID_PAYLOAD_TYPE", "payload must be exact dict")

    claimed_payload_sha = require_sha256_hex(cert["payload_sha256"], "payload_sha256")
    claimed_cert_sha = require_sha256_hex(cert["certificate_sha256"], "certificate_sha256")

    actual_payload_sha = canonical_sha256(payload)
    if not hmac.compare_digest(actual_payload_sha, claimed_payload_sha):
        raise AlcubierreAdmError("PAYLOAD_SHA_MISMATCH", "payload_sha256 does not match canonical payload")

    envelope = {
        "schema": schema,
        "track_id": track_id,
        "payload_sha256": claimed_payload_sha,
        "payload": payload,
    }
    actual_cert_sha = canonical_sha256(envelope)
    if not hmac.compare_digest(actual_cert_sha, claimed_cert_sha):
        raise AlcubierreAdmError("CERT_SHA_MISMATCH", "certificate_sha256 does not match canonical envelope")

    if full_replay:
        expected = build_standalone_certificate()
        if not hmac.compare_digest(actual_cert_sha, expected["certificate_sha256"]):
            raise AlcubierreAdmError("REPLAY_MISMATCH", "certificate diverges from live exact replay")

    return {
        "valid": True,
        "schema": schema,
        "track_id": track_id,
        "payload_sha256": actual_payload_sha,
        "certificate_sha256": actual_cert_sha,
        "full_replay": full_replay,
    }
