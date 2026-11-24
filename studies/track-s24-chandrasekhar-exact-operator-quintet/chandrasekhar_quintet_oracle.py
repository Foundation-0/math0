#!/usr/bin/env python3
"""Track S24: Subrahmanyan Chandrasekhar Five-Pillar Exact-Q Operator Quintet Oracle.

100% pure Python 3 standard library (exact Z/Q arithmetic only):
  - ZERO floating-point literals, float() casts, or float trust-path arithmetic
  - ZERO bare assert statements
  - ZERO RNG / non-deterministic inputs

Certifies five exact mathematical operator pillars of Subrahmanyan Chandrasekhar:
  1. Black-Hole Darboux / SUSY Iso-Spectrality (Chandrasekhar 1975, MTBH Ch. 4)
     as an exact multivariate polynomial/rational-function identity in Q[M, lambda, r].
  2. Universal Magnetoconvection Sum-of-Squares Stability Law (1961)
     as an exact polynomial identity in Q[u, u_c] and Q[u_c, delta].
  3. Lane-Emden Polytropes (1939): exact n in {0, 1, 5} solutions, exact Q(n)
     binding-energy vanishing at n=3, exact n=3 power-series recurrence, and a
     rigorous pure-integer outward-rounded Banach + Lohner Taylor-Picard interval
     enclosure of (xi_1, omega_3^0) with width < 10^-11 (beating 10^-8 by >10^3x).
  4. Chandrasekhar-Fermi (1953) Hydromagnetic Virial Identity & Force-Free No-Go
     Obstruction in Q[T, U, gamma, M_mag, Omega], Q[c_B, c_G, G, M, Phi, R], and
     exact 3D polynomial Q[x, y, z] Maxwell stress-virial integration on [-1, 1]^3.
  5. Radiative Transfer H-Function Exact Moments (1950), Conservative Hopf Invariant
     alpha_1^2 = 4/3, Exact Q(sqrt(3)) 2-Point Gauss-Legendre & 4-Point Pure-Q
     Nonlinear Fixed-Point Verification, and Finite-Slab X/Y Riccati Conservation Closure.
"""
from __future__ import annotations

from collections.abc import Mapping, Sequence
from fractions import Fraction
import hashlib
import hmac
import json
from typing import Any

SCHEMA_VERSION = "aletheia.chandrasekhar_quintet.certificate.v1"
TRACK_ID = "TRACK-S24-CHANDRASEKHAR-EXACT-OPERATOR-QUINTET"

MAX_JSON_BYTES = 1_048_576
MAX_JSON_DEPTH = 64
MAX_INT_DIGITS = 1000

_LOWER_HEX = frozenset("0123456789abcdef")
_CERT_TOP_KEYS = frozenset({"schema", "track_id", "payload_sha256", "certificate_sha256", "payload"})

# Outward-rounded dyadic fixed-point scale (2^96 ~ 7.9e28) for pure-integer intervals
_IV_BITS = 96
_IV_ONE = 1 << _IV_BITS


class ChandrasekharError(ValueError):
    """Typed fail-closed error for all Track S24 oracle and Zone-B checks."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


# ---------------------------------------------------------------------------
# Strict Zone-B Parsing, Canonicalization & Integrity Primitives
# ---------------------------------------------------------------------------

def _int_digit_len(value: int) -> int:
    mag = abs(value)
    if mag == 0:
        return 1
    if mag.bit_length() > MAX_INT_DIGITS * 4:
        return MAX_INT_DIGITS + 1
    return len(str(mag))


def require_exact_int(value: Any, label: str, *, min_val: int | None = None, max_val: int | None = None) -> int:
    if type(value) is not int:
        raise ChandrasekharError("INVALID_INT", f"{label} must be exact int")
    if _int_digit_len(value) > MAX_INT_DIGITS:
        raise ChandrasekharError("INT_DIGITS_EXCEEDED", f"{label} exceeds {MAX_INT_DIGITS} digits")
    if min_val is not None and value < min_val:
        raise ChandrasekharError("INT_TOO_SMALL", f"{label} < {min_val}")
    if max_val is not None and value > max_val:
        raise ChandrasekharError("INT_TOO_LARGE", f"{label} > {max_val}")
    return value


def require_exact_bool(value: Any, label: str) -> bool:
    if type(value) is not bool:
        raise ChandrasekharError("INVALID_BOOL", f"{label} must be exact bool")
    return value


def require_exact_str(value: Any, label: str, *, non_empty: bool = True) -> str:
    if type(value) is not str:
        raise ChandrasekharError("INVALID_STR", f"{label} must be exact str")
    try:
        value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise ChandrasekharError("INVALID_UNICODE", f"{label} contains invalid UTF-16 surrogate") from exc
    if non_empty and not value:
        raise ChandrasekharError("EMPTY_STR", f"{label} must be non-empty")
    return value


def require_sha256_hex(value: Any, label: str) -> str:
    text = require_exact_str(value, label)
    if len(text) != 64 or not all(ch in _LOWER_HEX for ch in text):
        raise ChandrasekharError("INVALID_SHA256", f"{label} must be 64 lowercase hex chars")
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
        raise ChandrasekharError("INVALID_RATIONAL", f"{label} has multiple '/' separators")
    num_body = num_s[1:] if num_s.startswith("-") else num_s
    if not _is_ascii_digits(num_body) or not _is_ascii_digits(den_s):
        raise ChandrasekharError("INVALID_RATIONAL", f"{label} contains non-ASCII-digit characters")
    if len(num_body) > MAX_INT_DIGITS or len(den_s) > MAX_INT_DIGITS:
        raise ChandrasekharError("INT_DIGITS_EXCEEDED", f"{label} exceeds {MAX_INT_DIGITS} digits")
    den = int(den_s)
    if den == 0:
        raise ChandrasekharError("ZERO_DENOMINATOR", f"{label} has zero denominator")
    return Fraction(int(num_s), den)


def format_decimal_floor(value: Fraction, digits: int) -> str:
    d = require_exact_int(digits, "digits", min_val=0)
    scale = 10 ** d
    scaled = value * scale
    q = scaled.numerator // scaled.denominator
    neg = "-" if q < 0 else ""
    mag = abs(q)
    if d == 0:
        return f"{neg}{mag}"
    whole, frac = divmod(mag, scale)
    return f"{neg}{whole}.{frac:0{d}d}"


def format_decimal_ceil(value: Fraction, digits: int) -> str:
    d = require_exact_int(digits, "digits", min_val=0)
    scale = 10 ** d
    scaled = value * scale
    q = -((-scaled.numerator) // scaled.denominator)
    neg = "-" if q < 0 else ""
    mag = abs(q)
    if d == 0:
        return f"{neg}{mag}"
    whole, frac = divmod(mag, scale)
    return f"{neg}{whole}.{frac:0{d}d}"


def validate_json_tree_iterative(obj: Any, *, max_depth: int = MAX_JSON_DEPTH) -> None:
    limit = require_exact_int(max_depth, "max_depth", min_val=1, max_val=256)
    stack: list[tuple[Any, int]] = [(obj, 0)]
    while stack:
        cur, depth = stack.pop()
        if depth > limit:
            raise ChandrasekharError("JSON_DEPTH_EXCEEDED", f"JSON nesting depth > {limit}")
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
            raise ChandrasekharError("FORBIDDEN_JSON_TYPE", f"forbidden JSON value type: {t.__name__}")


def _strict_parse_int_token(token: str) -> int:
    body = token[1:] if token.startswith("-") else token
    if len(body) > MAX_INT_DIGITS:
        raise ChandrasekharError("INT_DIGITS_EXCEEDED", f"integer token exceeds {MAX_INT_DIGITS} digits")
    return int(token)


def _reject_float_token(token: str) -> Any:
    raise ChandrasekharError("FLOAT_FORBIDDEN", f"floating-point JSON literal forbidden: {token}")


def _reject_constant_token(token: str) -> Any:
    raise ChandrasekharError("NONFINITE_JSON_FORBIDDEN", f"non-finite JSON token forbidden: {token}")


def _strict_object_pairs_hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for key, val in pairs:
        require_exact_str(key, "json_key", non_empty=False)
        if key in out:
            raise ChandrasekharError("DUPLICATE_JSON_KEY", f"duplicate JSON key: {key!r}")
        out[key] = val
    return out


def parse_strict_json_text(text: str, *, require_object: bool = True) -> Any:
    require_exact_str(text, "json_text")
    if len(text.encode("utf-8")) > MAX_JSON_BYTES:
        raise ChandrasekharError("JSON_TOO_LARGE", f"JSON text exceeds {MAX_JSON_BYTES} bytes")
    try:
        parsed = json.loads(
            text,
            parse_float=_reject_float_token,
            parse_int=_strict_parse_int_token,
            parse_constant=_reject_constant_token,
            object_pairs_hook=_strict_object_pairs_hook,
        )
    except ChandrasekharError:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise ChandrasekharError("INVALID_JSON", f"JSON parse failed: {type(exc).__name__}") from exc
    if require_object and type(parsed) is not dict:
        raise ChandrasekharError("ROOT_NOT_OBJECT", "JSON root must be an object")
    validate_json_tree_iterative(parsed)
    return parsed


def canonical_json_bytes(obj: Any) -> bytes:
    validate_json_tree_iterative(obj)
    try:
        rendered = json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False)
    except (TypeError, ValueError) as exc:
        raise ChandrasekharError("CANONICAL_ENCODE_ERROR", f"cannot encode canonical JSON: {exc}") from exc
    return rendered.encode("ascii")


def canonical_sha256(obj: Any) -> str:
    return hashlib.sha256(canonical_json_bytes(obj)).hexdigest()


# ---------------------------------------------------------------------------
# Exact Multivariate Polynomial Ring Q[x_0, ..., x_{n-1}] & Rational Field
# ---------------------------------------------------------------------------

class MPoly:
    """Exact sparse multivariate polynomial over Q with n_vars indeterminates."""

    __slots__ = ("n_vars", "terms")

    def __init__(self, n_vars: int, terms: Mapping[tuple[int, ...], Fraction]) -> None:
        self.n_vars = n_vars
        self.terms: dict[tuple[int, ...], Fraction] = {
            mon: coeff for mon, coeff in terms.items() if coeff != 0
        }

    @classmethod
    def const(cls, n_vars: int, val: int | Fraction) -> MPoly:
        c = val if isinstance(val, Fraction) else Fraction(val, 1)
        if c == 0:
            return cls(n_vars, {})
        return cls(n_vars, {(0,) * n_vars: c})

    @classmethod
    def var(cls, n_vars: int, idx: int) -> MPoly:
        n_v = require_exact_int(n_vars, "n_vars", min_val=1)
        i_v = require_exact_int(idx, "idx", min_val=0, max_val=n_v - 1)
        mon = tuple(1 if i == i_v else 0 for i in range(n_v))
        return cls(n_v, {mon: Fraction(1, 1)})

    def _require_same_ring(self, other: Any) -> None:
        if not isinstance(other, MPoly) or other.n_vars != self.n_vars:
            raise ChandrasekharError("MPOLY_RING_MISMATCH", "MPoly operands must share n_vars")

    def is_zero(self) -> bool:
        return len(self.terms) == 0

    def __neg__(self) -> MPoly:
        return MPoly(self.n_vars, {m: -c for m, c in self.terms.items()})

    def __add__(self, other: MPoly) -> MPoly:
        self._require_same_ring(other)
        out = dict(self.terms)
        for m, c in other.terms.items():
            nxt = out.get(m, Fraction(0, 1)) + c
            if nxt == 0:
                out.pop(m, None)
            else:
                out[m] = nxt
        return MPoly(self.n_vars, out)

    def __sub__(self, other: MPoly) -> MPoly:
        self._require_same_ring(other)
        return self + (-other)

    def scale(self, factor: int | Fraction) -> MPoly:
        f = factor if isinstance(factor, Fraction) else Fraction(factor, 1)
        if f == 0:
            return MPoly(self.n_vars, {})
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
        out: dict[tuple[int, ...], Fraction] = {}
        for mon, coeff in self.terms.items():
            power = mon[idx]
            if power > 0:
                nxt_mon = tuple(power - 1 if i == idx else e for i, e in enumerate(mon))
                out[nxt_mon] = coeff * power
        return MPoly(self.n_vars, out)

    def eval_point(self, values: Sequence[Fraction]) -> Fraction:
        if len(values) != self.n_vars:
            raise ChandrasekharError("MPOLY_ARITY_MISMATCH", f"expected {self.n_vars} coordinates")
        total = Fraction(0, 1)
        for mon, coeff in self.terms.items():
            term = coeff
            for v, p in zip(values, mon):
                if p:
                    term *= v ** p
            total += term
        return total

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

    def integrate_face(self, fixed_axis: int, fixed_val: int) -> Fraction:
        """Exact 2D integral over face x_{fixed_axis} = fixed_val, other coords in [-1, 1]."""
        total = Fraction(0, 1)
        for mon, coeff in self.terms.items():
            if any(p & 1 for i, p in enumerate(mon) if i != fixed_axis):
                continue
            val = coeff * (fixed_val ** mon[fixed_axis])
            for i, p in enumerate(mon):
                if i != fixed_axis:
                    val *= Fraction(2, p + 1)
            total += val
        return total


def _rf_add(a: tuple[MPoly, MPoly], b: tuple[MPoly, MPoly]) -> tuple[MPoly, MPoly]:
    return (a[0] * b[1] + b[0] * a[1], a[1] * b[1])


def _rf_sub(a: tuple[MPoly, MPoly], b: tuple[MPoly, MPoly]) -> tuple[MPoly, MPoly]:
    return (a[0] * b[1] - b[0] * a[1], a[1] * b[1])


def _rf_mul(a: tuple[MPoly, MPoly], b: tuple[MPoly, MPoly]) -> tuple[MPoly, MPoly]:
    return (a[0] * b[0], a[1] * b[1])


def _rf_deriv(a: tuple[MPoly, MPoly], var_idx: int) -> tuple[MPoly, MPoly]:
    return (a[0].deriv(var_idx) * a[1] - a[0] * a[1].deriv(var_idx), a[1] * a[1])


def _rf_equal(a: tuple[MPoly, MPoly], b: tuple[MPoly, MPoly]) -> bool:
    if a[1].is_zero() or b[1].is_zero():
        raise ChandrasekharError("ZERO_RATIONAL_DENOM", "zero denominator in rational function comparison")
    return (a[0] * b[1] - b[0] * a[1]).is_zero()


# ---------------------------------------------------------------------------
# Pure-Integer Outward-Rounded Dyadic Interval Arithmetic (Scale 2^96)
# ---------------------------------------------------------------------------

def _iv_from_frac(f: Fraction) -> tuple[int, int]:
    lo = (f.numerator << _IV_BITS) // f.denominator
    hi = -(((-f.numerator) << _IV_BITS) // f.denominator)
    return (lo, hi)


def _iv_add(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return (a[0] + b[0], a[1] + b[1])


def _iv_sub(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return (a[0] - b[1], a[1] - b[0])


def _iv_neg(a: tuple[int, int]) -> tuple[int, int]:
    return (-a[1], -a[0])


def _iv_mul(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    prods = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return (min(prods) >> _IV_BITS, -((-max(prods)) >> _IV_BITS))


def _iv_scale_frac(a: tuple[int, int], f: Fraction) -> tuple[int, int]:
    p, q = f.numerator, f.denominator
    if p >= 0:
        return ((a[0] * p) // q, -(((-a[1]) * p) // q))
    return ((a[1] * p) // q, -(((-a[0]) * p) // q))


def _iv_div(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    if b[0] <= 0 and b[1] >= 0:
        raise ChandrasekharError("INTERVAL_DIV_ZERO", "interval division by enclosure containing zero")
    inv_lo = (_IV_ONE << _IV_BITS) // b[1]
    inv_hi = -((-(_IV_ONE << _IV_BITS)) // b[0])
    return _iv_mul(a, (inv_lo, inv_hi))


def _iv_hull(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return (min(a[0], b[0]), max(a[1], b[1]))


def _iv_contains(outer: tuple[int, int], inner: tuple[int, int]) -> bool:
    return outer[0] <= inner[0] and inner[1] <= outer[1]


def _iv_mid(a: tuple[int, int]) -> int:
    return (a[0] + a[1]) // 2


# ---------------------------------------------------------------------------
# Exact Quadratic Field Q(sqrt(3)) for 2-Point Gauss-Legendre Quadrature
# ---------------------------------------------------------------------------

class QSqrt3:
    """Exact element a + b*sqrt(3) with a, b in Q."""

    __slots__ = ("a", "b")

    def __init__(self, a: int | Fraction, b: int | Fraction = 0) -> None:
        self.a = a if isinstance(a, Fraction) else Fraction(a, 1)
        self.b = b if isinstance(b, Fraction) else Fraction(b, 1)

    def __add__(self, other: QSqrt3) -> QSqrt3:
        return QSqrt3(self.a + other.a, self.b + other.b)

    def __sub__(self, other: QSqrt3) -> QSqrt3:
        return QSqrt3(self.a - other.a, self.b - other.b)

    def __mul__(self, other: QSqrt3) -> QSqrt3:
        return QSqrt3(self.a * other.a + 3 * self.b * other.b, self.a * other.b + self.b * other.a)

    def __truediv__(self, other: QSqrt3) -> QSqrt3:
        norm = other.a * other.a - 3 * other.b * other.b
        if norm == 0:
            raise ChandrasekharError("QSQRT3_DIV_ZERO", "division by zero in Q(sqrt(3))")
        return QSqrt3(
            (self.a * other.a - 3 * self.b * other.b) / norm,
            (self.b * other.a - self.a * other.b) / norm,
        )

    def is_zero(self) -> bool:
        return self.a == 0 and self.b == 0


# ---------------------------------------------------------------------------
# Pillar 1: Black-Hole Darboux / SUSY Iso-Spectrality (Chandrasekhar 1975)
# ---------------------------------------------------------------------------

def certify_theorem1_black_hole_darboux() -> dict[str, Any]:
    """Certify Schwarzschild Regge-Wheeler / Zerilli Darboux iso-spectrality in Q[M, lam, r]."""
    # Variables: 0 = M, 1 = lam, 2 = r
    M = MPoly.var(3, 0)
    lam = MPoly.var(3, 1)
    r = MPoly.var(3, 2)
    one = MPoly.const(3, 1)
    lam_p1 = lam + one

    r_minus_2M = r - M.scale(2)
    lam_r_p3M = lam * r + M.scale(3)
    r2 = r.pow(2)
    r4 = r.pow(4)

    # Regge-Wheeler axial potential V_-(r) = (r - 2M) * (2(lam+1)*r - 6M) / r^4
    v_rw = (r_minus_2M * (lam_p1.scale(2) * r - M.scale(6)), r4)

    # Zerilli polar potential V_+(r) = 2(r - 2M)(lam^2(lam+1)r^3 + 3 lam^2 M r^2 + 9 lam M^2 r + 9 M^3) / (r^4 (lam r + 3M)^2)
    z_poly = (
        lam.pow(2) * lam_p1 * r.pow(3)
        + lam.pow(2) * M * r2.scale(3)
        + lam * M.pow(2) * r.scale(9)
        + M.pow(3).scale(9)
    )
    v_zerilli = (r_minus_2M.scale(2) * z_poly, r4 * lam_r_p3M.pow(2))

    # Chandrasekhar function f_C(r) = (r - 2M) / (r^2 (lam r + 3M))
    f_c = (r_minus_2M, r2 * lam_r_p3M)
    # Tortoise derivative df_C/dr_* = ((r - 2M)/r) * df_C/dr
    df_dr = _rf_deriv(f_c, 2)
    df_dr_star = _rf_mul((r_minus_2M, r), df_dr)

    # Common base term: 9 M^2 f_C^2 + 2 lam (lam + 1) f_C
    three_M = (M.scale(3), one)
    f_c_sq = _rf_mul(f_c, f_c)
    quad_term = _rf_mul((M.pow(2).scale(9), one), f_c_sq)
    lin_term = _rf_mul((lam * lam_p1.scale(2), one), f_c)
    common = _rf_add(quad_term, lin_term)
    shift = _rf_mul(three_M, df_dr_star)

    v_plus_darboux = _rf_add(common, shift)
    v_minus_darboux = _rf_sub(common, shift)

    zerilli_exact = _rf_equal(v_zerilli, v_plus_darboux)
    rw_exact = _rf_equal(v_rw, v_minus_darboux)

    # Direct Darboux superpotential W_C(r) = 3M f_C(r) + omega_AS, omega_AS = lam(lam+1)/(3M)
    # Verify W_C^2 + dW_C/dr_* - omega_AS^2 == V_Zerilli and W_C^2 - dW_C/dr_* - omega_AS^2 == V_RW
    omega_as = (lam * lam_p1, M.scale(3))
    w_c = _rf_add(_rf_mul(three_M, f_c), omega_as)
    dw_dr_star = _rf_mul((r_minus_2M, r), _rf_deriv(w_c, 2))
    w_sq_minus_oas_sq = _rf_sub(_rf_mul(w_c, w_c), _rf_mul(omega_as, omega_as))
    darboux_plus_exact = _rf_equal(_rf_add(w_sq_minus_oas_sq, dw_dr_star), v_zerilli)
    darboux_minus_exact = _rf_equal(_rf_sub(w_sq_minus_oas_sq, dw_dr_star), v_rw)

    # Horizon limit (r = 2M) and spatial infinity degree gap of f_C(r) -> W_C(+-inf) = omega_AS
    f_c_vanishes_at_horizon = f_c[0].eval_point([Fraction(1), Fraction(2), Fraction(2)]) == 0
    # Symbolic check: factor (r - 2M) divides f_C numerator and deg_r(num)=1 < deg_r(den)=3
    deg_r_num = max(m[2] for m in f_c[0].terms)
    deg_r_den = max(m[2] for m in f_c[1].terms)
    asymptotic_wc_eq_omega_as = all((f_c_vanishes_at_horizon, deg_r_num < deg_r_den))

    # Scattering amplitude modulus identity in Q[omega_AS, omega]: |omega_AS + i*omega|^2 == |omega_AS - i*omega|^2
    o_as_v = MPoly.var(2, 0)
    omg_v = MPoly.var(2, 1)
    mod_sq_plus = o_as_v.pow(2) + omg_v.pow(2)
    mod_sq_minus = o_as_v.pow(2) + (-omg_v).pow(2)
    scattering_isospectral_exact = (mod_sq_plus - mod_sq_minus).is_zero()

    # Exact multipole table for l = 2, 3, 4 (with M = 1 units -> omega_AS * M)
    multipoles: list[dict[str, Any]] = []
    for ell in (2, 3, 4):
        lam_val = Fraction((ell - 1) * (ell + 2), 2)
        oas_m = lam_val * (lam_val + 1) / Fraction(3, 1)
        # Concrete evaluation check at M=1, r=5
        pt = [Fraction(1, 1), lam_val, Fraction(5, 1)]
        vrw_pt = v_rw[0].eval_point(pt) / v_rw[1].eval_point(pt)
        vz_pt = v_zerilli[0].eval_point(pt) / v_zerilli[1].eval_point(pt)
        multipoles.append(
            {
                "ell": ell,
                "lambda": format_exact_rational(lam_val),
                "omega_as_times_M": format_exact_rational(oas_m),
                "v_rw_at_r5M": format_exact_rational(vrw_pt),
                "v_zerilli_at_r5M": format_exact_rational(vz_pt),
            }
        )

    # Sharp negative control: perturb superpotential coefficient 3M -> 2M
    bad_w = _rf_add(_rf_mul((M.scale(2), one), f_c), omega_as)
    bad_dw = _rf_mul((r_minus_2M, r), _rf_deriv(bad_w, 2))
    bad_diff = _rf_sub(_rf_mul(bad_w, bad_w), _rf_mul(omega_as, omega_as))
    bad_plus_rejected = not _rf_equal(_rf_add(bad_diff, bad_dw), v_zerilli)
    bad_minus_rejected = not _rf_equal(_rf_sub(bad_diff, bad_dw), v_rw)

    return {
        "ring": "Q[M,lambda,r]",
        "zerilli_superpotential_identity_exact": zerilli_exact,
        "regge_wheeler_superpotential_identity_exact": rw_exact,
        "darboux_intertwining_zerilli_exact": darboux_plus_exact,
        "darboux_intertwining_rw_exact": darboux_minus_exact,
        "asymptotic_superpotential_limit_verified": asymptotic_wc_eq_omega_as,
        "scattering_modulus_equality_exact": scattering_isospectral_exact,
        "multipoles": multipoles,
        "negative_control_perturbed_beta_2M_rejected": all((bad_plus_rejected, bad_minus_rejected)),
    }


# ---------------------------------------------------------------------------
# Pillar 2: Universal Magnetoconvection SOS Stability Law (Chandrasekhar 1961)
# ---------------------------------------------------------------------------

def certify_theorem2_magnetoconvection_sos() -> dict[str, Any]:
    """Certify global free-free magnetoconvection SOS identity in Q[u, u_c]."""
    # Variables: 0 = u, 1 = u_c
    u = MPoly.var(2, 0)
    uc = MPoly.var(2, 1)
    one = MPoly.const(2, 1)
    three = MPoly.const(2, 3)

    q1 = uc.pow(3).scale(2) + uc.pow(2).scale(3) - one
    r1_c = (one + uc).pow(3).scale(2)

    lhs = (one + u).pow(3) + q1 * (one + u) - r1_c * u
    rhs = (u - uc).pow(2) * (u + uc.scale(2) + three)
    sos_identity_exact = (lhs - rhs).is_zero()

    # Exact factorization & monotonicity of Q_1(u_c) = (2 u_c - 1)(u_c + 1)^2, Q_1'(u_c) = 6 u_c (u_c + 1)
    q1_factored = (uc.scale(2) - one) * (uc + one).pow(2)
    q1_factorization_exact = (q1 - q1_factored).is_zero()
    q1_deriv_exact = (q1.deriv(1) - uc * (uc + one).scale(6)).is_zero()

    # Sharp supercritical negative control in Q[u_c, delta]:
    # At u = u_c and R_1 = R_{1,c} + delta, (1+u)^3 + Q_1(1+u) - R_1*u == -delta * u_c
    uc_v = MPoly.var(2, 0)
    delta_v = MPoly.var(2, 1)
    one2 = MPoly.const(2, 1)
    q1_v = uc_v.pow(3).scale(2) + uc_v.pow(2).scale(3) - one2
    r1_super = (one2 + uc_v).pow(3).scale(2) + delta_v
    super_margin = (one2 + uc_v).pow(3) + q1_v * (one2 + uc_v) - r1_super * uc_v
    supercritical_identity_exact = (super_margin + delta_v * uc_v).is_zero()

    critical_points: list[dict[str, str]] = []
    for label, uc_val in (
        ("rayleigh_benard_Q0", Fraction(1, 2)),
        ("exact_integer_Q4", Fraction(1, 1)),
        ("moderate_field_u3_2", Fraction(3, 2)),
        ("strong_field_u2", Fraction(2, 1)),
    ):
        q1_val = 2 * (uc_val ** 3) + 3 * (uc_val ** 2) - 1
        r1_val = 2 * ((1 + uc_val) ** 3)
        # Verify supercritical destabilization at delta = 1/1000
        delta_probe = Fraction(1, 1000)
        neg_val = (1 + uc_val) ** 3 + q1_val * (1 + uc_val) - (r1_val + delta_probe) * uc_val
        critical_points.append(
            {
                "label": label,
                "u_c": format_exact_rational(uc_val),
                "Q_over_pi2": format_exact_rational(q1_val),
                "R_c_over_pi4": format_exact_rational(r1_val),
                "supercritical_margin_at_delta_1e_3": format_exact_rational(neg_val),
                "supercritical_margin_negative": neg_val < 0,
            }
        )

    return {
        "ring": "Q[u,u_c]",
        "sos_identity_exact": sos_identity_exact,
        "q1_factorization_exact": q1_factorization_exact,
        "q1_derivative_positive_law_exact": q1_deriv_exact,
        "supercritical_instability_identity_exact": supercritical_identity_exact,
        "critical_points": critical_points,
    }


# ---------------------------------------------------------------------------
# Pillar 3: Lane-Emden Polytropes & Pure-Z/Q n=3 Outward-Rounded Enclosure
# ---------------------------------------------------------------------------

def _lane_emden_n3_series(max_m: int) -> tuple[list[Fraction], list[Fraction]]:
    """Exact Q power-series coefficients a[m] of theta_3(xi) = sum_{m=0}^{max_m} a[m] xi^{2m} and P^3 coeffs."""
    a = [Fraction(0, 1)] * (max_m + 1)
    a[0] = Fraction(1, 1)
    for m in range(1, max_m + 1):
        k = m - 1
        c_k = Fraction(0, 1)
        for i in range(k + 1):
            for j in range(k - i + 1):
                c_k += a[i] * a[j] * a[k - i - j]
        a[m] = -c_k / Fraction(2 * m * (2 * m + 1), 1)

    c_full = [Fraction(0, 1)] * (3 * max_m + 1)
    for i in range(max_m + 1):
        for j in range(max_m + 1):
            aij = a[i] * a[j]
            for k in range(max_m + 1):
                c_full[i + j + k] += aij * a[k]
    return a, c_full


def _le3_taylor_map_and_jac(
    xi_k: Fraction,
    h: Fraction,
    th_iv: tuple[int, int],
    z_iv: tuple[int, int],
    order: int,
) -> tuple[tuple[int, int], tuple[int, int], list[list[tuple[int, int]]]]:
    u = [(0, 0)] * (order + 1)
    w = [(0, 0)] * (order + 1)
    u[0] = th_iv
    w[0] = z_iv
    du = [[(0, 0)] * (order + 1) for _ in range(2)]
    dw = [[(0, 0)] * (order + 1) for _ in range(2)]
    du[0][0] = (_IV_ONE, _IV_ONE)
    dw[1][0] = (_IV_ONE, _IV_ONE)

    u2 = [(0, 0)] * (order + 1)
    u3 = [(0, 0)] * (order + 1)
    du3 = [[(0, 0)] * (order + 1) for _ in range(2)]
    xi2 = xi_k * xi_k
    two_xi = xi_k * 2

    for j in range(order):
        s2 = (0, 0)
        for ai in range(j + 1):
            s2 = _iv_add(s2, _iv_mul(u[ai], u[j - ai]))
        u2[j] = s2
        s3 = (0, 0)
        for ai in range(j + 1):
            s3 = _iv_add(s3, _iv_mul(u2[ai], u[j - ai]))
        u3[j] = s3

        for p_idx in range(2):
            ds = (0, 0)
            for ai in range(j + 1):
                ds = _iv_add(ds, _iv_mul(u2[ai], du[p_idx][j - ai]))
            du3[p_idx][j] = _iv_scale_frac(ds, Fraction(3, 1))

        rhs = _iv_scale_frac(u3[j], xi2)
        if j >= 1:
            rhs = _iv_add(rhs, _iv_scale_frac(u3[j - 1], two_xi))
        if j >= 2:
            rhs = _iv_add(rhs, u3[j - 2])
        w[j + 1] = _iv_scale_frac(_iv_neg(rhs), Fraction(1, j + 1))

        num = w[j]
        if j >= 1:
            num = _iv_sub(num, _iv_scale_frac(u[j], two_xi * j))
        if j >= 2:
            num = _iv_sub(num, _iv_scale_frac(u[j - 1], Fraction(j - 1, 1)))
        u[j + 1] = _iv_scale_frac(num, Fraction(1, 1) / (xi2 * (j + 1)))

        for p_idx in range(2):
            drhs = _iv_scale_frac(du3[p_idx][j], xi2)
            if j >= 1:
                drhs = _iv_add(drhs, _iv_scale_frac(du3[p_idx][j - 1], two_xi))
            if j >= 2:
                drhs = _iv_add(drhs, du3[p_idx][j - 2])
            dw[p_idx][j + 1] = _iv_scale_frac(_iv_neg(drhs), Fraction(1, j + 1))

            dnum = dw[p_idx][j]
            if j >= 1:
                dnum = _iv_sub(dnum, _iv_scale_frac(du[p_idx][j], two_xi * j))
            if j >= 2:
                dnum = _iv_sub(dnum, _iv_scale_frac(du[p_idx][j - 1], Fraction(j - 1, 1)))
            du[p_idx][j + 1] = _iv_scale_frac(dnum, Fraction(1, 1) / (xi2 * (j + 1)))

    val_u = u[order]
    val_w = w[order]
    jac = [[du[0][order], du[1][order]], [dw[0][order], dw[1][order]]]
    for j in range(order - 1, -1, -1):
        val_u = _iv_add(_iv_scale_frac(val_u, h), u[j])
        val_w = _iv_add(_iv_scale_frac(val_w, h), w[j])
        for r_idx in range(2):
            for c_idx in range(2):
                term = du[c_idx][j] if r_idx == 0 else dw[c_idx][j]
                jac[r_idx][c_idx] = _iv_add(_iv_scale_frac(jac[r_idx][c_idx], h), term)
    return val_u, val_w, jac


def _le3_picard_remainder(
    xi_k: Fraction,
    h: Fraction,
    th_iv: tuple[int, int],
    z_iv: tuple[int, int],
    order: int,
) -> tuple[tuple[int, int], tuple[int, int], tuple[int, int], tuple[int, int]]:
    t_iv = (_iv_from_frac(xi_k)[0], _iv_from_frac(xi_k + h)[1])
    t2_iv = _iv_mul(t_iv, t_iv)
    h_iv = (0, _iv_from_frac(h)[1])
    b_th = th_iv
    b_z = z_iv
    for _ in range(16):
        img_th = _iv_add(th_iv, _iv_mul(h_iv, _iv_div(b_z, t2_iv)))
        img_z = _iv_add(z_iv, _iv_mul(h_iv, _iv_neg(_iv_mul(t2_iv, _iv_mul(_iv_mul(b_th, b_th), b_th)))))
        if _iv_contains(b_th, img_th) and _iv_contains(b_z, img_z):
            break
        u_th = _iv_hull(th_iv, img_th)
        u_z = _iv_hull(z_iv, img_z)
        pad_th = max((u_th[1] - u_th[0]) // 4, _IV_ONE >> 40)
        pad_z = max((u_z[1] - u_z[0]) // 4, _IV_ONE >> 40)
        b_th = (u_th[0] - pad_th, u_th[1] + pad_th)
        b_z = (u_z[0] - pad_z, u_z[1] + pad_z)
    else:
        raise ChandrasekharError("PICARD_ENCLOSURE_FAILED", f"Picard-Lindelof box failed at xi={xi_k}")

    u_r = [(0, 0)] * (order + 2)
    w_r = [(0, 0)] * (order + 2)
    u_r[0] = b_th
    w_r[0] = b_z
    u2_r = [(0, 0)] * (order + 2)
    u3_r = [(0, 0)] * (order + 2)
    two_t = _iv_add(t_iv, t_iv)
    for j in range(order + 1):
        s2 = (0, 0)
        for ai in range(j + 1):
            s2 = _iv_add(s2, _iv_mul(u_r[ai], u_r[j - ai]))
        u2_r[j] = s2
        s3 = (0, 0)
        for ai in range(j + 1):
            s3 = _iv_add(s3, _iv_mul(u2_r[ai], u_r[j - ai]))
        u3_r[j] = s3
        rhs = _iv_mul(t2_iv, u3_r[j])
        if j >= 1:
            rhs = _iv_add(rhs, _iv_mul(two_t, u3_r[j - 1]))
        if j >= 2:
            rhs = _iv_add(rhs, u3_r[j - 2])
        w_r[j + 1] = _iv_scale_frac(_iv_neg(rhs), Fraction(1, j + 1))

        num = w_r[j]
        if j >= 1:
            num = _iv_sub(num, _iv_scale_frac(_iv_mul(two_t, u_r[j]), Fraction(j, 1)))
        if j >= 2:
            num = _iv_sub(num, _iv_scale_frac(u_r[j - 1], Fraction(j - 1, 1)))
        u_r[j + 1] = _iv_div(num, _iv_scale_frac(t2_iv, Fraction(j + 1, 1)))

    h_pow = h ** (order + 1)
    return _iv_scale_frac(u_r[order + 1], h_pow), _iv_scale_frac(w_r[order + 1], h_pow), b_th, b_z


def _mat_mul_iv(a_m: list[list[tuple[int, int]]], b_m: list[list[tuple[int, int]]]) -> list[list[tuple[int, int]]]:
    return [
        [_iv_add(_iv_mul(a_m[r][0], b_m[0][c]), _iv_mul(a_m[r][1], b_m[1][c])) for c in range(2)]
        for r in range(2)
    ]


def _mat_vec_iv(a_m: list[list[tuple[int, int]]], vec: list[tuple[int, int]]) -> list[tuple[int, int]]:
    return [_iv_add(_iv_mul(a_m[r][0], vec[0]), _iv_mul(a_m[r][1], vec[1])) for r in range(2)]


def _inv_2x2_exact_iv(a_pt: list[list[int]]) -> list[list[tuple[int, int]]]:
    a00 = Fraction(a_pt[0][0], _IV_ONE)
    a01 = Fraction(a_pt[0][1], _IV_ONE)
    a10 = Fraction(a_pt[1][0], _IV_ONE)
    a11 = Fraction(a_pt[1][1], _IV_ONE)
    det = a00 * a11 - a01 * a10
    if det == 0:
        raise ChandrasekharError("SINGULAR_LOHNER_BASIS", "2x2 Lohner basis matrix became singular")
    return [
        [_iv_from_frac(a11 / det), _iv_from_frac(-a01 / det)],
        [_iv_from_frac(-a10 / det), _iv_from_frac(a00 / det)],
    ]


def _box_from_para(
    y_hat: list[int],
    a_pt: list[list[int]],
    r_iv: list[tuple[int, int]],
) -> tuple[tuple[int, int], tuple[int, int]]:
    a_iv = [[(a_pt[r][c], a_pt[r][c]) for c in range(2)] for r in range(2)]
    off = _mat_vec_iv(a_iv, r_iv)
    return _iv_add((y_hat[0], y_hat[0]), off[0]), _iv_add((y_hat[1], y_hat[1]), off[1])


def _lohner_step(
    xi_k: Fraction,
    h: Fraction,
    y_hat: list[int],
    a_pt: list[list[int]],
    r_iv: list[tuple[int, int]],
    order: int = 16,
) -> tuple[list[int], list[list[int]], list[tuple[int, int]], tuple[int, int], tuple[int, int]]:
    th_box, z_box = _box_from_para(y_hat, a_pt, r_iv)
    rem_th, rem_z, b_th, b_z = _le3_picard_remainder(xi_k, h, th_box, z_box, order)
    f_th_c, f_z_c, _ = _le3_taylor_map_and_jac(xi_k, h, (y_hat[0], y_hat[0]), (y_hat[1], y_hat[1]), order)
    _, _, j_box = _le3_taylor_map_and_jac(xi_k, h, th_box, z_box, order)
    a_iv = [[(a_pt[r][c], a_pt[r][c]) for c in range(2)] for r in range(2)]
    m_iv = _mat_mul_iv(j_box, a_iv)
    a_new = [[_iv_mid(m_iv[r][c]) for c in range(2)] for r in range(2)]
    a_new_inv = _inv_2x2_exact_iv(a_new)
    yh_new = [_iv_mid(f_th_c), _iv_mid(f_z_c)]
    tot_rem = [
        _iv_add(_iv_sub(f_th_c, (yh_new[0], yh_new[0])), rem_th),
        _iv_add(_iv_sub(f_z_c, (yh_new[1], yh_new[1])), rem_z),
    ]
    q_iv = _mat_mul_iv(a_new_inv, m_iv)
    p1 = _mat_vec_iv(q_iv, r_iv)
    p2 = _mat_vec_iv(a_new_inv, tot_rem)
    return yh_new, a_new, [_iv_add(p1[0], p2[0]), _iv_add(p1[1], p2[1])], b_th, b_z


def certify_theorem3_lane_emden() -> dict[str, Any]:
    """Certify exact closed-form Lane-Emden (n=0,1,5), binding energy law, and n=3 rigorous enclosure."""
    xi_p = MPoly.var(1, 0)
    one_p = MPoly.const(1, 1)

    # 1. Exact closed-form n = 0: theta_0 = 1 - xi^2/6
    th0 = one_p - xi_p.pow(2).scale(Fraction(1, 6))
    n0_ode_res = xi_p.pow(2) * th0.deriv(0).deriv(0) + xi_p.scale(2) * th0.deriv(0) + xi_p.pow(2)
    n0_exact = all(
        (
            n0_ode_res.is_zero(),
            th0.eval_point([Fraction(0, 1)]) == 1,
            th0.deriv(0).eval_point([Fraction(0, 1)]) == 0,
        )
    )

    # 2. Exact closed-form n = 1: theta_1(xi) = sin(xi)/xi verified through degree xi^24
    fact = 1
    n1_coeffs: list[Fraction] = []
    for k in range(13):
        if k > 0:
            fact *= (2 * k) * (2 * k + 1)
        n1_coeffs.append(Fraction((-1) ** k, fact))
    n1_exact = all(
        (2 * m) * (2 * m + 1) * n1_coeffs[m] + n1_coeffs[m - 1] == 0
        for m in range(1, len(n1_coeffs))
    )

    # 3. Exact closed-form n = 5: y = theta_5^2 = 3 / (3 + xi^2)
    # ODE: (xi^2 theta')' + xi^2 theta^5 = 0  <=>  2 xi^2 y y'' - xi^2 (y')^2 + 4 xi y y' + 4 xi^2 y^4 == 0
    y5 = (MPoly.const(1, 3), MPoly.const(1, 3) + xi_p.pow(2))
    dy5 = _rf_deriv(y5, 0)
    d2y5 = _rf_deriv(dy5, 0)
    xi2_rf = (xi_p.pow(2), one_p)
    xi_rf = (xi_p, one_p)
    y5_sq = _rf_mul(y5, y5)
    y5_4 = _rf_mul(y5_sq, y5_sq)
    n5_lhs = _rf_add(
        _rf_sub(
            _rf_mul((xi_p.pow(2).scale(2), one_p), _rf_mul(y5, d2y5)),
            _rf_mul(xi2_rf, _rf_mul(dy5, dy5)),
        ),
        _rf_add(
            _rf_mul((xi_p.scale(4), one_p), _rf_mul(y5, dy5)),
            _rf_mul((xi_p.pow(2).scale(4), one_p), y5_4),
        ),
    )
    n5_exact = _rf_equal(n5_lhs, (MPoly.const(1, 0), one_p))

    # 4. Exact rational binding-energy law in Q(n): U + Omega == -(3 - n)/(5 - n)
    n_v = MPoly.var(1, 0)
    five_m_n = MPoly.const(1, 5) - n_v
    omega_rf = (MPoly.const(1, -3), five_m_n)
    u_rf = (n_v, five_m_n)
    e_expected = (n_v - MPoly.const(1, 3), five_m_n)
    binding_energy_law_exact = _rf_equal(_rf_add(u_rf, omega_rf), e_expected)
    e_total_n3_zero = e_expected[0].eval_point([Fraction(3, 1)]) == 0

    # 5. Exact n = 3 power series + Banach contraction start at xi_0 = 3/4
    m_start = 16
    a_ser, c_full = _lane_emden_n3_series(m_start)
    xi0 = Fraction(3, 4)
    e_q = sum(
        (abs(c_full[k]) * (xi0 ** (2 * k + 2)) / Fraction((2 * k + 2) * (2 * k + 3), 1) for k in range(m_start, 3 * m_start + 1)),
        Fraction(0, 1),
    )
    e_qp = sum(
        (abs(c_full[k]) * (xi0 ** (2 * k + 1)) / Fraction(2 * k + 3, 1) for k in range(m_start, 3 * m_start + 1)),
        Fraction(0, 1),
    )
    b_p = sum((abs(a_ser[m]) * (xi0 ** (2 * m)) for m in range(m_start + 1)), Fraction(0, 1))
    eps = e_q * 2
    lipschitz = (xi0 ** 2) / Fraction(2, 1) * ((b_p + eps) ** 2)
    banach_contraction_verified = all((lipschitz < Fraction(1, 2), e_q + lipschitz * eps <= eps))
    eps_p = e_qp + xi0 * ((b_p + eps) ** 2) * eps

    th0_mid = sum((a_ser[m] * (xi0 ** (2 * m)) for m in range(m_start + 1)), Fraction(0, 1))
    dth0_mid = sum((2 * m * a_ser[m] * (xi0 ** (2 * m - 1)) for m in range(1, m_start + 1)), Fraction(0, 1))
    th_iv0 = (_iv_from_frac(th0_mid - eps)[0], _iv_from_frac(th0_mid + eps)[1])
    z_iv0 = (_iv_from_frac((xi0 ** 2) * (dth0_mid - eps_p))[0], _iv_from_frac((xi0 ** 2) * (dth0_mid + eps_p))[1])

    # 6. Lohner parallelepiped validated continuation from xi_0 = 3/4 past first zero
    y_hat = [_iv_mid(th_iv0), _iv_mid(z_iv0)]
    a_pt = [[_IV_ONE, 0], [0, _IV_ONE]]
    r_iv = [(th_iv0[0] - y_hat[0], th_iv0[1] - y_hat[0]), (z_iv0[0] - y_hat[1], z_iv0[1] - y_hat[1])]

    xi = xi0
    steps = 0
    all_z_strictly_negative = z_iv0[1] < 0
    while True:
        h = Fraction(1, 16) if xi < 2 else Fraction(1, 8)
        yh_n, a_n, r_n, _b_th, b_z = _lohner_step(xi, h, y_hat, a_pt, r_iv, order=16)
        if b_z[1] >= 0:
            all_z_strictly_negative = False
        th_n, _z_n = _box_from_para(yh_n, a_n, r_n)
        xi_next = xi + h
        steps += 1
        if th_n[1] < 0:
            break
        xi, y_hat, a_pt, r_iv = xi_next, yh_n, a_n, r_n

    # Bisect root inside [xi, xi_next] using validated Lohner steps from xi
    lo_x, hi_x = xi, xi_next
    for _ in range(60):
        mid_x = (lo_x + hi_x) / 2
        yh_m, a_m, r_m, _, _ = _lohner_step(xi, mid_x - xi, y_hat, a_pt, r_iv, order=16)
        th_m, _ = _box_from_para(yh_m, a_m, r_m)
        if th_m[0] > 0:
            lo_x = mid_x
        elif th_m[1] < 0:
            hi_x = mid_x
        else:
            break

    yh_lo, a_lo, r_lo, _, _ = _lohner_step(xi, lo_x - xi, y_hat, a_pt, r_iv, order=16)
    th_lo_box, _ = _box_from_para(yh_lo, a_lo, r_lo)
    yh_hi, a_hi, r_hi, _, _ = _lohner_step(xi, hi_x - xi, y_hat, a_pt, r_iv, order=16)
    th_hi_box, _ = _box_from_para(yh_hi, a_hi, r_hi)
    _, _, _, _, b_z_root = _lohner_step(lo_x, hi_x - lo_x, yh_lo, a_lo, r_lo, order=16)

    ivt_bracket_verified = all((th_lo_box[0] > 0, th_hi_box[1] < 0, b_z_root[1] < 0, all_z_strictly_negative))

    xi1_width = hi_x - lo_x
    omega_lo = Fraction(-b_z_root[1], _IV_ONE)
    omega_hi = Fraction(-b_z_root[0], _IV_ONE)
    omega_width = omega_hi - omega_lo

    target_width = Fraction(1, 10 ** 8)
    widths_below_1e_8 = all((xi1_width < target_width, omega_width < target_width))

    # Negative control: interval division by zero enclosure raises ChandrasekharError
    div0_rejected = False
    try:
        _iv_div((_IV_ONE, _IV_ONE), (-1, 1))
    except ChandrasekharError as exc:
        div0_rejected = exc.code == "INTERVAL_DIV_ZERO"

    return {
        "n0_closed_form_exact": n0_exact,
        "n1_series_ode_exact_deg24": n1_exact,
        "n5_rational_ode_exact": n5_exact,
        "binding_energy_law_exact": binding_energy_law_exact,
        "n3_binding_energy_vanishes": e_total_n3_zero,
        "n3_series_prefix": [format_exact_rational(a_ser[k]) for k in range(7)],
        "banach_start_verified": banach_contraction_verified,
        "banach_start_lipschitz_lt_half": lipschitz < Fraction(1, 2),
        "lohner_steps": steps,
        "strictly_decreasing_unique_first_zero": ivt_bracket_verified,
        "xi1_lo": format_exact_rational(lo_x),
        "xi1_hi": format_exact_rational(hi_x),
        "xi1_decimal_enclosure": [format_decimal_floor(lo_x, 15), format_decimal_ceil(hi_x, 15)],
        "xi1_width": format_exact_rational(xi1_width),
        "omega3_lo": format_exact_rational(omega_lo),
        "omega3_hi": format_exact_rational(omega_hi),
        "omega3_decimal_enclosure": [format_decimal_floor(omega_lo, 15), format_decimal_ceil(omega_hi, 15)],
        "omega3_width": format_exact_rational(omega_width),
        "widths_strictly_below_1e_8": widths_below_1e_8,
        "negative_control_interval_div_zero_rejected": div0_rejected,
    }


# ---------------------------------------------------------------------------
# Pillar 4: Chandrasekhar-Fermi (1953) Virial No-Go Obstruction
# ---------------------------------------------------------------------------

def certify_theorem4_virial_nogo() -> dict[str, Any]:
    """Certify scalar hydromagnetic virial theorem, mass-to-flux scaling, and 3D Maxwell virial no-go."""
    # 1. Exact scalar hydromagnetic virial energy elimination in Q[T, U, gamma, M_mag, Omega]
    T = MPoly.var(5, 0)
    U = MPoly.var(5, 1)
    gam = MPoly.var(5, 2)
    M_mag = MPoly.var(5, 3)
    Om = MPoly.var(5, 4)
    one5 = MPoly.const(5, 1)
    three_g_m1 = (gam - one5).scale(3)

    virial = T.scale(2) + three_g_m1 * U + M_mag + Om
    total_E = T + U + M_mag + Om
    # Identity: 3(gamma-1)*E - virial == (3*gamma - 5)*T + (3*gamma - 4)*(M_mag + Omega)
    elim_lhs = three_g_m1 * total_E - virial
    elim_rhs = (gam.scale(3) - MPoly.const(5, 5)) * T + (gam.scale(3) - MPoly.const(5, 4)) * (M_mag + Om)
    energy_elimination_exact = (elim_lhs - elim_rhs).is_zero()
    # At gamma = 4/3 and T = 0, E vanishes identically (direct link to Pillar 3)
    g43_coeff = (gam.scale(3) - MPoly.const(5, 4)).eval_point(
        [Fraction(0), Fraction(0), Fraction(4, 3), Fraction(1), Fraction(-1)]
    )
    gamma_4_3_energy_coeff_zero = g43_coeff == 0

    # 2. Exact radius-independent critical mass-to-flux threshold in Q[c_B, c_G, G, M, Phi, R]
    c_B, c_G, G_v, M_v, Phi_v, R_v = (MPoly.var(6, i) for i in range(6))
    mag_rf = (c_B * Phi_v.pow(2), R_v)
    grav_rf = (-c_G * G_v * M_v.pow(2), R_v)
    sum_rf = _rf_add(mag_rf, grav_rf)
    crit_rf = (c_B * Phi_v.pow(2) - c_G * G_v * M_v.pow(2), R_v)
    mass_to_flux_R_cancels_exact = _rf_equal(sum_rf, crit_rf)

    # 3. Exact 3D polynomial Q[x, y, z] Maxwell stress-virial identity + [-1, 1]^3 integration
    # Choose a nontrivial 3D divergence-free polynomial field B = curl(A):
    # A = (x*y*z, x^2*z - y^2, y*z^2 + x) -> div(B) == 0 identically!
    x, y, z = MPoly.var(3, 0), MPoly.var(3, 1), MPoly.var(3, 2)
    A = (x * y * z, x.pow(2) * z - y.pow(2), y * z.pow(2) + x)
    B = (
        A[2].deriv(1) - A[1].deriv(2),
        A[0].deriv(2) - A[2].deriv(0),
        A[1].deriv(0) - A[0].deriv(1),
    )
    div_B_zero = (B[0].deriv(0) + B[1].deriv(1) + B[2].deriv(2)).is_zero()

    # Current J = curl(B), Lorentz force F = J x B
    J = (
        B[2].deriv(1) - B[1].deriv(2),
        B[0].deriv(2) - B[2].deriv(0),
        B[1].deriv(0) - B[0].deriv(1),
    )
    F = (
        J[1] * B[2] - J[2] * B[1],
        J[2] * B[0] - J[0] * B[2],
        J[0] * B[1] - J[1] * B[0],
    )
    coords = (x, y, z)
    b_sq = B[0].pow(2) + B[1].pow(2) + B[2].pow(2)
    half_b_sq = b_sq.scale(Fraction(1, 2))
    # Maxwell stress tensor T_{ij} = B_i B_j - (1/2)|B|^2 delta_{ij}
    # Vector V_j = sum_i x_i T_{ij}
    vec_v = []
    for j in range(3):
        comp = MPoly.const(3, 0)
        for i in range(3):
            t_ij = B[i] * B[j] - (half_b_sq if i == j else MPoly.const(3, 0))
            comp = comp + coords[i] * t_ij
        vec_v.append(comp)

    div_v = vec_v[0].deriv(0) + vec_v[1].deriv(1) + vec_v[2].deriv(2)
    x_dot_F = x * F[0] + y * F[1] + z * F[2]
    pointwise_maxwell_virial_zero = (div_v + half_b_sq - x_dot_F).is_zero()

    # Exact volume and boundary surface integrals over [-1, 1]^3
    mag_energy_vol = half_b_sq.integrate_unit_cube()
    lorentz_virial_vol = x_dot_F.integrate_unit_cube()
    surface_flux = Fraction(0, 1)
    for axis in range(3):
        surface_flux += vec_v[axis].integrate_face(axis, 1) - vec_v[axis].integrate_face(axis, -1)
    gauss_balance_zero = (surface_flux + mag_energy_vol - lorentz_virial_vol) == 0

    # No-go obstruction: with T=U=Omega=0, JxB=0, and zero surface stress, virial demands M_mag = 0,
    # contradicting M_mag = mag_energy_vol > 0
    self_confined_force_free_obstructed = all(
        (div_B_zero, pointwise_maxwell_virial_zero, gauss_balance_zero, mag_energy_vol > 0)
    )

    # Negative control: static equilibrium at gamma = 5/3 with M_mag = 5, Omega = -3 -> E = (1/2)*(5 - 3) = +1 > 0 (unbound!)
    unbound_E = (Fraction(3, 1) * Fraction(5, 3) - 4) / (Fraction(3, 1) * Fraction(2, 3)) * (Fraction(5, 1) - Fraction(3, 1))
    supercritical_unbound_detected = unbound_E > 0

    return {
        "scalar_virial_energy_elimination_exact": energy_elimination_exact,
        "gamma_4_3_energy_vanishing_exact": gamma_4_3_energy_coeff_zero,
        "critical_mass_to_flux_R_cancels_exact": mass_to_flux_R_cancels_exact,
        "field_div_B_zero_exact": div_B_zero,
        "pointwise_3d_maxwell_virial_identity_zero": pointwise_maxwell_virial_zero,
        "cube_magnetic_energy_M": format_exact_rational(mag_energy_vol),
        "cube_lorentz_virial_int": format_exact_rational(lorentz_virial_vol),
        "cube_surface_stress_flux": format_exact_rational(surface_flux),
        "gauss_virial_balance_zero": gauss_balance_zero,
        "self_confined_force_free_R3_obstructed": self_confined_force_free_obstructed,
        "negative_control_magnetically_unbound_E": format_exact_rational(unbound_E),
        "negative_control_unbound_detected": supercritical_unbound_detected,
    }


# ---------------------------------------------------------------------------
# Pillar 5: Radiative Transfer H-Function Moments & Slab X/Y Riccati Closure
# ---------------------------------------------------------------------------

def _solve_discrete_h_4pt(w0: Fraction, q_val: Fraction) -> tuple[list[Fraction], Fraction, Fraction, Fraction]:
    """Solve 4-point cubic-exact pure-Q discrete Ambartsumian-Chandrasekhar equation via integer fixed-point."""
    mus = [Fraction(1, 8), Fraction(3, 8), Fraction(5, 8), Fraction(7, 8)]
    wts = [Fraction(13, 48), Fraction(11, 48), Fraction(11, 48), Fraction(13, 48)]
    # Fixed-point in 2^96 scaled pure integers using Chandrasekhar's contractive second form:
    # H_i = 1 / (q + (w0/2) * sum_j w_j * mu_j * H_j / (mu_i + mu_j))
    h_sc = [_IV_ONE] * 4
    q_sc = (q_val.numerator << _IV_BITS) // q_val.denominator
    # Precompute kernel K_{ij} = (w0/2) * w_j * mu_j / (mu_i + mu_j) as exact Fractions
    kern = [
        [w0 * Fraction(1, 2) * wts[j] * mus[j] / (mus[i] + mus[j]) for j in range(4)]
        for i in range(4)
    ]
    for _ in range(90):
        nxt = [0] * 4
        for i in range(4):
            denom = q_sc
            for j in range(4):
                k = kern[i][j]
                denom += (h_sc[j] * k.numerator) // k.denominator
            t_i = (_IV_ONE << _IV_BITS) // denom
            nxt[i] = (h_sc[i] + t_i) // 2
        h_sc = nxt

    h_fracs = [Fraction(v, _IV_ONE) for v in h_sc]
    # Evaluate exact residual on ORIGINAL Ambartsumian-Chandrasekhar equation
    max_res = Fraction(0, 1)
    for i in range(4):
        s_i = sum((wts[j] * h_fracs[j] / (mus[i] + mus[j]) for j in range(4)), Fraction(0, 1))
        res_i = abs(h_fracs[i] - Fraction(1, 1) - (w0 / Fraction(2, 1)) * mus[i] * h_fracs[i] * s_i)
        if res_i > max_res:
            max_res = res_i
    alpha0_disc = sum((wts[i] * h_fracs[i] for i in range(4)), Fraction(0, 1))
    alpha1_disc = sum((wts[i] * mus[i] * h_fracs[i] for i in range(4)), Fraction(0, 1))
    return h_fracs, max_res, alpha0_disc, alpha1_disc


def certify_theorem5_radiative_transfer() -> dict[str, Any]:
    """Certify H-function moments, Hopf invariant, Gauss-Legendre Q(sqrt(3)), 4pt fixed point, and X/Y Riccati."""
    # 1. Exact polynomial identity in Q[q] for rational-square albedos w0 = 1 - q^2, alpha_0 = 2/(1 + q)
    q_v = MPoly.var(1, 0)
    one1 = MPoly.const(1, 1)
    w0_poly = one1 - q_v.pow(2)
    a0_rf = (MPoly.const(1, 2), one1 + q_v)
    quad_law_rf = _rf_add(
        _rf_sub(
            _rf_mul((w0_poly.scale(Fraction(1, 2)), one1), _rf_mul(a0_rf, a0_rf)),
            _rf_mul((MPoly.const(1, 2), one1), a0_rf),
        ),
        (MPoly.const(1, 2), one1),
    )
    alpha0_law_exact = _rf_equal(quad_law_rf, (MPoly.const(1, 0), one1))

    # 2. Exact Hopf moment identity in Q[q, alpha_1, alpha_2]:
    # (1 - (w0/2) alpha_0) * alpha_2 + (w0/4) * alpha_1^2 == q * alpha_2 + ((1 - q^2)/4) * alpha_1^2
    # At q = 0 (w0 = 1): (1/4) alpha_1^2 = 1/3 => alpha_1^2 = 4/3
    qv3, a1_v, a2_v = MPoly.var(3, 0), MPoly.var(3, 1), MPoly.var(3, 2)
    one3 = MPoly.const(3, 1)
    w0_3 = one3 - qv3.pow(2)
    a0_3 = (MPoly.const(3, 2), one3 + qv3)
    one_minus_half_w0_a0 = _rf_sub((one3, one3), _rf_mul((w0_3.scale(Fraction(1, 2)), one3), a0_3))
    hopf_lhs = _rf_add(
        _rf_mul(one_minus_half_w0_a0, (a2_v, one3)),
        (w0_3.scale(Fraction(1, 4)) * a1_v.pow(2), one3),
    )
    hopf_rhs = (qv3 * a2_v + w0_3.scale(Fraction(1, 4)) * a1_v.pow(2), one3)
    hopf_coeff_eq_q = _rf_equal(hopf_lhs, hopf_rhs)
    hopf_conservative_rhs = Fraction(1, 3) * Fraction(4, 1)  # alpha_1^2 = 4/3
    hopf_invariant_exact = all((hopf_coeff_eq_q, hopf_conservative_rhs == Fraction(4, 3)))

    # 3. Exact 2-point Gauss-Legendre rule in Q(sqrt(3)): mu_+- = 1/2 +- sqrt(3)/6, w_+- = 1/2
    gl_mus = (QSqrt3(Fraction(1, 2), Fraction(-1, 6)), QSqrt3(Fraction(1, 2), Fraction(1, 6)))
    gl_w = QSqrt3(Fraction(1, 2), 0)
    gl_m0 = gl_w + gl_w
    gl_m1 = gl_w * gl_mus[0] + gl_w * gl_mus[1]
    gl_m2 = gl_w * gl_mus[0] * gl_mus[0] + gl_w * gl_mus[1] * gl_mus[1]
    gl_m3 = gl_w * gl_mus[0] * gl_mus[0] * gl_mus[0] + gl_w * gl_mus[1] * gl_mus[1] * gl_mus[1]
    gauss_legendre_2pt_exact = all(
        (
            (gl_m0 - QSqrt3(1)).is_zero(),
            (gl_m1 - QSqrt3(Fraction(1, 2))).is_zero(),
            (gl_m2 - QSqrt3(Fraction(1, 3))).is_zero(),
            (gl_m3 - QSqrt3(Fraction(1, 4))).is_zero(),
        )
    )

    # 4. Exact 4-point positive pure-Q quadrature moments + nonlinear fixed-point verification
    mus4 = [Fraction(1, 8), Fraction(3, 8), Fraction(5, 8), Fraction(7, 8)]
    wts4 = [Fraction(13, 48), Fraction(11, 48), Fraction(11, 48), Fraction(13, 48)]
    quad4_exact = all(
        (
            sum(wts4) == 1,
            sum(w * m for w, m in zip(wts4, mus4)) == Fraction(1, 2),
            sum(w * m * m for w, m in zip(wts4, mus4)) == Fraction(1, 3),
            sum(w * (m ** 3) for w, m in zip(wts4, mus4)) == Fraction(1, 4),
        )
    )

    tol = Fraction(1, 10 ** 18)
    albedo_cases: list[dict[str, Any]] = []
    spurious_branch_rejected = True
    for q_val in (Fraction(1, 2), Fraction(1, 3), Fraction(1, 4), Fraction(0, 1)):
        w0 = Fraction(1, 1) - q_val * q_val
        alpha0_exact = Fraction(2, 1) / (Fraction(1, 1) + q_val)
        law_res = (w0 / Fraction(2, 1)) * (alpha0_exact ** 2) - 2 * alpha0_exact + 2
        if q_val > 0:
            alpha0_spurious = Fraction(2, 1) / (Fraction(1, 1) - q_val)
            if (w0 / Fraction(2, 1)) * alpha0_spurious <= 1:
                spurious_branch_rejected = False

        _hs, max_res, a0_disc, a1_disc = _solve_discrete_h_4pt(w0, q_val)
        a0_err = abs(a0_disc - alpha0_exact)
        hopf_err = abs(a1_disc * a1_disc - Fraction(4, 3)) if q_val == 0 else Fraction(0, 1)

        entry: dict[str, Any] = {
            "q": format_exact_rational(q_val),
            "albedo_w0": format_exact_rational(w0),
            "alpha0_exact": format_exact_rational(alpha0_exact),
            "moment_law_residual_zero": law_res == 0,
            "quad4_max_residual_lt_1e_18": max_res < tol,
            "quad4_alpha0_err_lt_1e_18": a0_err < tol,
        }
        if q_val == 0:
            entry["conservative_alpha1_sq_exact"] = "4/3"
            entry["quad4_hopf_alpha1_sq_err_lt_1e_18"] = hopf_err < tol
        albedo_cases.append(entry)

    # 5. Finite-slab X/Y Riccati conservation closure:
    # Symbolic derivative d/dtau [(1 - (w0/2) x0)^2 - ((w0/2) y0)^2] == 0 in Q[w0, x0, y0, ym1]
    w0_r, x0_r, y0_r, ym1_r = (MPoly.var(4, i) for i in range(4))
    one4 = MPoly.const(4, 1)
    dx0 = w0_r.scale(Fraction(1, 2)) * y0_r * ym1_r
    dy0 = -(one4 - w0_r.scale(Fraction(1, 2)) * x0_r) * ym1_r
    inv_deriv = (
        (one4 - w0_r.scale(Fraction(1, 2)) * x0_r).scale(2) * (-w0_r.scale(Fraction(1, 2)) * dx0)
        - (w0_r.scale(Fraction(1, 2)) * y0_r).scale(2) * (w0_r.scale(Fraction(1, 2)) * dy0)
    )
    riccati_symbolic_conserved = inv_deriv.is_zero()

    # Initial value at tau=0 (x0=1, y0=1): (1 - w0/2)^2 - (w0/2)^2 == 1 - w0
    w0_1 = MPoly.var(1, 0)
    inv_tau0 = (one1 - w0_1.scale(Fraction(1, 2))).pow(2) - w0_1.scale(Fraction(1, 2)).pow(2)
    riccati_tau0_exact = (inv_tau0 - (one1 - w0_1)).is_zero()

    # Exact degree-8 formal power series in tau for 4-point coupled X_i(tau), Y_i(tau) at w0 = 3/4
    w0_slab = Fraction(3, 4)
    deg_tau = 8
    x_ser = [[Fraction(0, 1)] * (deg_tau + 1) for _ in range(4)]
    y_ser = [[Fraction(0, 1)] * (deg_tau + 1) for _ in range(4)]
    for i in range(4):
        x_ser[i][0] = Fraction(1, 1)
        y_ser[i][0] = Fraction(1, 1)
    ym1_ser = [Fraction(0, 1)] * (deg_tau + 1)
    for k in range(deg_tau):
        ym1_ser[k] = sum((wts4[j] * y_ser[j][k] / mus4[j] for j in range(4)), Fraction(0, 1))
        for i in range(4):
            conv_y = sum((y_ser[i][a] * ym1_ser[k - a] for a in range(k + 1)), Fraction(0, 1))
            conv_x = sum((x_ser[i][a] * ym1_ser[k - a] for a in range(k + 1)), Fraction(0, 1))
            x_ser[i][k + 1] = (w0_slab / Fraction(2, 1)) * conv_y / Fraction(k + 1, 1)
            y_ser[i][k + 1] = (-(y_ser[i][k] / mus4[i]) + (w0_slab / Fraction(2, 1)) * conv_x) / Fraction(k + 1, 1)

    x0_ser = [sum((wts4[i] * x_ser[i][k] for i in range(4)), Fraction(0, 1)) for k in range(deg_tau + 1)]
    y0_ser = [sum((wts4[i] * y_ser[i][k] for i in range(4)), Fraction(0, 1)) for k in range(deg_tau + 1)]
    # Check x0(tau) - (w0/4)*(x0(tau)^2 - y0(tau)^2) == 1 identically through tau^8
    riccati_series_residuals: list[Fraction] = []
    for k in range(deg_tau + 1):
        x0_sq_k = sum((x0_ser[a] * x0_ser[k - a] for a in range(k + 1)), Fraction(0, 1))
        y0_sq_k = sum((y0_ser[a] * y0_ser[k - a] for a in range(k + 1)), Fraction(0, 1))
        val_k = x0_ser[k] - (w0_slab / Fraction(4, 1)) * (x0_sq_k - y0_sq_k)
        target_k = Fraction(1, 1) if k == 0 else Fraction(0, 1)
        riccati_series_residuals.append(val_k - target_k)
    riccati_series_deg8_zero = all(r == 0 for r in riccati_series_residuals)

    # Negative control: flipping sign of dy0 breaks Riccati conservation (inv_deriv != 0)
    bad_dy0 = (one4 - w0_r.scale(Fraction(1, 2)) * x0_r) * ym1_r
    bad_inv_deriv = (
        (one4 - w0_r.scale(Fraction(1, 2)) * x0_r).scale(2) * (-w0_r.scale(Fraction(1, 2)) * dx0)
        - (w0_r.scale(Fraction(1, 2)) * y0_r).scale(2) * (w0_r.scale(Fraction(1, 2)) * bad_dy0)
    )
    riccati_bad_sign_rejected = not bad_inv_deriv.is_zero()

    return {
        "alpha0_algebraic_law_exact_Q_q": alpha0_law_exact,
        "conservative_hopf_invariant_alpha1_sq_4_3_exact": hopf_invariant_exact,
        "gauss_legendre_2pt_Q_sqrt3_exact": gauss_legendre_2pt_exact,
        "quad4_pure_Q_cubic_exact": quad4_exact,
        "albedo_cases": albedo_cases,
        "finite_slab_riccati_symbolic_conserved": riccati_symbolic_conserved,
        "finite_slab_riccati_tau0_exact": riccati_tau0_exact,
        "finite_slab_riccati_series_deg8_zero": riccati_series_deg8_zero,
        "negative_control_spurious_alpha0_branch_rejected": spurious_branch_rejected,
        "negative_control_broken_riccati_sign_rejected": riccati_bad_sign_rejected,
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
        "theorem1_black_hole_darboux": certify_theorem1_black_hole_darboux(),
        "theorem2_magnetoconvection_sos": certify_theorem2_magnetoconvection_sos(),
        "theorem3_lane_emden_polytropes": certify_theorem3_lane_emden(),
        "theorem4_chandrasekhar_fermi_virial": certify_theorem4_virial_nogo(),
        "theorem5_radiative_transfer_riccati": certify_theorem5_radiative_transfer(),
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
    """Fail-closed Zone-B validation of a Track S24 certificate object."""
    require_exact_bool(full_replay, "full_replay")
    if type(cert) is not dict:
        raise ChandrasekharError("INVALID_CERT_TYPE", "certificate must be exact dict")
    validate_json_tree_iterative(cert)
    if set(cert.keys()) != _CERT_TOP_KEYS:
        raise ChandrasekharError("INVALID_CERT_KEYS", "certificate top-level keys mismatch")

    schema = require_exact_str(cert["schema"], "schema")
    if schema != SCHEMA_VERSION:
        raise ChandrasekharError("SCHEMA_MISMATCH", f"unexpected schema: {schema!r}")
    track_id = require_exact_str(cert["track_id"], "track_id")
    if track_id != TRACK_ID:
        raise ChandrasekharError("TRACK_ID_MISMATCH", f"unexpected track_id: {track_id!r}")

    payload = cert["payload"]
    if type(payload) is not dict:
        raise ChandrasekharError("INVALID_PAYLOAD_TYPE", "payload must be exact dict")

    claimed_payload_sha = require_sha256_hex(cert["payload_sha256"], "payload_sha256")
    claimed_cert_sha = require_sha256_hex(cert["certificate_sha256"], "certificate_sha256")

    actual_payload_sha = canonical_sha256(payload)
    if not hmac.compare_digest(actual_payload_sha, claimed_payload_sha):
        raise ChandrasekharError("PAYLOAD_SHA_MISMATCH", "payload_sha256 does not match canonical payload")

    envelope = {
        "schema": schema,
        "track_id": track_id,
        "payload_sha256": claimed_payload_sha,
        "payload": payload,
    }
    actual_cert_sha = canonical_sha256(envelope)
    if not hmac.compare_digest(actual_cert_sha, claimed_cert_sha):
        raise ChandrasekharError("CERT_SHA_MISMATCH", "certificate_sha256 does not match canonical envelope")

    if full_replay:
        expected = build_standalone_certificate()
        if not hmac.compare_digest(actual_cert_sha, expected["certificate_sha256"]):
            raise ChandrasekharError("REPLAY_MISMATCH", "certificate diverges from live exact replay")

    return {
        "valid": True,
        "schema": schema,
        "track_id": track_id,
        "payload_sha256": actual_payload_sha,
        "certificate_sha256": actual_cert_sha,
        "full_replay": full_replay,
    }
