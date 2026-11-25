"""Pure-Z/Q/Q[i] Chandrasekhar-Kendall Force-Free States, Magnetic
Helicity Conservation, Knotted Flux Tubes, and Exact Helical-Basis FFT/NTT
Spectral Convolutions.

Zero external dependencies, zero IEEE-754 floats, zero bare asserts, zero RNG.
Exact arithmetic over Z, Q (`fractions.Fraction`), and Q[i] (`(Fraction, Fraction)`),
with Zone-B fail-closed public API and certificate validation.
"""
from __future__ import annotations

from fractions import Fraction
import hashlib
import hmac
import json
import math
from typing import Any, Mapping, Sequence

SCHEMA_VERSION = "aletheia.ck_helicity_fft.certificate.v1"
TRACK_ID = "TRACK-S23A-CK-HELICITY-KNOTTED-FLUX-FFT"

MAX_JSON_BYTES = 1_048_576
MAX_JSON_DEPTH = 64
MAX_INT_BITS = 2048
MAX_INT_DIGITS = 616
MAX_RATIONAL_CHARS = 256
MAX_FORMAT_BITS = 4096

_HEX_LOWER = frozenset("0123456789abcdef")
_ASCII_DIGITS = frozenset("0123456789")
_CERT_KEYS = frozenset({"schema", "track_id", "payload_sha256", "certificate_sha256", "payload"})

# Dual NTT-friendly primes: p_1 = 119*2^23 + 1, p_2 = 5*2^25 + 1 (both primitive root 3)
NTT_PRIME_1 = 998244353
NTT_PRIME_2 = 167772161
NTT_PRIM_ROOT = 3

QComplex = tuple[Fraction, Fraction]
QVec3 = tuple[QComplex, QComplex, QComplex]
QMat3 = tuple[QVec3, QVec3, QVec3]


class CKHelicityError(ValueError):
    """Explicit fail-closed error (never stripped by python3 -O)."""

    def __init__(self, code: str, message: str) -> None:
        self.code = code
        self.message = message
        super().__init__(f"{code}: {message}")


# ---------------------------------------------------------------------------
# Zone-B Exact Type, Rational, JSON & Digest Primitives
# ---------------------------------------------------------------------------

def require_bool(val: Any, label: str) -> bool:
    if type(val) is not bool:
        raise CKHelicityError("INVALID_BOOL", f"{label} must be strict bool")
    return val


def require_int(
    val: Any,
    label: str,
    lo: int | None = None,
    hi: int | None = None,
) -> int:
    if type(val) is not int:
        raise CKHelicityError("INVALID_INT", f"{label} must be strict int")
    if val.bit_length() > MAX_INT_BITS:
        raise CKHelicityError("INT_TOO_LARGE", f"{label} exceeds {MAX_INT_BITS}-bit limit")
    if lo is not None:
        if type(lo) is not int:
            raise CKHelicityError("INVALID_BOUND", f"{label} lo bound must be strict int")
        if val < lo:
            raise CKHelicityError("INT_OUT_OF_RANGE", f"{label} < {lo}")
    if hi is not None:
        if type(hi) is not int:
            raise CKHelicityError("INVALID_BOUND", f"{label} hi bound must be strict int")
        if val > hi:
            raise CKHelicityError("INT_OUT_OF_RANGE", f"{label} > {hi}")
    return val


def require_str(val: Any, label: str, max_len: int = 4096) -> str:
    if type(val) is not str:
        raise CKHelicityError("INVALID_STR", f"{label} must be strict str")
    if len(val) > max_len:
        raise CKHelicityError("STR_TOO_LONG", f"{label} exceeds length limit")
    try:
        val.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise CKHelicityError("INVALID_UNICODE", f"{label} contains lone UTF-16 surrogate") from exc
    return val


def require_hex64(val: Any, label: str) -> str:
    s = require_str(val, label, max_len=64)
    if len(s) != 64 or any(ch not in _HEX_LOWER for ch in s):
        raise CKHelicityError("INVALID_HEX64", f"{label} must be 64 lowercase ASCII hex chars")
    return s


def constant_time_hex64_equal(left: Any, right: Any, label: str) -> bool:
    a = require_hex64(left, f"{label}.left")
    b = require_hex64(right, f"{label}.right")
    return hmac.compare_digest(a.encode("ascii"), b.encode("ascii"))


def _is_canonical_unsigned_digits(s: str) -> bool:
    if not s or any(ch not in _ASCII_DIGITS for ch in s):
        return False
    if len(s) > 1 and s[0] == "0":
        return False
    return True


def parse_exact_rational(raw: Any, label: str = "rational") -> Fraction:
    """Strictly parse exact int, Fraction, or canonical rational string ('p' or 'p/q')."""
    t = type(raw)
    if t is int:
        if raw.bit_length() > MAX_INT_BITS:
            raise CKHelicityError("RATIONAL_TOO_LARGE", f"{label} exceeds bit limit")
        return Fraction(raw, 1)
    if t is Fraction:
        if raw.numerator.bit_length() > MAX_INT_BITS or raw.denominator.bit_length() > MAX_INT_BITS:
            raise CKHelicityError("RATIONAL_TOO_LARGE", f"{label} fraction exceeds bit limit")
        return raw
    if t is not str:
        raise CKHelicityError("INVALID_RATIONAL_TYPE", f"{label} must be int, Fraction, or str")
    if not raw or len(raw) > MAX_RATIONAL_CHARS or not raw.isascii():
        raise CKHelicityError("INVALID_RATIONAL_STR", f"{label} string invalid")
    parts = raw.split("/")
    if len(parts) == 1:
        num_s, den_s = parts[0], None
    elif len(parts) == 2:
        num_s, den_s = parts[0], parts[1]
    else:
        raise CKHelicityError("INVALID_RATIONAL_STR", f"{label} contains multiple '/'")
    neg = num_s.startswith("-")
    num_digits = num_s[1:] if neg else num_s
    if not _is_canonical_unsigned_digits(num_digits):
        raise CKHelicityError("INVALID_RATIONAL_STR", f"{label} numerator not canonical")
    if neg and num_digits == "0":
        raise CKHelicityError("INVALID_RATIONAL_STR", f"{label} negative zero forbidden")
    num_val = -int(num_digits) if neg else int(num_digits)
    if den_s is None:
        den_val = 1
    else:
        if not _is_canonical_unsigned_digits(den_s):
            raise CKHelicityError("INVALID_RATIONAL_STR", f"{label} denominator not canonical")
        den_val = int(den_s)
        if den_val <= 1:
            raise CKHelicityError("INVALID_RATIONAL_STR", f"{label} denominator must be > 1 when '/' present")
        if math.gcd(abs(num_val), den_val) != 1:
            raise CKHelicityError("NON_CANONICAL_RATIONAL", f"{label} fraction is not reduced")
    if num_val.bit_length() > MAX_INT_BITS or den_val.bit_length() > MAX_INT_BITS:
        raise CKHelicityError("RATIONAL_TOO_LARGE", f"{label} exceeds bit limit")
    return Fraction(num_val, den_val)


def format_rational(val: Fraction, label: str = "rational") -> str:
    if type(val) is not Fraction:
        raise CKHelicityError("INVALID_RATIONAL_TYPE", f"{label} must be exact Fraction")
    if val.numerator.bit_length() > MAX_FORMAT_BITS or val.denominator.bit_length() > MAX_FORMAT_BITS:
        raise CKHelicityError("RATIONAL_TOO_LARGE", f"{label} exceeds formatting limit")
    if val.denominator == 1:
        return str(val.numerator)
    return f"{val.numerator}/{val.denominator}"


def _int_exceeds_limits(val: int) -> bool:
    if val.bit_length() > MAX_INT_BITS:
        return True
    return len(str(abs(val))) > MAX_INT_DIGITS


def validate_json_tree_iterative(obj: Any, max_depth: int = MAX_JSON_DEPTH) -> None:
    """Iterative Zone-B validator blocking cycles, deep nesting, floats, subclasses, huge ints, surrogates."""
    limit = require_int(max_depth, "max_depth", lo=1, hi=256)
    # Explicit DFS stack with enter/exit markers to detect reference cycles safely
    stack: list[tuple[Any, int, bool]] = [(obj, 0, False)]
    active_ids: set[int] = set()
    while stack:
        cur, depth, exiting = stack.pop()
        if exiting:
            active_ids.remove(id(cur))
            continue
        if depth > limit:
            raise CKHelicityError("JSON_DEPTH_EXCEEDED", f"JSON nesting exceeds {limit}")
        t = type(cur)
        if t is dict:
            cid = id(cur)
            if cid in active_ids:
                raise CKHelicityError("JSON_CYCLE", "cyclic dict forbidden")
            active_ids.add(cid)
            stack.append((cur, depth, True))
            for k, v in cur.items():
                require_str(k, "json_key", max_len=256)
                stack.append((v, depth + 1, False))
        elif t is list:
            cid = id(cur)
            if cid in active_ids:
                raise CKHelicityError("JSON_CYCLE", "cyclic list forbidden")
            active_ids.add(cid)
            stack.append((cur, depth, True))
            for item in cur:
                stack.append((item, depth + 1, False))
        elif t is int:
            if _int_exceeds_limits(cur):
                raise CKHelicityError("INT_TOO_LARGE", "JSON int exceeds bit/digit limit")
        elif t is str:
            require_str(cur, "json_str", max_len=65536)
        elif t is bool or cur is None:
            continue
        else:
            raise CKHelicityError("FORBIDDEN_JSON_TYPE", f"forbidden JSON value type: {t.__name__}")


def _no_duplicate_keys_hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise CKHelicityError("DUPLICATE_JSON_KEY", f"duplicate JSON key: {k}")
        out[k] = v
    return out


def _forbid_float(token: str) -> Any:
    raise CKHelicityError("FLOAT_FORBIDDEN", f"float literal forbidden: {token}")


def _forbid_constant(token: str) -> Any:
    raise CKHelicityError("NONFINITE_CONSTANT", f"non-finite JSON constant forbidden: {token}")


def parse_strict_json_text(text: Any, require_object: bool = True) -> Any:
    require_bool(require_object, "require_object")
    s = require_str(text, "json_text", max_len=MAX_JSON_BYTES)
    try:
        parsed = json.loads(
            s,
            object_pairs_hook=_no_duplicate_keys_hook,
            parse_float=_forbid_float,
            parse_constant=_forbid_constant,
        )
    except CKHelicityError:
        raise
    except (json.JSONDecodeError, ValueError, RecursionError) as exc:
        raise CKHelicityError("INVALID_JSON", f"strict JSON parse failed: {type(exc).__name__}") from exc
    validate_json_tree_iterative(parsed)
    if require_object and type(parsed) is not dict:
        raise CKHelicityError("JSON_NOT_OBJECT", "JSON root must be an object")
    return parsed


def canonical_json_bytes(obj: Any) -> bytes:
    validate_json_tree_iterative(obj)
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False).encode("ascii")


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


# ---------------------------------------------------------------------------
# Exact Gaussian Rational Algebra Q[i] and Vectors/Matrices in Q[i]^3
# ---------------------------------------------------------------------------

Q0 = Fraction(0, 1)
Q1 = Fraction(1, 1)
QC0: QComplex = (Q0, Q0)
QC1: QComplex = (Q1, Q0)
QCI: QComplex = (Q0, Q1)


def qc(re: int | Fraction, im: int | Fraction = 0) -> QComplex:
    return (parse_exact_rational(re, "re"), parse_exact_rational(im, "im"))


def qc_add(a: QComplex, b: QComplex) -> QComplex:
    return (a[0] + b[0], a[1] + b[1])


def qc_sub(a: QComplex, b: QComplex) -> QComplex:
    return (a[0] - b[0], a[1] - b[1])


def qc_neg(a: QComplex) -> QComplex:
    return (-a[0], -a[1])


def qc_mul(a: QComplex, b: QComplex) -> QComplex:
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def qc_conj(a: QComplex) -> QComplex:
    return (a[0], -a[1])


def qc_norm2(a: QComplex) -> Fraction:
    return a[0] * a[0] + a[1] * a[1]


def qc_scale(s: Fraction, a: QComplex) -> QComplex:
    return (s * a[0], s * a[1])


def qc_mul_i(a: QComplex) -> QComplex:
    return (-a[1], a[0])


def qc_format(a: QComplex) -> list[str]:
    return [format_rational(a[0], "qc.re"), format_rational(a[1], "qc.im")]


def qv_add(u: QVec3, v: QVec3) -> QVec3:
    return (qc_add(u[0], v[0]), qc_add(u[1], v[1]), qc_add(u[2], v[2]))


def qv_sub(u: QVec3, v: QVec3) -> QVec3:
    return (qc_sub(u[0], v[0]), qc_sub(u[1], v[1]), qc_sub(u[2], v[2]))


def qv_conj(u: QVec3) -> QVec3:
    return (qc_conj(u[0]), qc_conj(u[1]), qc_conj(u[2]))


def qv_scale(s: Fraction, u: QVec3) -> QVec3:
    return (qc_scale(s, u[0]), qc_scale(s, u[1]), qc_scale(s, u[2]))


def qv_hdot(u: QVec3, v: QVec3) -> QComplex:
    """Hermitian inner product <u, v> = sum_j conj(u_j) * v_j."""
    return qc_add(
        qc_add(qc_mul(qc_conj(u[0]), v[0]), qc_mul(qc_conj(u[1]), v[1])),
        qc_mul(qc_conj(u[2]), v[2]),
    )


def qv_norm2(u: QVec3) -> Fraction:
    return qc_norm2(u[0]) + qc_norm2(u[1]) + qc_norm2(u[2])


def qv_cross(u: QVec3, v: QVec3) -> QVec3:
    return (
        qc_sub(qc_mul(u[1], v[2]), qc_mul(u[2], v[1])),
        qc_sub(qc_mul(u[2], v[0]), qc_mul(u[0], v[2])),
        qc_sub(qc_mul(u[0], v[1]), qc_mul(u[1], v[0])),
    )


def qv_ik_cross(k: tuple[int, int, int], v: QVec3) -> QVec3:
    """Compute i * (k x v) over exact Q[i]^3."""
    kv = (qc(k[0]), qc(k[1]), qc(k[2]))
    c = qv_cross(kv, v)
    return (qc_mul_i(c[0]), qc_mul_i(c[1]), qc_mul_i(c[2]))


def qmat_vec(m: QMat3, v: QVec3) -> QVec3:
    rows: list[QComplex] = []
    for r in range(3):
        acc = QC0
        for c in range(3):
            acc = qc_add(acc, qc_mul(m[r][c], v[c]))
        rows.append(acc)
    return (rows[0], rows[1], rows[2])


def qmat_mul(a: QMat3, b: QMat3) -> QMat3:
    out: list[QVec3] = []
    for r in range(3):
        row: list[QComplex] = []
        for c in range(3):
            acc = QC0
            for j in range(3):
                acc = qc_add(acc, qc_mul(a[r][j], b[j][c]))
            row.append(acc)
        out.append((row[0], row[1], row[2]))
    return (out[0], out[1], out[2])


def qmat_add(a: QMat3, b: QMat3) -> QMat3:
    return tuple(
        tuple(qc_add(a[r][c], b[r][c]) for c in range(3))
        for r in range(3)
    )  # type: ignore[return-value]


def qmat_dagger(a: QMat3) -> QMat3:
    return tuple(
        tuple(qc_conj(a[c][r]) for c in range(3))
        for r in range(3)
    )  # type: ignore[return-value]


def qmat_eye() -> QMat3:
    return (
        (QC1, QC0, QC0),
        (QC0, QC1, QC0),
        (QC0, QC0, QC1),
    )


def qmat_zero() -> QMat3:
    return (
        (QC0, QC0, QC0),
        (QC0, QC0, QC0),
        (QC0, QC0, QC0),
    )


# ---------------------------------------------------------------------------
# Theorem 1: Knotted Flux-Tube Abelian U(1) Chern-Simons Helicity & Framing
# ---------------------------------------------------------------------------

def evaluate_flux_tube_helicity(
    name: str,
    fluxes: Sequence[Fraction],
    crossings: Sequence[tuple[int, int, int]],
    twists: Sequence[Fraction],
    ri_kinks: Sequence[int] | None = None,
) -> dict[str, Any]:
    """Exact combinatorial Gauss linking, writhe/twist framing, and U(1) helicity."""
    clean_name = require_str(name, "link.name", max_len=128)
    if type(fluxes) not in (list, tuple) or len(fluxes) == 0:
        raise CKHelicityError("INVALID_FLUXES", "fluxes must be a non-empty list/tuple")
    n = len(fluxes)
    phi = [parse_exact_rational(f, f"flux[{i}]") for i, f in enumerate(fluxes)]
    if type(twists) not in (list, tuple) or len(twists) != n:
        raise CKHelicityError("INVALID_TWISTS", "twists must match component count")
    tw = [parse_exact_rational(t, f"twist[{i}]") for i, t in enumerate(twists)]
    if type(crossings) not in (list, tuple):
        raise CKHelicityError("INVALID_CROSSINGS", "crossings must be list/tuple")

    pair_sum = [[0] * n for _ in range(n)]
    writhe = [0] * n
    for idx, cr in enumerate(crossings):
        if type(cr) not in (list, tuple) or len(cr) != 3:
            raise CKHelicityError("INVALID_CROSSING", f"crossing[{idx}] must be (over, under, sign)")
        over = require_int(cr[0], f"crossing[{idx}].over", lo=0, hi=n - 1)
        under = require_int(cr[1], f"crossing[{idx}].under", lo=0, hi=n - 1)
        sign = require_int(cr[2], f"crossing[{idx}].sign", lo=-1, hi=1)
        if sign == 0:
            raise CKHelicityError("INVALID_CROSSING_SIGN", f"crossing[{idx}] sign must be +1 or -1")
        if over == under:
            writhe[over] += sign
        else:
            pair_sum[over][under] += sign
            pair_sum[under][over] += sign

    lk_matrix = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if pair_sum[i][j] % 2 != 0:
                raise CKHelicityError(
                    "ODD_CROSSING_SUM",
                    f"inter-component crossing sum ({i},{j})={pair_sum[i][j]} must be even",
                )
            lk_val = pair_sum[i][j] // 2
            lk_matrix[i][j] = lk_val
            lk_matrix[j][i] = lk_val

    self_linking = [tw[i] + Fraction(writhe[i], 1) for i in range(n)]
    h_mutual = Q0
    for i in range(n):
        for j in range(n):
            if i != j:
                h_mutual += phi[i] * phi[j] * Fraction(lk_matrix[i][j], 1)
    h_self = sum((phi[i] * phi[i] * self_linking[i] for i in range(n)), Q0)
    h_total = h_mutual + h_self

    # Verify Calugareanu-White-Fuller Reidemeister I framing invariance
    if ri_kinks is None:
        kinks = [0] * n
    else:
        if type(ri_kinks) not in (list, tuple) or len(ri_kinks) != n:
            raise CKHelicityError("INVALID_RI_KINKS", "ri_kinks must match component count")
        kinks = [require_int(k, f"ri_kinks[{i}]", lo=-64, hi=64) for i, k in enumerate(ri_kinks)]

    writhe_ri = [writhe[i] + kinks[i] for i in range(n)]
    tw_ri = [tw[i] - Fraction(kinks[i], 1) for i in range(n)]
    sl_ri = [tw_ri[i] + Fraction(writhe_ri[i], 1) for i in range(n)]
    h_total_ri = h_mutual + sum((phi[i] * phi[i] * sl_ri[i] for i in range(n)), Q0)
    ri_invariant = (sl_ri, h_total_ri) == (self_linking, h_total)

    return {
        "name": clean_name,
        "n_components": n,
        "n_crossings": len(crossings),
        "fluxes": [format_rational(f) for f in phi],
        "twists": [format_rational(t) for t in tw],
        "writhes": writhe,
        "self_linkings": [format_rational(s) for s in self_linking],
        "linking_matrix": lk_matrix,
        "h_mutual": format_rational(h_mutual),
        "h_self": format_rational(h_self),
        "h_total": format_rational(h_total),
        "ri_kinks_tested": kinks,
        "ri_framing_invariant": ri_invariant,
    }


def _torus_parallel_cable_crossings(p: int, q: int) -> list[tuple[int, int, int]]:
    """Explicit positive-braid crossings for a 2-component parallel T(p,q) cable.

    Each component has minimal positive torus-braid writhe (p - 1) * q, and the two
    parallel torus-surface curves share 2 * p * q positive inter-component crossings
    (p * q with comp 0 over 1, p * q with comp 1 over 0), giving Lk(C1, C2) = p * q.
    """
    p_i = require_int(p, "torus.p", lo=2, hi=16)
    q_i = require_int(q, "torus.q", lo=2, hi=16)
    if math.gcd(p_i, q_i) != 1:
        raise CKHelicityError("TORUS_NOT_COPRIME", "torus knot parameters (p, q) must be coprime")
    self_n = (p_i - 1) * q_i
    inter_half = p_i * q_i
    crossings: list[tuple[int, int, int]] = []
    for _ in range(self_n):
        crossings.append((0, 0, 1))
        crossings.append((1, 1, 1))
    for _ in range(inter_half):
        crossings.append((0, 1, 1))
        crossings.append((1, 0, 1))
    return crossings


def build_theorem1_flux_tubes() -> dict[str, Any]:
    """Certify Theorem 1 across unknot, +/-Hopf, torus cables, Whitehead, and Borromean rings."""
    unknot = evaluate_flux_tube_helicity(
        "unknot_ri_compensated",
        [Fraction(3, 2)],
        [],
        [Q0],
        ri_kinks=[2],
    )
    hopf_pos = evaluate_flux_tube_helicity(
        "hopf_link_positive",
        [Fraction(3, 2), Fraction(5, 3)],
        [(0, 1, 1), (1, 0, 1)],
        [Q0, Q0],
        ri_kinks=[1, -1],
    )
    hopf_neg = evaluate_flux_tube_helicity(
        "hopf_link_negative",
        [Fraction(3, 2), Fraction(5, 3)],
        [(0, 1, -1), (1, 0, -1)],
        [Q0, Q0],
        ri_kinks=[-1, 1],
    )
    chiral_antisymmetry = (
        parse_exact_rational(hopf_pos["h_mutual"]) == -parse_exact_rational(hopf_neg["h_mutual"])
    )

    torus_specs = [
        ("trefoil_2_3_parallel_cable", 2, 3, [Fraction(1, 1), Fraction(2, 1)]),
        ("cinquefoil_2_5_parallel_cable", 2, 5, [Fraction(1, 2), Fraction(3, 2)]),
        ("torus_3_4_parallel_cable", 3, 4, [Fraction(1, 1), Fraction(1, 3)]),
    ]
    torus_results: list[dict[str, Any]] = []
    for label, p_val, q_val, flx in torus_specs:
        # Torus-surface framing: Wr = (p-1)*q, Tw_torus = q => Wr + Tw = p*q == Lk(C1, C2)
        res = evaluate_flux_tube_helicity(
            label,
            flx,
            _torus_parallel_cable_crossings(p_val, q_val),
            [Fraction(q_val, 1), Fraction(q_val, 1)],
            ri_kinks=[1, -2],
        )
        res["torus_p"] = p_val
        res["torus_q"] = q_val
        res["expected_pq_linking"] = p_val * q_val
        res["torus_framing_matches_pq"] = (
            res["linking_matrix"][0][1],
            res["self_linkings"],
        ) == (p_val * q_val, [str(p_val * q_val), str(p_val * q_val)])
        torus_results.append(res)

    whitehead = evaluate_flux_tube_helicity(
        "whitehead_link",
        [Fraction(2, 1), Fraction(3, 1)],
        [(0, 1, 1), (1, 0, 1), (0, 1, -1), (1, 0, -1), (0, 0, 1)],
        [Fraction(-1, 1), Q0],
        ri_kinks=[1, 0],
    )

    # Standard 6-crossing cyclic Borromean rings (0 over 1, 1 over 2, 2 over 0; each pair +1/-1)
    borromean = evaluate_flux_tube_helicity(
        "borromean_rings_obstruction",
        [Fraction(2, 1), Fraction(3, 1), Fraction(5, 1)],
        [(0, 1, 1), (0, 1, -1), (1, 2, 1), (1, 2, -1), (2, 0, 1), (2, 0, -1)],
        [Q0, Q0, Q0],
        ri_kinks=[1, -1, 2],
    )
    borromean_all_pairwise_zero = all(
        borromean["linking_matrix"][i][j] == 0 for i in range(3) for j in range(3)
    )

    # Negative must_fail control: odd inter-component crossing sum must fail closed
    odd_rejected = False
    odd_error_code = ""
    try:
        evaluate_flux_tube_helicity("bad_odd_crossings", [Q1, Q1], [(0, 1, 1)], [Q0, Q0])
    except CKHelicityError as exc:
        odd_rejected = exc.code == "ODD_CROSSING_SUM"
        odd_error_code = exc.code

    return {
        "unknot": unknot,
        "hopf_positive": hopf_pos,
        "hopf_negative": hopf_neg,
        "hopf_chiral_antisymmetry": chiral_antisymmetry,
        "torus_cables": torus_results,
        "whitehead_link": whitehead,
        "borromean_rings": borromean,
        "law5_borromean_obstruction": {
            "all_pairwise_lk_zero": borromean_all_pairwise_zero,
            "abelian_mutual_helicity": borromean["h_mutual"],
            "abelian_u1_blind_to_brunnian_triple_linking": (borromean_all_pairwise_zero, borromean["h_mutual"]) == (True, "0"),
            "milnor_triple_invariant_abs_reference": 1,
        },
        "must_fail_odd_crossing_sum": {
            "rejected": odd_rejected,
            "error_code": odd_error_code,
        },
    }


# ---------------------------------------------------------------------------
# Theorem 2A: Cylindrical Chandrasekhar-Kendall Exact Radial Power Series
# ---------------------------------------------------------------------------

def _series_add(a: Mapping[int, QComplex], b: Mapping[int, QComplex]) -> dict[int, QComplex]:
    out = dict(a)
    for k, v in b.items():
        nv = qc_add(out.get(k, QC0), v)
        if nv == QC0:
            out.pop(k, None)
        else:
            out[k] = nv
    return out


def _series_sub(a: Mapping[int, QComplex], b: Mapping[int, QComplex]) -> dict[int, QComplex]:
    out = dict(a)
    for k, v in b.items():
        nv = qc_sub(out.get(k, QC0), v)
        if nv == QC0:
            out.pop(k, None)
        else:
            out[k] = nv
    return out


def _series_scale(c: QComplex, a: Mapping[int, QComplex]) -> dict[int, QComplex]:
    if c == QC0:
        return {}
    out: dict[int, QComplex] = {}
    for k, v in a.items():
        nv = qc_mul(c, v)
        if nv != QC0:
            out[k] = nv
    return out


def _series_shift(a: Mapping[int, QComplex], delta: int) -> dict[int, QComplex]:
    return {k + delta: v for k, v in a.items() if v != QC0}


def _series_deriv(a: Mapping[int, QComplex]) -> dict[int, QComplex]:
    out: dict[int, QComplex] = {}
    for k, v in a.items():
        if k != 0:
            nv = qc_scale(Fraction(k, 1), v)
            if nv != QC0:
                out[k - 1] = nv
    return out


def verify_cylindrical_ck_series(
    lam: Fraction,
    kz: Fraction,
    m_mode: int,
    degree_terms: int,
    gamma_sq_override: Fraction | None = None,
) -> dict[str, Any]:
    """Certify div(B) == 0 and curl(B) == lam * B on exact formal Bessel series J_m(gamma r)."""
    lam_q = parse_exact_rational(lam, "ck.lambda")
    kz_q = parse_exact_rational(kz, "ck.kz")
    m = require_int(m_mode, "ck.m", lo=0, hi=8)
    deg = require_int(degree_terms, "ck.degree_terms", lo=3, hi=16)

    gamma_sq = lam_q * lam_q - kz_q * kz_q if gamma_sq_override is None else parse_exact_rational(gamma_sq_override, "ck.gamma_sq")

    # Exact Bessel series f(r) = sum_{j=0}^{deg} c_j r^{m + 2j}
    f_ser: dict[int, QComplex] = {}
    c_j = Q1
    f_ser[m] = (c_j, Q0)
    for j in range(1, deg + 1):
        c_j = -c_j * gamma_sq / Fraction(4 * j * (m + j), 1)
        if c_j != Q0:
            f_ser[m + 2 * j] = (c_j, Q0)

    df = _series_deriv(f_ser)
    d2f = _series_deriv(df)
    f_over_r = _series_shift(f_ser, -1)
    df_over_r = _series_shift(df, -1)
    f_over_r2 = _series_shift(f_ser, -2)

    # B_r = i * (lam * m * f/r + kz * f')
    b_r = _series_scale(
        QCI,
        _series_add(
            _series_scale((lam_q * Fraction(m, 1), Q0), f_over_r),
            _series_scale((kz_q, Q0), df),
        ),
    )
    # B_theta = -(lam * f' + m * kz * f/r)
    b_th = _series_scale(
        (-Q1, Q0),
        _series_add(
            _series_scale((lam_q, Q0), df),
            _series_scale((Fraction(m, 1) * kz_q, Q0), f_over_r),
        ),
    )
    # B_z = -(f'' + (1/r) f' - (m^2 / r^2) f)
    b_z = _series_scale(
        (-Q1, Q0),
        _series_sub(
            _series_add(d2f, df_over_r),
            _series_scale((Fraction(m * m, 1), Q0), f_over_r2),
        ),
    )

    # Exact cylindrical divergence: (1/r) d_r(r B_r) + (i m / r) B_th + i kz B_z
    div_b = _series_add(
        _series_add(
            _series_shift(_series_deriv(_series_shift(b_r, 1)), -1),
            _series_scale((Q0, Fraction(m, 1)), _series_shift(b_th, -1)),
        ),
        _series_scale((Q0, kz_q), b_z),
    )

    # Exact cylindrical curl:
    # (curl B)_r     = (i m / r) B_z - i kz B_th
    # (curl B)_theta = i kz B_r - d_r(B_z)
    # (curl B)_z     = (1/r) d_r(r B_th) - (i m / r) B_r
    curl_r = _series_sub(
        _series_scale((Q0, Fraction(m, 1)), _series_shift(b_z, -1)),
        _series_scale((Q0, kz_q), b_th),
    )
    curl_th = _series_sub(
        _series_scale((Q0, kz_q), b_r),
        _series_deriv(b_z),
    )
    curl_z = _series_sub(
        _series_shift(_series_deriv(_series_shift(b_th, 1)), -1),
        _series_scale((Q0, Fraction(m, 1)), _series_shift(b_r, -1)),
    )

    res_r = _series_sub(curl_r, _series_scale((lam_q, Q0), b_r))
    res_th = _series_sub(curl_th, _series_scale((lam_q, Q0), b_th))
    res_z = _series_sub(curl_z, _series_scale((lam_q, Q0), b_z))

    # Truncation boundary: B_z matches gamma^2 * f through degree m + 2*deg - 2,
    # so curl(B) - lam*B vanishes identically for all radial powers <= m + 2*deg - 3.
    verified_max_power = m + 2 * deg - 3
    div_nonzero = [p for p in sorted(div_b.keys()) if p <= verified_max_power]
    curl_r_nonzero = [p for p in sorted(res_r.keys()) if p <= verified_max_power]
    curl_th_nonzero = [p for p in sorted(res_th.keys()) if p <= verified_max_power]
    curl_z_nonzero = [p for p in sorted(res_z.keys()) if p <= verified_max_power]

    return {
        "lambda": format_rational(lam_q),
        "kz": format_rational(kz_q),
        "gamma_sq": format_rational(gamma_sq),
        "m": m,
        "degree_terms": deg,
        "verified_max_power": verified_max_power,
        "div_zero_exact": len(div_nonzero) == 0,
        "curl_eq_lambda_b_exact": (
            len(curl_r_nonzero) == 0 and len(curl_th_nonzero) == 0 and len(curl_z_nonzero) == 0
        ),
        "nonzero_residual_powers": {
            "div": div_nonzero,
            "curl_r": curl_r_nonzero,
            "curl_theta": curl_th_nonzero,
            "curl_z": curl_z_nonzero,
        },
        "leading_bz_coeff": qc_format(b_z.get(m, QC0)),
    }


# ---------------------------------------------------------------------------
# Theorem 2B: Pythagorean-Norm T^3 Helical Projectors & Woltjer-Arnold Bound
# ---------------------------------------------------------------------------

def exact_integer_norm(k: tuple[int, int, int]) -> int:
    if type(k) not in (list, tuple) or len(k) != 3:
        raise CKHelicityError("INVALID_WAVEVECTOR", "wavevector must be 3-tuple of int")
    k0 = require_int(k[0], "k[0]", lo=-1000, hi=1000)
    k1 = require_int(k[1], "k[1]", lo=-1000, hi=1000)
    k2 = require_int(k[2], "k[2]", lo=-1000, hi=1000)
    n2 = k0 * k0 + k1 * k1 + k2 * k2
    if n2 == 0:
        raise CKHelicityError("ZERO_WAVEVECTOR", "wavevector must be nonzero")
    root = math.isqrt(n2)
    if root * root != n2:
        raise CKHelicityError("NON_PYTHAGOREAN_WAVEVECTOR", f"wavevector {k} does not have integer norm")
    return root


def helical_projectors_exact(k: tuple[int, int, int]) -> tuple[int, QMat3, QMat3, QMat3]:
    """Build exact Q[i]^{3x3} helical projectors P_0, P_+, P_- for Pythagorean wavevector k."""
    norm_k = exact_integer_norm(k)
    kh = (Fraction(k[0], norm_k), Fraction(k[1], norm_k), Fraction(k[2], norm_k))
    half = Fraction(1, 2)

    p0_rows: list[QVec3] = []
    pp_rows: list[QVec3] = []
    pm_rows: list[QVec3] = []
    # Skew matrix K_x: (K_x v) = k_hat x v
    kx = (
        (Q0, -kh[2], kh[1]),
        (kh[2], Q0, -kh[0]),
        (-kh[1], kh[0], Q0),
    )
    for r in range(3):
        r0: list[QComplex] = []
        rp: list[QComplex] = []
        rm: list[QComplex] = []
        for c in range(3):
            p0_rc = kh[r] * kh[c]
            perp_rc = (Q1 if r == c else Q0) - p0_rc
            r0.append((p0_rc, Q0))
            rp.append((half * perp_rc, half * kx[r][c]))
            rm.append((half * perp_rc, -half * kx[r][c]))
        p0_rows.append((r0[0], r0[1], r0[2]))
        pp_rows.append((rp[0], rp[1], rp[2]))
        pm_rows.append((rm[0], rm[1], rm[2]))
    return (
        norm_k,
        (p0_rows[0], p0_rows[1], p0_rows[2]),
        (pp_rows[0], pp_rows[1], pp_rows[2]),
        (pm_rows[0], pm_rows[1], pm_rows[2]),
    )


def complex_mat3_to_real_sym6(m: QMat3) -> list[list[Fraction]]:
    """Real 6x6 representation [[A, -B], [B, A]] of Hermitian 3x3 matrix M = A + i B."""
    out = [[Q0] * 6 for _ in range(6)]
    for r in range(3):
        for c in range(3):
            a_rc, b_rc = m[r][c]
            out[r][c] = a_rc
            out[r][c + 3] = -b_rc
            out[r + 3][c] = b_rc
            out[r + 3][c + 3] = a_rc
    return out


def verify_helical_projector_algebra(k: tuple[int, int, int]) -> dict[str, Any]:
    norm_k, p0, pp, pm = helical_projectors_exact(k)
    eye = qmat_eye()
    zero = qmat_zero()
    sum_eq_eye = qmat_add(qmat_add(p0, pp), pm) == eye
    idempotent = (qmat_mul(p0, p0), qmat_mul(pp, pp), qmat_mul(pm, pm)) == (p0, pp, pm)
    orthogonal = (
        qmat_mul(p0, pp),
        qmat_mul(p0, pm),
        qmat_mul(pp, pm),
        qmat_mul(pp, p0),
        qmat_mul(pm, p0),
        qmat_mul(pm, pp),
    ) == (zero, zero, zero, zero, zero, zero)
    hermitian = (qmat_dagger(p0), qmat_dagger(pp), qmat_dagger(pm)) == (p0, pp, pm)
    # Check i k x (P_+/- e_j) == +/- ||k|| (P_+/- e_j) for all 3 standard basis vectors
    curl_eigen_ok = True
    basis = ((QC1, QC0, QC0), (QC0, QC1, QC0), (QC0, QC0, QC1))
    nk_q = Fraction(norm_k, 1)
    for ej in basis:
        vp = qmat_vec(pp, ej)
        vm = qmat_vec(pm, ej)
        if qv_ik_cross(k, vp) != qv_scale(nk_q, vp):
            curl_eigen_ok = False
        if qv_ik_cross(k, vm) != qv_scale(-nk_q, vm):
            curl_eigen_ok = False

    # Exact 6x6 real-symmetric representation check (M^T == M, M^2 == M, Tr(M) == 2)
    m6_p = complex_mat3_to_real_sym6(pp)
    m6_m = complex_mat3_to_real_sym6(pm)
    sym6_ok = all(
        m[r][c] == m[c][r]
        for m in (m6_p, m6_m)
        for r in range(6)
        for c in range(6)
    )
    tr6_p = sum((m6_p[i][i] for i in range(6)), Q0)
    tr6_m = sum((m6_m[i][i] for i in range(6)), Q0)

    return {
        "k": [k[0], k[1], k[2]],
        "norm_k": norm_k,
        "completeness_eq_I3": sum_eq_eye,
        "idempotent": idempotent,
        "orthogonal": orthogonal,
        "hermitian": hermitian,
        "curl_eigen_exact": curl_eigen_ok,
        "real_sym6_symmetric": sym6_ok,
        "real_sym6_traces": [format_rational(tr6_p), format_rational(tr6_m)],
    }


def evaluate_torus_field_energy_helicity(
    name: str,
    half_spectrum: Sequence[tuple[tuple[int, int, int], QVec3]],
) -> dict[str, Any]:
    """Evaluate exact energy E, helicity H (two independent formulas), and Woltjer-Arnold bound.

    `half_spectrum` lists positive-halfspace modes (k, seed_vec); each mode is projected
    onto the solenoidal subspace and paired with (-k, conj(B(k))) to enforce real fields.
    """
    clean_name = require_str(name, "field.name", max_len=128)
    if type(half_spectrum) not in (list, tuple) or len(half_spectrum) == 0:
        raise CKHelicityError("EMPTY_SPECTRUM", "spectrum must be non-empty")

    full_b: dict[tuple[int, int, int], QVec3] = {}
    for k, b_raw in half_spectrum:
        if k in full_b:
            raise CKHelicityError("DUPLICATE_MODE", f"duplicate mode or conjugate pair for k={k}")
        _, p0, pp, pm = helical_projectors_exact(k)
        # Ensure input is solenoidal (P_0 B == 0)
        if qmat_vec(p0, b_raw) != (QC0, QC0, QC0):
            raise CKHelicityError("NON_SOLENOIDAL_FIELD", f"mode k={k} violates k . B(k) == 0")
        full_b[k] = b_raw
        full_b[(-k[0], -k[1], -k[2])] = qv_conj(b_raw)

    e_total = Q0
    h_spectral = Q0
    h_ab_direct = QC0
    min_norm: int | None = None
    max_norm = 0
    pure_plus = True
    pure_minus = True

    for k, b_k in full_b.items():
        nk, _, pp, pm = helical_projectors_exact(k)
        if min_norm is None or nk < min_norm:
            min_norm = nk
        if nk > max_norm:
            max_norm = nk
        bp = qmat_vec(pp, b_k)
        bm = qmat_vec(pm, b_k)
        np2 = qv_norm2(bp)
        nm2 = qv_norm2(bm)
        if nm2 != Q0:
            pure_plus = False
        if np2 != Q0:
            pure_minus = False
        e_total += Fraction(1, 2) * (np2 + nm2)
        h_spectral += (np2 - nm2) / Fraction(nk, 1)
        # Independent Coulomb-gauge vector potential A(k) = (i k x B(k)) / ||k||^2
        a_k = qv_scale(Fraction(1, nk * nk), qv_ik_cross(k, b_k))
        h_ab_direct = qc_add(h_ab_direct, qv_hdot(a_k, b_k))

    direct_matches = h_ab_direct == (h_spectral, Q0)
    lam1 = Fraction(min_norm if min_norm is not None else 1, 1)
    slack = Fraction(2, 1) * e_total - lam1 * abs(h_spectral)

    is_single_shell = min_norm == max_norm
    is_beltrami_minimal = is_single_shell and (pure_plus or pure_minus)
    saturated = slack == Q0

    return {
        "name": clean_name,
        "n_full_modes": len(full_b),
        "lambda_1": format_rational(lam1),
        "energy_E": format_rational(e_total),
        "helicity_H": format_rational(h_spectral),
        "direct_AB_matches_spectral": direct_matches,
        "woltjer_arnold_slack_2E_minus_lam1_absH": format_rational(slack),
        "woltjer_arnold_holds": slack >= Q0,
        "woltjer_arnold_saturated": saturated,
        "is_minimal_beltrami_ck_state": is_beltrami_minimal,
    }


# ---------------------------------------------------------------------------
# Theorem 2C: Exact 3D Polynomial Chandrasekhar-Fermi (1953) Virial Identity
# ---------------------------------------------------------------------------

Poly3 = dict[tuple[int, int, int], Fraction]


def _p3_add(a: Poly3, b: Poly3) -> Poly3:
    out = dict(a)
    for exp, c in b.items():
        nv = out.get(exp, Q0) + c
        if nv == Q0:
            out.pop(exp, None)
        else:
            out[exp] = nv
    return out


def _p3_sub(a: Poly3, b: Poly3) -> Poly3:
    out = dict(a)
    for exp, c in b.items():
        nv = out.get(exp, Q0) - c
        if nv == Q0:
            out.pop(exp, None)
        else:
            out[exp] = nv
    return out


def _p3_mul(a: Poly3, b: Poly3) -> Poly3:
    out: Poly3 = {}
    for (ax, ay, az), ca in a.items():
        for (bx, by, bz), cb in b.items():
            key = (ax + bx, ay + by, az + bz)
            nv = out.get(key, Q0) + ca * cb
            if nv == Q0:
                out.pop(key, None)
            else:
                out[key] = nv
    return out


def _p3_scale(s: Fraction, a: Poly3) -> Poly3:
    if s == Q0:
        return {}
    return {k: s * v for k, v in a.items()}


def _p3_deriv(a: Poly3, axis: int) -> Poly3:
    out: Poly3 = {}
    for exp, c in a.items():
        deg = exp[axis]
        if deg > 0:
            nexp = list(exp)
            nexp[axis] = deg - 1
            out[(nexp[0], nexp[1], nexp[2])] = c * Fraction(deg, 1)
    return out


def _p3_int_cube(a: Poly3) -> Fraction:
    """Exact integral of polynomial over [-1, 1]^3."""
    total = Q0
    for (ex, ey, ez), c in a.items():
        if (ex % 2 == 0) and (ey % 2 == 0) and (ez % 2 == 0):
            total += c * Fraction(8, (ex + 1) * (ey + 1) * (ez + 1))
    return total


def _p3_int_face(a: Poly3, axis: int, val: int) -> Fraction:
    """Exact surface integral over face x_axis = val (+1 or -1) of [-1, 1]^3."""
    total = Q0
    other = [i for i in range(3) if i != axis]
    for exp, c in a.items():
        if (exp[other[0]] % 2 == 0) and (exp[other[1]] % 2 == 0):
            sign = -1 if (val == -1 and exp[axis] % 2 == 1) else 1
            total += c * Fraction(4 * sign, (exp[other[0]] + 1) * (exp[other[1]] + 1))
    return total


def build_chandrasekhar_fermi_virial() -> dict[str, Any]:
    """Certify exact 3D Maxwell stress virial divergence identity and no-self-confinement."""
    # Exact polynomial vector potential A(x,y,z) => B = curl(A) is identically divergence-free
    ax: Poly3 = {(0, 2, 1): Q1, (1, 0, 2): Fraction(1, 2)}
    ay: Poly3 = {(2, 0, 1): Fraction(-1, 1), (0, 1, 2): Fraction(3, 2)}
    az: Poly3 = {(1, 2, 0): Fraction(2, 1), (2, 1, 0): Fraction(-1, 2)}

    bx = _p3_sub(_p3_deriv(az, 1), _p3_deriv(ay, 2))
    by = _p3_sub(_p3_deriv(ax, 2), _p3_deriv(az, 0))
    bz = _p3_sub(_p3_deriv(ay, 0), _p3_deriv(ax, 1))
    b_vec = (bx, by, bz)

    div_b = _p3_add(_p3_add(_p3_deriv(bx, 0), _p3_deriv(by, 1)), _p3_deriv(bz, 2))
    # Current J = curl(B)
    jx = _p3_sub(_p3_deriv(bz, 1), _p3_deriv(by, 2))
    jy = _p3_sub(_p3_deriv(bx, 2), _p3_deriv(bz, 0))
    jz = _p3_sub(_p3_deriv(by, 0), _p3_deriv(bx, 1))
    # Lorentz force J x B
    lorentz = (
        _p3_sub(_p3_mul(jy, bz), _p3_mul(jz, by)),
        _p3_sub(_p3_mul(jz, bx), _p3_mul(jx, bz)),
        _p3_sub(_p3_mul(jx, by), _p3_mul(jy, bx)),
    )
    coords: tuple[Poly3, Poly3, Poly3] = (
        {(1, 0, 0): Q1},
        {(0, 1, 0): Q1},
        {(0, 0, 1): Q1},
    )
    x_dot_jxb = _p3_add(
        _p3_add(_p3_mul(coords[0], lorentz[0]), _p3_mul(coords[1], lorentz[1])),
        _p3_mul(coords[2], lorentz[2]),
    )

    b2 = _p3_add(_p3_add(_p3_mul(bx, bx), _p3_mul(by, by)), _p3_mul(bz, bz))
    half_b2 = _p3_scale(Fraction(1, 2), b2)

    # Maxwell stress tensor T_ij = B_i B_j - (1/2) |B|^2 delta_ij, virial flux F_j = sum_i x_i T_ij
    f_flux: list[Poly3] = []
    for j in range(3):
        acc: Poly3 = {}
        for i in range(3):
            t_ij = _p3_mul(b_vec[i], b_vec[j])
            if i == j:
                t_ij = _p3_sub(t_ij, half_b2)
            acc = _p3_add(acc, _p3_mul(coords[i], t_ij))
        f_flux.append(acc)

    div_f = _p3_add(_p3_add(_p3_deriv(f_flux[0], 0), _p3_deriv(f_flux[1], 1)), _p3_deriv(f_flux[2], 2))
    # Pointwise Chandrasekhar-Fermi identity: div(x . T) + (1/2)|B|^2 - x . (J x B) == 0
    pointwise_residual = _p3_sub(_p3_add(div_f, half_b2), x_dot_jxb)

    # Integrate over [-1, 1]^3: M_vol - int x.(J x B) == -oint (x . T) . dS
    mag_energy = _p3_int_cube(half_b2)
    lorentz_virial = _p3_int_cube(x_dot_jxb)
    surface_stress_flux = Q0
    for axis in range(3):
        surface_stress_flux += _p3_int_face(f_flux[axis], axis, 1) - _p3_int_face(f_flux[axis], axis, -1)

    gauss_virial_exact = (surface_stress_flux + mag_energy - lorentz_virial) == Q0

    # Scalar virial budget table: 2T + 3(gamma - 1)U + M + Omega - Sigma_S == 0
    def _virial_row(
        label: str,
        t_kin: Fraction,
        u_th: Fraction,
        gamma_ad: Fraction,
        m_mag: Fraction,
        omega_grav: Fraction,
        sigma_surf: Fraction,
    ) -> dict[str, Any]:
        lhs = Fraction(2, 1) * t_kin + Fraction(3, 1) * (gamma_ad - Q1) * u_th + m_mag + omega_grav
        residual = lhs - sigma_surf
        return {
            "case": label,
            "T": format_rational(t_kin),
            "U": format_rational(u_th),
            "gamma": format_rational(gamma_ad),
            "M": format_rational(m_mag),
            "Omega": format_rational(omega_grav),
            "Sigma_S": format_rational(sigma_surf),
            "virial_residual": format_rational(residual),
            "equilibrium_admissible": residual == Q0,
        }

    cases = [
        _virial_row("self_confined_force_free_vacuum_R3", Q0, Q0, Fraction(5, 3), mag_energy, Q0, Q0),
        _virial_row("gravity_confined_magnetized_star", Q0, Fraction(5, 1), Fraction(5, 3), mag_energy, -(Fraction(10, 1) + mag_energy), Q0),
        _virial_row("wall_confined_force_free_spheromak", Q0, Q0, Fraction(5, 3), mag_energy, Q0, mag_energy),
    ]

    return {
        "polynomial_div_B_zero": len(div_b) == 0,
        "pointwise_maxwell_virial_identity_zero": len(pointwise_residual) == 0,
        "cube_magnetic_energy_M": format_rational(mag_energy),
        "cube_lorentz_virial_int": format_rational(lorentz_virial),
        "cube_surface_stress_flux": format_rational(surface_stress_flux),
        "gauss_virial_cube_identity_exact": gauss_virial_exact,
        "self_confined_R3_obstructed": not cases[0]["equilibrium_admissible"],
        "scalar_virial_cases": cases,
    }


def build_theorem2_ck_and_woltjer() -> dict[str, Any]:
    cylindrical_modes = [
        verify_cylindrical_ck_series(Fraction(5, 1), Fraction(3, 1), 0, 8),
        verify_cylindrical_ck_series(Fraction(13, 2), Fraction(5, 2), 1, 8),
        verify_cylindrical_ck_series(Fraction(-10, 1), Fraction(6, 1), 2, 7),
    ]
    broken_dispersion = verify_cylindrical_ck_series(
        Fraction(5, 1), Fraction(3, 1), 0, 6, gamma_sq_override=Fraction(17, 1)
    )

    pythagorean_k = [
        (1, 0, 0),
        (0, 1, 0),
        (0, 0, 1),
        (1, 2, 2),
        (2, 3, 6),
        (1, 4, 8),
        (4, 4, 7),
    ]
    projector_checks = [verify_helical_projector_algebra(k) for k in pythagorean_k]

    # Build exact minimal Beltrami CK state on lowest shell ||k|| = 1 (pure + helicity)
    _, _, pp_x, _ = helical_projectors_exact((1, 0, 0))
    _, _, pp_y, _ = helical_projectors_exact((0, 1, 0))
    _, _, pp_z, _ = helical_projectors_exact((0, 0, 1))
    b_beltrami = [
        ((1, 0, 0), qmat_vec(pp_x, (QC0, qc(2), QC0))),
        ((0, 1, 0), qmat_vec(pp_y, (QC0, QC0, qc(3)))),
        ((0, 0, 1), qmat_vec(pp_z, (qc(1, 1), QC0, QC0))),
    ]
    woltjer_saturated = evaluate_torus_field_energy_helicity("lowest_shell_beltrami_ck_saturated", b_beltrami)

    # Mixed-shell / mixed-helicity state across ||k|| = 1, 3, 7, 9
    _, _, pp_3, pm_3 = helical_projectors_exact((1, 2, 2))
    _, _, pp_7, pm_7 = helical_projectors_exact((2, 3, 6))
    _, _, _, pm_9 = helical_projectors_exact((4, 4, 7))
    b_mixed = [
        ((1, 0, 0), qmat_vec(pp_x, (QC0, qc(2), QC0))),
        ((1, 2, 2), qv_add(qmat_vec(pp_3, (qc(3), QC0, QC0)), qmat_vec(pm_3, (QC0, qc(1), QC0)))),
        ((2, 3, 6), qv_add(qmat_vec(pp_7, (QC0, QC0, qc(7))), qmat_vec(pm_7, (qc(7, -7), QC0, QC0)))),
        ((4, 4, 7), qmat_vec(pm_9, (qc(9), QC0, QC0))),
    ]
    woltjer_strict = evaluate_torus_field_energy_helicity("mixed_shell_helical_strict_slack", b_mixed)

    virial = build_chandrasekhar_fermi_virial()

    return {
        "cylindrical_ck_modes": cylindrical_modes,
        "must_fail_broken_dispersion": {
            "div_zero_exact": broken_dispersion["div_zero_exact"],
            "curl_eq_lambda_b_exact": broken_dispersion["curl_eq_lambda_b_exact"],
            "residual_detected": not broken_dispersion["curl_eq_lambda_b_exact"],
        },
        "pythagorean_helical_projectors": projector_checks,
        "woltjer_arnold_saturated": woltjer_saturated,
        "woltjer_arnold_strict_slack": woltjer_strict,
        "chandrasekhar_fermi_virial": virial,
    }


# ---------------------------------------------------------------------------
# Theorem 3A: Exact Helical Triad-by-Triad Ideal Helicity Conservation
# ---------------------------------------------------------------------------

def verify_helical_triad_helicity_conservation(
    name: str,
    triad_k: tuple[tuple[int, int, int], tuple[int, int, int], tuple[int, int, int]],
    b_modes: tuple[QVec3, QVec3, QVec3],
    u_modes: tuple[QVec3, QVec3, QVec3],
    eta_resistivity: Fraction = Q0,
) -> dict[str, Any]:
    """Exact Q[i] proof that dH_triad/dt == 0 for ideal MHD on k + p + q = 0 (even non-solenoidal u)."""
    clean_name = require_str(name, "triad.name", max_len=128)
    eta = parse_exact_rational(eta_resistivity, "triad.eta")
    if eta < Q0:
        raise CKHelicityError("NEGATIVE_RESISTIVITY", "resistivity eta must be non-negative")

    k, p, q = triad_k
    if (k[0] + p[0] + q[0], k[1] + p[1] + q[1], k[2] + p[2] + q[2]) != (0, 0, 0):
        raise CKHelicityError("TRIAD_NOT_CLOSED", "triad wavevectors must satisfy k + p + q == 0")

    norms = [exact_integer_norm(v) for v in (k, p, q)]
    # Validate solenoidal B on all 3 legs and compute Coulomb-gauge A
    a_modes: list[QVec3] = []
    u_div_nonzero = False
    for idx, (wv, bk, uk) in enumerate(zip((k, p, q), b_modes, u_modes)):
        nk, p0, _, _ = helical_projectors_exact(wv)
        if qmat_vec(p0, bk) != (QC0, QC0, QC0):
            raise CKHelicityError("NON_SOLENOIDAL_FIELD", f"triad B[{idx}] not solenoidal")
        ak = qv_scale(Fraction(1, nk * nk), qv_ik_cross(wv, bk))
        a_modes.append(ak)
        if qmat_vec(p0, uk) != (QC0, QC0, QC0):
            u_div_nonzero = True

    # Each triad leg receives nonlinear EMF from the other two conjugate legs (-p, -q)
    legs = (
        (k, a_modes[0], b_modes[0], u_modes[0]),
        (p, a_modes[1], b_modes[1], u_modes[1]),
        (q, a_modes[2], b_modes[2], u_modes[2]),
    )
    transfers_ideal: list[Fraction] = []
    resistive_terms: list[Fraction] = []
    for i in range(3):
        j1 = (i + 1) % 3
        j2 = (i + 2) % 3
        wi, ai, bi, _ = legs[i]
        _, _, b1, u1 = legs[j1]
        _, _, b2, u2 = legs[j2]
        # u(-w1) x B(-w2) + u(-w2) x B(-w1) = conj(u1) x conj(b2) + conj(u2) x conj(b1)
        emf_i = qv_add(qv_cross(qv_conj(u1), qv_conj(b2)), qv_cross(qv_conj(u2), qv_conj(b1)))
        dt_b_ideal = qv_ik_cross(wi, emf_i)
        # Contribution of pair {+wi, -wi} to dH/dt = 4 * Re(<A(wi), d_t B(wi)>)
        # (factor 2 from H = sum <A, B> derivative -> 2 Re, times factor 2 from {+wi, -wi})
        t_i = Fraction(4, 1) * qv_hdot(ai, dt_b_ideal)[0]
        transfers_ideal.append(t_i)

        # Resistive term d_t B_res(wi) = -eta * ||wi||^2 * B(wi)
        n2_i = Fraction(norms[i] * norms[i], 1)
        dt_b_res = qv_scale(-eta * n2_i, bi)
        r_i = Fraction(4, 1) * qv_hdot(ai, dt_b_res)[0]
        resistive_terms.append(r_i)

    ideal_sum = transfers_ideal[0] + transfers_ideal[1] + transfers_ideal[2]
    resistive_sum = resistive_terms[0] + resistive_terms[1] + resistive_terms[2]

    # Independent helical-spectrum check of resistive dissipation:
    # -2 * eta * sum_{all +/- modes} ||k|| (|B_+|^2 - |B_-|^2)
    res_spectral = Q0
    for wv, bk in zip((k, p, q), b_modes):
        nk, _, pp, pm = helical_projectors_exact(wv)
        np2 = qv_norm2(qmat_vec(pp, bk))
        nm2 = qv_norm2(qmat_vec(pm, bk))
        # Factor 2 for {+wv, -wv} pair times -2*eta*nk => -4*eta*nk
        res_spectral += -Fraction(4, 1) * eta * Fraction(nk, 1) * (np2 - nm2)

    res_spectral_matches = res_spectral == resistive_sum

    return {
        "name": clean_name,
        "wavevectors": [[k[0], k[1], k[2]], [p[0], p[1], p[2]], [q[0], q[1], q[2]]],
        "norms": norms,
        "velocity_is_non_solenoidal": u_div_nonzero,
        "per_leg_ideal_dH_dt": [format_rational(t) for t in transfers_ideal],
        "nontrivial_interscale_transfer": any(t != Q0 for t in transfers_ideal),
        "total_ideal_dH_dt": format_rational(ideal_sum),
        "ideal_helicity_conserved_exact": ideal_sum == Q0,
        "eta_resistivity": format_rational(eta),
        "total_resistive_dH_dt": format_rational(resistive_sum),
        "resistive_spectral_matches": res_spectral_matches,
        "resistive_breaks_conservation": resistive_sum != Q0,
    }


# ---------------------------------------------------------------------------
# Theorem 3B: Exact 3D Radix-2 Q[i]-FFT (N=4) & Dual-Prime NTT/CRT (N=4, N=8)
# ---------------------------------------------------------------------------

def _fft1d_n4_qcomplex(vec: Sequence[QComplex], inverse: bool = False) -> list[QComplex]:
    """Exact 4-point radix-2 FFT over Q[i] using exact 4th root of unity w = -i (fwd) / +i (inv)."""
    if len(vec) != 4:
        raise CKHelicityError("INVALID_FFT_LEN", "exact Q[i] radix-2 FFT expects length 4")
    x0, x1, x2, x3 = vec[0], vec[1], vec[2], vec[3]
    a0 = qc_add(x0, x2)
    a1 = qc_sub(x0, x2)
    b0 = qc_add(x1, x3)
    b1 = qc_sub(x1, x3)
    # Forward: exp(-i pi/2) = -i; Inverse: exp(+i pi/2) = +i
    ib1 = qc_mul_i(b1)
    if inverse:
        out = [
            qc_add(a0, b0),
            qc_add(a1, ib1),
            qc_sub(a0, b0),
            qc_sub(a1, ib1),
        ]
        q4 = Fraction(1, 4)
        return [qc_scale(q4, z) for z in out]
    return [
        qc_add(a0, b0),
        qc_sub(a1, ib1),
        qc_sub(a0, b0),
        qc_add(a1, ib1),
    ]


def fft3d_n4_qcomplex(grid: list[list[list[QComplex]]], inverse: bool = False) -> list[list[list[QComplex]]]:
    """Exact separable 3D 4x4x4 FFT/IFFT over Q[i] (zero floats, zero rounding)."""
    # Transform along axis 2 (z)
    t1 = [[_fft1d_n4_qcomplex(grid[x][y], inverse=inverse) for y in range(4)] for x in range(4)]
    # Transform along axis 1 (y)
    t2 = [[[QC0] * 4 for _ in range(4)] for _ in range(4)]
    for x in range(4):
        for z in range(4):
            col = _fft1d_n4_qcomplex([t1[x][y][z] for y in range(4)], inverse=inverse)
            for y in range(4):
                t2[x][y][z] = col[y]
    # Transform along axis 0 (x)
    t3 = [[[QC0] * 4 for _ in range(4)] for _ in range(4)]
    for y in range(4):
        for z in range(4):
            col = _fft1d_n4_qcomplex([t2[x][y][z] for x in range(4)], inverse=inverse)
            for x in range(4):
                t3[x][y][z] = col[x]
    return t3


def ntt_1d_mod(vec: Sequence[int], prime: int, inverse: bool = False) -> list[int]:
    """Exact iterative radix-2 Cooley-Tukey NTT over F_p for power-of-2 length."""
    n = len(vec)
    if n == 0 or (n & (n - 1)) != 0:
        raise CKHelicityError("INVALID_NTT_LEN", "NTT length must be a power of 2")
    a = [v % prime for v in vec]
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

    length = 2
    while length <= n:
        wlen = pow(NTT_PRIM_ROOT, (prime - 1) // length, prime)
        if inverse:
            wlen = pow(wlen, prime - 2, prime)
        half = length >> 1
        for i in range(0, n, length):
            w = 1
            for k in range(half):
                u = a[i + k]
                v = (a[i + k + half] * w) % prime
                a[i + k] = (u + v) % prime
                a[i + k + half] = (u - v) % prime
                w = (w * wlen) % prime
        length <<= 1

    if inverse:
        inv_n = pow(n, prime - 2, prime)
        a = [(x * inv_n) % prime for x in a]
    return a


def ntt_3d_mod(grid: list[list[list[int]]], prime: int, inverse: bool = False) -> list[list[list[int]]]:
    n = len(grid)
    t1 = [[ntt_1d_mod(grid[x][y], prime, inverse=inverse) for y in range(n)] for x in range(n)]
    t2 = [[[0] * n for _ in range(n)] for _ in range(n)]
    for x in range(n):
        for z in range(n):
            col = ntt_1d_mod([t1[x][y][z] for y in range(n)], prime, inverse=inverse)
            for y in range(n):
                t2[x][y][z] = col[y]
    t3 = [[[0] * n for _ in range(n)] for _ in range(n)]
    for y in range(n):
        for z in range(n):
            col = ntt_1d_mod([t2[x][y][z] for x in range(n)], prime, inverse=inverse)
            for x in range(n):
                t3[x][y][z] = col[x]
    return t3


def crt_signed_pair(r1: int, r2: int) -> int:
    """Exact CRT reconstruction into balanced signed interval (-M/2, M/2] for M = p1 * p2."""
    p1 = NTT_PRIME_1
    p2 = NTT_PRIME_2
    inv_p1_mod_p2 = pow(p1, p2 - 2, p2)
    t = ((r2 - r1) % p2) * inv_p1_mod_p2 % p2
    val = r1 + p1 * t
    mod = p1 * p2
    if val > mod // 2:
        val -= mod
    return val


def ntt_crt_3d_cross_convolution(
    u_comps: tuple[list[list[list[int]]], list[list[list[int]]], list[list[list[int]]]],
    b_comps: tuple[list[list[list[int]]], list[list[list[int]]], list[list[list[int]]]],
) -> tuple[list[list[list[int]]], list[list[list[int]]], list[list[list[int]]]]:
    """Exact 3D circular cross-product convolution via dual-prime NTT + CRT."""
    n = len(u_comps[0])

    def _conv_mod(prime: int) -> tuple[list[list[list[int]]], list[list[list[int]]], list[list[list[int]]]]:
        uh = [ntt_3d_mod(u_comps[c], prime, inverse=False) for c in range(3)]
        bh = [ntt_3d_mod(b_comps[c], prime, inverse=False) for c in range(3)]
        ch = [[[[0] * n for _ in range(n)] for _ in range(n)] for _ in range(3)]
        for x in range(n):
            for y in range(n):
                for z in range(n):
                    u0, u1, u2 = uh[0][x][y][z], uh[1][x][y][z], uh[2][x][y][z]
                    b0, b1, b2 = bh[0][x][y][z], bh[1][x][y][z], bh[2][x][y][z]
                    ch[0][x][y][z] = (u1 * b2 - u2 * b1) % prime
                    ch[1][x][y][z] = (u2 * b0 - u0 * b2) % prime
                    ch[2][x][y][z] = (u0 * b1 - u1 * b0) % prime
        return (
            ntt_3d_mod(ch[0], prime, inverse=True),
            ntt_3d_mod(ch[1], prime, inverse=True),
            ntt_3d_mod(ch[2], prime, inverse=True),
        )

    c_p1 = _conv_mod(NTT_PRIME_1)
    c_p2 = _conv_mod(NTT_PRIME_2)
    out = [
        [
            [
                [crt_signed_pair(c_p1[comp][x][y][z], c_p2[comp][x][y][z]) for z in range(n)]
                for y in range(n)
            ]
            for x in range(n)
        ]
        for comp in range(3)
    ]
    return (out[0], out[1], out[2])


def direct_3d_cross_convolution_int(
    u_comps: tuple[list[list[list[int]]], list[list[list[int]]], list[list[list[int]]]],
    b_comps: tuple[list[list[list[int]]], list[list[list[int]]], list[list[list[int]]]],
) -> tuple[list[list[list[int]]], list[list[list[int]]], list[list[list[int]]]]:
    """Direct O(N^6) exact integer 3D circular cross-product convolution reference."""
    n = len(u_comps[0])
    out = [[[[0] * n for _ in range(n)] for _ in range(n)] for _ in range(3)]
    for kx in range(n):
        for ky in range(n):
            for kz in range(n):
                c0 = c1 = c2 = 0
                for px in range(n):
                    qx = (kx - px) % n
                    for py in range(n):
                        qy = (ky - py) % n
                        for pz in range(n):
                            qz = (kz - pz) % n
                            u0 = u_comps[0][px][py][pz]
                            u1 = u_comps[1][px][py][pz]
                            u2 = u_comps[2][px][py][pz]
                            b0 = b_comps[0][qx][qy][qz]
                            b1 = b_comps[1][qx][qy][qz]
                            b2 = b_comps[2][qx][qy][qz]
                            c0 += u1 * b2 - u2 * b1
                            c1 += u2 * b0 - u0 * b2
                            c2 += u0 * b1 - u1 * b0
                out[0][kx][ky][kz] = c0
                out[1][kx][ky][kz] = c1
                out[2][kx][ky][kz] = c2
    return (out[0], out[1], out[2])


def _build_qcomplex_fft_and_ntt_section() -> dict[str, Any]:
    # 1. Exact 4x4x4 3D Q[i]-FFT convolution & Parseval check (w_4 = i exact in Q[i]!)
    # Deterministic integer spatial fields u(x,y,z) and B(x,y,z) on Z_4^3
    def _make_int_vector_field(n: int, salt: int) -> tuple[list[list[list[int]]], list[list[list[int]]], list[list[list[int]]]]:
        comps: list[list[list[list[int]]]] = []
        for comp in range(3):
            grid = [
                [
                    [
                        ((3 * x + 5 * y + 7 * z + 11 * comp + salt) % 13) - 6
                        for z in range(n)
                    ]
                    for y in range(n)
                ]
                for x in range(n)
            ]
            comps.append(grid)
        return (comps[0], comps[1], comps[2])

    u4_int = _make_int_vector_field(4, 1)
    b4_int = _make_int_vector_field(4, 7)

    u4_qc = [
        [[[qc(u4_int[c][x][y][z]) for z in range(4)] for y in range(4)] for x in range(4)]
        for c in range(3)
    ]
    b4_qc = [
        [[[qc(b4_int[c][x][y][z]) for z in range(4)] for y in range(4)] for x in range(4)]
        for c in range(3)
    ]

    # Forward & inverse roundtrip + Parseval identity on B
    b4_hat = [fft3d_n4_qcomplex(b4_qc[c], inverse=False) for c in range(3)]
    b4_rt = [fft3d_n4_qcomplex(b4_hat[c], inverse=True) for c in range(3)]
    fft4_roundtrip_exact = b4_rt == b4_qc

    spatial_l2 = sum(
        (qc_norm2(b4_qc[c][x][y][z]) for c in range(3) for x in range(4) for y in range(4) for z in range(4)),
        Q0,
    )
    spectral_l2 = sum(
        (qc_norm2(b4_hat[c][x][y][z]) for c in range(3) for x in range(4) for y in range(4) for z in range(4)),
        Q0,
    )
    fft4_parseval_exact = (Fraction(64, 1) * spatial_l2) == spectral_l2

    # Exact 3D convolution theorem: FFT(u x B) == (1/64) * (u_hat (*) B_hat)
    u4_hat = [fft3d_n4_qcomplex(u4_qc[c], inverse=False) for c in range(3)]
    uxb_spatial = [[[[QC0] * 4 for _ in range(4)] for _ in range(4)] for _ in range(3)]
    for x in range(4):
        for y in range(4):
            for z in range(4):
                uv = (u4_qc[0][x][y][z], u4_qc[1][x][y][z], u4_qc[2][x][y][z])
                bv = (b4_qc[0][x][y][z], b4_qc[1][x][y][z], b4_qc[2][x][y][z])
                cv = qv_cross(uv, bv)
                for c in range(3):
                    uxb_spatial[c][x][y][z] = cv[c]
    uxb_hat_fft = [fft3d_n4_qcomplex(uxb_spatial[c], inverse=False) for c in range(3)]

    inv64 = Fraction(1, 64)
    conv_mismatch = 0
    for kx in range(4):
        for ky in range(4):
            for kz in range(4):
                acc = (QC0, QC0, QC0)
                for px in range(4):
                    qx = (kx - px) % 4
                    for py in range(4):
                        qy = (ky - py) % 4
                        for pz in range(4):
                            qz = (kz - pz) % 4
                            uv = (u4_hat[0][px][py][pz], u4_hat[1][px][py][pz], u4_hat[2][px][py][pz])
                            bv = (b4_hat[0][qx][qy][qz], b4_hat[1][qx][qy][qz], b4_hat[2][qx][qy][qz])
                            acc = qv_add(acc, qv_cross(uv, bv))
                expected = qv_scale(inv64, acc)
                got = (uxb_hat_fft[0][kx][ky][kz], uxb_hat_fft[1][kx][ky][kz], uxb_hat_fft[2][kx][ky][kz])
                if expected != got:
                    conv_mismatch += 1

    # 2. Exact Dual-Prime NTT + CRT 3D cross-convolution vs direct O(N^6) reference on N=4
    ntt4_conv = ntt_crt_3d_cross_convolution(u4_int, b4_int)
    dir4_conv = direct_3d_cross_convolution_int(u4_int, b4_int)
    ntt4_exact_match = ntt4_conv == dir4_conv
    ntt4_max_abs = max(
        abs(ntt4_conv[c][x][y][z]) for c in range(3) for x in range(4) for y in range(4) for z in range(4)
    )

    # 3. Exact 8x8x8 (512-node) Dual-Prime NTT roundtrip + modular Parseval + cross-conv sanity
    u8_int = _make_int_vector_field(8, 3)
    b8_int = _make_int_vector_field(8, 11)
    b8_ntt1 = ntt_3d_mod(b8_int[0], NTT_PRIME_1, inverse=False)
    b8_rt1 = ntt_3d_mod(b8_ntt1, NTT_PRIME_1, inverse=True)
    ntt8_roundtrip_p1 = all(
        b8_rt1[x][y][z] == (b8_int[0][x][y][z] % NTT_PRIME_1)
        for x in range(8)
        for y in range(8)
        for z in range(8)
    )
    # Modular Parseval over F_{p1}: N^3 * sum x(r) * x(-r) == sum X(k)^2 (mod p1)
    lhs_p1 = 0
    rhs_p1 = 0
    for x in range(8):
        for y in range(8):
            for z in range(8):
                lhs_p1 = (lhs_p1 + b8_int[0][x][y][z] * b8_int[0][(-x) % 8][(-y) % 8][(-z) % 8]) % NTT_PRIME_1
                rhs_p1 = (rhs_p1 + b8_ntt1[x][y][z] * b8_ntt1[x][y][z]) % NTT_PRIME_1
    ntt8_parseval_p1 = ((512 * lhs_p1) % NTT_PRIME_1) == rhs_p1

    ntt8_conv = ntt_crt_3d_cross_convolution(u8_int, b8_int)
    # Exact spot-check at (0,0,0) and (3,5,7) against direct sum over all 512 indices
    spot_ok = True
    for (kx, ky, kz) in ((0, 0, 0), (3, 5, 7)):
        c0 = c1 = c2 = 0
        for px in range(8):
            qx = (kx - px) % 8
            for py in range(8):
                qy = (ky - py) % 8
                for pz in range(8):
                    qz = (kz - pz) % 8
                    u0, u1, u2 = u8_int[0][px][py][pz], u8_int[1][px][py][pz], u8_int[2][px][py][pz]
                    b0, b1, b2 = b8_int[0][qx][qy][qz], b8_int[1][qx][qy][qz], b8_int[2][qx][qy][qz]
                    c0 += u1 * b2 - u2 * b1
                    c1 += u2 * b0 - u0 * b2
                    c2 += u0 * b1 - u1 * b0
        if (ntt8_conv[0][kx][ky][kz], ntt8_conv[1][kx][ky][kz], ntt8_conv[2][kx][ky][kz]) != (c0, c1, c2):
            spot_ok = False

    return {
        "qcomplex_fft3d_n4": {
            "grid_shape": [4, 4, 4],
            "roundtrip_exact": fft4_roundtrip_exact,
            "spatial_l2": format_rational(spatial_l2),
            "spectral_l2": format_rational(spectral_l2),
            "parseval_exact": fft4_parseval_exact,
            "convolution_theorem_mismatches": conv_mismatch,
            "convolution_theorem_exact": conv_mismatch == 0,
        },
        "ntt_crt_3d": {
            "primes": [NTT_PRIME_1, NTT_PRIME_2],
            "primitive_root": NTT_PRIM_ROOT,
            "crt_modulus": str(NTT_PRIME_1 * NTT_PRIME_2),
            "n4_all_192_entries_exact_match": ntt4_exact_match,
            "n4_max_abs_entry": ntt4_max_abs,
            "n8_grid_nodes": 512,
            "n8_roundtrip_p1_exact": ntt8_roundtrip_p1,
            "n8_modular_parseval_p1_exact": ntt8_parseval_p1,
            "n8_spotcheck_direct_match": spot_ok,
        },
    }


def build_theorem3_triads_and_fft() -> dict[str, Any]:
    # Triad 1: (1,2,2) + (-1,2,-2) + (0,-4,0) == 0, integer norms (3, 3, 4), solenoidal u
    t1_k = ((1, 2, 2), (-1, 2, -2), (0, -4, 0))
    _, _, pp1_k, pm1_k = helical_projectors_exact(t1_k[0])
    _, _, pp1_p, pm1_p = helical_projectors_exact(t1_k[1])
    _, _, pp1_q, pm1_q = helical_projectors_exact(t1_k[2])
    t1_b = (
        qv_add(qmat_vec(pp1_k, (qc(3), QC0, QC0)), qmat_vec(pm1_k, (QC0, qc(3, 3), QC0))),
        qmat_vec(pp1_p, (QC0, QC0, qc(6, -3))),
        qv_add(qmat_vec(pp1_q, (qc(4), QC0, QC0)), qmat_vec(pm1_q, (QC0, QC0, qc(2, 4)))),
    )
    t1_u_sol = (
        qmat_vec(pp1_k, (QC0, qc(3), QC0)),
        qmat_vec(pm1_p, (qc(3, 3), QC0, QC0)),
        qmat_vec(pp1_q, (QC0, QC0, qc(4))),
    )
    triad_334_sol = verify_helical_triad_helicity_conservation(
        "pythagorean_triad_3_3_4_solenoidal_u", t1_k, t1_b, t1_u_sol
    )

    # Triad 2: genuinely 3D distinct integer norms (6,2,3)+(-2,2,-1)+(-4,-4,-2)==0, norms (7, 3, 6)
    # with deliberately NON-SOLENOIDAL (compressible) velocity u!
    t2_k = ((6, 2, 3), (-2, 2, -1), (-4, -4, -2))
    _, _, pp2_k, pm2_k = helical_projectors_exact(t2_k[0])
    _, _, pp2_p, pm2_p = helical_projectors_exact(t2_k[1])
    _, _, pp2_q, pm2_q = helical_projectors_exact(t2_k[2])
    t2_b = (
        qv_add(qmat_vec(pp2_k, (qc(7, 0), QC0, QC0)), qmat_vec(pm2_k, (QC0, qc(0, 7), QC0))),
        qv_add(qmat_vec(pp2_p, (QC0, qc(3), QC0)), qmat_vec(pm2_p, (qc(3, -3), QC0, QC0))),
        qmat_vec(pp2_q, (qc(6), QC0, qc(0, 6))),
    )
    t2_u_comp = (
        (qc(6, 1), qc(2, -1), qc(3, 2)),   # non-orthogonal to (6,2,3) -> compressible!
        (qc(-2, 3), qc(2, 1), qc(-1, 4)),  # non-orthogonal to (-2,2,-1)
        (qc(-4, -2), qc(-4, 1), qc(-2, 3)),
    )
    triad_736_comp = verify_helical_triad_helicity_conservation(
        "pythagorean_triad_7_3_6_compressible_u", t2_k, t2_b, t2_u_comp
    )

    # Triad 3: classic (3,4,5) triad (3,0,0)+(0,4,0)+(-3,-4,0)==0 with resistive control eta = 1/10
    t3_k = ((3, 0, 0), (0, 4, 0), (-3, -4, 0))
    _, _, pp3_k, _ = helical_projectors_exact(t3_k[0])
    _, _, pp3_p, _ = helical_projectors_exact(t3_k[1])
    _, _, pp3_q, _ = helical_projectors_exact(t3_k[2])
    t3_b = (
        qmat_vec(pp3_k, (QC0, qc(2), QC0)),
        qmat_vec(pp3_p, (QC0, QC0, qc(3, 1))),
        qmat_vec(pp3_q, (QC0, QC0, qc(5))),
    )
    t3_u = (
        (qc(1, 2), qc(3), qc(-1)),
        (qc(2), qc(-1, 1), qc(4)),
        (qc(-2), qc(1), qc(3, -2)),
    )
    triad_345_resistive = verify_helical_triad_helicity_conservation(
        "pythagorean_triad_3_4_5_resistive_control", t3_k, t3_b, t3_u, eta_resistivity=Fraction(1, 10)
    )

    spectral = _build_qcomplex_fft_and_ntt_section()

    return {
        "triads": [triad_334_sol, triad_736_comp, triad_345_resistive],
        "spectral_convolutions": spectral,
    }


# ---------------------------------------------------------------------------
# Standalone Certificate Assembly & Full-Replay Zone-B Payload Validator
# ---------------------------------------------------------------------------

def build_standalone_certificate() -> dict[str, Any]:
    payload = {
        "oracle_class": "exact",
        "novelty_classification": "N1",
        "zero_floats_exact_arithmetic": True,
        "theorem1_flux_tube_helicity": build_theorem1_flux_tubes(),
        "theorem2_ck_and_woltjer": build_theorem2_ck_and_woltjer(),
        "theorem3_triads_and_fft": build_theorem3_triads_and_fft(),
    }
    payload_sha = sha256_hex(canonical_json_bytes(payload))
    cert_body = {
        "schema": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": payload_sha,
        "payload": payload,
    }
    cert_sha = sha256_hex(canonical_json_bytes(cert_body))
    return {
        "schema": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": payload_sha,
        "certificate_sha256": cert_sha,
        "payload": payload,
    }


def validate_certificate_payload(cert: Any, full_replay: bool = True) -> dict[str, Any]:
    """Zone-B hardened in-memory certificate validator (callable directly in-process)."""
    require_bool(full_replay, "full_replay")
    validate_json_tree_iterative(cert)
    if type(cert) is not dict:
        raise CKHelicityError("CERT_NOT_DICT", "certificate root must be strict dict")
    if frozenset(cert.keys()) != _CERT_KEYS:
        raise CKHelicityError("INVALID_CERT_KEYS", "certificate keys mismatch")
    if cert["schema"] != SCHEMA_VERSION:
        raise CKHelicityError("INVALID_SCHEMA", "unexpected certificate schema")
    if cert["track_id"] != TRACK_ID:
        raise CKHelicityError("INVALID_TRACK_ID", "unexpected track_id")

    payload = cert["payload"]
    if type(payload) is not dict:
        raise CKHelicityError("PAYLOAD_NOT_DICT", "payload must be strict dict")

    claimed_payload_sha = require_hex64(cert["payload_sha256"], "payload_sha256")
    actual_payload_sha = sha256_hex(canonical_json_bytes(payload))
    if not constant_time_hex64_equal(claimed_payload_sha, actual_payload_sha, "payload_sha256"):
        raise CKHelicityError("PAYLOAD_SHA_MISMATCH", "payload_sha256 mismatch")

    claimed_cert_sha = require_hex64(cert["certificate_sha256"], "certificate_sha256")
    cert_body = {
        "schema": cert["schema"],
        "track_id": cert["track_id"],
        "payload_sha256": claimed_payload_sha,
        "payload": payload,
    }
    actual_cert_sha = sha256_hex(canonical_json_bytes(cert_body))
    if not constant_time_hex64_equal(claimed_cert_sha, actual_cert_sha, "certificate_sha256"):
        raise CKHelicityError("CERT_SHA_MISMATCH", "certificate_sha256 mismatch")

    if full_replay:
        fresh = build_standalone_certificate()
        if not constant_time_hex64_equal(actual_payload_sha, fresh["payload_sha256"], "recomputed_payload_sha256"):
            raise CKHelicityError("RECOMPUTATION_MISMATCH", "payload differs from deterministic recomputation")

    return {
        "valid": True,
        "schema": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": actual_payload_sha,
        "certificate_sha256": actual_cert_sha,
        "full_replay": full_replay,
    }
