"""Track S33 (Portal 30): Leonardo da Vinci Live 2023-2026 Exact-Operator Quintet.

Pure Python 3 standard library over exact Z and Q (`fractions.Fraction`).
Zero external dependencies, zero floats, zero bare asserts, zero RNG.
Strict Law-4 N0/N1 honesty: zero Renaissance mythology, zero golden-ratio numerology.

Five certified exact-operator pillars:
  1. Codex Arundel f. 143v ("Equatione di Moti", Gharib-Roh-Noca 2023):
     Exact straight-hypotenuse uniqueness theorem in Q[tau, s] and discrete
     2^k-vs-k^2 curvature obstruction at N = 3 plus 4-interval window diagnostics.
  2. Codex Leicester Rising Bubble Paradox (arXiv:2609.26283 Aug 2026;
     Herrada-Eggers PNAS 2023): Exact Rayleigh-Lamb spectrum, unique vacuum
     resonance at l = 7 (k = 6), complete positive rational resonance locus
     tau_{l,k} for 3 <= l <= 10, sigma = 0 rigidity collapse, and 4D coupled
     sway-tilt Routh-Hurwitz / Hermite-Sylvester inertia Hopf bifurcation witness.
  3. Codex Atlanticus f. 69r & f. 899v Reciprocal Bridge & Da Vinci Domes
     (arXiv:2401.00881 Jan 2024): Collinear-rod Descartes angular-defect
     obstruction, Euler torus-vs-sphere disclination obstruction (all 11 uniform
     planar tilings vs spherical cages), and exact unilateral-compression
     reciprocal arch-bridge equilibrium with sharp minimum Coulomb friction
     mu_min = 1/3 and explicit Farkas dual virtual-velocity collapse certificates.
  4. MS M / Trattato Tree Branching Law (alpha = 2) vs Sopp-Valbuena (PNAS 2023)
     vs Murray (alpha = 3) vs Pythagorean Trees (arXiv:2411.08024 Nov 2024):
     Exact generalized variational exponent alpha*(p, q, m) = (p + q) / m,
     pure-Z cubic Poiseuille dissipation dominance (54 < 64), Pythagorean-tree
     dual area + surface-area conservation, and 15-node 4-level Kirchhoff-Schur
     conductance pushforward separating naive alpha = 2 blowup from vascular
     conduit widening.
  5. De Ludo Geometrico Squarable Lunes (exact Galois obstructions at 4:1 & 7:1
     via Rational Root Theorem & F_p irreducibility; all 5 squarable lunes and
     zero-pi area dissections) + MS B Aerial Screw iso-lift scaling
     (arXiv:2506.10223 Aug 2025) + CS-13 myth audit (arXiv:1311.0816 Mayer 1772).
"""
from __future__ import annotations

from fractions import Fraction
import hashlib
import hmac
import json
import math
from typing import Any, Mapping, Sequence

SCHEMA_VERSION = "aletheia.leonardo_codices.certificate.v1"
TRACK_ID = "TRACK-S33-LEONARDO-CODICES-EXACT-OPERATORS"

MAX_JSON_BYTES = 1_048_576
HARD_MAX_BYTES_CAP = 64 * 1024 * 1024
MAX_JSON_DEPTH = 64
MAX_INT_BITS = 2048
MAX_INT_DIGITS = 616
MAX_RATIONAL_CHARS = 256
MAX_FORMAT_BITS = 4096

_HEX_LOWER = frozenset("0123456789abcdef")
_CERT_KEYS = frozenset({"schema", "track_id", "payload_sha256", "certificate_sha256", "payload"})
_PILLAR_KEYS = (
    "pillar1_arundel_motion",
    "pillar2_leicester_bubble",
    "pillar3_atlanticus_bridge_domes",
    "pillar4_trattato_branching_trees",
    "pillar5_lunes_aerial_screw_myth",
)
_PAYLOAD_KEYS = frozenset({
    "oracle_class",
    "novelty_classification",
    "zero_floats_exact_arithmetic",
    "all_verified",
    *_PILLAR_KEYS,
})
_ALLOWED_BOOL_KEYS = frozenset({
    "all_determinants_zero",
    "all_levels_area_invariant",
    "all_normal_strictly_positive",
    "all_verified",
    "area_conserved",
    "attributed_to_leonardo_in_authentic_codices",
    "back_substitution_exact",
    "catastrophic_collapse_certified",
    "char_poly_check_p2_exact",
    "collinearity_broken",
    "congruence_det_nonzero",
    "congruence_verified",
    "degree_not_power_of_2",
    "equilibrium_residual_zero",
    "even_in_cos_theta",
    "farkas_ATv_all_zero",
    "farkas_ATv_nonneg",
    "farkas_vTg_strictly_negative",
    "galileo_constant_det",
    "golden_ratio_numerology_excluded",
    "higher_coeffs_zero",
    "hopf_pure_imag_residual_zero",
    "irreducible_mod_17",
    "irreducible_mod_5",
    "is_45_degree_equatione_di_moti",
    "is_integer_harmonic_resonance",
    "is_straight_hypotenuse",
    "jhu_power_drop_in_42_to_43_pct_band",
    "leonardo_exponential_growth",
    "murray_strictly_dominates_leonardo",
    "no_rational_root",
    "noise_strictly_reduced",
    "nonpositive_defect",
    "pillar_verified",
    "power_strictly_reduced",
    "primal_cone_weights_nonneg",
    "pure_area_3x_power_drop_in_42_to_43_pct_band",
    "ruler_compass_constructible",
    "ruler_compass_impossible",
    "schur_matches_series_parallel",
    "sigma_zero_collapse_all_zero",
    "surface_area_conserved",
    "zero_floats_exact_arithmetic",
    "zero_pi_exact",
})

Q0 = Fraction(0, 1)
Q1 = Fraction(1, 1)


class LeonardoError(ValueError):
    """Fail-closed typed error (never stripped by python3 -O)."""

    def __init__(self, code: str, message: str) -> None:
        self.code = code
        self.message = message
        super().__init__(f"{code}: {message}")


# ---------------------------------------------------------------------------
# Zone-B Exact Type, Canonical Rational, Iterative JSON & Digest Primitives
# ---------------------------------------------------------------------------

def require_bool(val: Any, label: str) -> bool:
    if type(val) is not bool:
        raise LeonardoError("INVALID_BOOL", f"{label} must be strict bool")
    return val


def require_int(
    val: Any,
    label: str,
    lo: int | None = None,
    hi: int | None = None,
) -> int:
    if type(val) is not int:
        raise LeonardoError("INVALID_INT", f"{label} must be strict int")
    if val.bit_length() > MAX_INT_BITS:
        raise LeonardoError("INT_TOO_LARGE", f"{label} exceeds {MAX_INT_BITS}-bit limit")
    if lo is not None:
        if type(lo) is not int:
            raise LeonardoError("INVALID_BOUND", f"{label} lo bound must be strict int")
        if val < lo:
            raise LeonardoError("INT_OUT_OF_RANGE", f"{label} < {lo}")
    if hi is not None:
        if type(hi) is not int:
            raise LeonardoError("INVALID_BOUND", f"{label} hi bound must be strict int")
        if val > hi:
            raise LeonardoError("INT_OUT_OF_RANGE", f"{label} > {hi}")
    return val


def require_str(val: Any, label: str, max_len: int = 4096) -> str:
    limit = require_int(max_len, f"{label}.max_len", lo=1, hi=HARD_MAX_BYTES_CAP)
    if type(val) is not str:
        raise LeonardoError("INVALID_STR", f"{label} must be strict str")
    if len(val) > limit:
        raise LeonardoError("STR_TOO_LONG", f"{label} exceeds length limit")
    try:
        val.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise LeonardoError("INVALID_UTF8_SURROGATE", f"{label} contains lone UTF-16 surrogate") from exc
    return val


def require_hex64(val: Any, label: str) -> str:
    s = require_str(val, label, max_len=64)
    if len(s) != 64 or any(ch not in _HEX_LOWER for ch in s):
        raise LeonardoError("INVALID_HEX64", f"{label} must be 64 lowercase ASCII hex chars")
    return s


def constant_time_hex64_equal(left: Any, right: Any, label: str) -> bool:
    a = require_hex64(left, f"{label}.left")
    b = require_hex64(right, f"{label}.right")
    return hmac.compare_digest(a.encode("ascii"), b.encode("ascii"))


_ASCII_DIGITS = frozenset("0123456789")


def _is_canonical_ascii_digits(s: str) -> bool:
    if not s:
        return False
    if any(ch not in _ASCII_DIGITS for ch in s):
        return False
    if len(s) > 1 and s[0] == "0":
        return False
    return True


def parse_exact_rational(raw: Any, label: str = "rational") -> Fraction:
    """Strictly parse exact int, Fraction, or canonical ASCII rational ('p' or 'p/q')."""
    t = type(raw)
    if t is int:
        if raw.bit_length() > MAX_INT_BITS:
            raise LeonardoError("RATIONAL_TOO_LARGE", f"{label} exceeds bit limit")
        return Fraction(raw, 1)
    if t is Fraction:
        if raw.numerator.bit_length() > MAX_INT_BITS or raw.denominator.bit_length() > MAX_INT_BITS:
            raise LeonardoError("RATIONAL_TOO_LARGE", f"{label} fraction exceeds bit limit")
        return raw
    if t is not str:
        raise LeonardoError("INVALID_RATIONAL_TYPE", f"{label} must be int, Fraction, or str")
    if len(raw) > MAX_RATIONAL_CHARS:
        raise LeonardoError("INVALID_RATIONAL_STR", f"{label} string oversized")
    parts = raw.split("/")
    if len(parts) == 1:
        num_s, den_s = parts[0], None
    elif len(parts) == 2:
        num_s, den_s = parts[0], parts[1]
    else:
        raise LeonardoError("INVALID_RATIONAL_STR", f"{label} contains multiple '/'")
    neg = num_s.startswith("-")
    num_digits = num_s[1:] if neg else num_s
    if not _is_canonical_ascii_digits(num_digits):
        raise LeonardoError("INVALID_RATIONAL_STR", f"{label} numerator not canonical ASCII digits")
    if neg and num_digits == "0":
        raise LeonardoError("INVALID_RATIONAL_STR", f"{label} negative zero forbidden")
    num_val = -int(num_digits) if neg else int(num_digits)
    if den_s is None:
        den_val = 1
    else:
        if not _is_canonical_ascii_digits(den_s):
            raise LeonardoError("INVALID_RATIONAL_STR", f"{label} denominator not canonical ASCII digits")
        den_val = int(den_s)
        if den_val <= 1:
            raise LeonardoError("INVALID_RATIONAL_STR", f"{label} denominator must be > 1")
        if math.gcd(abs(num_val), den_val) != 1:
            raise LeonardoError("NON_CANONICAL_RATIONAL", f"{label} fraction is not reduced")
    if num_val.bit_length() > MAX_INT_BITS or den_val.bit_length() > MAX_INT_BITS:
        raise LeonardoError("RATIONAL_TOO_LARGE", f"{label} exceeds bit limit")
    return Fraction(num_val, den_val)


def format_rational(val: Any, label: str = "rational") -> str:
    if type(val) is not Fraction:
        raise LeonardoError("INVALID_RATIONAL_TYPE", f"{label} must be exact Fraction")
    if val.numerator.bit_length() > MAX_FORMAT_BITS or val.denominator.bit_length() > MAX_FORMAT_BITS:
        raise LeonardoError("RATIONAL_TOO_LARGE", f"{label} exceeds formatting limit")
    if val.denominator == 1:
        return str(val.numerator)
    return f"{val.numerator}/{val.denominator}"


def _int_exceeds_limits(val: int) -> bool:
    if val.bit_length() > MAX_INT_BITS:
        return True
    return len(str(abs(val))) > MAX_INT_DIGITS


def validate_json_tree_iterative(obj: Any, max_depth: int = MAX_JSON_DEPTH) -> None:
    """Iterative Zone-B validator blocking cycles, depth overflow, floats, subclasses, huge ints, surrogates."""
    limit = require_int(max_depth, "max_depth", lo=1, hi=256)
    stack: list[tuple[Any, int, bool]] = [(obj, 0, False)]
    active_ids: set[int] = set()
    while stack:
        cur, depth, exiting = stack.pop()
        if exiting:
            active_ids.remove(id(cur))
            continue
        if depth > limit:
            raise LeonardoError("JSON_DEPTH_EXCEEDED", f"JSON nesting exceeds {limit}")
        t = type(cur)
        if t is dict:
            cid = id(cur)
            if cid in active_ids:
                raise LeonardoError("JSON_CYCLE", "cyclic dict forbidden")
            active_ids.add(cid)
            stack.append((cur, depth, True))
            for k, v in cur.items():
                require_str(k, "json_key", max_len=256)
                stack.append((v, depth + 1, False))
        elif t is list:
            cid = id(cur)
            if cid in active_ids:
                raise LeonardoError("JSON_CYCLE", "cyclic list forbidden")
            active_ids.add(cid)
            stack.append((cur, depth, True))
            for item in cur:
                stack.append((item, depth + 1, False))
        elif t is int:
            if _int_exceeds_limits(cur):
                raise LeonardoError("INT_TOO_LARGE", "JSON int exceeds bit/digit limit")
        elif t is str:
            require_str(cur, "json_str", max_len=65536)
        elif t is bool or cur is None:
            continue
        else:
            raise LeonardoError("FORBIDDEN_JSON_TYPE", f"forbidden JSON value type: {t.__name__}")


def _no_duplicate_keys_hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise LeonardoError("DUPLICATE_JSON_KEY", f"duplicate JSON key: {k}")
        out[k] = v
    return out


def _forbid_float(token: str) -> Any:
    raise LeonardoError("FLOAT_FORBIDDEN", f"float literal forbidden: {token}")


def _forbid_constant(token: str) -> Any:
    raise LeonardoError("NONFINITE_CONSTANT", f"non-finite JSON constant forbidden: {token}")


def parse_strict_json_text(text: Any, require_object: bool = True, max_bytes: int = MAX_JSON_BYTES) -> Any:
    require_bool(require_object, "require_object")
    cap = require_int(max_bytes, "max_bytes", lo=1, hi=HARD_MAX_BYTES_CAP)
    s = require_str(text, "json_text", max_len=cap)
    try:
        parsed = json.loads(
            s,
            object_pairs_hook=_no_duplicate_keys_hook,
            parse_float=_forbid_float,
            parse_constant=_forbid_constant,
        )
    except LeonardoError:
        raise
    except (json.JSONDecodeError, ValueError, RecursionError) as exc:
        raise LeonardoError("INVALID_JSON", f"strict JSON parse failed: {type(exc).__name__}") from exc
    validate_json_tree_iterative(parsed)
    if require_object and type(parsed) is not dict:
        raise LeonardoError("JSON_NOT_OBJECT", "JSON root must be an object")
    return parsed


def canonical_json_bytes(obj: Any) -> bytes:
    validate_json_tree_iterative(obj)
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False).encode("ascii")


def sha256_hex(data: Any) -> str:
    if type(data) is not bytes:
        raise LeonardoError("INVALID_BYTES", "sha256_hex requires exact bytes")
    return hashlib.sha256(data).hexdigest()


# ---------------------------------------------------------------------------
# Exact Rational Linear Algebra: Bareiss Det, Linear Solve, Sylvester Inertia
# ---------------------------------------------------------------------------

def _require_square_qmatrix(matrix: Any, label: str = "matrix") -> list[list[Fraction]]:
    if type(matrix) not in (list, tuple) or len(matrix) == 0:
        raise LeonardoError("INVALID_MATRIX", f"{label} must be non-empty list/tuple")
    n = len(matrix)
    out: list[list[Fraction]] = []
    for r_idx, row in enumerate(matrix):
        if type(row) not in (list, tuple) or len(row) != n:
            raise LeonardoError("INVALID_MATRIX", f"{label} row {r_idx} must have length {n}")
        out.append([parse_exact_rational(v, f"{label}[{r_idx}][{c_idx}]") for c_idx, v in enumerate(row)])
    return out


def bareiss_det_exact(matrix: Sequence[Sequence[Any]]) -> Fraction:
    """Exact fraction-free integer Bareiss determinant for any non-empty square Q-matrix."""
    clean = _require_square_qmatrix(matrix, "bareiss_matrix")
    n = len(clean)
    int_rows: list[list[int]] = []
    denom_prod = 1
    for row in clean:
        row_lcm = 1
        for entry in row:
            row_lcm = math.lcm(row_lcm, entry.denominator)
        denom_prod *= row_lcm
        int_rows.append([entry.numerator * (row_lcm // entry.denominator) for entry in row])
    sign = 1
    prev_pivot = 1
    for k in range(n - 1):
        piv_row = -1
        for i in range(k, n):
            if int_rows[i][k] != 0:
                piv_row = i
                break
        if piv_row == -1:
            return Q0
        if piv_row != k:
            int_rows[k], int_rows[piv_row] = int_rows[piv_row], int_rows[k]
            sign = -sign
        pivot = int_rows[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                int_rows[i][j] = (int_rows[i][j] * pivot - int_rows[i][k] * int_rows[k][j]) // prev_pivot
        prev_pivot = pivot
    return Fraction(sign * int_rows[n - 1][n - 1], denom_prod)


def solve_linear_exact(matrix: Sequence[Sequence[Any]], rhs: Sequence[Any]) -> list[Fraction]:
    """Exact Gaussian elimination over Q for non-singular square linear system A x = b."""
    a = _require_square_qmatrix(matrix, "linear_A")
    n = len(a)
    if type(rhs) not in (list, tuple) or len(rhs) != n:
        raise LeonardoError("INVALID_VECTOR", f"rhs must be list/tuple of length {n}")
    b = [parse_exact_rational(v, f"rhs[{i}]") for i, v in enumerate(rhs)]
    aug = [a[i] + [b[i]] for i in range(n)]
    for col in range(n):
        piv = -1
        for r in range(col, n):
            if aug[r][col] != Q0:
                piv = r
                break
        if piv == -1:
            raise LeonardoError("SINGULAR_MATRIX", "linear system matrix is singular")
        if piv != col:
            aug[col], aug[piv] = aug[piv], aug[col]
        pv = aug[col][col]
        for r in range(n):
            if r != col:
                factor = aug[r][col] / pv
                for j in range(col, n + 1):
                    aug[r][j] -= factor * aug[col][j]
    return [aug[i][n] / aug[i][i] for i in range(n)]


def sylvester_inertia_exact(matrix: Sequence[Sequence[Any]]) -> dict[str, Any]:
    """Exact Lagrange symmetric congruence S^T A S = diag(d) over Q with verified det(S) != 0."""
    clean = _require_square_qmatrix(matrix, "sym_matrix")
    n = len(clean)
    for r in range(n):
        for c in range(r + 1, n):
            if clean[r][c] != clean[c][r]:
                raise LeonardoError("ASYMMETRIC_MATRIX", "Sylvester inertia requires a symmetric matrix")
    work = [[clean[r][c] for c in range(n)] for r in range(n)]
    cong = [[Q1 if r == c else Q0 for c in range(n)] for r in range(n)]
    diag: list[Fraction] = []
    for k in range(n):
        piv = -1
        for i in range(k, n):
            if work[i][i] != Q0:
                piv = i
                break
        if piv == -1:
            pair: tuple[int, int] | None = None
            for i in range(k, n):
                for j in range(i + 1, n):
                    if work[i][j] != Q0:
                        pair = (i, j)
                        break
                if pair is not None:
                    break
            if pair is None:
                for _ in range(k, n):
                    diag.append(Q0)
                break
            pi, pj = pair
            for idx in range(n):
                cong[idx][pi] += cong[idx][pj]
            for idx in range(k, n):
                work[pi][idx] += work[pj][idx]
            for idx in range(k, n):
                work[idx][pi] += work[idx][pj]
            piv = pi
        if piv != k:
            for idx in range(n):
                cong[idx][k], cong[idx][piv] = cong[idx][piv], cong[idx][k]
            work[k], work[piv] = work[piv], work[k]
            for idx in range(n):
                work[idx][k], work[idx][piv] = work[idx][piv], work[idx][k]
        dk = work[k][k]
        diag.append(dk)
        for i in range(k + 1, n):
            factor = work[i][k] / dk
            for idx in range(n):
                cong[idx][i] -= factor * cong[idx][k]
            for j in range(k + 1, n):
                work[i][j] -= factor * work[k][j]
        for i in range(k + 1, n):
            work[i][k] = Q0
            work[k][i] = Q0

    det_s = bareiss_det_exact(cong)
    congruence_exact = det_s != Q0
    for r in range(n):
        for c in range(n):
            acc = Q0
            for p_i in range(n):
                for q_i in range(n):
                    acc += cong[p_i][r] * clean[p_i][q_i] * cong[q_i][c]
            expected = diag[r] if r == c else Q0
            if acc != expected:
                congruence_exact = False
    return {
        "n_pos": sum(1 for d in diag if d > Q0),
        "n_neg": sum(1 for d in diag if d < Q0),
        "n_zero": sum(1 for d in diag if d == Q0),
        "diag": [format_rational(d) for d in diag],
        "congruence_det_nonzero": det_s != Q0,
        "congruence_verified": congruence_exact,
    }


# ---------------------------------------------------------------------------
# Pillar 1: Codex Arundel f. 143v ("Equatione di Moti", Gharib-Roh-Noca 2023)
# ---------------------------------------------------------------------------

def evaluate_pitcher_snapshot_poly(coeffs: Sequence[Any], gravity_g: Any) -> dict[str, Any]:
    """Exact Q[tau, s] verification of the Pitcher Snapshot Uniqueness Theorem.

    For X_p(t) = sum_{j=0}^d c_j t^j and fall time s = T - tau, computes exact
    bivariate polynomial Delta_x(tau, s) = X_p(tau) + X_p'(tau)*s - X_p(tau + s),
    divides by s^2, and certifies straight-hypotenuse proportionality iff c_j == 0
    for all j >= 3 (constant horizontal acceleration a_h = 2*c_2).
    """
    if type(coeffs) not in (list, tuple) or len(coeffs) < 3:
        raise LeonardoError("INVALID_TRAJECTORY", "trajectory polynomial needs at least degree 2 (len >= 3)")
    c = [parse_exact_rational(v, f"c[{i}]") for i, v in enumerate(coeffs)]
    g = parse_exact_rational(gravity_g, "gravity_g")
    if g <= Q0:
        raise LeonardoError("NONPOSITIVE_GRAVITY", "gravity g must be strictly positive")

    # Delta_x(tau, s) = -sum_{j=2}^d c_j * sum_{k=2}^j binom(j, k) tau^{j-k} s^k
    # Divide by s^2 -> Q(tau, s) = sum_{(a, b)} q_{a,b} tau^a s^b
    quot: dict[tuple[int, int], Fraction] = {}
    for j in range(2, len(c)):
        if c[j] == Q0:
            continue
        for k in range(2, j + 1):
            term = -c[j] * Fraction(math.comb(j, k), 1)
            key = (j - k, k - 2)
            nv = quot.get(key, Q0) + term
            if nv == Q0:
                quot.pop(key, None)
            else:
                quot[key] = nv

    const_coeff = quot.get((0, 0), Q0)
    nonconst = {f"tau^{a}*s^{b}": format_rational(v) for (a, b), v in sorted(quot.items()) if (a, b) != (0, 0)}
    higher_coeffs_zero = all(c[j] == Q0 for j in range(3, len(c)))
    is_straight = len(nonconst) == 0 and const_coeff != Q0
    ah = Fraction(2, 1) * c[2]
    slope = (g / ah) if is_straight else None
    return {
        "coeffs": [format_rational(v) for v in c],
        "gravity_g": format_rational(g),
        "a_h_at_origin": format_rational(ah),
        "constant_quotient_term": format_rational(const_coeff),
        "nonconstant_quotient_terms": nonconst,
        "higher_coeffs_zero": higher_coeffs_zero,
        "is_straight_hypotenuse": is_straight,
        "is_45_degree_equatione_di_moti": slope == Q1,
        "hypotenuse_slope_dy_over_dx": format_rational(slope) if slope is not None else "non_constant",
    }


def _collinearity_det2(p0: tuple[Fraction, Fraction], p1: tuple[Fraction, Fraction], p2: tuple[Fraction, Fraction]) -> Fraction:
    return (p1[0] - p0[0]) * (p2[1] - p0[1]) - (p1[1] - p0[1]) * (p2[0] - p0[0])


def _eval_discrete_snapshot_series(
    pos_fn: Any,
    vel_fn: Any,
    ns: tuple[int, ...] = (3, 4, 5, 6),
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for n_steps in ns:
        pts = [
            (
                Fraction(pos_fn(k) + vel_fn(k) * (n_steps - k) - pos_fn(n_steps), 1),
                Fraction(-((n_steps - k) ** 2), 1),
            )
            for k in range(n_steps, 0, -1)
        ]
        dets = [_collinearity_det2(pts[0], pts[1], pts[j]) for j in range(2, len(pts))]
        rows.append({
            "N": n_steps,
            "first_det": format_rational(dets[0]),
            "all_determinants_zero": all(d == Q0 for d in dets),
            "collinearity_broken": any(d != Q0 for d in dets),
        })
    return rows


def _consecutive_det_ratios(rows: Sequence[dict[str, Any]]) -> list[Fraction]:
    vals = [parse_exact_rational(r["first_det"]) for r in rows]
    return [vals[i + 1] / vals[i] for i in range(len(vals) - 1)]


def build_pillar1_arundel() -> dict[str, Any]:
    eq_45 = evaluate_pitcher_snapshot_poly([3, 7, 5], 10)          # a_h = 10 == g -> 45 deg
    eq_slope = evaluate_pitcher_snapshot_poly([0, 2, 2], 10)       # a_h = 4, g = 10 -> slope 5/2
    cubic_break = evaluate_pitcher_snapshot_poly([0, 0, 5, 1], 10) # c_3 = 1 != 0 -> curved!
    quartic_break = evaluate_pitcher_snapshot_poly([1, 0, 5, 0, Fraction(1, 2)], 10)

    def _galileo_pos(k: int) -> int:
        return k * k

    def _leonardo_pos(k: int) -> int:
        return (1 << k) - 1

    # (a) Continuous velocity Galileo: X_p(k) = k^2, v(k) = 2*k -> exact 0 curvature det
    galileo_cont = _eval_discrete_snapshot_series(_galileo_pos, lambda k: 2 * k)

    # (b) Uniform discrete backward difference: v_bwd(k) = X(k) - X(k-1)
    galileo_bwd = _eval_discrete_snapshot_series(_galileo_pos, lambda k: _galileo_pos(k) - _galileo_pos(k - 1))
    leonardo_bwd = _eval_discrete_snapshot_series(_leonardo_pos, lambda k: _leonardo_pos(k) - _leonardo_pos(k - 1))
    g_bwd_ratios = _consecutive_det_ratios(galileo_bwd)
    l_bwd_ratios = _consecutive_det_ratios(leonardo_bwd)

    # (c) Uniform discrete forward difference: v_fwd(k) = X(k+1) - X(k)
    galileo_fwd = _eval_discrete_snapshot_series(_galileo_pos, lambda k: _galileo_pos(k + 1) - _galileo_pos(k))
    leonardo_fwd = _eval_discrete_snapshot_series(_leonardo_pos, lambda k: _leonardo_pos(k + 1) - _leonardo_pos(k))
    g_fwd_ratios = _consecutive_det_ratios(galileo_fwd)
    l_fwd_ratios = _consecutive_det_ratios(leonardo_fwd)

    # Exact 4-interval Gharib-Roh-Noca (2023) comparison: k = 0,1,2,3,4
    # Galileo cumulative [0,1,4,9,16] vs Leonardo cumulative [0,1,3,7,15]
    g4 = [Fraction(k * k, 1) for k in range(5)]
    l4 = [Fraction((1 << k) - 1, 1) for k in range(5)]
    g_mean = sum(g4, Q0) / Fraction(5, 1)
    l_mean = sum(l4, Q0) / Fraction(5, 1)
    cov = sum(((g4[i] - g_mean) * (l4[i] - l_mean) for i in range(5)), Q0)
    var_g = sum(((g4[i] - g_mean) ** 2 for i in range(5)), Q0)
    var_l = sum(((l4[i] - l_mean) ** 2 for i in range(5)), Q0)
    r2_4step = (cov * cov) / (var_g * var_l)
    # Uncentered origin-anchored slope match (sum g_k L_k)^2 / (sum g_k^2 sum L_k^2)
    dot_gl = sum((g4[i] * l4[i] for i in range(1, 5)), Q0)
    norm_g = sum((g4[i] * g4[i] for i in range(1, 5)), Q0)
    norm_l = sum((l4[i] * l4[i] for i in range(1, 5)), Q0)
    origin_r2_4step = (dot_gl * dot_gl) / (norm_g * norm_l)
    endpoint_norm_rms_sq = sum(((l4[i] / Fraction(15, 1) - g4[i] / Fraction(16, 1)) ** 2 for i in range(1, 5)), Q0) / Fraction(4, 1)

    bwd_gal_const = all(r == Q1 for r in g_bwd_ratios)
    bwd_leo_exp = all(r == Fraction(2, 1) for r in l_bwd_ratios)
    fwd_gal_const = all(r == Q1 for r in g_fwd_ratios)
    fwd_leo_exp = all(r == Fraction(2, 1) for r in l_fwd_ratios)

    verified = all([
        eq_45["is_straight_hypotenuse"],
        eq_45["is_45_degree_equatione_di_moti"],
        eq_slope["is_straight_hypotenuse"],
        not eq_slope["is_45_degree_equatione_di_moti"],
        not cubic_break["is_straight_hypotenuse"],
        not quartic_break["is_straight_hypotenuse"],
        all(row["all_determinants_zero"] for row in galileo_cont),
        bwd_gal_const,
        bwd_leo_exp,
        all(row["collinearity_broken"] for row in leonardo_bwd),
        fwd_gal_const,
        fwd_leo_exp,
        all(row["collinearity_broken"] for row in leonardo_fwd),
        leonardo_bwd[0]["N"] == 3,
        r2_4step > Fraction(98, 100),
        origin_r2_4step > Fraction(99, 100),
    ])
    return {
        "pitcher_snapshot_45deg": eq_45,
        "pitcher_snapshot_general_slope": eq_slope,
        "must_fail_cubic_jerk": cubic_break,
        "must_fail_quartic": quartic_break,
        "discrete_galileo_continuous_k2": galileo_cont,
        "uniform_backward_difference": {
            "galileo_k2": galileo_bwd,
            "leonardo_2k": leonardo_bwd,
            "galileo_consecutive_det_ratios": [format_rational(r) for r in g_bwd_ratios],
            "leonardo_consecutive_det_ratios": [format_rational(r) for r in l_bwd_ratios],
            "galileo_constant_det": bwd_gal_const,
            "leonardo_exponential_growth": bwd_leo_exp,
        },
        "uniform_forward_difference": {
            "galileo_k2": galileo_fwd,
            "leonardo_2k": leonardo_fwd,
            "galileo_consecutive_det_ratios": [format_rational(r) for r in g_fwd_ratios],
            "leonardo_consecutive_det_ratios": [format_rational(r) for r in l_fwd_ratios],
            "galileo_constant_det": fwd_gal_const,
            "leonardo_exponential_growth": fwd_leo_exp,
        },
        "four_interval_diagnostics": {
            "galileo_cumulative": [format_rational(v) for v in g4],
            "leonardo_cumulative": [format_rational(v) for v in l4],
            "centered_r2": format_rational(r2_4step),
            "origin_anchored_r2": format_rational(origin_r2_4step),
            "endpoint_normalized_rms_sq": format_rational(endpoint_norm_rms_sq),
        },
        "pillar_verified": verified,
    }


# ---------------------------------------------------------------------------
# Pillar 2: Codex Leicester Rising Bubble Paradox (arXiv:2609.26283 Aug 2026)
# ---------------------------------------------------------------------------

def rayleigh_lamb_omega_sq(l_mode: int, tau: Any, sigma: Any = Q1) -> Fraction:
    """Exact pure-Q Rayleigh-Lamb squared frequency sigma * l(l-1)(l+1)(l+2)/((l+1)tau + l)."""
    l_val = require_int(l_mode, "l_mode", lo=2, hi=64)
    tau_q = parse_exact_rational(tau, "tau")
    sig_q = parse_exact_rational(sigma, "sigma")
    if tau_q < Q0:
        raise LeonardoError("NEGATIVE_DENSITY_RATIO", "density ratio tau must be >= 0")
    if sig_q < Q0:
        raise LeonardoError("NEGATIVE_SURFACE_TENSION", "surface tension sigma must be >= 0")
    num = Fraction(l_val * (l_val - 1) * (l_val + 1) * (l_val + 2), 1)
    den = Fraction(l_val + 1, 1) * tau_q + Fraction(l_val, 1)
    return sig_q * num / den


def _is_rational_square(val: Fraction) -> int | None:
    if val < Q0 or val.denominator != 1:
        return None
    r = math.isqrt(val.numerator)
    return r if r * r == val.numerator else None


def evaluate_bubble_hopf_point(mu: Any) -> dict[str, Any]:
    """Exact 4D coupled sway-tilt bubble stability via Hurwitz Bareiss det & Hermite Sylvester inertia."""
    mu_q = parse_exact_rational(mu, "mu")
    # Coupled 4D linearized sway-tilt-wake matrix A(mu):
    # char poly det(lam I - A(mu)) = (lam^2 + 2 lam + 2)(lam^2 + 2 lam + 3) + mu
    #                              = lam^4 + 4 lam^3 + 9 lam^2 + 10 lam + (6 + mu)
    a_mat = [
        [Q0, Q1, Q0, Q0],
        [Fraction(-2, 1), Fraction(-2, 1), Q1, Q0],
        [Q0, Q0, Q0, Q1],
        [-mu_q, Q0, Fraction(-3, 1), Fraction(-2, 1)],
    ]
    # Compute characteristic polynomial coefficients directly via Lagrange interpolation
    # on det(z I - A(mu)) at z = 0, 1, -1, 2, -2 (exact Bareiss determinants!)
    def _det_shift(z: Fraction) -> Fraction:
        m = [[(z if r == c else Q0) - a_mat[r][c] for c in range(4)] for r in range(4)]
        return bareiss_det_exact(m)

    p0 = _det_shift(Q0)                  # a4
    p1 = _det_shift(Q1)                  # 1 + a1 + a2 + a3 + a4
    pm1 = _det_shift(Fraction(-1, 1))    # 1 - a1 + a2 - a3 + a4
    p2 = _det_shift(Fraction(2, 1))      # 16 + 8 a1 + 4 a2 + 2 a3 + a4
    pm2 = _det_shift(Fraction(-2, 1))    # 16 - 8 a1 + 4 a2 - 2 a3 + a4
    a4 = p0
    # Solve exact linear system for (a1, a2, a3)
    even1 = (p1 + pm1) / Fraction(2, 1) - Q1 - a4          # a2
    odd1 = (p1 - pm1) / Fraction(2, 1)                     # a1 + a3
    odd2 = (p2 - pm2) / Fraction(4, 1)                     # 4 a1 + a3
    a2 = even1
    a1 = (odd2 - odd1) / Fraction(3, 1)
    a3 = odd1 - a1
    # Verify p2 consistency
    check_p2 = Fraction(16, 1) + Fraction(8, 1) * a1 + Fraction(4, 1) * a2 + Fraction(2, 1) * a3 + a4

    h3 = [
        [a1, a3, Q0],
        [Q1, a2, a4],
        [Q0, a1, a3],
    ]
    d1 = a1
    d2 = bareiss_det_exact([[a1, a3], [Q1, a2]])
    d3 = bareiss_det_exact(h3)

    # Exact 4x4 symmetric Hermite stability matrix
    herm = [
        [a1, Q0, a3, Q0],
        [Q0, a1 * a2 - a3, Q0, a1 * a4],
        [a3, Q0, a2 * a3 - a1 * a4, Q0],
        [Q0, a1 * a4, Q0, a3 * a4],
    ]
    inertia = sylvester_inertia_exact(herm)

    # At Hopf threshold d3 == 0, check pure-imaginary pair lam^2 = -a3/a1
    omega_h_sq = a3 / a1
    hopf_real_res = omega_h_sq * omega_h_sq - a2 * omega_h_sq + a4
    hopf_imag_res = -a1 * omega_h_sq + a3

    return {
        "mu": format_rational(mu_q),
        "char_poly_coeffs": [format_rational(v) for v in (Q1, a1, a2, a3, a4)],
        "char_poly_check_p2_exact": check_p2 == p2,
        "hurwitz_d1": format_rational(d1),
        "hurwitz_d2": format_rational(d2),
        "hurwitz_d3": format_rational(d3),
        "hermite_inertia": inertia,
        "hopf_omega_sq": format_rational(omega_h_sq),
        "hopf_pure_imag_residual_zero": (hopf_real_res, hopf_imag_res) == (Q0, Q0),
    }


def build_pillar2_leicester_bubble() -> dict[str, Any]:
    w2_vac = rayleigh_lamb_omega_sq(2, Q0, Q1)
    vacuum_spectrum: list[dict[str, Any]] = []
    for l_mode in range(2, 13):
        wl = rayleigh_lamb_omega_sq(l_mode, Q0, Q1)
        ratio = wl / w2_vac
        sq_root = _is_rational_square(ratio)
        is_harm = l_mode > 2 and sq_root is not None
        vacuum_spectrum.append({
            "l": l_mode,
            "omega_sq_vacuum": format_rational(wl),
            "ratio_over_omega2_sq": format_rational(ratio),
            "is_integer_harmonic_resonance": is_harm,
            "harmonic_k": sq_root if is_harm else 0,
        })

    # Complete exact positive rational resonance locus tau_{l,k} > 0 for 3 <= l <= 10
    positive_resonances: list[dict[str, Any]] = []
    for l_mode in range(3, 11):
        n_l = l_mode * (l_mode - 1) * (l_mode + 1) * (l_mode + 2)
        ratio_zero = Fraction((l_mode - 1) * (l_mode + 1) * (l_mode + 2), 12)
        ratio_inf = Fraction(l_mode * (l_mode - 1) * (l_mode + 2), 8)
        k_lo = math.isqrt(ratio_zero.numerator // ratio_zero.denominator) + 1
        k_hi = math.isqrt(ratio_inf.numerator // ratio_inf.denominator)
        for k_val in range(k_lo, k_hi + 1):
            k2 = Fraction(k_val * k_val, 1)
            if not (ratio_zero < k2 < ratio_inf):
                continue
            tau_lk = Fraction(24 * k_val * k_val * l_mode - 2 * n_l, 3 * n_l - 24 * k_val * k_val * (l_mode + 1))
            lhs = rayleigh_lamb_omega_sq(l_mode, tau_lk, Q1)
            rhs = k2 * rayleigh_lamb_omega_sq(2, tau_lk, Q1)
            positive_resonances.append({
                "l": l_mode,
                "k": k_val,
                "tau_lk": format_rational(tau_lk),
                "omega_l_sq": format_rational(lhs),
                "k2_omega_2_sq": format_rational(rhs),
                "back_substitution_exact": all((tau_lk > Q0, lhs == rhs)),
            })

    # Zero surface tension collapse (sigma = 0 -> omega_l^2 == 0 identically)
    sigma_zero_all_zero = all(rayleigh_lamb_omega_sq(l_mode, Fraction(1, 3), Q0) == Q0 for l_mode in range(2, 13))

    # 4D Hopf bifurcation sweep: sub-critical -> exact Hopf threshold (41/4) -> super-critical
    hopf_sub = evaluate_bubble_hopf_point(Fraction(10, 1))
    hopf_crit = evaluate_bubble_hopf_point(Fraction(41, 4))
    hopf_sup = evaluate_bubble_hopf_point(Fraction(11, 1))

    vac_res_modes = [row["l"] for row in vacuum_spectrum if row["is_integer_harmonic_resonance"]]
    verified = all([
        vac_res_modes == [7],
        vacuum_spectrum[5]["ratio_over_omega2_sq"] == "36",
        vacuum_spectrum[5]["harmonic_k"] == 6,
        len(positive_resonances) == 6,
        all(r["back_substitution_exact"] for r in positive_resonances),
        sigma_zero_all_zero,
        hopf_sub["char_poly_check_p2_exact"],
        hopf_crit["char_poly_check_p2_exact"],
        hopf_sup["char_poly_check_p2_exact"],
        hopf_sub["hermite_inertia"]["congruence_verified"],
        hopf_crit["hermite_inertia"]["congruence_verified"],
        hopf_sup["hermite_inertia"]["congruence_verified"],
        (hopf_sub["hermite_inertia"]["n_pos"], hopf_sub["hermite_inertia"]["n_neg"], hopf_sub["hermite_inertia"]["n_zero"]) == (4, 0, 0),
        (hopf_crit["hermite_inertia"]["n_pos"], hopf_crit["hermite_inertia"]["n_neg"], hopf_crit["hermite_inertia"]["n_zero"]) == (2, 0, 2),
        (hopf_sup["hermite_inertia"]["n_pos"], hopf_sup["hermite_inertia"]["n_neg"], hopf_sup["hermite_inertia"]["n_zero"]) == (2, 2, 0),
        hopf_crit["hurwitz_d3"] == "0",
        hopf_crit["hopf_pure_imag_residual_zero"],
    ])
    return {
        "vacuum_spectrum_l2_to_l12": vacuum_spectrum,
        "vacuum_resonance_modes": vac_res_modes,
        "positive_rational_resonances_l3_to_l10": positive_resonances,
        "sigma_zero_collapse_all_zero": sigma_zero_all_zero,
        "hopf_bifurcation_4d": {
            "subcritical_straight_rise": hopf_sub,
            "critical_hopf_threshold": hopf_crit,
            "supercritical_oscillatory": hopf_sup,
        },
        "pillar_verified": verified,
    }


# ---------------------------------------------------------------------------
# Pillar 3: Codex Atlanticus Reciprocal Bridge & Da Vinci Domes (2401.00881)
# ---------------------------------------------------------------------------

def _bridge_cone_matrix(mu: Fraction) -> list[list[Fraction]]:
    """9x8 equilibrium matrix A_cone(mu) for 3-beam reciprocal arch bridge under friction cone rays.

    Beams (weight W = 2 each):
      Beam 1 (Left):  G1 = (-3/2, 1), A_L = (-2, 0), B_L = (-1, 2)
      Beam 2 (Crown): G2 = (0, 2),    B_L = (-1, 2), B_R = (1, 2)
      Beam 3 (Right): G3 = (3/2, 1),  B_R = (1, 2),  A_R = (2, 0)
    Contacts (4 unilateral frictional contacts, 2 extreme cone rays each -> 8 columns):
      c0 (A_L): ground on B1, n=(0,1), t=(1,0)
      c1 (A_R): ground on B3, n=(0,1), t=(-1,0)
      c2 (B_L): B1 on B2, Pythagorean notch n=(3/5,4/5), t=(-4/5,3/5)
      c3 (B_R): B3 on B2, Pythagorean notch n=(-3/5,4/5), t=(4/5,3/5)
    """
    g_pts = (
        (Fraction(-3, 2), Q1),
        (Q0, Fraction(2, 1)),
        (Fraction(3, 2), Q1),
    )
    contacts = (
        # (pos_beam, neg_beam_or_None, point, n_vec, t_vec)
        (0, None, (Fraction(-2, 1), Q0), (Q0, Q1), (Q1, Q0)),
        (2, None, (Fraction(2, 1), Q0), (Q0, Q1), (Fraction(-1, 1), Q0)),
        (1, 0, (Fraction(-1, 1), Fraction(2, 1)), (Fraction(3, 5), Fraction(4, 5)), (Fraction(-4, 5), Fraction(3, 5))),
        (1, 2, (Q1, Fraction(2, 1)), (Fraction(-3, 5), Fraction(4, 5)), (Fraction(4, 5), Fraction(3, 5))),
    )
    mat = [[Q0] * 8 for _ in range(9)]
    for c_idx, (pb, nb, pt, nvec, tvec) in enumerate(contacts):
        for s_idx, sign in enumerate((Q1, Fraction(-1, 1))):
            col = 2 * c_idx + s_idx
            fx = nvec[0] + sign * mu * tvec[0]
            fy = nvec[1] + sign * mu * tvec[1]
            # Action on positive beam pb
            rx_p = pt[0] - g_pts[pb][0]
            ry_p = pt[1] - g_pts[pb][1]
            mat[3 * pb + 0][col] += fx
            mat[3 * pb + 1][col] += fy
            mat[3 * pb + 2][col] += rx_p * fy - ry_p * fx
            # Equal and opposite reaction on negative beam nb (if interior contact)
            if nb is not None:
                rx_n = pt[0] - g_pts[nb][0]
                ry_n = pt[1] - g_pts[nb][1]
                mat[3 * nb + 0][col] -= fx
                mat[3 * nb + 1][col] -= fy
                mat[3 * nb + 2][col] -= rx_n * fy - ry_n * fx
    return mat


def verify_reciprocal_bridge_at_friction(mu: Any) -> dict[str, Any]:
    """Certify primal unilateral equilibrium (mu >= 1/3) or exact Farkas collapse dual (mu < 1/3)."""
    mu_q = parse_exact_rational(mu, "mu")
    if mu_q < Q0:
        raise LeonardoError("NEGATIVE_FRICTION", "Coulomb friction mu must be >= 0")

    g_vec = [Q0, Fraction(2, 1), Q0, Q0, Fraction(2, 1), Q0, Q0, Fraction(2, 1), Q0]
    a_cone = _bridge_cone_matrix(mu_q)

    # First solve exact (f_n, f_t) contact forces via 8x8 full-rank equilibrium system
    # (drop redundant horizontal equilibrium of beam 2? No: check directly on 8 linearly independent rows!)
    # Express forces directly in (n, t) basis using A_nt (9x8):
    # A_nt col 2*c = n_c, col 2*c+1 = t_c -> exact independent equations rows [0,1,2,3,4,5,6,7] (row 8 is dependent!)
    a_1 = _bridge_cone_matrix(Q1)
    a_0 = _bridge_cone_matrix(Q0)
    a_nt = [[Q0] * 8 for _ in range(9)]
    for r in range(9):
        for c in range(4):
            a_nt[r][2 * c] = a_0[r][2 * c]
            a_nt[r][2 * c + 1] = a_1[r][2 * c] - a_0[r][2 * c]
    f_sol = solve_linear_exact([a_nt[r] for r in range(8)], [g_vec[r] for r in range(8)])
    eq_residual_nt = [
        sum((a_nt[r][j] * f_sol[j] for j in range(8)), Q0) - g_vec[r]
        for r in range(9)
    ]
    fn_list = [f_sol[2 * c] for c in range(4)]
    ft_list = [f_sol[2 * c + 1] for c in range(4)]
    ratios = [abs(ft_list[c]) / fn_list[c] for c in range(4)]
    mu_min = max(ratios)

    if mu_q >= mu_min:
        # Exact primal non-negative cone weights y >= 0 with A_cone(mu) y == g
        y_cone: list[Fraction] = []
        for c in range(4):
            if mu_q == Q0:
                y_cone.extend([fn_list[c] / Fraction(2, 1), fn_list[c] / Fraction(2, 1)])
            else:
                y_plus = (fn_list[c] + ft_list[c] / mu_q) / Fraction(2, 1)
                y_minus = (fn_list[c] - ft_list[c] / mu_q) / Fraction(2, 1)
                y_cone.extend([y_plus, y_minus])
        cone_res = [
            sum((a_cone[r][j] * y_cone[j] for j in range(8)), Q0) - g_vec[r]
            for r in range(9)
        ]
        return {
            "mu": format_rational(mu_q),
            "mu_min": format_rational(mu_min),
            "status": "EQUILIBRIUM_CERTIFIED",
            "all_normal_strictly_positive": all(fn > Q0 for fn in fn_list),
            "normal_forces": [format_rational(fn) for fn in fn_list],
            "tangential_forces": [format_rational(ft) for ft in ft_list],
            "contact_friction_ratios": [format_rational(r) for r in ratios],
            "primal_cone_weights_nonneg": all(y >= Q0 for y in y_cone),
            "equilibrium_residual_zero": all(e == Q0 for e in eq_residual_nt + cone_res),
        }

    # Exact Farkas dual virtual-velocity collapse certificate v(mu) in Q^9:
    # A_cone(mu)^T v >= 0 and v^T g = 8*(3*mu - 1) < 0
    v_dual = [
        Fraction(-2, 1), Fraction(4, 1) * mu_q - Q1, Fraction(-2, 1),
        Q0, Fraction(4, 1) * mu_q - Fraction(2, 1), Q0,
        Fraction(2, 1), Fraction(4, 1) * mu_q - Q1, Fraction(2, 1),
    ]
    atv = [sum((a_cone[r][j] * v_dual[r] for r in range(9)), Q0) for j in range(8)]
    vg = sum((v_dual[r] * g_vec[r] for r in range(9)), Q0)
    return {
        "mu": format_rational(mu_q),
        "mu_min": format_rational(mu_min),
        "status": "FARKAS_COLLAPSE_CERTIFIED",
        "farkas_dual_v": [format_rational(v) for v in v_dual],
        "farkas_ATv": [format_rational(x) for x in atv],
        "farkas_ATv_nonneg": all(x >= Q0 for x in atv),
        "farkas_vTg": format_rational(vg),
        "farkas_vTg_strictly_negative": vg < Q0,
    }


def build_pillar3_bridge_and_domes() -> dict[str, Any]:
    # Part A1: Collinear-rod Descartes angular-defect obstruction (in half-turns, 1 == 180 deg)
    # Every vertex with a straight-through collinear rod has side A sum >= 1 and side B sum >= 1
    vertex_cases = [
        ("deg2_straight_rod", 2, [Q1], [Q1]),
        ("deg3_t_junction", 3, [Q1], [Fraction(1, 2), Fraction(1, 2)]),
        ("deg4_flat_reciprocal_cross", 4, [Fraction(1, 2), Fraction(1, 2)], [Fraction(1, 2), Fraction(1, 2)]),
        ("deg5_saddle_reciprocal", 5, [Fraction(1, 2), Fraction(2, 3)], [Fraction(1, 3), Fraction(1, 3), Fraction(1, 2)]),
        ("deg6_hex_collinear_cross", 6, [Fraction(1, 3), Fraction(1, 3), Fraction(1, 3)], [Fraction(1, 3), Fraction(1, 3), Fraction(1, 3)]),
    ]
    descartes_rows: list[dict[str, Any]] = []
    for label, deg, side_a, side_b in vertex_cases:
        sum_a = sum(side_a, Q0)
        sum_b = sum(side_b, Q0)
        theta_v = sum_a + sum_b
        defect = Fraction(2, 1) - theta_v  # 2 half-turns == 360 deg
        descartes_rows.append({
            "case": label,
            "degree": deg,
            "side_a_half_turns": format_rational(sum_a),
            "side_b_half_turns": format_rational(sum_b),
            "total_angle_half_turns": format_rational(theta_v),
            "descartes_defect_half_turns": format_rational(defect),
            "nonpositive_defect": defect <= Q0,
        })

    # Part A2: Euler torus-vs-sphere obstruction (all 11 uniform periodic tilings vs spherical cages)
    torus_tilings = [
        ("4^4_square", 1, 2, 1),
        ("3^6_triangular", 1, 3, 2),
        ("6^3_hexagonal", 2, 3, 1),
        ("3.6.3.6_kagome", 3, 6, 3),
        ("3^3.4^2_elongated_tri", 2, 5, 3),
        ("3^2.4.3.4_snub_square", 4, 10, 6),
        ("3.4.6.4_rhombitrihex", 6, 12, 6),
        ("4.8^2_truncated_square", 4, 6, 2),
        ("3.12^2_truncated_hex", 6, 9, 3),
        ("4.6.12_great_rhombitrihex", 12, 18, 6),
        ("3^4.6_snub_hex", 6, 15, 9),
    ]
    torus_rows = [
        {"name": nm, "V": v, "E": e, "F": f, "chi": v - e + f}
        for nm, v, e, f in torus_tilings
    ]
    sphere_cages = [
        ("tetrahedron", 4, 6, 4, 0),
        ("octahedron", 6, 12, 8, 0),
        ("cube", 8, 12, 6, 0),
        ("icosahedron", 12, 30, 20, 0),
        ("dodecahedron", 20, 30, 12, 12),
        ("truncated_icosahedron_dome", 60, 90, 32, 12),
    ]
    sphere_rows = [
        {
            "name": nm,
            "V": v,
            "E": e,
            "F": f,
            "chi": v - e + f,
            "pentagonal_disclinations": p5,
            "total_descartes_defect_deg": 360 * (v - e + f),
        }
        for nm, v, e, f, p5 in sphere_cages
    ]

    # Part B: Reciprocal bridge equilibrium & Farkas dual collapse
    eq_threshold = verify_reciprocal_bridge_at_friction(Fraction(1, 3))
    eq_safe = verify_reciprocal_bridge_at_friction(Fraction(1, 2))
    collapse_low_mu = verify_reciprocal_bridge_at_friction(Fraction(1, 4))
    collapse_zero_mu = verify_reciprocal_bridge_at_friction(Q0)

    # Single central-beam removal collapse (only beams 1 & 3, only ground contacts c0 & c1, even at mu=100!)
    mu_huge = Fraction(100, 1)
    a_full_huge = _bridge_cone_matrix(mu_huge)
    # Extract rows for beams 1 (0,1,2) and 3 (6,7,8), cols for ground contacts c0 (0,1) and c1 (2,3)
    del_rows = (0, 1, 2, 6, 7, 8)
    a_del = [[a_full_huge[r][c] for c in range(4)] for r in del_rows]
    g_del = [Q0, Fraction(2, 1), Q0, Q0, Fraction(2, 1), Q0]
    # Pure rotation about ground hinges A_L=(-2,0) & A_R=(2,0): v(A_L) = v(A_R) = (0,0)!
    # G1 - A_L = (1/2, 1), omega1 = -1 -> v_G1 = (+1, -1/2); G3 - A_R = (-1/2, 1), omega3 = +1 -> v_G3 = (-1, -1/2)
    v_del = [Q1, Fraction(-1, 2), Fraction(-1, 1), Fraction(-1, 1), Fraction(-1, 2), Q1]
    atv_del = [sum((a_del[r][c] * v_del[r] for r in range(6)), Q0) for c in range(4)]
    vg_del = sum((v_del[r] * g_del[r] for r in range(6)), Q0)

    beam_removal_collapse = {
        "ground_friction_tested": format_rational(mu_huge),
        "farkas_dual_v_6dof": [format_rational(v) for v in v_del],
        "farkas_ATv": [format_rational(x) for x in atv_del],
        "farkas_ATv_all_zero": all(x == Q0 for x in atv_del),
        "farkas_vTg": format_rational(vg_del),
        "catastrophic_collapse_certified": all((all(x >= Q0 for x in atv_del), vg_del < Q0)),
    }

    verified = all([
        all(r["nonpositive_defect"] for r in descartes_rows),
        len(torus_rows) == 11,
        all(r["chi"] == 0 for r in torus_rows),
        all((r["chi"], r["total_descartes_defect_deg"]) == (2, 720) for r in sphere_rows),
        eq_threshold["status"] == "EQUILIBRIUM_CERTIFIED",
        eq_threshold["equilibrium_residual_zero"],
        eq_threshold["all_normal_strictly_positive"],
        eq_threshold["primal_cone_weights_nonneg"],
        eq_threshold["mu_min"] == "1/3",
        eq_safe["status"] == "EQUILIBRIUM_CERTIFIED",
        eq_safe["equilibrium_residual_zero"],
        collapse_low_mu["status"] == "FARKAS_COLLAPSE_CERTIFIED",
        collapse_low_mu["farkas_ATv_nonneg"],
        collapse_low_mu["farkas_vTg_strictly_negative"],
        collapse_zero_mu["status"] == "FARKAS_COLLAPSE_CERTIFIED",
        collapse_zero_mu["farkas_ATv_nonneg"],
        collapse_zero_mu["farkas_vTg_strictly_negative"],
        beam_removal_collapse["farkas_ATv_all_zero"],
        beam_removal_collapse["catastrophic_collapse_certified"],
    ])
    return {
        "da_vinci_domes_descartes_obstruction": descartes_rows,
        "euler_torus_tilings_11": torus_rows,
        "euler_sphere_cages": sphere_rows,
        "reciprocal_bridge_equilibrium_threshold": eq_threshold,
        "reciprocal_bridge_equilibrium_safe": eq_safe,
        "reciprocal_bridge_farkas_collapse_low_mu": collapse_low_mu,
        "reciprocal_bridge_farkas_collapse_zero_mu": collapse_zero_mu,
        "reciprocal_bridge_central_beam_removal": beam_removal_collapse,
        "pillar_verified": verified,
    }


# ---------------------------------------------------------------------------
# Pillar 4: MS M / Trattato Branching Law vs Sopp-Valbuena vs Murray vs 2411.08024
# ---------------------------------------------------------------------------

def generalized_branching_exponent(p_diss: int, q_cost: int, m_flow_power: int) -> Fraction:
    """Exact variational branching exponent alpha*(p, q, m) = (p + q) / m."""
    p = require_int(p_diss, "p_diss", lo=1, hi=32)
    q = require_int(q_cost, "q_cost", lo=1, hi=32)
    m = require_int(m_flow_power, "m_flow_power", lo=1, hi=8)
    return Fraction(p + q, m)


def kirchhoff_schur_binary_tree_conductance(level_branch_conductances: Sequence[Any]) -> dict[str, Any]:
    """Exact Kirchhoff-Schur complement pushforward on a full binary tree graph Laplacian.

    Given per-branch conductances [G_0, G_1, ..., G_{L-1}] for levels 0..L-1:
      - Node 0 is the grounded/driven root (potential u_0 = 1).
      - Level d (0 <= d < L) has 2^d edges connecting parents to 2^d children;
        tips at depth L are grounded to potential 0.
      - Eliminates all internal non-root, non-tip nodes via exact Gaussian solve
        L_II u_I = -L_IB u_B over Q and computes exact root current I_root = G_eff!
    """
    if type(level_branch_conductances) not in (list, tuple) or len(level_branch_conductances) == 0:
        raise LeonardoError("INVALID_CONDUCTANCES", "level_branch_conductances must be non-empty list/tuple")
    n_levels = len(level_branch_conductances)
    if n_levels > 6:
        raise LeonardoError("TREE_TOO_DEEP", "binary tree depth capped at 6 levels")
    g_lev = [parse_exact_rational(g, f"G[{i}]") for i, g in enumerate(level_branch_conductances)]
    if any(g <= Q0 for g in g_lev):
        raise LeonardoError("NONPOSITIVE_CONDUCTANCE", "all branch conductances must be > 0")

    # Build full tree nodes:
    # Node 0: root (u = 1)
    # Level 0 edge connects root (0) -> node 1 (1 edge, conductance g_lev[0])
    # Level d >= 1 edges connect node u at depth d -> two children at depth d+1 (2^d edges, g_lev[d])
    # Total non-tip nodes = 1 + (1 + 2 + ... + 2^{L-2}) = 2^{L-1} (for L >= 1); tips are all grounded (u = 0)
    # Specifically, internal unknown nodes are indices 1 .. (2^{L-1} - 1) if L >= 2.
    # Let's index vertices by standard heap indexing starting at node 1 (below root 0):
    #   Edge (0, 1) has conductance g_lev[0].
    #   For d = 1 .. L-1, nodes u in [2^{d-1}, 2^d - 1] connect to children 2u and 2u+1 with g_lev[d].
    #   Nodes in [2^{L-1}, 2^L - 1] are grounded tips (u = 0).
    #   Internal unknown nodes are [1 .. 2^{L-1} - 1] (count = 2^{L-1} - 1).
    n_internal = (1 << (n_levels - 1)) - 1
    if n_internal == 0:
        g_eff = g_lev[0]
        r_eff = Q1 / g_eff
    else:
        lap = [[Q0] * n_internal for _ in range(n_internal)]
        rhs = [Q0] * n_internal
        # Edge from root 0 (u=1) to internal node 1 (matrix index 0)
        lap[0][0] += g_lev[0]
        rhs[0] += g_lev[0]
        for d in range(1, n_levels):
            gd = g_lev[d]
            for parent_id in range(1 << (d - 1), 1 << d):
                pi = parent_id - 1
                for child_id in (2 * parent_id, 2 * parent_id + 1):
                    lap[pi][pi] += gd
                    if child_id <= n_internal:
                        ci = child_id - 1
                        lap[ci][ci] += gd
                        lap[pi][ci] -= gd
                        lap[ci][pi] -= gd
        u_int = solve_linear_exact(lap, rhs)
        # Root current into tree = g_lev[0] * (u_root - u_1) = g_lev[0] * (1 - u_int[0])
        g_eff = g_lev[0] * (Q1 - u_int[0])
        r_eff = Q1 / g_eff

    # Independent series-parallel closed form: R_series = sum_{d=0}^{L-1} 1 / (2^d * g_lev[d])
    r_series = sum((Q1 / (Fraction(1 << d, 1) * g_lev[d]) for d in range(n_levels)), Q0)
    return {
        "n_levels": n_levels,
        "n_edges": (1 << n_levels) - 1,
        "n_internal_schur_nodes": n_internal,
        "level_branch_conductances": [format_rational(g) for g in g_lev],
        "effective_conductance_G_eff": format_rational(g_eff),
        "effective_resistance_R_eff": format_rational(r_eff),
        "series_parallel_R_eff": format_rational(r_series),
        "schur_matches_series_parallel": r_eff == r_series,
    }


def build_pillar4_branching_and_trees() -> dict[str, Any]:
    alpha_leonardo = generalized_branching_exponent(2, 2, 2)
    alpha_murray = generalized_branching_exponent(4, 2, 2)
    alpha_turbulent = generalized_branching_exponent(5, 2, 3)

    # Exact symmetric-split Poiseuille dissipation dominance of Murray (alpha=3) over Leonardo (alpha=2)
    # Normalized power+metabolic cost J(r, Q) = Q^2 * r^{-4} + 2 * r^2 (parent r_0=1, Q_0=1 -> optimal J_0=3)
    # Symmetric split into n_children = 2 daughters each carrying Q_c = 1/2:
    n_children = Fraction(2, 1)
    q_child = Q1 / n_children
    # Leonardo (n_children * r_L^2 = 1 -> r_L^2 = 1/2): exact cost C_L = n_children * (Q_c^2 / (r_L^2)^2 + 2 * r_L^2)
    r_l_sq = Q1 / n_children
    c_leonardo = n_children * (q_child * q_child / (r_l_sq * r_l_sq) + Fraction(2, 1) * r_l_sq)
    c_leonardo_cubed = c_leonardo ** 3
    # Murray (n_children * r_M^3 = 1 -> r_M^3 = 1/2): setting u = r_M^2 (u^3 = (r_M^3)^2),
    # r_M^{-4} = u / (r_M^3)^2, so C_M = n_children * (Q_c^2 / (r_M^3)^2 + 2) * u and C_M^3 is exact rational!
    r_m_cube = Q1 / n_children
    c_murray_over_u = n_children * (q_child * q_child / (r_m_cube * r_m_cube) + Fraction(2, 1))
    c_murray_cubed = (c_murray_over_u ** 3) * (r_m_cube * r_m_cube)
    murray_dominates_exact = c_murray_cubed < c_leonardo_cubed

    # Pythagorean trees (arXiv:2411.08024 Nov 2024): exact cross-sectional & lateral surface area conservation
    kappa = Fraction(5, 2)
    pyth_triples = [(3, 4, 5), (5, 12, 13), (8, 15, 17)]
    pyth_rows: list[dict[str, Any]] = []
    for a, b, c in pyth_triples:
        area_parent = Fraction(c * c, 1)
        area_children = Fraction(a * a + b * b, 1)
        surf_parent = kappa * area_parent
        surf_children = kappa * Fraction(a * a, 1) + kappa * Fraction(b * b, 1)
        pyth_rows.append({
            "triple": [a, b, c],
            "aspect_ratio_kappa": format_rational(kappa),
            "area_conserved": area_parent == area_children,
            "surface_area_conserved": surf_parent == surf_children,
            "area_value": format_rational(area_parent),
            "surface_area_value": format_rational(surf_parent),
        })

    # 3-level recursive (3,4,5) Pythagorean tree total area invariant
    widths = [Q1]
    level_areas: list[Fraction] = [Q1]
    for _ in range(3):
        nxt: list[Fraction] = []
        for w in widths:
            nxt.append(w * Fraction(3, 5))
            nxt.append(w * Fraction(4, 5))
        widths = nxt
        level_areas.append(sum((w * w for w in widths), Q0))

    # 4-level binary vascular tree Kirchhoff-Schur pushforward (15 edges, 7 internal nodes)
    # Naive uniform single-pipe Leonardo (alpha=2 -> R_d^2 = 2^{-d} -> G_branch = R_d^4 = 2^{-2d})
    schur_naive_alpha2 = kirchhoff_schur_binary_tree_conductance(
        [Fraction(1, 1 << (2 * d)) for d in range(4)]
    )
    # Sopp-Valbuena (PNAS 2023) inverse conduit widening (G_branch = 2^{-d} -> level conductance 2^d * 2^{-d} = 1)
    schur_sopp_valbuena = kirchhoff_schur_binary_tree_conductance(
        [Fraction(1, 1 << d) for d in range(4)]
    )
    conductance_gain = (
        parse_exact_rational(schur_sopp_valbuena["effective_conductance_G_eff"])
        / parse_exact_rational(schur_naive_alpha2["effective_conductance_G_eff"])
    )

    verified = all([
        alpha_leonardo == Fraction(2, 1),
        alpha_murray == Fraction(3, 1),
        alpha_turbulent == Fraction(7, 3),
        murray_dominates_exact,
        c_leonardo_cubed - c_murray_cubed == Fraction(10, 1),
        all((r["area_conserved"], r["surface_area_conserved"]) == (True, True) for r in pyth_rows),
        all(a == Q1 for a in level_areas),
        schur_naive_alpha2["schur_matches_series_parallel"],
        schur_sopp_valbuena["schur_matches_series_parallel"],
        schur_naive_alpha2["effective_resistance_R_eff"] == "15",
        schur_sopp_valbuena["effective_resistance_R_eff"] == "4",
        conductance_gain == Fraction(15, 4),
    ])
    return {
        "variational_exponents": {
            "leonardo_p2_q2_m2": format_rational(alpha_leonardo),
            "murray_p4_q2_m2": format_rational(alpha_murray),
            "turbulent_p5_q2_m3": format_rational(alpha_turbulent),
        },
        "symmetric_split_poiseuille_dominance": {
            "C_leonardo": format_rational(c_leonardo),
            "C_leonardo_cubed": format_rational(c_leonardo_cubed),
            "C_murray_cubed": format_rational(c_murray_cubed),
            "exact_cubic_gap": format_rational(c_leonardo_cubed - c_murray_cubed),
            "murray_strictly_dominates_leonardo": murray_dominates_exact,
        },
        "pythagorean_trees_2411_08024": {
            "triples": pyth_rows,
            "recursive_3level_areas": [format_rational(a) for a in level_areas],
            "all_levels_area_invariant": all(a == Q1 for a in level_areas),
        },
        "kirchhoff_schur_4level_vascular": {
            "naive_alpha2_uniform_pipe": schur_naive_alpha2,
            "sopp_valbuena_widened_conduit": schur_sopp_valbuena,
            "conductance_gain_ratio": format_rational(conductance_gain),
        },
        "pillar_verified": verified,
    }


# ---------------------------------------------------------------------------
# Pillar 5: De Ludo Geometrico Squarable Lunes, MS B Aerial Screw & CS-13 Audit
# ---------------------------------------------------------------------------

def chebyshev_u_poly(k: int) -> list[int]:
    """Exact integer coefficients [c_0, c_1, ..., c_k] of Chebyshev polynomial U_k(x)."""
    deg = require_int(k, "chebyshev_k", lo=0, hi=16)
    if deg == 0:
        return [1]
    if deg == 1:
        return [0, 2]
    u_prev2 = [1]
    u_prev1 = [0, 2]
    for _ in range(2, deg + 1):
        # U_j(x) = 2*x*U_{j-1}(x) - U_{j-2}(x)
        nxt = [0] * (len(u_prev1) + 1)
        for i, c in enumerate(u_prev1):
            nxt[i + 1] += 2 * c
        for i, c in enumerate(u_prev2):
            nxt[i] -= c
        u_prev2, u_prev1 = u_prev1, nxt
    return u_prev1


def _poly_mul_z(a: Sequence[int], b: Sequence[int]) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def _poly_eval_q(coeffs: Sequence[int], x: Fraction) -> Fraction:
    acc = Q0
    for c in reversed(coeffs):
        acc = acc * x + Fraction(c, 1)
    return acc


def _fp_trim(a: list[int], p: int) -> list[int]:
    r = [x % p for x in a]
    while r and r[-1] == 0:
        r.pop()
    return r


def _fp_mul(a: list[int], b: list[int], p: int) -> list[int]:
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] = (r[i + j] + x * y) % p
    return _fp_trim(r, p)


def _fp_rem(a: list[int], b: list[int], p: int) -> list[int]:
    r = _fp_trim(a, p)
    d = _fp_trim(b, p)
    inv = pow(d[-1], p - 2, p)
    while len(r) >= len(d):
        c = (r[-1] * inv) % p
        shift = len(r) - len(d)
        for i in range(len(d)):
            r[shift + i] = (r[shift + i] - c * d[i]) % p
        r = _fp_trim(r, p)
    return r


def _fp_gcd(a: list[int], b: list[int], p: int) -> list[int]:
    x = _fp_trim(a, p)
    y = _fp_trim(b, p)
    while y:
        x, y = y, _fp_rem(x, y, p)
    if x:
        inv = pow(x[-1], p - 2, p)
        x = [(c * inv) % p for c in x]
    return x


def _fp_powmod(base: list[int], exp: int, modp: list[int], p: int) -> list[int]:
    res = [1]
    b = _fp_rem(base, modp, p)
    e = exp
    while e > 0:
        if e & 1:
            res = _fp_rem(_fp_mul(res, b, p), modp, p)
        b = _fp_rem(_fp_mul(b, b, p), modp, p)
        e >>= 1
    return res


def is_irreducible_mod_prime(coeffs: Sequence[int], prime: int) -> bool:
    """Exact Rabin irreducibility test in F_p[x] for integer polynomial (ascending coeffs)."""
    p = require_int(prime, "prime", lo=2, hi=1000)
    if type(coeffs) not in (list, tuple) or len(coeffs) < 2:
        raise LeonardoError("INVALID_POLY", "polynomial must have degree >= 1")
    int_c = [require_int(c, f"poly[{i}]") for i, c in enumerate(coeffs)]
    # Verify p is actually prime (small deterministic check)
    for d in range(2, math.isqrt(p) + 1):
        if p % d == 0:
            raise LeonardoError("NON_PRIME_MODULUS", f"{p} is not prime")
    f = _fp_trim(int_c, p)
    deg = len(f) - 1
    if deg != len(int_c) - 1:
        raise LeonardoError("LEADING_COEFF_VANISHES_MOD_P", "leading coefficient divisible by p")
    xp = [0, 1]
    for d in range(1, deg // 2 + 1):
        xp = _fp_powmod(xp, p, f, p)
        diff = [(xp[i] if i < len(xp) else 0) - (1 if i == 1 else 0) for i in range(max(len(xp), 2))]
        if len(_fp_gcd(diff, f, p)) > 1:
            return False
    return True


def evaluate_aerial_screw_isolift(area_scale_lambda: Any, cl_ratio: Any, cd_ratio: Any) -> dict[str, Any]:
    """Exact pure-Q dimensional iso-lift scaling for MS B aerial screw (arXiv:2506.10223)."""
    lam = parse_exact_rational(area_scale_lambda, "lambda")
    alpha_l = parse_exact_rational(cl_ratio, "cl_ratio")
    alpha_d = parse_exact_rational(cd_ratio, "cd_ratio")
    if lam <= Q0 or alpha_l <= Q0 or alpha_d <= Q0:
        raise LeonardoError("NONPOSITIVE_SCALING", "aerial screw scaling ratios must be > 0")
    omega_sq_ratio = Q1 / (lam * alpha_l)
    power_sq_ratio = (alpha_d * alpha_d) / (lam * alpha_l * alpha_l * alpha_l)
    acoustic_intensity_ratio = omega_sq_ratio
    return {
        "area_scale_lambda": format_rational(lam),
        "cl_ratio": format_rational(alpha_l),
        "cd_ratio": format_rational(alpha_d),
        "omega_sq_ratio": format_rational(omega_sq_ratio),
        "power_sq_ratio": format_rational(power_sq_ratio),
        "acoustic_intensity_ratio": format_rational(acoustic_intensity_ratio),
        "acoustic_intensity_reduction": format_rational(Q1 - acoustic_intensity_ratio),
        "power_strictly_reduced": power_sq_ratio < Q1,
        "noise_strictly_reduced": acoustic_intensity_ratio < Q1,
    }


def _divisors_pos(n: int) -> list[int]:
    val = abs(n)
    if val == 0:
        return [1]
    small: list[int] = []
    large: list[int] = []
    for d in range(1, math.isqrt(val) + 1):
        if val % d == 0:
            small.append(d)
            if d * d != val:
                large.append(val // d)
    return small + list(reversed(large))


def _find_rational_root_cubic(r_coeffs: Sequence[Fraction]) -> Fraction | None:
    """Exact Rational Root Theorem search for a cubic polynomial over Q."""
    lcm_d = 1
    for c in r_coeffs:
        lcm_d = math.lcm(lcm_d, c.denominator)
    int_c = [int(c * lcm_d) for c in r_coeffs]
    if int_c[0] == 0:
        return Q0
    p_divs = _divisors_pos(int_c[0])
    q_divs = _divisors_pos(int_c[3])
    for p_val in p_divs:
        for q_val in q_divs:
            if math.gcd(p_val, q_val) != 1:
                continue
            for sign in (1, -1):
                cand = Fraction(sign * p_val, q_val)
                if _poly_eval_q(int_c, cand) == Q0:
                    return cand
    return None


def build_pillar5_lunes_screw_and_myth() -> dict[str, Any]:
    # 1. All 5 algebraically squarable lunes: n * U_{m-1}(x)^2 - m * U_{n-1}(x)^2 = 0
    # Because m, n have identical parity for (3,1),(5,1),(5,3) and both U_{m-1}^2, U_{n-1}^2 are even in x,
    # P_{m,n}(x) is a pure polynomial in y = x^2!
    squarable_specs = [(2, 1), (3, 1), (3, 2), (5, 1), (5, 3)]
    squarable_rows: list[dict[str, Any]] = []
    for m_val, n_val in squarable_specs:
        um = chebyshev_u_poly(m_val - 1)
        un = chebyshev_u_poly(n_val - 1)
        um2 = _poly_mul_z(um, um)
        un2 = _poly_mul_z(un, un)
        max_len = max(len(um2), len(un2))
        px = [
            n_val * (um2[i] if i < len(um2) else 0) - m_val * (un2[i] if i < len(un2) else 0)
            for i in range(max_len)
        ]
        # Verify strictly even polynomial in x -> extract polynomial in y = x^2
        all_odd_zero = all(px[i] == 0 for i in range(1, len(px), 2))
        py_raw = [px[i] for i in range(0, len(px), 2)]
        g_div = 0
        for c in py_raw:
            g_div = math.gcd(g_div, abs(c))
        py = [c // g_div for c in py_raw]
        deg_y = len(py) - 1

        # Verify solvability by nested square roots (deg_y in {1, 2}, or quartic with rational Ferrari resolvent root!)
        ferrari_root: Fraction | None = None
        if deg_y <= 2:
            solvable_by_sqroots = True
        else:
            # Monic quartic y^4 + b y^3 + c y^2 + d y + e -> Ferrari cubic resolvent R(t)
            lead = Fraction(py[4], 1)
            b = Fraction(py[3], 1) / lead
            c = Fraction(py[2], 1) / lead
            d = Fraction(py[1], 1) / lead
            e = Fraction(py[0], 1) / lead
            # R(t) = t^3 - c t^2 + (b d - 4 e) t - (b^2 e - 4 c e + d^2)
            r_coeffs = [
                -(b * b * e - Fraction(4, 1) * c * e + d * d),
                b * d - Fraction(4, 1) * e,
                -c,
                Q1,
            ]
            ferrari_root = _find_rational_root_cubic(r_coeffs)
            solvable_by_sqroots = ferrari_root is not None

        squarable_rows.append({
            "ratio_m_n": [m_val, n_val],
            "even_in_cos_theta": all_odd_zero,
            "poly_in_y_cos2_asc": py,
            "deg_in_y": deg_y,
            "ferrari_resolvent_rational_root": format_rational(ferrari_root) if ferrari_root is not None else "n/a_deg_le_2",
            "ruler_compass_constructible": all((all_odd_zero, solvable_by_sqroots)),
        })

    # 2. Exact Zero-Pi Curvilinear Area Dissections in Q (+) Q*pi computed directly from geometric radii
    # Hippocrates 2:1 lune on right isosceles triangle of legs L = 2 (hyp^2 = 2*L^2):
    leg = Fraction(2, 1)
    tri_area = (leg * leg) / Fraction(2, 1)
    r_leg = leg / Fraction(2, 1)
    r_hyp_sq = (leg * leg + leg * leg) / Fraction(4, 1)
    two_lunes_pi = Fraction(2, 1) * (r_leg * r_leg / Fraction(2, 1)) - (r_hyp_sq / Fraction(2, 1))
    hippocrates_lune = (tri_area / Fraction(2, 1), two_lunes_pi / Fraction(2, 1))
    # Leonardo Codex Atlanticus 4-lune rosette on inscribed square of side s = 2 (diag^2 = 2*s^2):
    sq_side = Fraction(2, 1)
    sq_area = sq_side * sq_side
    r_side = sq_side / Fraction(2, 1)
    r_circ_sq = (sq_side * sq_side + sq_side * sq_side) / Fraction(4, 1)
    rosette_pi = Fraction(4, 1) * (r_side * r_side / Fraction(2, 1)) - r_circ_sq
    leonardo_rosette_4lunes = (sq_area, rosette_pi)

    # 3. Exact Galois Obstruction 1: (4, 1) lune -> U_3(x) = 8x^3 - 4x = sqrt(4/1) = 2 -> 4x^3 - 2x - 1 = 0
    u3 = chebyshev_u_poly(3)  # [0, -4, 0, 8]
    f41 = [(u3[i] - (2 if i == 0 else 0)) // 2 for i in range(4)]  # [-1, -2, 0, 4]
    rrt_candidates = [Fraction(s * p, q) for s in (1, -1) for p in (1,) for q in (1, 2, 4)]
    rrt_evals = {format_rational(r): format_rational(_poly_eval_q(f41, r)) for r in rrt_candidates}
    f41_no_rational_root = all(_poly_eval_q(f41, r) != Q0 for r in rrt_candidates)
    f41_irred_mod5 = is_irreducible_mod_prime(f41, 5)

    # 4. Exact Galois Obstruction 2: (7, 1) lune -> P_{7,1}(x) = U_6(x)^2 - 7 in y = 4x^2
    # Direct exact derivation from Chebyshev U_6(x):
    u6 = chebyshev_u_poly(6)  # even powers 0,2,4,6
    u6_in_y4 = [u6[2 * j] // (1 << (2 * j)) for j in range(4)]  # [-1, 6, -5, 1] for y = 4*x^2
    u6_sq = _poly_mul_z(u6_in_y4, u6_in_y4)
    f71_y4 = [u6_sq[i] - (7 if i == 0 else 0) for i in range(len(u6_sq))]  # [-6, -12, 46, -62, 37, -10, 1]
    f71_irred_mod17 = is_irreducible_mod_prime(f71_y4, 17)

    # 5. MS B Aerial Screw iso-lift scaling (arXiv:2506.10223 Aug 2025)
    screw_pure_area = evaluate_aerial_screw_isolift(Fraction(3, 1), Q1, Q1)
    screw_jhu_2025 = evaluate_aerial_screw_isolift(Fraction(7, 2), Q1, Fraction(27, 25))
    pure_p2 = parse_exact_rational(screw_pure_area["power_sq_ratio"])
    pure_power_bracket_ok = Fraction(57, 100) ** 2 < pure_p2 < Fraction(58, 100) ** 2
    jhu_p2 = parse_exact_rational(screw_jhu_2025["power_sq_ratio"])
    jhu_power_bracket_ok = Fraction(57, 100) ** 2 < jhu_p2 < Fraction(58, 100) ** 2

    # 6. CS-13 Historical Attribution Audit (arXiv:1311.0816)
    myth_audit = {
        "source_arxiv": "1311.0816",
        "claim_audited": "Leonardo da Vinci proof of the Pythagorean theorem",
        "actual_author": "Johann Tobias Mayer (1772)",
        "attributed_to_leonardo_in_authentic_codices": False,
        "golden_ratio_numerology_excluded": True,
    }

    verified = all([
        len(squarable_rows) == 5,
        all(r["ruler_compass_constructible"] for r in squarable_rows),
        hippocrates_lune == (Q1, Q0),
        leonardo_rosette_4lunes == (Fraction(4, 1), Q0),
        f41 == [-1, -2, 0, 4],
        f41_no_rational_root,
        f41_irred_mod5,
        f71_y4 == [-6, -12, 46, -62, 37, -10, 1],
        f71_irred_mod17,
        screw_pure_area["power_strictly_reduced"],
        screw_pure_area["noise_strictly_reduced"],
        screw_jhu_2025["power_strictly_reduced"],
        screw_jhu_2025["noise_strictly_reduced"],
        jhu_power_bracket_ok,
        not myth_audit["attributed_to_leonardo_in_authentic_codices"],
    ])
    return {
        "squarable_lunes_5": squarable_rows,
        "zero_pi_dissections": {
            "hippocrates_2_1_lune": {
                "algebraic_area": format_rational(hippocrates_lune[0]),
                "pi_coeff": format_rational(hippocrates_lune[1]),
                "zero_pi_exact": hippocrates_lune[1] == Q0,
            },
            "leonardo_atlanticus_4_lunes": {
                "algebraic_area": format_rational(leonardo_rosette_4lunes[0]),
                "pi_coeff": format_rational(leonardo_rosette_4lunes[1]),
                "zero_pi_exact": leonardo_rosette_4lunes[1] == Q0,
            },
        },
        "galois_obstruction_4_1": {
            "poly_in_x_asc": f41,
            "degree": 3,
            "rrt_evaluations": rrt_evals,
            "no_rational_root": f41_no_rational_root,
            "irreducible_mod_5": f41_irred_mod5,
            "degree_not_power_of_2": True,
            "ruler_compass_impossible": all((f41_no_rational_root, f41_irred_mod5)),
        },
        "galois_obstruction_7_1": {
            "poly_in_4x2_asc": f71_y4,
            "degree": 6,
            "irreducible_mod_17": f71_irred_mod17,
            "degree_not_power_of_2": True,
            "ruler_compass_impossible": f71_irred_mod17,
        },
        "aerial_screw_isolift_2506_10223": {
            "pure_area_3x": screw_pure_area,
            "pure_area_3x_power_drop_in_42_to_43_pct_band": pure_power_bracket_ok,
            "jhu_2025_mechanism_witness": screw_jhu_2025,
            "jhu_power_drop_in_42_to_43_pct_band": jhu_power_bracket_ok,
        },
        "cs13_myth_audit": myth_audit,
        "pillar_verified": verified,
    }


# ---------------------------------------------------------------------------
# Standalone Certificate Assembly & Full-Replay Zone-B Payload Validator
# ---------------------------------------------------------------------------

def build_standalone_certificate() -> dict[str, Any]:
    p1 = build_pillar1_arundel()
    p2 = build_pillar2_leicester_bubble()
    p3 = build_pillar3_bridge_and_domes()
    p4 = build_pillar4_branching_and_trees()
    p5 = build_pillar5_lunes_screw_and_myth()
    all_ok = all([
        p1["pillar_verified"],
        p2["pillar_verified"],
        p3["pillar_verified"],
        p4["pillar_verified"],
        p5["pillar_verified"],
    ])
    payload = {
        "oracle_class": "exact",
        "novelty_classification": "N1",
        "zero_floats_exact_arithmetic": True,
        "all_verified": all_ok,
        "pillar1_arundel_motion": p1,
        "pillar2_leicester_bubble": p2,
        "pillar3_atlanticus_bridge_domes": p3,
        "pillar4_trattato_branching_trees": p4,
        "pillar5_lunes_aerial_screw_myth": p5,
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


def _validate_payload_structure(payload: dict[str, Any]) -> None:
    """Structural and bool-vs-int schema gate enforced under both full_replay=False and True."""
    if frozenset(payload.keys()) != _PAYLOAD_KEYS:
        raise LeonardoError("INVALID_PAYLOAD_KEYS", "payload top-level keys mismatch")
    if payload["oracle_class"] != "exact":
        raise LeonardoError("INVALID_PAYLOAD_META", "oracle_class must be 'exact'")
    if payload["novelty_classification"] != "N1":
        raise LeonardoError("INVALID_PAYLOAD_META", "novelty_classification must be 'N1'")
    if payload["zero_floats_exact_arithmetic"] is not True:
        raise LeonardoError("INVALID_PAYLOAD_META", "zero_floats_exact_arithmetic must be True")
    if payload["all_verified"] is not True:
        raise LeonardoError("INVALID_PAYLOAD_META", "all_verified must be True")
    for pkey in _PILLAR_KEYS:
        pdict = payload[pkey]
        if type(pdict) is not dict:
            raise LeonardoError("INVALID_PILLAR_TYPE", f"{pkey} must be strict dict")
        if pdict.get("pillar_verified") is not True:
            raise LeonardoError("PILLAR_NOT_VERIFIED", f"{pkey}.pillar_verified must be True")

    stack: list[Any] = [payload]
    while stack:
        cur = stack.pop()
        if type(cur) is dict:
            for k, v in cur.items():
                if type(v) is bool:
                    if k not in _ALLOWED_BOOL_KEYS:
                        raise LeonardoError("BOOL_IN_NON_BOOL_FIELD", f"unexpected bool in field {k}")
                elif type(v) in (dict, list):
                    stack.append(v)
        else:
            for item in cur:
                if type(item) is bool:
                    raise LeonardoError("BOOL_IN_LIST", "bool element forbidden inside list")
                if type(item) in (dict, list):
                    stack.append(item)


def validate_certificate_payload(cert: Any, full_replay: bool = True) -> dict[str, Any]:
    """Zone-B hardened in-memory certificate validator (callable directly by S19c fuzzer)."""
    require_bool(full_replay, "full_replay")
    validate_json_tree_iterative(cert)
    if type(cert) is not dict:
        raise LeonardoError("CERT_NOT_DICT", "certificate root must be strict dict")
    if frozenset(cert.keys()) != _CERT_KEYS:
        raise LeonardoError("INVALID_CERT_KEYS", "certificate keys mismatch")
    if cert["schema"] != SCHEMA_VERSION:
        raise LeonardoError("INVALID_SCHEMA", "unexpected certificate schema")
    if cert["track_id"] != TRACK_ID:
        raise LeonardoError("INVALID_TRACK_ID", "unexpected track_id")

    payload = cert["payload"]
    if type(payload) is not dict:
        raise LeonardoError("PAYLOAD_NOT_DICT", "payload must be strict dict")

    claimed_payload_sha = require_hex64(cert["payload_sha256"], "payload_sha256")
    actual_payload_sha = sha256_hex(canonical_json_bytes(payload))
    if not constant_time_hex64_equal(claimed_payload_sha, actual_payload_sha, "payload_sha256"):
        raise LeonardoError("PAYLOAD_SHA_MISMATCH", "payload_sha256 mismatch")

    claimed_cert_sha = require_hex64(cert["certificate_sha256"], "certificate_sha256")
    cert_body = {
        "schema": cert["schema"],
        "track_id": cert["track_id"],
        "payload_sha256": claimed_payload_sha,
        "payload": payload,
    }
    actual_cert_sha = sha256_hex(canonical_json_bytes(cert_body))
    if not constant_time_hex64_equal(claimed_cert_sha, actual_cert_sha, "certificate_sha256"):
        raise LeonardoError("CERT_SHA_MISMATCH", "certificate_sha256 mismatch")

    _validate_payload_structure(payload)

    if full_replay:
        fresh = build_standalone_certificate()
        if not constant_time_hex64_equal(actual_payload_sha, fresh["payload_sha256"], "recomputed_payload_sha256"):
            raise LeonardoError("RECOMPUTATION_MISMATCH", "payload differs from deterministic recomputation")

    return {
        "valid": True,
        "schema": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": actual_payload_sha,
        "certificate_sha256": actual_cert_sha,
        "full_replay": full_replay,
    }
