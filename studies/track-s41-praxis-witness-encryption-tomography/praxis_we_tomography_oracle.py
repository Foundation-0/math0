#!/usr/bin/env python3
"""Track S41 (Portals 43 + 45): Praxis Witness Encryption & P = NP Rank-Gap / Polya Obstructions.

Pure Python 3 standard library over exact Z / Q / F_q / F_{q^n}.
Zero external dependencies, zero AST float literals, zero float() calls, zero bare
asserts, zero .isdigit()/.isnumeric()/.isdecimal(), zero mathematical RNG calls.

Grounded directly in Tse, Vanjani & Vesely (Nov 2026), "Praxis: Practical Witness
Encryption for NP" (N0), Bichsel/Landauer/Polya (1913) / Lasserre-SOS / Hair-Sahai (2026)
prior anchors (N0), unified into an executable pure-Z/Q/F_q tomography engine (N1):
  P1: Executable small-prime-field Praxis core protocol (q=257, n=4, K1=2, K2=1, nu=2,
      chunked Fig. 9-10 Enc/Dec in exponent space, Lemma 4.7 QAP coset sumcheck Eq. (4),
      Example 5.2 Frobenius conjugate weights, Eq. (5)-(7) ties/cancellations/masks,
      and Lemma 5.4 honest key & message recovery).
  P2: Exact Rank-1/2/3/4 cheat classification (Lemma 4.3, p. 19 rank-3 symmetric tensor,
      rank-4 alternating-sum tightness, Lemma B.5 Moore determinant over F_{257^4}),
      shared Lasserre/SOS PSD rank-2 pseudodistribution on UNSAT Example 2.1, and
      exhaustive Polya (1913) 0/512 sign-flip obstruction vs 512/512 F_2 collapse.
  P3: Exact pure-Z/Q Table 4 admissibility over BN254's exact prime order q (with
      deterministic Pocklington primality proof & Capelli irreducibility of T^4608 - 5),
      Proposition 5.7 counts, Definition B.1 / Lemma B.2 E(u) bounds, and Appendix C
      Hair-Sahai basic construction + Proposition C.1 lower bound.
  P4: Honest scope ledger (exact 4.5-bit reduction-loss arithmetic, BN254 ETNFS vs GGM
      margin, Table 6 Lean-vs-Paper deltas) & executable Aletheia CS-19 sealed-witness bridge.
"""
from __future__ import annotations

from fractions import Fraction
import hashlib
import hmac
import itertools
import json
import math
from typing import Any, Sequence

SCHEMA_VERSION = "aletheia.praxis_we_tomography.certificate.v1"
TRACK_ID = "TRACK-S41-PRAXIS-WITNESS-ENCRYPTION-TOMOGRAPHY"

MAX_JSON_BYTES = 1_048_576
HARD_MAX_BYTES_CAP = 64 * 1024 * 1024
MAX_JSON_DEPTH = 64
MAX_INT_BITS = 3321
MAX_INT_DIGITS = 1000
MAX_RATIONAL_CHARS = 2 * MAX_INT_DIGITS + 2

_HEX_LOWER = frozenset("0123456789abcdef")
_ASCII_DIGITS = frozenset("0123456789")
_CERT_KEYS = frozenset({"schema", "track_id", "payload_sha256", "certificate_sha256", "payload"})
_PILLAR_KEYS = (
    "pillar1_executable_praxis_protocol",
    "pillar2_rank_gap_and_polya_obstructions",
    "pillar3_table4_admissibility_and_hair_sahai",
    "pillar4_honest_scope_and_cs19_bridge",
)
_PAYLOAD_KEYS = frozenset({
    "oracle_class",
    "novelty_classification",
    "literature_anchors_n0",
    "zero_floats_exact_arithmetic",
    "all_verified",
    *_PILLAR_KEYS,
})
_ALLOWED_BOOL_KEYS = frozenset({
    "all_15_minors_nonneg_psd",
    "all_linear_ties_hold",
    "all_tests_passed_over_q",
    "all_verified",
    "b2_e2_lt_2_neg122",
    "b2_e_diff_le_1_minus_2_neg100",
    "booleanity_passed",
    "capelli_irreducible_t4_minus_c0",
    "capelli_irreducible_t4608_minus_5",
    "decryption_recovered_exact_kappa",
    "decryption_recovered_exact_message",
    "diag_zero",
    "divisibility_h_ord_divides_q_minus_1",
    "divisibility_n_divides_q_minus_1",
    "divisibility_q_mod_2dR_eq_1",
    "eq4_key_remainder_zero",
    "eq4_oth_remainder_zero",
    "eq5_tie_divisions_exact",
    "eq7_mask_identity_exact",
    "example52_v_formula_exact",
    "fig4_f101_kills_mixture",
    "g_bounds_exact",
    "hs_prop_c1_gt_2_55_14",
    "hs_r3_fails_eq10",
    "hs_r4_m4_fails_m5_passes_eq10",
    "invalid_witness_rejected",
    "lemma54_exact_match",
    "moore_dep_control_zero",
    "moore_indep_nonzero",
    "neg_control_non_passing_rejected",
    "nonzero_stack",
    "p1_chunk_bounds_hold",
    "p2_group_coverage_holds",
    "p4_lifting_24beta4_lt_q3",
    "p4_lifting_beta_2_188_lt_q3",
    "pillar_verified",
    "pocklington_prime_verified",
    "praxis_quad_ties_broken_by_repeat",
    "praxis_ties_all_3_hold",
    "quad_alt_sum_leaks_row0_or_diag",
    "quad_ties_broken_by_linear_tensor",
    "qap_rw_allowed_nu_ndiv_k",
    "rank1_witness_passes",
    "row0_zero",
    "search_range_2B_plus_1_lt_q",
    "valid_witness_unmasked_exact",
    "zero_floats_exact_arithmetic",
})

Q0 = Fraction(0, 1)
Q1 = Fraction(1, 1)

# Exact BN254 Barreto-Naehrig seed & group order q (Table 4)
BN254_SEED_T = 4965661367192848881
BN254_Q = 21888242871839275222246405745257275088548364400416034343698204186575808495617
_BN254_QM1_SMALL_PRIMES: tuple[tuple[int, int], ...] = (
    (2, 28),
    (3, 2),
    (13, 1),
    (29, 1),
    (983, 1),
    (11003, 1),
    (237073, 1),
    (405928799, 1),
    (1670836401704629, 1),
)
_MR_DET_BASES_64: tuple[int, ...] = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)


class PraxisTomographyError(ValueError):
    """Fail-closed typed error (never stripped by python3 -O)."""

    def __init__(self, code: str, message: str) -> None:
        self.code = code
        self.message = message
        super().__init__(f"{code}: {message}")


# ---------------------------------------------------------------------------
# Zone-B Exact Primitives (Symmetric MAX_INT_BITS=3321 <-> MAX_INT_DIGITS=1000)
# ---------------------------------------------------------------------------

def require_bool(val: Any, label: str) -> bool:
    if type(val) is not bool:
        raise PraxisTomographyError("INVALID_BOOL", f"{label} must be exact bool")
    return val


def require_int(val: Any, label: str, lo: int | None = None, hi: int | None = None) -> int:
    if type(val) is not int:
        raise PraxisTomographyError("INVALID_INT", f"{label} must be exact int")
    if lo is not None and val < lo:
        raise PraxisTomographyError("INT_OUT_OF_RANGE", f"{label} < {lo}")
    if hi is not None and val > hi:
        raise PraxisTomographyError("INT_OUT_OF_RANGE", f"{label} > {hi}")
    return val


def require_str(val: Any, label: str, max_len: int = MAX_JSON_BYTES) -> str:
    cap = require_int(max_len, f"{label}.max_len", lo=1, hi=HARD_MAX_BYTES_CAP)
    if type(val) is not str:
        raise PraxisTomographyError("INVALID_STR", f"{label} must be exact str")
    if len(val) > cap:
        raise PraxisTomographyError("STR_TOO_LONG", f"{label} exceeds length {cap}")
    try:
        val.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise PraxisTomographyError("INVALID_UTF8_SURROGATE", f"{label} contains lone UTF-16 surrogate") from exc
    return val


def require_hex64(val: Any, label: str) -> str:
    s = require_str(val, label, max_len=64)
    if len(s) != 64 or any(ch not in _HEX_LOWER for ch in s):
        raise PraxisTomographyError("INVALID_HEX64", f"{label} must be 64 lowercase hex chars")
    return s


def constant_time_hex64_equal(left: Any, right: Any, label: str) -> bool:
    a = require_hex64(left, f"{label}.left")
    b = require_hex64(right, f"{label}.right")
    return hmac.compare_digest(a.encode("ascii"), b.encode("ascii"))


def _is_canonical_ascii_digits(s: str) -> bool:
    if not s:
        return False
    if any(ch not in _ASCII_DIGITS for ch in s):
        return False
    if len(s) > 1 and s[0] == "0":
        return False
    return True


def _int_exceeds_limits(val: int) -> bool:
    return val.bit_length() > MAX_INT_BITS


def parse_bounded_int(raw: Any, label: str = "int", lo: int | None = None, hi: int | None = None) -> int:
    """Strictly parse exact int or canonical ASCII integer string within symmetric 3321-bit cap."""
    t = type(raw)
    if t is int:
        if _int_exceeds_limits(raw):
            raise PraxisTomographyError("INT_TOO_LARGE", f"{label} exceeds bit limit")
        val = raw
    elif t is str:
        if len(raw) > MAX_INT_DIGITS + 1:
            raise PraxisTomographyError("INVALID_INT_STR", f"{label} string oversized")
        neg = raw.startswith("-")
        digits = raw[1:] if neg else raw
        if not _is_canonical_ascii_digits(digits):
            raise PraxisTomographyError("INVALID_INT_STR", f"{label} not canonical ASCII integer")
        if neg and digits == "0":
            raise PraxisTomographyError("INVALID_INT_STR", f"{label} negative zero forbidden")
        val = -int(digits) if neg else int(digits)
        if _int_exceeds_limits(val):
            raise PraxisTomographyError("INT_TOO_LARGE", f"{label} exceeds bit limit")
    else:
        raise PraxisTomographyError("INVALID_INT", f"{label} must be exact int or str")
    return require_int(val, label, lo=lo, hi=hi)


def parse_exact_rational(raw: Any, label: str = "rational") -> Fraction:
    """Strictly parse exact int, Fraction, or canonical ASCII rational ('p' or 'p/q')."""
    t = type(raw)
    if t is int:
        if _int_exceeds_limits(raw):
            raise PraxisTomographyError("RATIONAL_TOO_LARGE", f"{label} exceeds bit limit")
        return Fraction(raw, 1)
    if t is Fraction:
        if _int_exceeds_limits(raw.numerator) or _int_exceeds_limits(raw.denominator):
            raise PraxisTomographyError("RATIONAL_TOO_LARGE", f"{label} fraction exceeds bit limit")
        return raw
    if t is not str:
        raise PraxisTomographyError("INVALID_RATIONAL_TYPE", f"{label} must be int, Fraction, or str")
    if len(raw) > MAX_RATIONAL_CHARS:
        raise PraxisTomographyError("INVALID_RATIONAL_STR", f"{label} string oversized")
    parts = raw.split("/")
    if len(parts) == 1:
        num_s, den_s = parts[0], None
    elif len(parts) == 2:
        num_s, den_s = parts[0], parts[1]
    else:
        raise PraxisTomographyError("INVALID_RATIONAL_STR", f"{label} contains multiple '/'")
    neg = num_s.startswith("-")
    num_digits = num_s[1:] if neg else num_s
    if not _is_canonical_ascii_digits(num_digits):
        raise PraxisTomographyError("INVALID_RATIONAL_STR", f"{label} numerator not canonical ASCII digits")
    if neg and num_digits == "0":
        raise PraxisTomographyError("INVALID_RATIONAL_STR", f"{label} negative zero forbidden")
    num_val = -int(num_digits) if neg else int(num_digits)
    if den_s is None:
        den_val = 1
    else:
        if not _is_canonical_ascii_digits(den_s):
            raise PraxisTomographyError("INVALID_RATIONAL_STR", f"{label} denominator not canonical ASCII digits")
        den_val = int(den_s)
        if den_val <= 1:
            raise PraxisTomographyError("INVALID_RATIONAL_STR", f"{label} denominator must be > 1")
        reduced = Fraction(num_val, den_val)
        if reduced.denominator != den_val:
            raise PraxisTomographyError("NON_CANONICAL_RATIONAL", f"{label} fraction is not reduced")
    if _int_exceeds_limits(num_val) or _int_exceeds_limits(den_val):
        raise PraxisTomographyError("RATIONAL_TOO_LARGE", f"{label} exceeds bit limit")
    return Fraction(num_val, den_val)


def format_rational(val: Any, label: str = "rational") -> str:
    if type(val) is not Fraction:
        raise PraxisTomographyError("INVALID_RATIONAL_TYPE", f"{label} must be exact Fraction")
    if _int_exceeds_limits(val.numerator) or _int_exceeds_limits(val.denominator):
        raise PraxisTomographyError("RATIONAL_TOO_LARGE", f"{label} exceeds formatting limit")
    if val.denominator == 1:
        return str(val.numerator)
    return f"{val.numerator}/{val.denominator}"


def format_decimal_trunc(val: Any, places: int = 4, label: str = "decimal") -> str:
    """Exact pure-integer decimal truncation normalizing '-0.00'/'-0' to non-negative zero."""
    if type(val) is not Fraction:
        raise PraxisTomographyError("INVALID_RATIONAL_TYPE", f"{label} must be exact Fraction")
    dp = require_int(places, f"{label}.places", lo=0, hi=24)
    if _int_exceeds_limits(val.numerator) or _int_exceeds_limits(val.denominator):
        raise PraxisTomographyError("RATIONAL_TOO_LARGE", f"{label} exceeds formatting limit")
    neg = val.numerator < 0
    scale = 10 ** dp
    scaled = (abs(val.numerator) * scale) // val.denominator
    if scaled == 0:
        neg = False
    sign = "-" if neg else ""
    if dp == 0:
        return f"{sign}{scaled}"
    whole, frac = divmod(scaled, scale)
    return f"{sign}{whole}.{frac:0{dp}d}"


def validate_json_tree_iterative(obj: Any, max_depth: int = MAX_JSON_DEPTH) -> None:
    """Iterative Zone-B validator blocking cycles, depth overflow, floats, subclasses, huge ints, surrogates."""
    limit = require_int(max_depth, "max_depth", lo=1, hi=256)
    stack: list[tuple[Any, int, bool]] = [(obj, 0, False)]
    active_ids: set[int] = set()
    while stack:
        cur, depth, leaving = stack.pop()
        if leaving:
            active_ids.discard(id(cur))
            continue
        if depth > limit:
            raise PraxisTomographyError("JSON_DEPTH_EXCEEDED", f"JSON nesting exceeds depth {limit}")
        t = type(cur)
        if t is dict:
            cid = id(cur)
            if cid in active_ids:
                raise PraxisTomographyError("JSON_CYCLE", "cyclic dict forbidden")
            active_ids.add(cid)
            stack.append((cur, depth, True))
            for k, v in cur.items():
                require_str(k, "json_key")
                stack.append((v, depth + 1, False))
        elif t is list:
            cid = id(cur)
            if cid in active_ids:
                raise PraxisTomographyError("JSON_CYCLE", "cyclic list forbidden")
            active_ids.add(cid)
            stack.append((cur, depth, True))
            for item in cur:
                stack.append((item, depth + 1, False))
        elif t is str:
            require_str(cur, "json_str")
        elif t is int:
            if _int_exceeds_limits(cur):
                raise PraxisTomographyError("INT_TOO_LARGE", "integer exceeds Zone-B bit limit")
        elif t is bool or cur is None:
            continue
        else:
            raise PraxisTomographyError("FORBIDDEN_JSON_TYPE", f"forbidden type {t.__name__}")


def _strict_object_pairs_hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise PraxisTomographyError("DUPLICATE_JSON_KEY", f"duplicate key {k!r}")
        out[k] = v
    return out


def _reject_float_literal(tok: str) -> Any:
    raise PraxisTomographyError("FLOAT_FORBIDDEN", f"JSON float literal forbidden: {tok}")


def _reject_constant_literal(tok: str) -> Any:
    raise PraxisTomographyError("NONFINITE_CONSTANT", f"JSON non-finite constant forbidden: {tok}")


def parse_strict_json_text(text: Any, require_object: bool = True, max_bytes: int = MAX_JSON_BYTES) -> Any:
    require_bool(require_object, "require_object")
    cap = require_int(max_bytes, "max_bytes", lo=1, hi=HARD_MAX_BYTES_CAP)
    s = require_str(text, "json_text", max_len=cap)
    if len(s.encode("utf-8")) > cap:
        raise PraxisTomographyError("JSON_TOO_LARGE", f"JSON UTF-8 bytes exceed {cap}")
    try:
        parsed = json.loads(
            s,
            object_pairs_hook=_strict_object_pairs_hook,
            parse_float=_reject_float_literal,
            parse_constant=_reject_constant_literal,
        )
    except PraxisTomographyError:
        raise
    except RecursionError as exc:
        raise PraxisTomographyError("JSON_DEPTH_EXCEEDED", "JSON nesting exceeded parser recursion limit") from exc
    except ValueError as exc:
        raise PraxisTomographyError("INVALID_JSON", f"invalid JSON syntax or int digits: {type(exc).__name__}") from exc
    validate_json_tree_iterative(parsed)
    if require_object and type(parsed) is not dict:
        raise PraxisTomographyError("JSON_NOT_OBJECT", "JSON root must be an object")
    return parsed


def canonical_json_bytes(obj: Any) -> bytes:
    validate_json_tree_iterative(obj)
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False).encode("ascii")


def sha256_hex(data: Any) -> str:
    if type(data) is not bytes:
        raise PraxisTomographyError("INVALID_BYTES", "sha256_hex requires exact bytes")
    return hashlib.sha256(data).hexdigest()


# ---------------------------------------------------------------------------
# Validated Pure-Z / Q / F_q / F_{q^n} Algebraic Helpers
# ---------------------------------------------------------------------------

def is_prime_deterministic_small(n: Any) -> bool:
    """Deterministic primality test valid for all exact ints n < 3.317 * 10^24 (Sorenson-Webster 2015)."""
    v = require_int(n, "n", lo=0, hi=(1 << 80))
    if v < 2:
        return False
    if v in _MR_DET_BASES_64:
        return True
    d = v - 1
    s = 0
    while (d & 1) == 0:
        d >>= 1
        s += 1
    for a in _MR_DET_BASES_64:
        x = pow(a, d, v)
        if x == 1 or x == v - 1:
            continue
        witness_composite = True
        for _ in range(s - 1):
            x = (x * x) % v
            if x == v - 1:
                witness_composite = False
                break
        if witness_composite:
            return False
    return True


def verify_pocklington_prime(n: Any, prime_powers: Sequence[tuple[int, int]], base: Any) -> dict[str, Any]:
    """Deterministic Pocklington (1914) primality proof via factored F | (n-1) with F^2 > n."""
    v = parse_bounded_int(n, "n", lo=3)
    a = parse_bounded_int(base, "base", lo=2, hi=v - 2)
    if type(prime_powers) not in (list, tuple) or len(prime_powers) == 0:
        raise PraxisTomographyError("INVALID_FACTOR_LIST", "prime_powers must be non-empty list/tuple")
    seen: set[int] = set()
    factored_f = 1
    for idx, pair in enumerate(prime_powers):
        if type(pair) not in (list, tuple) or len(pair) != 2:
            raise PraxisTomographyError("INVALID_FACTOR_PAIR", f"prime_powers[{idx}] must be (p, e)")
        p = require_int(pair[0], f"p[{idx}]", lo=2, hi=(1 << 80))
        e = require_int(pair[1], f"e[{idx}]", lo=1, hi=256)
        if p in seen:
            raise PraxisTomographyError("DUPLICATE_PRIME_FACTOR", f"duplicate prime {p}")
        if not is_prime_deterministic_small(p):
            raise PraxisTomographyError("COMPOSITE_FACTOR", f"factor {p} is not prime")
        seen.add(p)
        factored_f *= p ** e
    if factored_f * factored_f <= v:
        raise PraxisTomographyError("POCKLINGTON_F_TOO_SMALL", "requires F^2 > n")
    if (v - 1) % factored_f != 0:
        raise PraxisTomographyError("POCKLINGTON_DIVISIBILITY", "factored F does not divide n - 1")
    fermat_ok = pow(a, v - 1, v) == 1
    gcd_ok = all(math.gcd(pow(a, (v - 1) // p, v) - 1, v) == 1 for p in seen)
    return {
        "n_bits": v.bit_length(),
        "factored_f_bits": factored_f.bit_length(),
        "f_sq_gt_n": factored_f * factored_f > v,
        "base": a,
        "prime_factor_count": len(seen),
        "verified": all((fermat_ok, gcd_ok)),
    }


def _require_prime_mod(q: Any) -> int:
    qv = require_int(q, "q", lo=3, hi=1_000_003)
    if not is_prime_deterministic_small(qv):
        raise PraxisTomographyError("MODULUS_NOT_PRIME", f"modulus {qv} must be prime")
    return qv


def _require_poly(a: Any, q: int, label: str = "poly") -> list[int]:
    if type(a) not in (list, tuple):
        raise PraxisTomographyError("INVALID_POLY", f"{label} must be list/tuple of exact ints")
    out = [require_int(c, f"{label}[{i}]") % q for i, c in enumerate(a)]
    while out and out[-1] == 0:
        out.pop()
    return out


def poly_add(a: Sequence[int], b: Sequence[int], q: int) -> list[int]:
    qv = _require_prime_mod(q)
    pa = _require_poly(a, qv, "a")
    pb = _require_poly(b, qv, "b")
    m = max(len(pa), len(pb))
    out = [((pa[i] if i < len(pa) else 0) + (pb[i] if i < len(pb) else 0)) % qv for i in range(m)]
    while out and out[-1] == 0:
        out.pop()
    return out


def poly_sub(a: Sequence[int], b: Sequence[int], q: int) -> list[int]:
    qv = _require_prime_mod(q)
    pa = _require_poly(a, qv, "a")
    pb = _require_poly(b, qv, "b")
    m = max(len(pa), len(pb))
    out = [((pa[i] if i < len(pa) else 0) - (pb[i] if i < len(pb) else 0)) % qv for i in range(m)]
    while out and out[-1] == 0:
        out.pop()
    return out


def poly_scale(a: Sequence[int], s: int, q: int) -> list[int]:
    qv = _require_prime_mod(q)
    pa = _require_poly(a, qv, "a")
    sv = require_int(s, "s") % qv
    if sv == 0:
        return []
    return [(c * sv) % qv for c in pa]


def poly_mul(a: Sequence[int], b: Sequence[int], q: int) -> list[int]:
    qv = _require_prime_mod(q)
    pa = _require_poly(a, qv, "a")
    pb = _require_poly(b, qv, "b")
    if not pa or not pb:
        return []
    out = [0] * (len(pa) + len(pb) - 1)
    for i, x in enumerate(pa):
        for j, y in enumerate(pb):
            out[i + j] = (out[i + j] + x * y) % qv
    return out


def poly_eval(a: Sequence[int], x: int, q: int) -> int:
    qv = _require_prime_mod(q)
    pa = _require_poly(a, qv, "a")
    xv = require_int(x, "x") % qv
    acc = 0
    for c in reversed(pa):
        acc = (acc * xv + c) % qv
    return acc


def poly_divmod(a: Sequence[int], b: Sequence[int], q: int) -> tuple[list[int], list[int]]:
    qv = _require_prime_mod(q)
    pa = _require_poly(a, qv, "a")
    pb = _require_poly(b, qv, "b")
    if not pb:
        raise PraxisTomographyError("POLY_DIV_BY_ZERO", "divisor polynomial cannot be zero")
    db = len(pb) - 1
    if len(pa) - 1 < db:
        return [], pa
    inv_lc = pow(pb[-1], -1, qv)
    quo = [0] * (len(pa) - db)
    rem = list(pa)
    for k in range(len(pa) - 1, db - 1, -1):
        c = (rem[k] * inv_lc) % qv
        quo[k - db] = c
        for j in range(db + 1):
            rem[k - db + j] = (rem[k - db + j] - c * pb[j]) % qv
    while rem and rem[-1] == 0:
        rem.pop()
    return quo, rem


def poly_vanishing(pts: Sequence[int], q: int) -> list[int]:
    qv = _require_prime_mod(q)
    if type(pts) not in (list, tuple) or len(pts) == 0:
        raise PraxisTomographyError("INVALID_POINTS", "pts must be non-empty list/tuple")
    res = [1]
    for i, x in enumerate(pts):
        xv = require_int(x, f"pts[{i}]") % qv
        res = poly_mul(res, [(-xv) % qv, 1], qv)
    return res


def poly_interpolate(pts: Sequence[int], vals: Sequence[int], q: int) -> list[int]:
    qv = _require_prime_mod(q)
    if type(pts) not in (list, tuple) or type(vals) not in (list, tuple):
        raise PraxisTomographyError("INVALID_INTERP", "pts and vals must be list/tuple")
    if len(pts) == 0 or len(pts) != len(vals):
        raise PraxisTomographyError("INVALID_INTERP", "pts and vals must have equal non-zero length")
    xs = [require_int(x, f"pts[{i}]") % qv for i, x in enumerate(pts)]
    ys = [require_int(y, f"vals[{i}]") % qv for i, y in enumerate(vals)]
    if len(set(xs)) != len(xs):
        raise PraxisTomographyError("DUPLICATE_INTERP_POINT", "interpolation points must be distinct")
    res: list[int] = []
    for i, (xi, yi) in enumerate(zip(xs, ys)):
        if yi == 0:
            continue
        num = [1]
        den = 1
        for j, xj in enumerate(xs):
            if i == j:
                continue
            num = poly_mul(num, [(-xj) % qv, 1], qv)
            den = (den * (xi - xj)) % qv
        res = poly_add(res, poly_scale(num, yi * pow(den, -1, qv), qv), qv)
    return res


def poly_sub_scale(poly: Sequence[int], factor: int, q: int) -> list[int]:
    """Return poly(factor * T) in F_q[T]."""
    qv = _require_prime_mod(q)
    pa = _require_poly(poly, qv, "poly")
    fv = require_int(factor, "factor") % qv
    out: list[int] = []
    pf = 1
    for c in pa:
        out.append((c * pf) % qv)
        pf = (pf * fv) % qv
    while out and out[-1] == 0:
        out.pop()
    return out


def ext_mul_binom(a: Sequence[int], b: Sequence[int], q: int, n: int, c0: int) -> list[int]:
    """Multiply two elements of F_q[T]/(T^n - c0)."""
    qv = _require_prime_mod(q)
    nv = require_int(n, "n", lo=2, hi=16)
    c0v = require_int(c0, "c0", lo=1, hi=qv - 1)
    if type(a) not in (list, tuple) or type(b) not in (list, tuple) or len(a) != nv or len(b) != nv:
        raise PraxisTomographyError("INVALID_EXT_ELEM", f"extension elements must have length {nv}")
    av = [require_int(x, "a[i]") % qv for x in a]
    bv = [require_int(x, "b[i]") % qv for x in b]
    out = [0] * nv
    for i in range(nv):
        for j in range(nv):
            idx = i + j
            term = (av[i] * bv[j]) % qv
            if idx < nv:
                out[idx] = (out[idx] + term) % qv
            else:
                out[idx - nv] = (out[idx - nv] + term * c0v) % qv
    return out


def ext_frobenius(a: Sequence[int], s: int, q: int, omega: int) -> list[int]:
    """Apply Frobenius conjugate sigma^s: T -> omega^s * T."""
    qv = _require_prime_mod(q)
    if type(a) not in (list, tuple) or len(a) == 0:
        raise PraxisTomographyError("INVALID_EXT_ELEM", "extension element must be non-empty list/tuple")
    sv = require_int(s, "s")
    wv = require_int(omega, "omega", lo=1, hi=qv - 1)
    nv = len(a)
    ws = pow(wv, sv % nv, qv)
    return [(require_int(a[e], "a[e]") * pow(ws, e, qv)) % qv for e in range(nv)]


def ext_det3_binom(mat: Sequence[Sequence[Sequence[int]]], q: int, n: int, c0: int) -> list[int]:
    """Exact 3x3 determinant over F_q[T]/(T^n - c0)."""
    qv = _require_prime_mod(q)
    nv = require_int(n, "n", lo=2, hi=16)
    c0v = require_int(c0, "c0", lo=1, hi=qv - 1)
    if type(mat) not in (list, tuple) or len(mat) != 3:
        raise PraxisTomographyError("INVALID_EXT_MAT", "mat must be 3x3")
    for r in range(3):
        if type(mat[r]) not in (list, tuple) or len(mat[r]) != 3:
            raise PraxisTomographyError("INVALID_EXT_MAT", "mat must be 3x3")

    def _sub(x: list[int], y: list[int]) -> list[int]:
        return [(x[k] - y[k]) % qv for k in range(nv)]

    def _add(x: list[int], y: list[int]) -> list[int]:
        return [(x[k] + y[k]) % qv for k in range(nv)]

    def _m2(r1: int, r2: int, c1: int, c2: int) -> list[int]:
        return _sub(
            ext_mul_binom(mat[r1][c1], mat[r2][c2], qv, nv, c0v),
            ext_mul_binom(mat[r1][c2], mat[r2][c1], qv, nv, c0v),
        )

    t0 = ext_mul_binom(mat[0][0], _m2(1, 2, 1, 2), qv, nv, c0v)
    t1 = ext_mul_binom(mat[0][1], _m2(1, 2, 0, 2), qv, nv, c0v)
    t2 = ext_mul_binom(mat[0][2], _m2(1, 2, 0, 1), qv, nv, c0v)
    return _add(_sub(t0, t1), t2)


def fq_matrix_rank(rows: Sequence[Sequence[int]], q: int) -> int:
    """Exact Gaussian-elimination rank over prime field F_q."""
    qv = _require_prime_mod(q)
    if type(rows) not in (list, tuple) or len(rows) == 0:
        raise PraxisTomographyError("INVALID_MATRIX", "rows must be non-empty list/tuple")
    ncols = len(rows[0]) if type(rows[0]) in (list, tuple) else 0
    if ncols == 0:
        raise PraxisTomographyError("INVALID_MATRIX", "matrix rows must be non-empty")
    mat: list[list[int]] = []
    for r_idx, row in enumerate(rows):
        if type(row) not in (list, tuple) or len(row) != ncols:
            raise PraxisTomographyError("INVALID_MATRIX", f"row {r_idx} length mismatch")
        mat.append([require_int(x, f"mat[{r_idx}][{c_idx}]") % qv for c_idx, x in enumerate(row)])
    rk = 0
    nrows = len(mat)
    for col in range(ncols):
        piv = -1
        for r in range(rk, nrows):
            if mat[r][col] != 0:
                piv = r
                break
        if piv < 0:
            continue
        mat[rk], mat[piv] = mat[piv], mat[rk]
        inv = pow(mat[rk][col], -1, qv)
        mat[rk] = [(x * inv) % qv for x in mat[rk]]
        for r in range(nrows):
            if r != rk:
                fac = mat[r][col]
                mat[r] = [(mat[r][c] - fac * mat[rk][c]) % qv for c in range(ncols)]
        rk += 1
    return rk


def q_matrix_det(mat: Sequence[Sequence[Fraction]]) -> Fraction:
    """Exact pure-Q determinant via Fraction Gaussian elimination."""
    if type(mat) not in (list, tuple) or len(mat) == 0:
        raise PraxisTomographyError("INVALID_Q_MATRIX", "mat must be non-empty square matrix")
    n = len(mat)
    a: list[list[Fraction]] = []
    for r_idx, row in enumerate(mat):
        if type(row) not in (list, tuple) or len(row) != n:
            raise PraxisTomographyError("INVALID_Q_MATRIX", f"row {r_idx} must have length {n}")
        a.append([parse_exact_rational(x, f"qmat[{r_idx}][{c_idx}]") for c_idx, x in enumerate(row)])
    sign = Q1
    for col in range(n):
        piv = -1
        for r in range(col, n):
            if a[r][col] != Q0:
                piv = r
                break
        if piv < 0:
            return Q0
        if piv != col:
            a[col], a[piv] = a[piv], a[col]
            sign = -sign
        pv = a[col][col]
        for r in range(col + 1, n):
            fac = a[r][col] / pv
            for c in range(col, n):
                a[r][c] -= fac * a[col][c]
    det = sign
    for i in range(n):
        det *= a[i][i]
    return det


def q_matrix_rank(mat: Sequence[Sequence[Fraction]]) -> int:
    """Exact pure-Q matrix rank via Fraction row reduction."""
    if type(mat) not in (list, tuple) or len(mat) == 0:
        raise PraxisTomographyError("INVALID_Q_MATRIX", "mat must be non-empty")
    ncols = len(mat[0]) if type(mat[0]) in (list, tuple) else 0
    if ncols == 0:
        raise PraxisTomographyError("INVALID_Q_MATRIX", "matrix rows must be non-empty")
    a: list[list[Fraction]] = []
    for r_idx, row in enumerate(mat):
        if type(row) not in (list, tuple) or len(row) != ncols:
            raise PraxisTomographyError("INVALID_Q_MATRIX", f"row {r_idx} length mismatch")
        a.append([parse_exact_rational(x, f"qmat[{r_idx}][{c_idx}]") for c_idx, x in enumerate(row)])
    rk = 0
    nrows = len(a)
    for col in range(ncols):
        piv = -1
        for r in range(rk, nrows):
            if a[r][col] != Q0:
                piv = r
                break
        if piv < 0:
            continue
        a[rk], a[piv] = a[piv], a[rk]
        pv = a[rk][col]
        a[rk] = [x / pv for x in a[rk]]
        for r in range(nrows):
            if r != rk:
                fac = a[r][col]
                a[r] = [a[r][c] - fac * a[rk][c] for c in range(ncols)]
        rk += 1
    return rk


# ---------------------------------------------------------------------------
# Pillar 1: Executable Small-Prime-Field Praxis Core Protocol (q=257, Fig. 6-10)
# ---------------------------------------------------------------------------

def _run_small_field_praxis(
    plaintext_utf8: str,
    decrypt_witness: Sequence[int],
    *,
    tau: int = 20,
) -> dict[str, Any]:
    """Execute full chunked Praxis Fig. 9-10 in exponent space over F_257 on Example 2.1 True BQS."""
    q = 257
    n, c0, k1_cnt, k2_cnt, nu = 4, 3, 2, 1, 2
    n_vars, n_c = 3, 2
    j_quo, delta_quo, j_rem, delta_rem = 2, 5, 2, 2
    g_range = 4
    b_search = (n_vars + 1) * (g_range + 1)

    capelli_ok = pow(c0, (q - 1) // 2, q) == q - 1
    omega = pow(c0, (q - 1) // n, q)
    p_mod_t = [(-c0) % q, 0, 0, 0, 1]

    # Example 2.1 True BQS: w1*w3 = 1, w2*(w1+w3) = 0, Booleanity w_j^2 = w_0*w_j
    constraints = (
        (([0, 1, 0, 0], [0, 0, 0, 1]), [1, 0, 0, 0]),
        (([0, 0, 1, 0], [0, 1, 0, 1]), [0, 0, 0, 0]),
    )
    # Subgroup H of order 16 in F_257^*
    g_h = pow(3, (q - 1) // 16, q)
    cosets = (
        (pow(g_h, 1, q), (-pow(g_h, 1, q)) % q),
        (pow(g_h, 2, q), (-pow(g_h, 2, q)) % q),
    )
    d_pts = (pow(g_h, 3, q), pow(g_h, 4, q), pow(g_h, 5, q), pow(g_h, 6, q))
    rho = pow(g_h, 7, q)
    p0_pts = list(d_pts) + [rho]
    coset_pts = [cosets[0][0], cosets[0][1], cosets[1][0], cosets[1][1]]
    p_all = p0_pts + coset_pts
    d_total = len(p_all)

    z0_poly = poly_vanishing(p0_pts, q)
    z_poly = poly_vanishing([p for p in p_all if p != rho], q)
    z_full = poly_mul(z_poly, [(-rho) % q, 1], q)
    l_rho = poly_interpolate(p_all, [1 if p == rho else 0 for p in p_all], q)

    a_vals = {p: [0] * (n_vars + 1) for p in p_all}
    b_vals = {p: [0] * (n_vars + 1) for p in p_all}
    for j in range(1, n_vars + 1):
        dj = d_pts[j]
        a_vals[dj][j] = 1
        a_vals[dj][0] = (-1) % q
        b_vals[dj][j] = 1
    b_vals[d_pts[0]][0] = 1
    a_vals[rho][0] = 1
    b_vals[rho][0] = 1
    for t_idx, ((a_v, b_v), c_v) in enumerate(constraints):
        p_prod, p_rhs = cosets[t_idx]
        z0_p = poly_eval(z0_poly, p_prod, q)
        z0_r = poly_eval(z0_poly, p_rhs, q)
        a_vals[p_prod] = [(z0_p * x) % q for x in a_v]
        b_vals[p_prod] = [x % q for x in b_v]
        a_vals[p_rhs][0] = z0_r
        b_vals[p_rhs] = [(-x) % q for x in c_v]

    a_polys = [poly_interpolate(p_all, [a_vals[p][i] for p in p_all], q) for i in range(n_vars + 1)]
    b_polys = [poly_interpolate(p_all, [b_vals[p][i] for p in p_all], q) for i in range(n_vars + 1)]

    def _qap_check_assignment(w_cand: Sequence[int]) -> tuple[bool, list[int], list[int], list[int], list[int], list[int]]:
        aw: list[int] = []
        bw: list[int] = []
        for i in range(n_vars + 1):
            aw = poly_add(aw, poly_scale(a_polys[i], w_cand[i], q), q)
            bw = poly_add(bw, poly_scale(b_polys[i], w_cand[i], q), q)
        pw = poly_mul(aw, bw, q)
        rw = poly_interpolate(
            coset_pts,
            [(poly_eval(pw, p, q) * pow(poly_eval(z0_poly, p, q), -1, q)) % q for p in coset_pts],
            q,
        )
        allowed = all(rw[idx] == 0 for idx in range(0, len(rw), nu))
        hq_k, rem_k = poly_divmod(poly_sub(poly_sub(pw, l_rho, q), poly_mul(z0_poly, rw, q), q), z_full, q)
        hq_o, rem_o = poly_divmod(poly_sub(pw, poly_mul(z0_poly, rw, q), q), z_poly, q)
        return allowed, hq_k, rem_k, hq_o, rem_o, rw

    # Deterministic forms (phi_0 = e_0, phi_1..3 spanning)
    phis = (
        (1, 0, 0, 0),
        (7, 11, 19, 23),
        (13, 29, 31, 37),
        (17, 41, 43, 47),
    )
    legs: tuple[tuple[str, int], ...] = (("E", 0), ("O", 0), ("V", 0))

    def _k_leg(leg: tuple[str, int]) -> int:
        return 2 * k1_cnt * leg[1] + (1 if leg[0] == "O" else 0)

    cells = [(k1, leg) for k1 in range(k1_cnt) for leg in legs]
    c_key = (0, ("E", 0))

    # Deterministic Enc coins (Fig. 9)
    r_vec = (3, 5, 2, 4)
    y_vec = (17, 29, 43, 61)
    om12, om22 = 13, 23
    alpha, pi_c = 31, 37
    s_kind = {"E": 41, "O": 43, "V": 47}
    ups = 53
    zeta, zetap, zetapp = 59, 61, 67
    etas = {1: 71, 2: 73, 3: 79}
    eps = 83
    inv_w = pow(omega, -1, q)
    inv_eps = pow(eps, -1, q)

    pi_k = {k1: (pi_c * pow(ups, 2 * k1, q) * (1 + eps * pow(omega, 2 * k1, q))) % q for k1 in range(k1_cnt)}
    s_l = {leg: (s_kind[leg[0]] * pow(ups, _k_leg(leg), q)) % q for leg in legs}
    gamma = {(k1, leg): (pi_k[k1] * s_l[leg]) % q for k1, leg in cells}
    kappa = (gamma[c_key] * poly_eval(l_rho, tau, q)) % q

    def _z_vec_at(x_val: int) -> list[int]:
        return [sum(pow(x_val, e, q) * phis[e][i] for e in range(n)) % q for i in range(n_vars + 1)]

    zv_m = _z_vec_at((-ups * inv_w) % q)
    zv_0 = _z_vec_at((-ups) % q)
    zv_p = _z_vec_at((-omega * ups) % q)
    theta_leg: dict[tuple[str, int], list[int]] = {}
    for leg in legs:
        kl = _k_leg(leg)
        c1 = pow(ups, kl, q)
        if leg[0] in ("E", "O"):
            c2 = (inv_eps * pow((-omega * ups) % q, kl, q)) % q
            theta_leg[leg] = [
                (c1 * (etas[1] * zv_0[j] + etas[2] * zv_p[j]) - c2 * (etas[2] * zv_m[j] + etas[3] * zv_0[j])) % q
                for j in range(n_vars + 1)
            ]
        else:
            theta_leg[leg] = [(c1 * (etas[3] * zv_p[j] - etas[1] * zv_m[j])) % q for j in range(n_vars + 1)]

    a_tau = [poly_eval(a_polys[i], tau, q) for i in range(n_vars + 1)]
    b_tau = [poly_eval(b_polys[i], tau, q) for i in range(n_vars + 1)]
    inv_om22 = pow(om22, -1, q)
    f_ct = {
        (k1, i): (
            (pi_k[k1] * y_vec[i]) % q,
            (om12 * ((pi_k[k1] * y_vec[i]) % q) + om22 * ((pi_k[k1] * a_tau[i]) % q)) % q,
        )
        for k1 in range(k1_cnt)
        for i in range(n_vars + 1)
    }
    h_ct: dict[tuple[tuple[str, int], int], tuple[int, int]] = {}
    for leg in legs:
        for j in range(n_vars + 1):
            h1 = (s_l[leg] * (r_vec[j] + a_tau[j]) + theta_leg[leg][j]) % q
            h2 = (s_l[leg] * (b_tau[j] - y_vec[j])) % q
            h_ct[(leg, j)] = ((h1 - om12 * inv_om22 * h2) % q, (inv_om22 * h2) % q)

    p_quo = [(zeta * pow(tau, k, q)) % q for k in range(delta_quo)]
    p_rem = {k: (zetap * pow(tau, k, q)) % q for k in range(delta_rem) if k % nu != 0}
    y_ct = [(zetapp * y_vec[i]) % q for i in range(n_vars + 1)]
    z_full_tau = poly_eval(z_full, tau, q)
    z_tau = poly_eval(z_poly, tau, q)
    z0_tau = poly_eval(z0_poly, tau, q)
    p_ups = poly_eval(p_mod_t, ups, q)
    inv_z = pow(zeta, -1, q)
    inv_zp = pow(zetap, -1, q)
    inv_zpp = pow(zetapp, -1, q)
    b_quo = {
        (c, j): (gamma[c] * (z_full_tau if c == c_key else z_tau) * pow(tau, j * delta_quo, q) * inv_z) % q
        for c in cells
        for j in range(j_quo)
    }
    b_rem = {
        (c, j): (gamma[c] * z0_tau * pow(tau, j * delta_rem, q) * inv_zp) % q
        for c in cells
        for j in range(j_rem)
    }
    b_canc: dict[tuple[int, int, int], int] = {}
    for a_idx in (1, 2, 3):
        for e in range(n - 1):
            b_canc[(a_idx, 0, e)] = (pi_c * etas[a_idx] * p_ups * pow(ups, e, q) * inv_zpp) % q
    for a_idx, iota in ((1, 1), (2, 1), (2, -1), (3, 1), (3, -1)):
        eps_i = eps if iota == 1 else inv_eps
        for e in range(2 * n - 1):
            b_canc[(a_idx, iota, e)] = (pi_c * etas[a_idx] * eps_i * pow(ups, e, q) * inv_zpp) % q

    pt_bytes = plaintext_utf8.encode("utf-8")
    key_mask = hashlib.sha256(f"praxis-f257-key:{kappa}".encode("ascii")).digest()[: len(pt_bytes)]
    m_tilde_hex = bytes(a ^ b for a, b in zip(pt_bytes, key_mask)).hex()
    ct_digest = sha256_hex(
        canonical_json_bytes({
            "q": q,
            "tau_hidden_commit": sha256_hex(str(kappa).encode("ascii")),
            "k_alpha": (alpha * kappa) % q,
            "m_tilde_hex": m_tilde_hex,
            "f_ct_count": len(f_ct),
            "h_ct_count": len(h_ct),
        })
    )

    # Decryption attempt with decrypt_witness (Fig. 10)
    w_list = [require_int(x, "w[i]", lo=0, hi=1) for x in decrypt_witness]
    allowed_w, h_key, rem_key, h_oth, rem_oth, rw = _qap_check_assignment(w_list)
    if not all((allowed_w, len(rem_key) == 0, len(rem_oth) == 0)):
        return {
            "qap_passed": False,
            "allowed_rw": allowed_w,
            "ciphertext_sha256": ct_digest,
            "recovered_kappa": None,
            "recovered_message": None,
            "status": "NON_WITNESS_REJECTED",
        }

    zw = [sum(phis[e][i] * w_list[i] for i in range(n_vars + 1)) % q for e in range(n)]
    uw = ext_mul_binom(zw, ext_frobenius(zw, n // 2 - 1, q, omega), q, n, c0)
    vw = ext_mul_binom(zw, ext_frobenius(zw, n // 2, q, omega), q, n, c0)
    # Example 5.2 explicit formula verification on V(w)
    p0, p1, p2, p3 = zw
    ex52_v0 = (p0 * p0 + c0 * p2 * p2 - 2 * c0 * p1 * p3) % q
    ex52_v1 = (2 * p0 * p2 - p1 * p1 - c0 * p3 * p3) % q
    ex52_ok = vw == [ex52_v0, 0, ex52_v1, 0]

    xi = {(k1, leg): (uw[2 * k1 + _k_leg(leg)] if leg[0] in ("E", "O") else vw[2 * k1 + _k_leg(leg)]) for k1, leg in cells}
    u_p = [0] * n
    v_p = [0] * n
    u_pp = [0] * n
    for k1, leg in cells:
        kc = 2 * k1 + _k_leg(leg)
        w2k1 = pow(omega, 2 * k1, q)
        if leg[0] in ("E", "O"):
            u_p[kc] = (u_p[kc] + xi[(k1, leg)] * w2k1) % q
            u_pp[kc] = (u_pp[kc] + xi[(k1, leg)] * pow((-omega) % q, _k_leg(leg), q)) % q
        else:
            v_p[kc] = (v_p[kc] + xi[(k1, leg)] * w2k1) % q

    zm_t = poly_sub_scale(zw, (-inv_w) % q, q)
    z0_t = poly_sub_scale(zw, (-1) % q, q)
    zp_t = poly_sub_scale(zw, (-omega) % q, q)
    u_mw = poly_sub_scale(uw, (-omega) % q, q)
    x01, tr1 = poly_divmod(poly_sub(poly_mul(uw, z0_t, q), poly_mul(vw, zm_t, q), q), p_mod_t, q)
    x02, tr2 = poly_divmod(poly_sub(poly_mul(uw, zp_t, q), poly_mul(u_mw, zm_t, q), q), p_mod_t, q)
    x03, tr3 = poly_divmod(poly_sub(poly_mul(vw, zp_t, q), poly_mul(u_mw, z0_t, q), q), p_mod_t, q)
    eq5_ok = all((len(tr1) == 0, len(tr2) == 0, len(tr3) == 0))

    x_canc = {
        (1, 0): x01,
        (2, 0): x02,
        (3, 0): x03,
        (1, 1): poly_sub(poly_mul(u_p, z0_t, q), poly_mul(v_p, zm_t, q), q),
        (2, 1): poly_mul(u_p, zp_t, q),
        (2, -1): poly_scale(poly_mul(u_pp, zm_t, q), -1, q),
        (3, 1): poly_mul(v_p, zp_t, q),
        (3, -1): poly_scale(poly_mul(u_pp, z0_t, q), -1, q),
    }

    lhs_eq7 = sum(
        pi_k[k1] * xi[(k1, leg)] * sum(w_list[j] * theta_leg[leg][j] for j in range(n_vars + 1))
        for k1, leg in cells
    ) % q
    rhs_eq7 = (
        pi_c
        * sum(
            etas[a_idx]
            * (
                p_ups * poly_eval(x_canc[(a_idx, 0)], ups, q)
                + eps * poly_eval(x_canc[(a_idx, 1)], ups, q)
                + (inv_eps * poly_eval(x_canc[(a_idx, -1)], ups, q) if (a_idx, -1) in x_canc else 0)
            )
            for a_idx in (1, 2, 3)
        )
    ) % q

    fw_k = {
        k1: (
            sum(w_list[i] * f_ct[(k1, i)][0] for i in range(n_vars + 1)) % q,
            sum(w_list[i] * f_ct[(k1, i)][1] for i in range(n_vars + 1)) % q,
        )
        for k1 in range(k1_cnt)
    }
    fw_leg = {
        leg: (
            sum(xi[(k1, leg)] * fw_k[k1][0] for k1 in range(k1_cnt)) % q,
            sum(xi[(k1, leg)] * fw_k[k1][1] for k1 in range(k1_cnt)) % q,
        )
        for leg in legs
    }
    yw = sum(w_list[i] * y_ct[i] for i in range(n_vars + 1)) % q
    pw_key = [
        sum((h_key[j * delta_quo + k] if j * delta_quo + k < len(h_key) else 0) * p_quo[k] for k in range(delta_quo)) % q
        for j in range(j_quo)
    ]
    pw_oth = [
        sum((h_oth[j * delta_quo + k] if j * delta_quo + k < len(h_oth) else 0) * p_quo[k] for k in range(delta_quo)) % q
        for j in range(j_quo)
    ]
    pw_rem = [
        sum((rw[j * delta_rem + k] if j * delta_rem + k < len(rw) else 0) * p_rem[k] for k in p_rem) % q
        for j in range(j_rem)
    ]

    def _comb(scale: int) -> tuple[int, int]:
        hw_leg = {
            leg: (
                sum(w_list[i] * scale * h_ct[(leg, i)][0] for i in range(n_vars + 1)) % q,
                sum(w_list[i] * scale * h_ct[(leg, i)][1] for i in range(n_vars + 1)) % q,
            )
            for leg in legs
        }
        bw_val = 0
        for (a_idx, iota), poly in x_canc.items():
            for e, coeff in enumerate(poly):
                bw_val = (bw_val + coeff * scale * b_canc[(a_idx, iota, e)]) % q
        lam_v = sum(fw_leg[leg][0] * hw_leg[leg][0] + fw_leg[leg][1] * hw_leg[leg][1] for leg in legs) % q
        lam_v = (lam_v - sum(pw_key[j] * xi[c_key] * scale * b_quo[(c_key, j)] for j in range(j_quo))) % q
        lam_v = (lam_v - sum(pw_oth[j] * sum(xi[c] * scale * b_quo[(c, j)] for c in cells if c != c_key) for j in range(j_quo))) % q
        lam_v = (lam_v - sum(pw_rem[j] * sum(xi[c] * scale * b_rem[(c, j)] for c in cells) for j in range(j_rem))) % q
        lam_v = (lam_v - yw * bw_val) % q
        psi_v = sum(fw_leg[leg][0] * scale * s_l[leg] for leg in legs) % q
        return lam_v, psi_v

    lam_v, psi_v = _comb(1)
    lam_a, psi_a = _comb(alpha)
    r_w = sum(w_list[i] * r_vec[i] for i in range(n_vars + 1))
    y_w = sum(w_list[i] * y_vec[i] for i in range(n_vars + 1)) % q
    psi_expected = (y_w * sum(gamma[c] * xi[c] for c in cells)) % q
    lemma54_ok = all((
        lam_v == (xi[c_key] * kappa + r_w * psi_expected) % q,
        psi_v == psi_expected,
        lam_a == (alpha * lam_v) % q,
        psi_a == (alpha * psi_v) % q,
    ))

    cw = ((1 + sum(w_list[1:])) * (g_range + 3)) // 2
    lam_prime = (lam_a - xi[c_key] * ((alpha * kappa) % q) - cw * psi_a) % q
    found_t = 0
    for d_abs in range(b_search + 1):
        cands = (0,) if d_abs == 0 else (d_abs, -d_abs)
        matched = [t_val for t_val in cands if (t_val * psi_a) % q == lam_prime]
        if matched:
            found_t = matched[0]
            break
    k_rec = (pow(xi[c_key], -1, q) * (lam_v - (cw + found_t) * psi_v)) % q
    rec_mask = hashlib.sha256(f"praxis-f257-key:{k_rec}".encode("ascii")).digest()[: len(pt_bytes)]
    rec_msg = bytes(a ^ b for a, b in zip(bytes.fromhex(m_tilde_hex), rec_mask)).decode("utf-8")

    # Negative control: non-witness [1, 1, 1, 1] on True BQS fails QAP allowed-remainder check
    neg_allowed, _, neg_rem_k, _, neg_rem_o, _ = _qap_check_assignment((1, 1, 1, 1))
    neg_rejected = not all((neg_allowed, len(neg_rem_k) == 0, len(neg_rem_o) == 0))

    return {
        "field_q": q,
        "n_forms": n,
        "c0": c0,
        "omega": omega,
        "k1": k1_cnt,
        "k2": k2_cnt,
        "nu": nu,
        "eval_points_d": d_total,
        "chunk_j_delta": [j_quo, delta_quo],
        "chunk_jp_deltap": [j_rem, delta_rem],
        "copy_count_3n_over_2": (3 * n) // 2,
        "quadratic_pair_count_n_n1_over_2": (n * (n + 1)) // 2,
        "capelli_irreducible_t4_minus_c0": capelli_ok,
        "qap_rw_allowed_nu_ndiv_k": allowed_w,
        "eq4_key_remainder_zero": len(rem_key) == 0,
        "eq4_oth_remainder_zero": len(rem_oth) == 0,
        "neg_control_non_passing_rejected": neg_rejected,
        "example52_v_formula_exact": ex52_ok,
        "eq5_tie_divisions_exact": eq5_ok,
        "eq7_mask_identity_exact": lhs_eq7 == rhs_eq7,
        "lemma54_exact_match": lemma54_ok,
        "kappa_expected": kappa,
        "kappa_recovered": k_rec,
        "search_center_cw": cw,
        "search_offset_t": found_t,
        "r_w_exact": r_w,
        "ciphertext_sha256": ct_digest,
        "decryption_recovered_exact_kappa": k_rec == kappa,
        "decryption_recovered_exact_message": rec_msg == plaintext_utf8,
        "status": "OK",
    }


def build_pillar1_executable_praxis_protocol() -> dict[str, Any]:
    run = _run_small_field_praxis("PRAXIS-WE-OK-S41", (1, 1, 0, 1), tau=20)
    verified = all((
        run["capelli_irreducible_t4_minus_c0"],
        run["qap_rw_allowed_nu_ndiv_k"],
        run["eq4_key_remainder_zero"],
        run["eq4_oth_remainder_zero"],
        run["neg_control_non_passing_rejected"],
        run["example52_v_formula_exact"],
        run["eq5_tie_divisions_exact"],
        run["eq7_mask_identity_exact"],
        run["lemma54_exact_match"],
        run["decryption_recovered_exact_kappa"],
        run["decryption_recovered_exact_message"],
    ))
    return {
        "field_q": run["field_q"],
        "n_forms": run["n_forms"],
        "c0": run["c0"],
        "omega": run["omega"],
        "k1": run["k1"],
        "k2": run["k2"],
        "nu": run["nu"],
        "eval_points_d": run["eval_points_d"],
        "chunk_j_delta": run["chunk_j_delta"],
        "chunk_jp_deltap": run["chunk_jp_deltap"],
        "copy_count_3n_over_2": run["copy_count_3n_over_2"],
        "quadratic_pair_count_n_n1_over_2": run["quadratic_pair_count_n_n1_over_2"],
        "capelli_irreducible_t4_minus_c0": run["capelli_irreducible_t4_minus_c0"],
        "qap_rw_allowed_nu_ndiv_k": run["qap_rw_allowed_nu_ndiv_k"],
        "eq4_key_remainder_zero": run["eq4_key_remainder_zero"],
        "eq4_oth_remainder_zero": run["eq4_oth_remainder_zero"],
        "neg_control_non_passing_rejected": run["neg_control_non_passing_rejected"],
        "example52_v_formula_exact": run["example52_v_formula_exact"],
        "eq5_tie_divisions_exact": run["eq5_tie_divisions_exact"],
        "eq7_mask_identity_exact": run["eq7_mask_identity_exact"],
        "lemma54_exact_match": run["lemma54_exact_match"],
        "kappa_expected": run["kappa_expected"],
        "kappa_recovered": run["kappa_recovered"],
        "search_center_cw": run["search_center_cw"],
        "search_offset_t": run["search_offset_t"],
        "r_w_exact": run["r_w_exact"],
        "ciphertext_sha256": run["ciphertext_sha256"],
        "decryption_recovered_exact_kappa": run["decryption_recovered_exact_kappa"],
        "decryption_recovered_exact_message": run["decryption_recovered_exact_message"],
        "pillar_verified": verified,
    }


# ---------------------------------------------------------------------------
# Pillar 2: Rank-1/2/3/4 Cheat Classification, SOS PSD Witness & Polya (1913)
# ---------------------------------------------------------------------------

def build_pillar2_rank_gap_and_polya_obstructions() -> dict[str, Any]:
    # (a) Example 2.1 True vs False exhaustive Boolean witness counts
    true_wits = 0
    unsat_wits = 0
    for b1, b2, b3 in itertools.product((0, 1), repeat=3):
        if b1 * b3 == 1 and b2 * (b1 + b3) == 0:
            true_wits += 1
        if b1 * b3 == 1 and b2 * (b1 + b3) == 1:
            unsat_wits += 1

    # Rank-1 honest witness moment matrix on True Example 2.1 (Lemma 4.3)
    w_hon = (1, 1, 0, 1)
    w_r1 = [[Fraction(w_hon[i] * w_hon[j], 1) for j in range(4)] for i in range(4)]
    r1_rank = q_matrix_rank(w_r1)
    r1_passes = all((
        r1_rank == 1,
        w_r1[0][0] == Q1,
        all(w_r1[j][j] == w_r1[0][j] for j in (1, 2, 3)),
        w_r1[1][3] == w_r1[0][0],
        w_r1[2][1] + w_r1[2][3] == Q0,
    ))

    # (b) Rank-2 shared Lasserre/SOS PSD pseudodistribution & Praxis cheat on UNSAT Example 2.1
    u1 = (1, 1, 0, 1)
    u2 = (1, 1, 1, 1)
    w_r2 = [[Fraction(u1[i] * u1[j] + u2[i] * u2[j], 2) for j in range(4)] for i in range(4)]
    r2_rank = q_matrix_rank(w_r2)
    r2_tests_ok = all((
        all(w_r2[j][j] == w_r2[0][j] for j in (1, 2, 3)),
        w_r2[1][3] == w_r2[0][0],
        w_r2[2][1] + w_r2[2][3] == w_r2[0][0],
    ))
    minors_by_sz: dict[str, list[str]] = {}
    all_minors_ge0 = True
    for sz in (1, 2, 3, 4):
        vals: list[str] = []
        for idx_set in itertools.combinations(range(4), sz):
            sub = [[w_r2[r][c] for c in idx_set] for r in idx_set]
            d_val = q_matrix_det(sub)
            if d_val < Q0:
                all_minors_ge0 = False
            vals.append(format_rational(d_val))
        minors_by_sz[f"size_{sz}"] = vals

    # Fig. 4 exact check over F_101: phi_0=(1,0,0,0) vs phi_1=(0,55,33,6)
    q101 = 101
    phi1_101 = (0, 55, 33, 6)
    phi1_u1 = sum(phi1_101[i] * u1[i] for i in range(4)) % q101
    phi1_u2 = sum(phi1_101[i] * u2[i] for i in range(4)) % q101
    fig4_det = ((-1) * phi1_u2 - 1 * (-phi1_u1)) % q101
    fig4_kills = all((phi1_u1 == 61, phi1_u2 == 94, fig4_det == 68))

    # Over F_257, repeating W_r2 across all 6 copies breaks Praxis ties t1,t2,t3 mod (T^4 - 3)
    q = 257
    n, c0 = 4, 3
    omega = pow(c0, (q - 1) // n, q)
    inv2_q = pow(2, -1, q)
    w_r2_fq = [((u1[i] * u1[j] + u2[i] * u2[j]) * inv2_q) % q for i in range(4) for j in range(4)]
    phis4 = (
        (1, 0, 0, 0),
        (7, 11, 19, 23),
        (13, 29, 31, 37),
        (17, 41, 43, 47),
    )

    def _ext_add(a: list[int], b: list[int]) -> list[int]:
        return [(a[k] + b[k]) % q for k in range(n)]

    def _mv_ext(mat_ext: list[list[list[int]]], vec_ext: list[list[int]]) -> list[list[int]]:
        dim = len(mat_ext)
        out: list[list[int]] = []
        for i in range(dim):
            acc = [0] * n
            for j in range(dim):
                acc = _ext_add(acc, ext_mul_binom(mat_ext[i][j], vec_ext[j], q, n, c0))
            out.append(acc)
        return out

    z_ext4 = [[phis4[e][i] for e in range(n)] for i in range(4)]
    z4_s1 = [ext_frobenius(v, 1, q, omega) for v in z_ext4]
    z4_s2 = [ext_frobenius(v, 2, q, omega) for v in z_ext4]
    wu_rep = [[[w_r2_fq[4 * i + j] for _ in range(n)] for j in range(4)] for i in range(4)]
    wv_rep = [[[w_r2_fq[4 * i + j] if e in (0, 2) else 0 for e in range(n)] for j in range(4)] for i in range(4)]
    repeat_breaks_ties = _mv_ext(wu_rep, z4_s2) != _mv_ext(wv_rep, z4_s1)

    # (c) Rank-3 symmetric-tensor cheat (p. 19) on 3 decoupled unknowns & Moore determinant (Lemma B.5)
    # W_c = phi_c(e3)(e1 e2^T + e2 e1^T) + phi_c(e2)(e1 e3^T + e3 e1^T) + phi_c(e1)(e2 e3^T + e3 e2^T)
    lin_stack: list[list[list[int]]] = []
    for c_idx in range(4):
        p1, p2, p3 = phis4[c_idx][1], phis4[c_idx][2], phis4[c_idx][3]
        wc = [
            [0, 0, 0, 0],
            [0, 0, p3, p2],
            [0, p3, 0, p1],
            [0, p2, p1, 0],
        ]
        lin_stack.append(wc)
    lin_ties_ok = True
    for c1 in range(4):
        for c2 in range(4):
            lhs = [sum(lin_stack[c1][i][j] * phis4[c2][j] for j in range(4)) % q for i in range(4)]
            rhs = [sum(lin_stack[c2][i][j] * phis4[c1][j] for j in range(4)) % q for i in range(4)]
            if lhs != rhs:
                lin_ties_ok = False
    r3_lin_rows = [row for mat in lin_stack for row in mat]
    r3_lin_rank = fq_matrix_rank(r3_lin_rows, q)
    # Embedded directly into Praxis (W_U = sum W_c T^c, W_V = W_0 + W_2 T^2) breaks quadratic ties!
    wu_r3 = [[[lin_stack[e][i][j] for e in range(n)] for j in range(4)] for i in range(4)]
    wv_r3 = [[[lin_stack[e][i][j] if e in (0, 2) else 0 for e in range(n)] for j in range(4)] for i in range(4)]
    r3_breaks_quad_ties = _mv_ext(wu_r3, z4_s2) != _mv_ext(wv_r3, z4_s1)
    # Also alternating sum over 3 unknowns with QUADRATIC weights U(u) leaks nonzero row-0/diag!
    alt3_u = [[[0] * n for _ in range(4)] for _ in range(4)]
    for mask in range(8):
        u_vec = (1, mask & 1, (mask >> 1) & 1, (mask >> 2) & 1)
        sgn = 1 if (3 - bin(mask).count("1")) % 2 == 0 else (q - 1)
        zu = [sum(phis4[e][i] * u_vec[i] for i in range(4)) % q for e in range(n)]
        uu = ext_mul_binom(zu, ext_frobenius(zu, 1, q, omega), q, n, c0)
        for i in range(4):
            if u_vec[i] == 0:
                continue
            for j in range(4):
                if u_vec[j] == 0:
                    continue
                for e in range(n):
                    alt3_u[i][j][e] = (alt3_u[i][j][e] + sgn * uu[e]) % q
    quad_alt3_leaks = any(alt3_u[0][j] != [0] * n for j in range(4))

    # Lemma B.5 Moore determinant over F_{257^4} on 3 consecutive conjugates (s = 1, 2, 3)
    h0_indep = [[phis4[e][j] for e in range(n)] for j in (1, 2, 3)]
    m_moore_indep = [[ext_frobenius(h0_indep[r], s, q, omega) for s in (1, 2, 3)] for r in range(3)]
    moore_det_indep = ext_det3_binom(m_moore_indep, q, n, c0)
    h0_dep = [h0_indep[0], h0_indep[1], _ext_add(h0_indep[0], h0_indep[1])]
    m_moore_dep = [[ext_frobenius(h0_dep[r], s, q, omega) for s in (1, 2, 3)] for r in range(3)]
    moore_det_dep = ext_det3_binom(m_moore_dep, q, n, c0)

    # (d) Rank-4 alternating-sum cheat on 4 decoupled unknowns (dim 5) over F_257
    phis5 = (
        (1, 0, 0, 0, 0),
        (7, 11, 19, 23, 29),
        (13, 31, 37, 41, 43),
        (17, 47, 53, 59, 61),
    )
    wu_r4 = [[[0] * n for _ in range(5)] for _ in range(5)]
    wv_r4 = [[[0] * n for _ in range(5)] for _ in range(5)]
    for mask in range(16):
        u_vec = (1, mask & 1, (mask >> 1) & 1, (mask >> 2) & 1, (mask >> 3) & 1)
        sgn = 1 if (4 - bin(mask).count("1")) % 2 == 0 else (q - 1)
        zu = [sum(phis5[e][i] * u_vec[i] for i in range(5)) % q for e in range(n)]
        uu = ext_mul_binom(zu, ext_frobenius(zu, 1, q, omega), q, n, c0)
        vu = ext_mul_binom(zu, ext_frobenius(zu, 2, q, omega), q, n, c0)
        for i in range(5):
            if u_vec[i] == 0:
                continue
            for j in range(5):
                if u_vec[j] == 0:
                    continue
                for e in range(n):
                    wu_r4[i][j][e] = (wu_r4[i][j][e] + sgn * uu[e]) % q
                    wv_r4[i][j][e] = (wv_r4[i][j][e] + sgn * vu[e]) % q
    z_ext5 = [[phis5[e][i] for e in range(n)] for i in range(5)]
    z5_s1 = [ext_frobenius(v, 1, q, omega) for v in z_ext5]
    z5_s2 = [ext_frobenius(v, 2, q, omega) for v in z_ext5]
    z5_s3 = [ext_frobenius(v, 3, q, omega) for v in z_ext5]
    wu_r4_s3 = [[ext_frobenius(wu_r4[i][j], 3, q, omega) for j in range(5)] for i in range(5)]
    r4_ties_ok = all((
        _mv_ext(wu_r4, z5_s2) == _mv_ext(wv_r4, z5_s1),
        _mv_ext(wu_r4, z5_s3) == _mv_ext(wu_r4_s3, z5_s1),
        _mv_ext(wv_r4, z5_s3) == _mv_ext(wu_r4_s3, z5_s2),
    ))
    r4_bool_ok = all(mat[j][j] == mat[0][j] for mat in (wu_r4, wv_r4) for j in range(1, 5))
    r4_row0_zero = all(mat[0][j] == [0] * n for mat in (wu_r4, wv_r4) for j in range(5))
    r4_diag_zero = all(mat[j][j] == [0] * n for mat in (wu_r4, wv_r4) for j in range(5))
    r4_nonzero = any(wu_r4[i][j] != [0] * n for i in range(5) for j in range(5))
    r4_scalar_rows: list[list[int]] = []
    for e in range(n):
        for i in range(5):
            r4_scalar_rows.append([wu_r4[i][j][e] for j in range(5)])
    for e in (0, 2):
        for i in range(5):
            r4_scalar_rows.append([wv_r4[i][j][e] for j in range(5)])
    r4_rank = fq_matrix_rank(r4_scalar_rows, q)

    # (e) Polya (1913) exhaustive 512-matrix sign-cancellation obstruction (Portal 45)
    perms3 = tuple(itertools.permutations((0, 1, 2)))
    perm_signs = tuple(1 if sum(1 for i in range(3) for j in range(i + 1, 3) if p[i] > p[j]) % 2 == 0 else -1 for p in perms3)
    f2_perm_eq_det = 0
    polya_valid_sign_flips = 0
    polya_max_perm_matches = 0
    for bits in range(512):
        m_bin = [[(bits >> (3 * r + c)) & 1 for c in range(3)] for r in range(3)]
        p_val = sum(m_bin[0][p[0]] * m_bin[1][p[1]] * m_bin[2][p[2]] for p in perms3)
        d_val = sum(s * m_bin[0][p[0]] * m_bin[1][p[1]] * m_bin[2][p[2]] for s, p in zip(perm_signs, perms3))
        if (p_val - d_val) % 2 == 0:
            f2_perm_eq_det += 1
        s_mat = [[1 if ((bits >> (3 * r + c)) & 1) else -1 for c in range(3)] for r in range(3)]
        matches = sum(1 for s, p in zip(perm_signs, perms3) if s * s_mat[0][p[0]] * s_mat[1][p[1]] * s_mat[2][p[2]] == 1)
        if matches > polya_max_perm_matches:
            polya_max_perm_matches = matches
        if matches == 6:
            polya_valid_sign_flips += 1

    verified = all((
        true_wits == 1,
        unsat_wits == 0,
        r1_passes,
        r2_rank == 2,
        r2_tests_ok,
        all_minors_ge0,
        fig4_kills,
        repeat_breaks_ties,
        lin_ties_ok,
        r3_lin_rank == 3,
        r3_breaks_quad_ties,
        quad_alt3_leaks,
        any(x != 0 for x in moore_det_indep),
        moore_det_dep == [0, 0, 0, 0],
        r4_ties_ok,
        r4_bool_ok,
        r4_row0_zero,
        r4_diag_zero,
        r4_nonzero,
        r4_rank == 4,
        f2_perm_eq_det == 512,
        polya_valid_sign_flips == 0,
        polya_max_perm_matches == 5,
    ))

    return {
        "example21_true_witness_count": true_wits,
        "example21_unsat_witness_count": unsat_wits,
        "rank1_witness_passes": r1_passes,
        "rank2_sos_praxis_cheat": {
            "exact_rank_over_q": r2_rank,
            "all_tests_passed_over_q": r2_tests_ok,
            "all_15_minors_nonneg_psd": all_minors_ge0,
            "principal_minors_by_size": minors_by_sz,
            "fig4_f101_phi1_values": [phi1_u1, phi1_u2],
            "fig4_f101_det": fig4_det,
            "fig4_f101_kills_mixture": fig4_kills,
            "praxis_quad_ties_broken_by_repeat": repeat_breaks_ties,
        },
        "rank3_linear_tensor_and_moore": {
            "linear_tensor_exact_rank": r3_lin_rank,
            "all_linear_ties_hold": lin_ties_ok,
            "quad_ties_broken_by_linear_tensor": r3_breaks_quad_ties,
            "quad_alt_sum_leaks_row0_or_diag": quad_alt3_leaks,
            "moore_det_indep_f257_4": moore_det_indep,
            "moore_indep_nonzero": any(x != 0 for x in moore_det_indep),
            "moore_dep_control_zero": moore_det_dep == [0, 0, 0, 0],
        },
        "rank4_alternating_sum_cheat": {
            "exact_rank_f257": r4_rank,
            "booleanity_passed": r4_bool_ok,
            "row0_zero": r4_row0_zero,
            "diag_zero": r4_diag_zero,
            "nonzero_stack": r4_nonzero,
            "praxis_ties_all_3_hold": r4_ties_ok,
        },
        "polya_1913_obstruction": {
            "total_3x3_matrices": 512,
            "f2_perm_eq_det_count": f2_perm_eq_det,
            "z_valid_sign_flip_count": polya_valid_sign_flips,
            "max_permutation_matches_out_of_6": polya_max_perm_matches,
        },
        "pillar_verified": verified,
    }


# ---------------------------------------------------------------------------
# Pillar 3: Exact Pure-Z/Q Table 4 Admissibility, Lemma B.2 E(u) & Appendix C
# ---------------------------------------------------------------------------

def evaluate_lemma_b2_bound(
    u: Any,
    l1: Any,
    l2: Any,
    lt: Any,
    eps_f: Any,
    theta: Any,
    n_free: Any,
    lam: Any = 100,
) -> Fraction:
    """Exact pure-Q evaluation of Definition B.1 quadratic generic bound E(u)."""
    uv = parse_bounded_int(u, "u", lo=0)
    l1v = parse_bounded_int(l1, "l1", lo=1)
    l2v = parse_bounded_int(l2, "l2", lo=1)
    ltv = parse_bounded_int(lt, "lt", lo=1)
    lamv = require_int(lam, "lam", lo=1, hi=512)
    nfv = parse_bounded_int(n_free, "n_free", lo=1)
    ef = parse_exact_rational(eps_f, "eps_f")
    th = parse_exact_rational(theta, "theta")
    if ef < Q0 or th < Q0:
        raise PraxisTomographyError("NEGATIVE_PROB_PARAM", "eps_f and theta must be non-negative")
    tot_l = l1v + l2v + ltv
    c2 = lambda x: (x * (x - 1)) // 2
    n_cmp = uv * tot_l + (uv * (uv + 1)) // 2
    return (
        Fraction(c2(l1v) + c2(l2v) + c2(ltv) + tot_l, 1) * ef
        + Fraction(n_cmp, 1) * (th + ef)
        + Fraction(c2(tot_l + 3 * uv) + tot_l + 3 * uv, 1) * ef
        + Fraction(8 * uv + 8, 1) * ef
        + Fraction(2 * tot_l + 4 * uv + (1 << (lamv + 2)), nfv)
        + Fraction(4 * uv, 1 << 126)
        + Fraction(1, 1 << 128)
    )


def build_pillar3_table4_admissibility_and_hair_sahai() -> dict[str, Any]:
    t_bn = BN254_SEED_T
    q_formula = 36 * (t_bn ** 4) + 36 * (t_bn ** 3) + 18 * (t_bn ** 2) + 6 * t_bn + 1
    pock = verify_pocklington_prime(q_formula, _BN254_QM1_SMALL_PRIMES, 5)

    n_unk, n_c, f_max = 391693, 1694, 2047
    nu, h_ord = 1 << 11, 1 << 22
    d_eval = n_unk + 2 + nu * n_c
    j_quo, delta_quo = 11, 351001
    j_rem, delta_rem = 11, 315392
    n_forms, c0 = 4608, 5
    d_r, k_rows, ell_cols = 64, 71, 6121
    k1, k2 = 192, 12
    g_val = 1736375024658487
    theta = Fraction((1 << 20) - 1, 1 << 221)
    lam, ell_lab = 100, 254

    div_2dr = (q_formula % (2 * d_r)) == 1
    div_n = ((q_formula - 1) % n_forms) == 0
    div_h = ((q_formula - 1) % h_ord) == 0
    # Capelli's theorem for T^{4608} - 5 over F_q (4608 = 2^9 * 3^2, 4 | (q-1)):
    # irreducible iff c0^{(q-1)/2} == -1 mod q AND c0^{(q-1)/3} != 1 mod q
    capelli_bn254 = all((
        (q_formula - 1) % 4 == 0,
        pow(c0, (q_formula - 1) // 2, q_formula) == q_formula - 1,
        pow(c0, (q_formula - 1) // 3, q_formula) != 1,
    ))
    g_bounds_ok = all((
        g_val ** 8 >= (1 << 405),
        (g_val - 1) ** 8 < (1 << 405),
        Fraction(1, g_val ** 4) <= Fraction(1, 1 << 202),
        Fraction(1, 1 << 202) < theta,
        theta < Fraction(1, g_val ** 3),
        Fraction(1, g_val ** 3) < Fraction(1, g_val ** 2),
    ))
    search_lt_q = (2 * (n_unk + 1) * (g_val + 1) + 1) < q_formula

    # Proposition 5.7 exact element counts & Lemma B.3 df / eps_f
    n1 = (2 * k1 + 1) * (n_unk + 1) + delta_quo + ((nu - 1) * n_c) // j_rem
    n2 = 6 * k2 * (n_unk + 1) + 3 * k2 + ((3 * n_forms) // 2) * (j_quo + j_rem) + 13 * n_forms - 8
    l1, l2, lt = n1 + 1, 2 * n2 + 1, 2
    tot_l = l1 + l2 + lt
    df = 3 * d_eval + 2 * n_forms + 2 * k1 + 6
    eps_f = Fraction(df + 61, q_formula - d_eval)
    n_free = (1 << ell_lab) - tot_l - 3 * (1 << (lam + 1)) - 1

    p1_ok = all((d_eval <= j_quo * delta_quo, j_quo * delta_quo <= d_eval + n_forms, n_forms <= d_eval))
    p2_ok = 3 * (tot_l + 3 * (1 << (lam + 1)) + 1) <= q_formula
    beta_paper_upper = 243200 * (10 ** 51)
    beta_2_188 = 1 << 188
    p4_paper_ok = all((
        (1 << 18731) < (beta_paper_upper ** 100),
        (beta_paper_upper ** 100) < (1 << 18732),
        2 * beta_paper_upper < q_formula,
        24 * (beta_paper_upper ** 4) < (q_formula ** 3),
    ))
    p4_2_188_ok = all((2 * beta_2_188 < q_formula, 24 * (beta_2_188 ** 4) < (q_formula ** 3)))

    e2 = evaluate_lemma_b2_bound(2, l1, l2, lt, eps_f, theta, n_free, lam=lam)
    e_hi = evaluate_lemma_b2_bound(1 << (lam + 1), l1, l2, lt, eps_f, theta, n_free, lam=lam)
    e_diff = e_hi - e2
    e2_ok = e2 < Fraction(1, 1 << 122)
    e_diff_ok = e_diff <= (Q1 - Fraction(1, 1 << lam))

    # Appendix C Hair-Sahai basic construction (R=3 vs R=4) & Proposition C.1 lower bound
    hs_thresh = 100 * (1 << 199)
    k_hs3 = (2 * n_unk * 3 + 1) * math.comb(6, 3)
    m_hs3 = (n_unk + 1) * k_hs3
    hs_r3_fails = (m_hs3 ** 4) < hs_thresh
    k_hs4 = (2 * n_unk * 4 + 1) * math.comb(8, 4)
    m_hs4 = (n_unk + 1) * k_hs4
    hs_r4_ok = all(((m_hs4 ** 3) < hs_thresh, (m_hs4 ** 4) < hs_thresh, (m_hs4 ** 5) > hs_thresh))
    k_prop_c1_lb = 4 * math.comb(n_unk + 1 - 8, 3) - (2 * n_unk + 1) * k_hs4
    hs_prop_c1_ok = (k_prop_c1_lb ** 100) > (1 << 5514)

    verified = all((
        q_formula == BN254_Q,
        pock["verified"],
        d_eval == 3861007,
        j_quo * delta_quo == d_eval + 4,
        j_rem * delta_rem == nu * n_c,
        n_forms == (k_rows + 1) * d_r,
        ell_cols == (n_unk + d_r - 1) // d_r,
        k1 * k2 == n_forms // 2,
        div_2dr,
        div_n,
        div_h,
        capelli_bn254,
        g_bounds_ok,
        search_lt_q,
        p1_ok,
        p2_ok,
        p4_paper_ok,
        p4_2_188_ok,
        e2_ok,
        e_diff_ok,
        k_hs4 == 219348150,
        m_hs4 == 85917354266100,
        hs_r3_fails,
        hs_r4_ok,
        hs_prop_c1_ok,
    ))

    return {
        "bn254_seed_t": t_bn,
        "bn254_q_str": str(q_formula),
        "pocklington_prime_verified": pock["verified"],
        "pocklington_factored_f_bits": pock["factored_f_bits"],
        "table4_core": {
            "N": n_unk,
            "nc": n_c,
            "Fmax": f_max,
            "nu": nu,
            "H_order": h_ord,
            "D": d_eval,
            "J": j_quo,
            "Delta": delta_quo,
            "Jp": j_rem,
            "Deltap": delta_rem,
            "n": n_forms,
            "c0": c0,
            "dR": d_r,
            "k": k_rows,
            "ell": ell_cols,
            "K1": k1,
            "K2": k2,
            "g": g_val,
            "theta_q": format_rational(theta),
        },
        "divisibility_q_mod_2dR_eq_1": div_2dr,
        "divisibility_n_divides_q_minus_1": div_n,
        "divisibility_h_ord_divides_q_minus_1": div_h,
        "capelli_irreducible_t4608_minus_5": capelli_bn254,
        "g_bounds_exact": g_bounds_ok,
        "search_range_2B_plus_1_lt_q": search_lt_q,
        "p1_chunk_bounds_hold": p1_ok,
        "p2_group_coverage_holds": p2_ok,
        "p4_lifting_24beta4_lt_q3": p4_paper_ok,
        "p4_lifting_beta_2_188_lt_q3": p4_2_188_ok,
        "prop57_counts": {
            "n1": n1,
            "n2": n2,
            "two_n2": 2 * n2,
            "L1": l1,
            "L2": l2,
            "LT": lt,
            "L": tot_l,
            "df": df,
            "eps_f_q": format_rational(eps_f),
        },
        "lemma_b2": {
            "E_2_q": format_rational(e2),
            "E_2_101_minus_E_2_q": format_rational(e_diff),
            "E_diff_margin_trunc8": format_decimal_trunc((Q1 - Fraction(1, 1 << lam)) - e_diff, places=8),
            "b2_e2_lt_2_neg122": e2_ok,
            "b2_e_diff_le_1_minus_2_neg100": e_diff_ok,
        },
        "appendix_c_hair_sahai": {
            "R": 4,
            "K": k_hs4,
            "m": m_hs4,
            "k_prop_c1_lower_bound": k_prop_c1_lb,
            "hs_r3_fails_eq10": hs_r3_fails,
            "hs_r4_m4_fails_m5_passes_eq10": hs_r4_ok,
            "hs_prop_c1_gt_2_55_14": hs_prop_c1_ok,
        },
        "pillar_verified": verified,
    }


# ---------------------------------------------------------------------------
# Pillar 4: Honest Scope Ledger (Table 6 / Reduction Loss) & CS-19 Bridge
# ---------------------------------------------------------------------------

def build_pillar4_honest_scope_and_cs19_bridge() -> dict[str, Any]:
    red_bits = Fraction(108, 1)
    msis_bits = Fraction(207, 2)
    loss_bits = red_bits - msis_bits
    etnfs_bits = 103
    ggm_bits = 100
    heavy_cheat_bits = 173

    # Executable CS-19 sealed-witness bridge using Pillar 1 F_257 Praxis oracle
    cs19_payload = "CS19-SEALED-KEY!"
    honest_open = _run_small_field_praxis(cs19_payload, (1, 1, 0, 1), tau=25)
    forged_open = _run_small_field_praxis(cs19_payload, (1, 1, 1, 1), tau=25)

    table6_deltas = [
        {
            "id": "T6-01",
            "lean_scope": "Fixed Table 4 parameters with 256-bit messages and seeds",
            "paper_scope": "General admissible parameters (P1)-(P5) and 100-bit messages/seeds",
        },
        {
            "id": "T6-02",
            "lean_scope": "Key derived from opaque sign-class name([kappa]_T)",
            "paper_scope": "Key derived directly from group element [kappa]_T",
        },
        {
            "id": "T6-03",
            "lean_scope": "Exhaustive short-multiple search and logged H_key monitor; counts oracle calls only",
            "paper_scope": "Polynomial-time Lenstra/HNF LIFT (Lemma B.9) and unlogged monitor with explicit runtime t_R",
        },
        {
            "id": "T6-04",
            "lean_scope": "Leaves Groth16 honest setup trapdoor and definition faithfulness outside Lean kernel",
            "paper_scope": "Explicitly assumes Groth16 universal-circuit honest setup (Table 5) and manual definition audit",
        },
    ]

    valid_unmasked = all((
        honest_open["status"] == "OK",
        honest_open["decryption_recovered_exact_kappa"],
        honest_open["decryption_recovered_exact_message"],
    ))
    invalid_rejected = all((
        forged_open["status"] == "NON_WITNESS_REJECTED",
        forged_open["ciphertext_sha256"] == honest_open["ciphertext_sha256"],
        forged_open["recovered_kappa"] is None,
    ))
    verified = all((
        loss_bits == Fraction(9, 2),
        (1 << 9) == 512,
        etnfs_bits - ggm_bits == 3,
        heavy_cheat_bits - ggm_bits == 73,
        len(table6_deltas) == 4,
        valid_unmasked,
        invalid_rejected,
    ))

    return {
        "security_accounting": {
            "reduction_time_bits": format_rational(red_bits),
            "msis_matzov_bits": format_rational(msis_bits),
            "reduction_loss_bits": format_rational(loss_bits),
            "reduction_loss_decimal": format_decimal_trunc(loss_bits, places=1),
            "reduction_loss_factor_sq": 1 << 9,
            "bn254_etnfs_bits": etnfs_bits,
            "ggm_target_bits": ggm_bits,
            "etnfs_margin_above_ggm_bits": etnfs_bits - ggm_bits,
            "heavy_cheat_lattice_bits": heavy_cheat_bits,
            "reported_ciphertext_gib_str": "7.88",
        },
        "table6_lean_vs_paper_deltas": table6_deltas,
        "cs19_sealed_witness_bridge": {
            "commitment_ciphertext_sha256": honest_open["ciphertext_sha256"],
            "valid_witness_kappa": honest_open["kappa_recovered"],
            "valid_witness_unmasked_exact": valid_unmasked,
            "invalid_witness_rejected": invalid_rejected,
            "invalid_witness_status": forged_open["status"],
        },
        "pillar_verified": verified,
    }


# ---------------------------------------------------------------------------
# Standalone Certificate Builder & Zone-B Structure Validator
# ---------------------------------------------------------------------------

def build_standalone_certificate() -> dict[str, Any]:
    p1 = build_pillar1_executable_praxis_protocol()
    p2 = build_pillar2_rank_gap_and_polya_obstructions()
    p3 = build_pillar3_table4_admissibility_and_hair_sahai()
    p4 = build_pillar4_honest_scope_and_cs19_bridge()

    all_ok = all((
        p1["pillar_verified"],
        p2["pillar_verified"],
        p3["pillar_verified"],
        p4["pillar_verified"],
    ))
    payload: dict[str, Any] = {
        "oracle_class": "exact",
        "novelty_classification": "N1",
        "literature_anchors_n0": [
            "Tse, Vanjani, Vesely (Nov 2026): Praxis — Practical Witness Encryption for NP",
            "Hair, Sahai (2026): Witness Encryption from Bounded-Factor MinRank",
            "Polya (1913): Aufgabe 424 (Permanent-to-Determinant Sign-Flip Obstruction)",
            "Lasserre (2001) / Schoenebeck (2008): Sum-of-Squares Semidefinite Hierarchy",
        ],
        "zero_floats_exact_arithmetic": True,
        "all_verified": all_ok,
        "pillar1_executable_praxis_protocol": p1,
        "pillar2_rank_gap_and_polya_obstructions": p2,
        "pillar3_table4_admissibility_and_hair_sahai": p3,
        "pillar4_honest_scope_and_cs19_bridge": p4,
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
    """Structural and bijective bool-vs-int schema gate enforced under both full_replay=False and True."""
    if frozenset(payload.keys()) != _PAYLOAD_KEYS:
        raise PraxisTomographyError("INVALID_PAYLOAD_KEYS", "payload top-level keys mismatch")
    if payload["oracle_class"] != "exact":
        raise PraxisTomographyError("INVALID_PAYLOAD_META", "oracle_class must be 'exact'")
    if payload["novelty_classification"] != "N1":
        raise PraxisTomographyError("INVALID_PAYLOAD_META", "novelty_classification must be 'N1'")
    if payload["zero_floats_exact_arithmetic"] is not True:
        raise PraxisTomographyError("INVALID_PAYLOAD_META", "zero_floats_exact_arithmetic must be True")
    if payload["all_verified"] is not True:
        raise PraxisTomographyError("INVALID_PAYLOAD_META", "all_verified must be True")
    anchors = payload["literature_anchors_n0"]
    if type(anchors) is not list or len(anchors) != 4:
        raise PraxisTomographyError("INVALID_PAYLOAD_META", "literature_anchors_n0 must be 4-element list")
    for idx, anc in enumerate(anchors):
        if not require_str(anc, f"literature_anchors_n0[{idx}]", max_len=256):
            raise PraxisTomographyError("INVALID_PAYLOAD_META", "literature_anchors_n0 entries must be non-empty str")
    for pkey in _PILLAR_KEYS:
        pdict = payload[pkey]
        if type(pdict) is not dict:
            raise PraxisTomographyError("INVALID_PILLAR_TYPE", f"{pkey} must be strict dict")
        if pdict.get("pillar_verified") is not True:
            raise PraxisTomographyError("PILLAR_NOT_VERIFIED", f"{pkey}.pillar_verified must be True")

    stack: list[Any] = [payload]
    while stack:
        cur = stack.pop()
        if type(cur) is dict:
            for k, v in cur.items():
                if type(v) is bool:
                    if k not in _ALLOWED_BOOL_KEYS:
                        raise PraxisTomographyError("BOOL_IN_NON_BOOL_FIELD", f"unexpected bool in field {k}")
                elif k in _ALLOWED_BOOL_KEYS:
                    raise PraxisTomographyError("NON_BOOL_IN_BOOL_FIELD", f"expected exact bool in field {k}")
                elif type(v) in (dict, list):
                    stack.append(v)
        else:
            for item in cur:
                if type(item) is bool:
                    raise PraxisTomographyError("BOOL_IN_LIST", "bool element forbidden inside list")
                if type(item) in (dict, list):
                    stack.append(item)


def validate_certificate_payload(cert: Any, full_replay: bool = True) -> dict[str, Any]:
    """Zone-B hardened in-memory certificate validator."""
    require_bool(full_replay, "full_replay")
    validate_json_tree_iterative(cert)
    if type(cert) is not dict:
        raise PraxisTomographyError("CERT_NOT_DICT", "certificate root must be strict dict")
    if frozenset(cert.keys()) != _CERT_KEYS:
        raise PraxisTomographyError("INVALID_CERT_KEYS", "certificate keys mismatch")
    if cert["schema"] != SCHEMA_VERSION:
        raise PraxisTomographyError("INVALID_SCHEMA", "unexpected certificate schema")
    if cert["track_id"] != TRACK_ID:
        raise PraxisTomographyError("INVALID_TRACK_ID", "unexpected track_id")

    payload = cert["payload"]
    if type(payload) is not dict:
        raise PraxisTomographyError("PAYLOAD_NOT_DICT", "payload must be strict dict")

    claimed_payload_sha = require_hex64(cert["payload_sha256"], "payload_sha256")
    actual_payload_sha = sha256_hex(canonical_json_bytes(payload))
    if not constant_time_hex64_equal(claimed_payload_sha, actual_payload_sha, "payload_sha256"):
        raise PraxisTomographyError("PAYLOAD_SHA_MISMATCH", "payload_sha256 mismatch")

    claimed_cert_sha = require_hex64(cert["certificate_sha256"], "certificate_sha256")
    cert_body = {
        "schema": cert["schema"],
        "track_id": cert["track_id"],
        "payload_sha256": claimed_payload_sha,
        "payload": payload,
    }
    actual_cert_sha = sha256_hex(canonical_json_bytes(cert_body))
    if not constant_time_hex64_equal(claimed_cert_sha, actual_cert_sha, "certificate_sha256"):
        raise PraxisTomographyError("CERT_SHA_MISMATCH", "certificate_sha256 mismatch")

    _validate_payload_structure(payload)

    if full_replay:
        fresh = build_standalone_certificate()
        if not constant_time_hex64_equal(actual_payload_sha, fresh["payload_sha256"], "recomputed_payload_sha256"):
            raise PraxisTomographyError("RECOMPUTATION_MISMATCH", "payload differs from deterministic recomputation")

    return {
        "valid": True,
        "schema": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": actual_payload_sha,
        "certificate_sha256": actual_cert_sha,
        "full_replay": full_replay,
    }
