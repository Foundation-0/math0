"""Pure-Z / F_2 / F_{2^m} / Q clean-room oracle for the MiniMax-AI/Research
Cryptography Portal Audit (57842cef92e84eaf8e2535b12f48ba5586080ddd).

Zero shared code with MiniMax-AI/Research. Zero floats. Zero bare assert statements.
Pure Python 3 standard library only (int, Fraction, hashlib, json).

Three computational verification pillars plus a fail-closed certification wrapper
(with declared upstream inputs reported in their own section outside all_gates_passed):
  1. BentSum (arXiv:2610.32239): Independent pure-Z Walsh-Hadamard & ANF verification
     of q_3 (n=6), Tokareva bent-sum counterexample cylQ3(4) (n=8), derivative
     counterexample liftCylQ3(4) (n=10), explicit hypothesis checks, and positive
     Maiorana-McFarland bent-sum / bent-derivative controls.
  2. Fast Algebraic Cryptanalysis & Blender-256:
     - ARADI (ePrint 2024/1240): involutive L_0..L_3, unique symmetry/orthogonality of
       L_3 = (8,9,7) with 8 disjoint 4-column islands, S-box super-S-box degree-3
       collapse, LATINCRYPT 2025 blind-column audit (max 24/32 covered), analytical
       198-equation 5-round zero-sum certificate (99 row x + 99 row z) with 0 violations
       on 2 seeded key trials (sampled), and L_3' = (7,3,11) mitigation (0 masks).
     - COLM (GF(2^128)): Rabin irreducibility proof of x^128+x^7+x^2+x+1, exact 1/3,
       transplant set {1,3,4,5,6,7,129,130} (first m=129), COLM_tau obstruction for all
       tau in 1..127, plus definitional fade/rank controls and J. Cryptol. 2024 anchor.
     - SBC-VOLE (GF(2^257)): Frobenius irreducibility of x^257+x^12+1 and single-signature
       linear key recovery on a single seeded SplitMix64 instance (sampled).
     - Blender-256: Theorem 2 8-cycle word-parity obstruction (p_4 = p_0 ^ 1,
       p_5 = p_1 ^ 1) sampled over a 24-step stream from standard IV, clean-room 12-step
       entry obeying Theorem 2, and from-IV 2-adic Smith Normal Form subgroup closure
       [0,0,1,1,2,2,3,3] -> [0,0,1,1,1,1,1,1].
  3. Background Algebraic Identities Verified in This Audit:
     - Binary Goppa codes (TII-McEliece): clean-room GF(2^5) binary Goppa code
       verifying Theorem 1 (sigma'_S(X) = g(X)^2, e_2(z_S) = g_{t-1}^2) on all 13
       min-weight codewords, exact full-code equality between the shortened code
       (n'=21) and the Goppa code on the shorter support, plus TII-125/250 F(d) anchors.
     - Parity-sublattice & Gram-conditioning identities (HAWK): exact rank-8
       parity-congruence sublattice Lambda' = 2*Z^8 + Z*u_parity generation &
       index 2^(n-1) = 128 check, det(H G H^T) = 2^(2(n-1)) det(G) via Bareiss
       determinant, planted unimodular backward-substitution check, AND blind exact
       pure-Q LLL reduction on B_raw (without B_good) recovering max diagonal 41.
"""

from fractions import Fraction
import hashlib
import json

SCHEMA_VERSION = "minimax_cryptanalysis_audit.v2"
STUDY_ID = "expedition-minimax-cryptanalysis-audit109r"
UPSTREAM_REPO = "MiniMax-AI/Research"
UPSTREAM_COMMIT = "57842cef92e84eaf8e2535b12f48ba5586080ddd"
MAX_CONTAINER_DEPTH = 64
MAX_INT_DIGITS = 1000
MAX_INT_BITS = 3321

REQUIRED_LEAN_FILES = (
    "BentSum.lean",
    "BentSum/Basic.lean",
    "BentSum/Congruence.lean",
    "BentSum/Counterexample.lean",
    "BentSum/Derivative.lean",
)

BANNED_METAPHOR_TOKENS = (
    "alchemy",
    "magic",
    "mystical",
    "quantum_leap",
    "soul",
    "vibe",
    "consciousness",
    "telepathy",
)

STANDARD_BLENDER_IV256 = (
    0x6A09E667,
    0xBB67AE85,
    0x3C6EF372,
    0xA54FF53A,
    0x510E527F,
    0x9B05688C,
    0x1F83D9AB,
    0x5BE0CD19,
)

STANDARD_ARADI_ROT_CONSTS = ((11, 8, 14), (10, 9, 11), (9, 4, 14), (8, 9, 7))
STANDARD_COLM_MOD128 = (1 << 128) | (1 << 7) | (1 << 2) | (1 << 1) | 1
STANDARD_SBCVOLE_MOD257 = (1 << 257) | (1 << 12) | 1
STANDARD_GOPPA_POLY = (1, 2, 1, 1)
STANDARD_HAWK_PARITY = (1, 1, 0, 1, 0, 1, 1, 0)


class MinimaxCryptError(ValueError):
    """Structured fail-closed error for the MiniMax cryptanalysis study."""

    def __init__(self, code, detail):
        self.code = str(code)
        self.detail = str(detail)
        super().__init__(f"{self.code}: {self.detail}")


# =============================================================================
# Core Type, Hygiene, Canonical JSON & Exact Linear Algebra Primitives
# =============================================================================


def verify_no_floats(obj, path="root", allow_fraction=True, max_depth=MAX_CONTAINER_DEPTH):
    """Iteratively reject floats, non-str dict keys, oversized ints, deep nesting, and unsupported types."""
    stack = [(obj, path, 0)]
    while stack:
        cur, cur_path, depth = stack.pop()
        if depth > max_depth:
            raise MinimaxCryptError("MAX_DEPTH_EXCEEDED", f"container depth > {max_depth} at {cur_path}")
        cur_type = type(cur)
        if isinstance(cur, (float, complex)):
            raise MinimaxCryptError("FLOAT_FORBIDDEN", f"non-exact numeric at {cur_path}")
        if isinstance(cur, Fraction):
            if not allow_fraction:
                raise MinimaxCryptError("INVALID_JSON_TYPE", f"Fraction not JSON-serializable at {cur_path}")
            continue
        if cur_type is dict:
            for k, v in cur.items():
                if isinstance(k, (float, complex)):
                    raise MinimaxCryptError("FLOAT_FORBIDDEN", f"non-exact numeric at {cur_path}.<key>")
                if type(k) is not str:
                    raise MinimaxCryptError("INVALID_KEY_TYPE", f"non-str dict key at {cur_path}")
                stack.append((v, f"{cur_path}.{k}", depth + 1))
            continue
        if cur_type in (list, tuple):
            for idx, item in enumerate(cur):
                stack.append((item, f"{cur_path}[{idx}]", depth + 1))
            continue
        if cur_type is int:
            if abs(cur).bit_length() > MAX_INT_BITS:
                raise MinimaxCryptError("INT_TOO_LARGE", f"integer bit length > {MAX_INT_BITS} at {cur_path}")
            continue
        if cur_type not in (bool, str, type(None)):
            raise MinimaxCryptError("INVALID_JSON_TYPE", f"unsupported type {cur_type.__name__} at {cur_path}")


def require_exact_int(val, name, min_value=None, max_value=None):
    if type(val) is not int:
        raise MinimaxCryptError("INVALID_INT", f"{name} must be exact int")
    if abs(val).bit_length() > MAX_INT_BITS:
        raise MinimaxCryptError("INT_TOO_LARGE", f"{name} exceeds {MAX_INT_BITS} bits")
    if min_value is not None and val < min_value:
        raise MinimaxCryptError("RANGE_ERROR", f"{name}={val} < {min_value}")
    if max_value is not None and val > max_value:
        raise MinimaxCryptError("RANGE_ERROR", f"{name}={val} > {max_value}")
    return val


def require_exact_bool(val, name):
    if type(val) is not bool:
        raise MinimaxCryptError("INVALID_BOOL", f"{name} must be exact bool")
    return val


def require_non_empty_str(val, name):
    if type(val) is not str or not val.strip() or val != val.strip():
        raise MinimaxCryptError("INVALID_STR", f"{name} must be non-empty stripped str")
    return val


def require_hex_sha256(val, name):
    s = require_non_empty_str(val, name)
    if len(s) != 64 or any(ch not in "0123456789abcdef" for ch in s) or s == "0" * 64:
        raise MinimaxCryptError("INVALID_SHA256", f"{name} must be non-zero 64 lowercase hex chars")
    return s


def require_hex_sha1(val, name):
    s = require_non_empty_str(val, name)
    if len(s) != 40 or any(ch not in "0123456789abcdef" for ch in s) or s == "0" * 40:
        raise MinimaxCryptError("INVALID_COMMIT", f"{name} must be non-zero 40 lowercase hex chars")
    return s


def frac_str(q):
    if not isinstance(q, Fraction):
        raise MinimaxCryptError("INVALID_FRACTION", "expected Fraction")
    return f"{q.numerator}/{q.denominator}"


def format_exact_decimal(q, places=6):
    """Exact half-to-even decimal string of Fraction q with zero floats."""
    if not isinstance(q, Fraction):
        raise MinimaxCryptError("INVALID_FRACTION", "expected Fraction")
    places = require_exact_int(places, "places", min_value=0, max_value=12)
    neg = q < 0
    aq = -q if neg else q
    scale = 10 ** places
    num = aq.numerator * scale
    den = aq.denominator
    quot, rem = divmod(num, den)
    twice_rem = 2 * rem
    if twice_rem > den or (twice_rem == den and (quot & 1)):
        quot += 1
    prefix = "-" if (neg and quot > 0) else ""
    if places == 0:
        return f"{prefix}{quot}"
    whole, frac = divmod(quot, scale)
    return f"{prefix}{whole}.{frac:0{places}d}"


def canonical_json_bytes(obj):
    verify_no_floats(obj, "canonical_json", allow_fraction=False)
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def canonical_sha256(obj):
    return hashlib.sha256(canonical_json_bytes(obj)).hexdigest()


def _strict_equal(a, b):
    """Recursive exact equality with strict type identity (rejects 1 == True)."""
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        if a.keys() != b.keys():
            return False
        return all(_strict_equal(a[k], b[k]) for k in a)
    if isinstance(a, (list, tuple)):
        if len(a) != len(b):
            return False
        return all(_strict_equal(x, y) for x, y in zip(a, b))
    return a == b


def enforce_operator_label_hygiene(labels):
    """Ensure every operator label is a non-empty strict mathematical identifier."""
    if not isinstance(labels, (list, tuple)) or not labels:
        raise MinimaxCryptError("INVALID_LABELS", "operator_labels must be non-empty sequence")
    clean = []
    for idx, raw in enumerate(labels):
        lbl = require_non_empty_str(raw, f"operator_labels[{idx}]")
        low = lbl.lower()
        for tok in BANNED_METAPHOR_TOKENS:
            if tok in low:
                raise MinimaxCryptError("METAPHOR_LABEL_REJECTED", f"banned metaphor token {tok} in {lbl}")
        clean.append(lbl)
    return {"checked_count": len(clean), "labels": clean, "passed": True}


class _SplitMix64:
    """Pure-integer deterministic PRNG (zero random module, zero floats)."""

    def __init__(self, seed):
        self._state = seed & 0xFFFFFFFFFFFFFFFF

    def next_u64(self):
        self._state = (self._state + 0x9E3779B97F4A7C15) & 0xFFFFFFFFFFFFFFFF
        z = self._state
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & 0xFFFFFFFFFFFFFFFF
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & 0xFFFFFFFFFFFFFFFF
        return z ^ (z >> 31)

    def next_u32(self):
        return self.next_u64() & 0xFFFFFFFF

    def next_bits(self, k):
        val = 0
        shift = 0
        while shift < k:
            val |= self.next_u64() << shift
            shift += 64
        return val & ((1 << k) - 1)


def _gf2_rref_pivots(rows):
    """Exact GF(2) reduced row echelon form over Python int bitmasks."""
    pivs = {}
    for row in rows:
        v = row
        while v:
            hb = v.bit_length() - 1
            if hb in pivs:
                v ^= pivs[hb]
            else:
                pivs[hb] = v
                v = 0
    for p in sorted(pivs):
        pv = pivs[p]
        for q in sorted(pivs):
            if q != p and ((pivs[q] >> p) & 1):
                pivs[q] ^= pv
    return pivs


def _gf2_poly_mod(a, m):
    dm = m.bit_length() - 1
    while a.bit_length() - 1 >= dm:
        a ^= m << (a.bit_length() - 1 - dm)
    return a


def _gf2_poly_mul_mod(a, b, m):
    prod = 0
    while b:
        lsb = b & -b
        prod ^= a << (lsb.bit_length() - 1)
        b ^= lsb
    return _gf2_poly_mod(prod, m)


def _gf2_poly_gcd(a, b):
    while b:
        a, b = b, _gf2_poly_mod(a, b)
    return a


def _gf2_poly_inv(a, mod):
    """Exact polynomial inverse in GF(2)[x]/(mod) via extended Euclidean algorithm."""
    if a == 0 or _gf2_poly_gcd(a, mod) != 1:
        return None
    u, v = _gf2_poly_mod(a, mod), mod
    g1, g2 = 1, 0
    while u != 1:
        j = u.bit_length() - v.bit_length()
        if j < 0:
            u, v = v, u
            g1, g2 = g2, g1
            j = -j
        u ^= v << j
        g1 ^= g2 << j
    return _gf2_poly_mod(g1, mod)


def _gf2_poly_is_irred_pow2(f):
    """Exact Rabin irreducibility test over GF(2) for polynomials of degree 2^r."""
    deg = f.bit_length() - 1
    if deg <= 0 or (deg & (deg - 1)) != 0:
        return False
    xpow = 2
    half = deg // 2
    for step in range(1, deg + 1):
        xpow = _gf2_poly_mul_mod(xpow, xpow, f)
        if step == half and _gf2_poly_gcd(xpow ^ 2, f) != 1:
            return False
    return xpow == 2


def _bareiss_det_exact(mat):
    """Exact integer matrix determinant via fraction-free Bareiss elimination."""
    n = len(mat)
    a = [list(row) for row in mat]
    sign = 1
    prev = 1
    for k in range(n - 1):
        if a[k][k] == 0:
            sw = next((r for r in range(k + 1, n) if a[r][k] != 0), -1)
            if sw == -1:
                return 0
            a[k], a[sw] = a[sw], a[k]
            sign = -sign
        piv = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                a[i][j] = (a[i][j] * piv - a[i][k] * a[k][j]) // prev
        prev = piv
    return sign * a[n - 1][n - 1]


def _mat_mul_z(a, b):
    n = len(a)
    k = len(b)
    m = len(b[0])
    return [[sum(a[i][t] * b[t][j] for t in range(k)) for j in range(m)] for i in range(n)]


def _mat_t_z(a):
    return [[a[r][c] for r in range(len(a))] for c in range(len(a[0]))]


def _exact_lll_reduce(basis, delta=Fraction(3, 4)):
    """Exact pure-Q LLL basis reduction returning (reduced_basis, unimodular_U) with U * basis == reduced_basis."""
    n = len(basis)
    m = len(basis[0])
    b = [list(r) for r in basis]
    u = [[1 if i == j else 0 for j in range(n)] for i in range(n)]

    def gso():
        bs = [[Fraction(x) for x in r] for r in b]
        mu = [[Fraction(0)] * n for _ in range(n)]
        norms = [Fraction(0)] * n
        for i in range(n):
            for j in range(i):
                if norms[j] == 0:
                    return None
                num = sum(Fraction(b[i][t]) * bs[j][t] for t in range(m))
                mu[i][j] = num / norms[j]
                for t in range(m):
                    bs[i][t] -= mu[i][j] * bs[j][t]
            norms[i] = sum(x * x for x in bs[i])
        return bs, mu, norms

    res = gso()
    if res is None:
        return b, u
    bs, mu, norms = res
    k = 1
    while k < n:
        for j in range(k - 1, -1, -1):
            q = (2 * mu[k][j].numerator + mu[k][j].denominator) // (2 * mu[k][j].denominator)
            if q != 0:
                b[k] = [b[k][t] - q * b[j][t] for t in range(m)]
                u[k] = [u[k][t] - q * u[j][t] for t in range(n)]
                res = gso()
                if res is None:
                    return b, u
                bs, mu, norms = res
        if norms[k] >= (delta - mu[k][k - 1] * mu[k][k - 1]) * norms[k - 1]:
            k += 1
        else:
            b[k], b[k - 1] = b[k - 1], b[k]
            u[k], u[k - 1] = u[k - 1], u[k]
            res = gso()
            if res is None:
                return b, u
            bs, mu, norms = res
            k = max(k - 1, 1)
    return b, u


def snf_2adic_valuations_exact(rows, word_bits=32):
    """Exact 2-adic Smith Normal Form valuations over Z / 2^word_bits Z."""
    w = require_exact_int(word_bits, "word_bits", min_value=2, max_value=64)
    if not isinstance(rows, (list, tuple)) or not rows:
        raise MinimaxCryptError("INVALID_MATRIX", "rows must be non-empty list of int rows")
    first = rows[0]
    if not isinstance(first, (list, tuple)) or not first:
        raise MinimaxCryptError("INVALID_MATRIX", "matrix row must be non-empty list")
    ncols = len(first)
    mod = 1 << w
    mask = mod - 1
    mat = []
    for ri, row in enumerate(rows):
        if not isinstance(row, (list, tuple)) or len(row) != ncols:
            raise MinimaxCryptError("INVALID_MATRIX", f"row {ri} width mismatch")
        mat.append([require_exact_int(x, f"mat[{ri}][{ci}]") & mask for ci, x in enumerate(row)])
    nrows = len(mat)
    exps = []
    for c in range(min(nrows, ncols)):
        best_v = w
        bi, bj = -1, -1
        for i in range(c, nrows):
            row_i = mat[i]
            for j in range(c, ncols):
                val = row_i[j]
                if val != 0:
                    v = (val & -val).bit_length() - 1
                    if v < best_v:
                        best_v, bi, bj = v, i, j
                        if best_v == 0:
                            break
            if best_v == 0:
                break
        if best_v == w:
            exps.extend([w] * (ncols - c))
            break
        if bi != c:
            mat[c], mat[bi] = mat[bi], mat[c]
        if bj != c:
            for i in range(nrows):
                mat[i][c], mat[i][bj] = mat[i][bj], mat[i][c]
        inv_unit = pow(mat[c][c] >> best_v, -1, mod)
        mat[c] = [(x * inv_unit) & mask for x in mat[c]]
        piv_row = mat[c]
        for i in range(c + 1, nrows):
            entry = mat[i][c]
            if entry != 0:
                q = entry >> best_v
                mat[i] = [(mat[i][j] - q * piv_row[j]) & mask for j in range(ncols)]
        for j in range(c + 1, ncols):
            mat[c][j] = 0
        exps.append(best_v)
    if len(exps) < ncols:
        exps.extend([w] * (ncols - len(exps)))
    return sorted(exps)


# =============================================================================
# Portal Summary Validation & Declared Upstream Inputs (Outside all_gates_passed)
# =============================================================================


def validate_portal_summary(raw_summary):
    """Validate live or pinned portal summary schema and upstream commit pin strictly (fail-closed)."""
    verify_no_floats(raw_summary, "portal_summary")
    if type(raw_summary) is not dict:
        raise MinimaxCryptError("INVALID_PORTAL_SUMMARY", "portal_summary must be dict")
    req_top = {
        "diag_source",
        "upstream_commit",
        "bentsum_lean",
        "blender_snf_witness",
        "blender_issues_text_checks",
        "tii_94_summary",
    }
    if set(raw_summary.keys()) != req_top:
        raise MinimaxCryptError("INVALID_PORTAL_SUMMARY", "portal_summary key set mismatch")
    diag_src = require_non_empty_str(raw_summary["diag_source"], "diag_source")
    if diag_src not in ("live_portal_read", "standalone_pinned_fixture"):
        raise MinimaxCryptError("INVALID_PORTAL_SUMMARY", f"unexpected diag_source {diag_src}")
    commit = require_hex_sha1(raw_summary["upstream_commit"], "upstream_commit")
    if commit != UPSTREAM_COMMIT:
        raise MinimaxCryptError("COMMIT_MISMATCH", f"upstream_commit {commit} != pinned {UPSTREAM_COMMIT}")

    # 1. Lean 4 lexical manifest section
    lean = raw_summary["bentsum_lean"]
    req_lean = {"files_checked", "banned_construct_findings", "lean_file_sha256"}
    if type(lean) is not dict or set(lean.keys()) != req_lean:
        raise MinimaxCryptError("INVALID_LEAN_MANIFEST", "bentsum_lean schema mismatch")
    files_checked = require_exact_int(lean["files_checked"], "bentsum_lean.files_checked", min_value=1)
    banned = require_exact_int(lean["banned_construct_findings"], "bentsum_lean.banned_construct_findings", min_value=0)
    fmap = lean["lean_file_sha256"]
    if type(fmap) is not dict or set(fmap.keys()) != set(REQUIRED_LEAN_FILES):
        raise MinimaxCryptError("INVALID_LEAN_MANIFEST", "lean_file_sha256 keys mismatch")
    if files_checked != len(fmap):
        raise MinimaxCryptError("INVALID_LEAN_MANIFEST", "files_checked contradicts lean_file_sha256 count")
    clean_fmap = {k: require_hex_sha256(fmap[k], f"lean_sha.{k}") for k in REQUIRED_LEAN_FILES}

    # 2. Blender SNF witness section
    bsnf = raw_summary["blender_snf_witness"]
    req_bsnf = {
        "witness_sha256",
        "unshifted_count",
        "shifted_multi_count",
        "unshifted_snf_exps",
        "shifted_multi_snf_exps",
        "f2_xor_fail_count",
        "mod32_superposition_pass_count",
    }
    if type(bsnf) is not dict or set(bsnf.keys()) != req_bsnf:
        raise MinimaxCryptError("INVALID_BLENDER_WITNESS", "blender_snf_witness schema mismatch")
    bsnf_sha = require_hex_sha256(bsnf["witness_sha256"], "blender_snf_witness.witness_sha256")
    unsh_n = require_exact_int(bsnf["unshifted_count"], "unshifted_count", min_value=1)
    sh_n = require_exact_int(bsnf["shifted_multi_count"], "shifted_multi_count", min_value=2)
    f2_fail = require_exact_int(bsnf["f2_xor_fail_count"], "f2_xor_fail_count", min_value=0)
    mod_pass = require_exact_int(bsnf["mod32_superposition_pass_count"], "mod32_superposition_pass_count", min_value=0)
    unsh_exps = bsnf["unshifted_snf_exps"]
    sh_exps = bsnf["shifted_multi_snf_exps"]
    if type(unsh_exps) is not list or len(unsh_exps) != 8:
        raise MinimaxCryptError("INVALID_BLENDER_WITNESS", "unshifted_snf_exps must have length 8")
    if type(sh_exps) is not list or len(sh_exps) != 8:
        raise MinimaxCryptError("INVALID_BLENDER_WITNESS", "shifted_multi_snf_exps must have length 8")
    clean_unsh = [require_exact_int(x, f"unsh[{i}]", min_value=0, max_value=32) for i, x in enumerate(unsh_exps)]
    clean_sh = [require_exact_int(x, f"sh[{i}]", min_value=0, max_value=32) for i, x in enumerate(sh_exps)]

    # 3. Blender Issues #1 & #2 text flags
    biss = raw_summary["blender_issues_text_checks"]
    req_biss = {"issue1_global_minimum_claim_present", "issue2_sec33_w0246_in_x_notx_present"}
    if type(biss) is not dict or set(biss.keys()) != req_biss:
        raise MinimaxCryptError("INVALID_BLENDER_ISSUES", "blender_issues_text_checks schema mismatch")
    clean_biss = {
        "issue1_global_minimum_claim_present": require_exact_bool(
            biss["issue1_global_minimum_claim_present"], "issue1_global_minimum_claim_present"
        ),
        "issue2_sec33_w0246_in_x_notx_present": require_exact_bool(
            biss["issue2_sec33_w0246_in_x_notx_present"], "issue2_sec33_w0246_in_x_notx_present"
        ),
    }

    # 4. TII-94 summary section
    tii = raw_summary["tii_94_summary"]
    req_tii = {"summary_sha256", "total_solved", "route_a_solved", "route_b_solved", "first_bloods"}
    if type(tii) is not dict or set(tii.keys()) != req_tii:
        raise MinimaxCryptError("INVALID_TII_SUMMARY", "tii_94_summary schema mismatch")
    tii_sha = require_hex_sha256(tii["summary_sha256"], "tii_94_summary.summary_sha256")
    tot_s = require_exact_int(tii["total_solved"], "tii.total_solved", min_value=1)
    ra_s = require_exact_int(tii["route_a_solved"], "tii.route_a_solved", min_value=0, max_value=tot_s)
    rb_s = require_exact_int(tii["route_b_solved"], "tii.route_b_solved", min_value=0, max_value=tot_s)
    fb_s = require_exact_int(tii["first_bloods"], "tii.first_bloods", min_value=0, max_value=tot_s)
    if ra_s + rb_s != tot_s:
        raise MinimaxCryptError("TII_SUM_MISMATCH", "route_a_solved + route_b_solved != total_solved")

    return {
        "diag_source": diag_src,
        "upstream_commit": commit,
        "bentsum_lean": {
            "files_checked": files_checked,
            "banned_construct_findings": banned,
            "lean_file_sha256": clean_fmap,
        },
        "blender_snf_witness": {
            "witness_sha256": bsnf_sha,
            "unshifted_count": unsh_n,
            "shifted_multi_count": sh_n,
            "unshifted_snf_exps": clean_unsh,
            "shifted_multi_snf_exps": clean_sh,
            "f2_xor_fail_count": f2_fail,
            "mod32_superposition_pass_count": mod_pass,
        },
        "blender_issues_text_checks": clean_biss,
        "tii_94_summary": {
            "summary_sha256": tii_sha,
            "total_solved": tot_s,
            "route_a_solved": ra_s,
            "route_b_solved": rb_s,
            "first_bloods": fb_s,
        },
    }


def build_declared_upstream_inputs(ps):
    """Build the separate declared_upstream_inputs record (kept strictly outside all_gates_passed)."""
    is_live = ps["diag_source"] == "live_portal_read"
    biss = ps["blender_issues_text_checks"]
    return {
        "claim_scope": "anchor",
        "excluded_from_all_gates_passed": True,
        "diag_source": ps["diag_source"],
        "provenance_status": (
            "measured_from_live_checkout_and_pin_verified"
            if is_live
            else "declared_pinned_fixture_not_remeasured_offline"
        ),
        "upstream_repo": UPSTREAM_REPO,
        "upstream_commit": ps["upstream_commit"],
        "bentsum_lean_manifest": {
            "files_checked": ps["bentsum_lean"]["files_checked"],
            "banned_construct_findings": ps["bentsum_lean"]["banned_construct_findings"],
            "lean_file_sha256": ps["bentsum_lean"]["lean_file_sha256"],
            "scan_scope": "lexical_token_scan_not_lean_kernel_elaboration",
        },
        "blender_snf_witness_manifest": {
            "witness_sha256": ps["blender_snf_witness"]["witness_sha256"],
            "unshifted_count": ps["blender_snf_witness"]["unshifted_count"],
            "shifted_multi_count": ps["blender_snf_witness"]["shifted_multi_count"],
            "unshifted_snf_exps": ps["blender_snf_witness"]["unshifted_snf_exps"],
            "shifted_multi_snf_exps": ps["blender_snf_witness"]["shifted_multi_snf_exps"],
            "f2_xor_fail_count": ps["blender_snf_witness"]["f2_xor_fail_count"],
            "mod32_superposition_pass_count": ps["blender_snf_witness"]["mod32_superposition_pass_count"],
            "mod32_superposition_scope": "definitional_additive_identity_over_Z_mod_2_32",
        },
        "blender_issues_declared_text_flags": {
            "issue1_global_minimum_claim_present": biss["issue1_global_minimum_claim_present"],
            "issue2_sec33_w0246_in_x_notx_present": biss["issue2_sec33_w0246_in_x_notx_present"],
        },
        "conditional_issue_rulings": {
            "issue1_ruling": (
                "Given upstream Blender/paper/main.tex at pinned commit 57842cef stating "
                "'global minimum' for the two-step silent-carry healing family, Proposition 6 "
                "length arithmetic proves 24 bytes minimum only within that two-step family, "
                "not globally."
            ),
            "issue2_ruling": (
                "Given upstream Blender/paper/main.tex at pinned commit 57842cef sec. 3.3 "
                "stating 'steer W_0, W_2, W_4, W_6 in {x, ~x}', that prose conflicts with the "
                "Theorem 2 standard-IV parity invariant p_4 = p_0 ^ 1, whereas clean-room "
                "12-step entry stays on shifted phase constants obeying Theorem 2."
            ),
        },
        "tii_94_campaign_manifest": {
            "summary_sha256": ps["tii_94_summary"]["summary_sha256"],
            "total_solved": ps["tii_94_summary"]["total_solved"],
            "route_a_solved": ps["tii_94_summary"]["route_a_solved"],
            "route_b_solved": ps["tii_94_summary"]["route_b_solved"],
            "first_bloods": ps["tii_94_summary"]["first_bloods"],
        },
    }


# =============================================================================
# Pillar 1: BentSum Pure-Z Walsh-Hadamard & ANF Verification
# =============================================================================


def _fwht_exact(vals):
    """Exact integer Fast Walsh-Hadamard Transform."""
    a = list(vals)
    n = len(a)
    h = 1
    while h < n:
        step = h * 2
        for i in range(0, n, step):
            for j in range(i, i + h):
                u = a[j]
                v = a[j + h]
                a[j] = u + v
                a[j + h] = u - v
        h = step
    return a


def _anf_degree_exact(truth_table):
    """Exact algebraic normal form degree over F_2 via Mobius transform."""
    coeffs = list(truth_table)
    n = len(coeffs)
    h = 1
    while h < n:
        step = h * 2
        for i in range(0, n, step):
            for j in range(i, i + h):
                coeffs[j + h] ^= coeffs[j]
        h = step
    return max((idx.bit_count() for idx, v in enumerate(coeffs) if v), default=-1)


def audit_bentsum_walsh_exact(
    q3_tt=None,
    cyl4_tt=None,
    g8_tt=None,
    pos_r8=None,
    lift4_tt=None,
    g10_tt=None,
):
    """Pillar 1: Independent pure-Z Walsh-Hadamard & ANF verification of BentSum objects."""
    # 1. q3 on F_2^6: z0*z1 + z2*z3 + z4*z5
    if q3_tt is None:
        q3_tt = [
            (((z >> 0) & 1) & ((z >> 1) & 1))
            ^ (((z >> 2) & 1) & ((z >> 3) & 1))
            ^ (((z >> 4) & 1) & ((z >> 5) & 1))
            for z in range(64)
        ]
    q3_wt = sum(q3_tt)
    q3_deg = _anf_degree_exact(q3_tt)
    q3_walsh = _fwht_exact([1 - 2 * b for b in q3_tt])
    q3_is_bent = all(w * w == 64 for w in q3_walsh)

    # 2. cylQ3(4) on F_2^8: x0*x1*q3(x2..x7)
    if cyl4_tt is None:
        cyl4_tt = [
            (((x >> 0) & 1) & ((x >> 1) & 1)) & q3_tt[x >> 2]
            for x in range(256)
        ]
    cyl4_wt = sum(cyl4_tt)
    cyl4_deg = _anf_degree_exact(cyl4_tt)
    cyl4_in_coset = all((x & 3) == 3 for x, v in enumerate(cyl4_tt) if v == 1)
    cyl4_wt_mod8 = cyl4_wt % 8
    const_derivs = []
    for a in range(256):
        vals = {cyl4_tt[x] ^ cyl4_tt[x ^ a] for x in range(256)}
        if len(vals) == 1:
            const_derivs.append([a, next(iter(vals))])

    # 3. Positive bent-sum control inside same codimension-2 coset {x0=x1=1} on F_2^8
    if g8_tt is None:
        g8_tt = [
            (((x >> 0) & 1) & ((x >> 4) & 1))
            ^ (((x >> 1) & 1) & ((x >> 5) & 1))
            ^ (((x >> 2) & 1) & ((x >> 6) & 1))
            ^ (((x >> 3) & 1) & ((x >> 7) & 1))
            for x in range(256)
        ]
    if pos_r8 is None:
        pos_r8 = [((x >> 0) & 1) & ((x >> 1) & 1) & ((x >> 2) & 1) for x in range(256)]
    h8_tt = [g8_tt[x] ^ pos_r8[x] for x in range(256)]
    g8_bent = all(w * w == 256 for w in _fwht_exact([1 - 2 * b for b in g8_tt]))
    h8_bent = all(w * w == 256 for w in _fwht_exact([1 - 2 * b for b in h8_tt]))
    cyl4_plus_g8_bent = all(
        w * w == 256 for w in _fwht_exact([1 - 2 * (g8_tt[x] ^ cyl4_tt[x]) for x in range(256)])
    )
    phi8 = [(1 - 2 * g8_tt[x]) if pos_r8[x] else 0 for x in range(256)]
    wphi8 = _fwht_exact(phi8)
    wphi8_values_ok = set(wphi8) <= {0, 16, -16}
    zero_on_01 = [w for w in range(256) if (w & 3) == 0]
    parseval_n_even = sum(1 for w in zero_on_01 if wphi8[w] != 0)
    pos_r8_wt = sum(pos_r8)

    # 4. liftCylQ3(4) on F_2^10: x1 + cylQ3(4)(x2..x9)
    if lift4_tt is None:
        lift4_tt = [((x >> 1) & 1) ^ cyl4_tt[x >> 2] for x in range(1024)]
    lift4_wt = sum(lift4_tt)
    lift4_deg = _anf_degree_exact(lift4_tt)
    lift4_periods = [y for y in range(1024) if all(lift4_tt[x] == lift4_tt[x ^ y] for x in range(1024))]

    # 5. Positive bent-derivative control on F_2^10: g10(a,b,z) = a*b + a*pos_r8(z) + g8(z)
    if g10_tt is None:
        g10_tt = [
            (((x >> 0) & 1) & ((x >> 1) & 1)) ^ (((x >> 0) & 1) & pos_r8[x >> 2]) ^ g8_tt[x >> 2]
            for x in range(1024)
        ]
    g10_bent = all(w * w == 1024 for w in _fwht_exact([1 - 2 * b for b in g10_tt]))
    dg10_e0 = [g10_tt[x] ^ g10_tt[x ^ 1] for x in range(1024)]
    expected_dg10 = [((x >> 1) & 1) ^ pos_r8[x >> 2] for x in range(1024)]
    dg10_matches = dg10_e0 == expected_dg10

    checks = {
        "q3_is_bent": q3_is_bent,
        "q3_weight_28": q3_wt == 28,
        "q3_degree_2": q3_deg == 2,
        "cylq3_n8_weight_28": cyl4_wt == 28,
        "cylq3_n8_degree_4": cyl4_deg == 4,
        "cylq3_n8_in_codim2_coset": cyl4_in_coset,
        "cylq3_n8_weight_not_div_8": cyl4_wt_mod8 == 4,
        "cylq3_n8_only_zero_const_deriv": const_derivs == [[0, 0]],
        "cylq3_n8_plus_g8_not_bent": not cyl4_plus_g8_bent,
        "pos_ctrl_g8_bent": g8_bent,
        "pos_ctrl_h8_bent": h8_bent,
        "pos_ctrl_wphi_ternary": wphi8_values_ok,
        "pos_ctrl_parseval_N_even_8": parseval_n_even == 8,
        "pos_ctrl_weight_32_div_8": pos_r8_wt == 32,
        "liftcylq3_n10_balanced_512": lift4_wt == 512,
        "liftcylq3_n10_degree_4": lift4_deg == 4,
        "liftcylq3_n10_only_period_e0": lift4_periods == [0, 1],
        "pos_ctrl_g10_bent": g10_bent,
        "pos_ctrl_dg10_matches_lift": dg10_matches,
    }
    return {
        "claim_scope": "exact",
        "check_scopes": {k: "exact" for k in checks},
        "counterexample_scope_note": (
            "Tokareva's conjecture states every degree <= n/2 Boolean function on even n >= 4 "
            "is a sum of two bent functions. Python verifies exact finite n=6,8,10 hypotheses "
            "(cylQ3(4): deg=4=n/2, support in codim-2 coset, wt=28 not divisible by 8; "
            "liftCylQ3(4): balanced, deg=4=n/2-1, unique nonzero period e_0) and positive "
            "Maiorana-McFarland controls; the general weight-congruence theorem 2^(k+1) | wt(f) "
            "ruling out any bent-sum decomposition of cylQ3(4) is cited from arXiv:2610.32239."
        ),
        "q3_weight": q3_wt,
        "q3_degree": q3_deg,
        "q3_is_bent": q3_is_bent,
        "cylq3_n8_weight": cyl4_wt,
        "cylq3_n8_degree": cyl4_deg,
        "cylq3_n8_weight_mod_8": cyl4_wt_mod8,
        "cylq3_n8_const_deriv_count": len(const_derivs),
        "cylq3_n8_plus_g8_bent": cyl4_plus_g8_bent,
        "positive_bentsum_parseval_N": parseval_n_even,
        "positive_bentsum_weight": pos_r8_wt,
        "liftcylq3_n10_weight": lift4_wt,
        "liftcylq3_n10_degree": lift4_deg,
        "liftcylq3_n10_periods": lift4_periods,
        "checks": checks,
        "passed": all(checks.values()),
    }


# =============================================================================
# Pillar 2: Clean-Room Verification of ARADI, COLM, SBC-VOLE & Blender-256
# =============================================================================


def _rol16(x, n):
    n &= 15
    x &= 0xFFFF
    return (((x << n) | (x >> (16 - n))) & 0xFFFF) if n else x


def _aradi_linear_l(word, a, b, c):
    u = (word >> 16) & 0xFFFF
    lo = word & 0xFFFF
    nu = u ^ _rol16(u, a) ^ _rol16(lo, c)
    nl = lo ^ _rol16(lo, a) ^ _rol16(u, b)
    return ((nu << 16) | nl) & 0xFFFFFFFF


def _aradi_word_mat(a, b, c):
    mat = [[0] * 32 for _ in range(32)]
    for col in range(32):
        out = _aradi_linear_l(1 << col, a, b, c)
        for row in range(32):
            mat[row][col] = (out >> row) & 1
    return mat


def _gf2_mat_mul(a, b):
    n = len(a)
    return [[sum(a[r][k] & b[k][c] for k in range(n)) & 1 for c in range(n)] for r in range(n)]


def _gf2_is_id(a):
    n = len(a)
    return all(a[r][c] == (1 if r == c else 0) for r in range(n) for c in range(n))


def _aradi_cancel_dim(mat):
    rows = []
    for p in range(32):
        for q in range(32):
            if p == q:
                continue
            mask = 0
            for r in range(32):
                if mat[r][p] & mat[r][q]:
                    mask |= 1 << r
            if mask:
                rows.append(mask)
    return 32 - len(_gf2_rref_pivots(rows))


def _aradi_sbox_word(w, x, y, z):
    x ^= w & y
    z ^= x & y
    y ^= w & z
    w ^= x & z
    return w & 0xFFFFFFFF, x & 0xFFFFFFFF, y & 0xFFFFFFFF, z & 0xFFFFFFFF


def _audit_aradi_exact(
    rot_consts=STANDARD_ARADI_ROT_CONSTS,
    mitigation_rc=(7, 3, 11),
    sbox_tbl=None,
    num_rounds=5,
    seed=0x20261122A8AD1001,
    num_trials=2,
):
    """Clean-room NSA ARADI linear-layer algebra, blind-column audit & 198-eq certificate."""
    mats = [_aradi_word_mat(*rc) for rc in rot_consts]
    invol_all = all(_gf2_is_id(_gf2_mat_mul(m, m)) for m in mats)
    cancel_dims = [_aradi_cancel_dim(m) for m in mats]
    sym_flags = [m == _mat_t_z(m) for m in mats]
    orth_flags = [_gf2_is_id(_gf2_mat_mul(_mat_t_z(m), m)) for m in mats]

    # Connected components (islands) of L_3 derived directly from M_3 via BFS
    m3 = mats[3]
    seen = set()
    islands = []
    for start in range(32):
        if start in seen:
            continue
        comp = {start}
        queue = [start]
        while queue:
            node = queue.pop()
            for nb in range(32):
                if m3[node][nb] and nb not in comp:
                    comp.add(nb)
                    queue.append(nb)
        seen.update(comp)
        islands.append(sorted(comp))
    islands_len_8 = len(islands) == 8
    islands_size_4 = all(len(g) == 4 for g in islands)
    islands_ok = all((islands_len_8, islands_size_4))

    # S-box super-S-box ANF degrees (must collapse to deg 3, zero deg-4 wxyz term)
    if sbox_tbl is None:
        sbox_tbl = []
        for u in range(16):
            ow, ox, oy, oz = _aradi_sbox_word(u & 1, (u >> 1) & 1, (u >> 2) & 1, (u >> 3) & 1)
            sbox_tbl.append(ow | (ox << 1) | (oy << 2) | (oz << 3))
    super_x_tt = [((sbox_tbl[u] >> 1) & 1) ^ (((sbox_tbl[u] >> 0) & 1) & ((sbox_tbl[u] >> 2) & 1)) for u in range(16)]
    super_z_tt = [
        ((sbox_tbl[u] >> 3) & 1)
        ^ ((((sbox_tbl[u] >> 1) & 1) ^ ((sbox_tbl[u] >> 0) & 1)) & ((sbox_tbl[u] >> 2) & 1))
        for u in range(16)
    ]
    super_x_deg = _anf_degree_exact(super_x_tt)
    super_z_deg = _anf_degree_exact(super_z_tt)

    # LATINCRYPT 2025 blind-column audit across all 32 single-column differences at r0=0
    blind_counts = []
    for c0 in range(32):
        active = {c0}
        for r in (0, 1, 2):
            mr = mats[r]
            active = {row for row in range(32) if any(mr[row][col] for col in active)}
        dead = [col for col in range(32) if col not in active]
        covered = {col for k in dead for col in range(32) if m3[k][col]}
        blind_counts.append(32 - len(covered))
    blind_hist = {"8": blind_counts.count(8), "13": blind_counts.count(13)}

    # Analytical 198-equation 5-round zero-sum certificate on 48-point prefix of 6D cube
    or_shift = [[1 << (i | j) for j in range(64)] for i in range(64)]

    def mul_s64(s1, s2):
        res = 0
        m1 = s1
        while m1:
            lo1 = m1 & -m1
            row = or_shift[lo1.bit_length() - 1]
            m1 ^= lo1
            m2 = s2
            while m2:
                lo2 = m2 & -m2
                res |= row[lo2.bit_length() - 1]
                m2 ^= lo2
        return res

    cube_dirs = ((2, 15), (2, 17), (2, 22), (2, 25), (2, 30), (3, 30))
    st = [[1] * 32 for _ in range(4)]
    for t, (wi, bi) in enumerate(cube_dirs):
        st[wi][bi] |= 1 << (1 << t)
    for r in range(3):
        nw, nx, ny, nz = [0] * 32, [0] * 32, [0] * 32, [0] * 32
        for b in range(32):
            if (st[0][b] | st[1][b] | st[2][b] | st[3][b]) == 1:
                nw[b] = nx[b] = ny[b] = nz[b] = 1
            else:
                uw, ux, uy, uz = st[0][b] | 1, st[1][b] | 1, st[2][b] | 1, st[3][b] | 1
                wy = mul_s64(uw, uy)
                xy = mul_s64(ux, uy)
                xz = mul_s64(ux, uz)
                wz = mul_s64(uw, uz)
                nw[b] = uw | wy | xy | xz | mul_s64(wy, uz)
                nx[b] = ux | wy
                ny[b] = uy | wy | wz | mul_s64(ux, wy)
                nz[b] = uz | xy | wy
        mr = mats[r]
        nxt = []
        for ws in (nw, nx, ny, nz):
            out = [0] * 32
            for row in range(32):
                acc = 0
                mrow = mr[row]
                for col in range(32):
                    if mrow[col]:
                        acc |= ws[col]
                out[row] = acc
            nxt.append(out)
        st = nxt

    v_mono = [0] * 64
    for m in range(64):
        vec = 0
        for p in range(48):
            if (p & m) == m:
                vec |= 1 << p
        v_mono[m] = vec

    m0 = mats[0]
    equations = []
    island_nulls = []
    for grp in islands:
        col_mask = 0
        for c in range(32):
            if sum(m0[b][c] for b in grp) & 1:
                col_mask |= 1 << c
        supp_g = 1
        for b in grp:
            s1 = st[0][b] | st[1][b] | st[2][b] | st[3][b] | 1
            s2 = mul_s64(s1, s1)
            supp_g |= mul_s64(s2, s1)
        rows = [v_mono[m] for m in range(64) if (supp_g >> m) & 1]
        pivs = _gf2_rref_pivots(rows)
        null_basis = []
        for f in range(48):
            if f not in pivs:
                vec = 1 << f
                for p, pv in pivs.items():
                    if (pv >> f) & 1:
                        vec |= 1 << p
                null_basis.append(vec)
        island_nulls.append(len(null_basis))
        for pm in null_basis:
            equations.append((1, col_mask, pm))
            equations.append((3, col_mask, pm))

    # Sampled empirical zero-violation check on deterministic round-key trials
    prng = _SplitMix64(seed)
    violations = 0
    for _ in range(num_trials):
        base = [prng.next_u32() for _ in range(4)]
        rks = [[prng.next_u32() for _ in range(4)] for _ in range(num_rounds)]
        outs = []
        for p in range(48):
            w, x, y, z = base[0], base[1], base[2], base[3]
            for t, (wi, bi) in enumerate(cube_dirs):
                if (p >> t) & 1:
                    if wi == 2:
                        y ^= 1 << bi
                    else:
                        z ^= 1 << bi
            for step in range(num_rounds):
                rk = rks[step]
                w, x, y, z = _aradi_sbox_word(w ^ rk[0], x ^ rk[1], y ^ rk[2], z ^ rk[3])
                a, b, c = rot_consts[step & 3]
                w = _aradi_linear_l(w, a, b, c)
                x = _aradi_linear_l(x, a, b, c)
                y = _aradi_linear_l(y, a, b, c)
                z = _aradi_linear_l(z, a, b, c)
            outs.append((w, x, y, z))
        for row_idx, cm, pm in equations:
            acc = 0
            m_pm = pm
            while m_pm:
                lo = m_pm & -m_pm
                p_idx = lo.bit_length() - 1
                acc ^= (outs[p_idx][row_idx] & cm).bit_count() & 1
                m_pm ^= lo
            violations += acc

    # Mitigation L_3' = (7, 3, 11)
    m3p = _aradi_word_mat(*mitigation_rc)
    m3p_invol = _gf2_is_id(_gf2_mat_mul(m3p, m3p))
    m3p_cancel_dim = _aradi_cancel_dim(m3p)

    checks = {
        "all_L_involutive": invol_all,
        "cancel_dims_0_0_0_8": cancel_dims == [0, 0, 0, 8],
        "L3_only_symmetric": sym_flags == [False, False, False, True],
        "L3_only_orthogonal": orth_flags == [False, False, False, True],
        "L3_eight_4col_islands": islands_ok,
        "super_sbox_deg_x_3": super_x_deg == 3,
        "super_sbox_deg_z_3": super_z_deg == 3,
        "latincrypt_blind_hist_exact": blind_hist == {"8": 16, "13": 16},
        "zero_sum_eq_count_198": len(equations) == 198,
        "island_nullities_exact": island_nulls == [16, 12, 10, 12, 18, 0, 16, 15],
        "zero_empirical_violations": violations == 0,
        "mitigation_L3p_involutive": m3p_invol,
        "mitigation_L3p_zero_cancel": m3p_cancel_dim == 0,
    }
    check_scopes = {k: ("sampled" if k == "zero_empirical_violations" else "exact") for k in checks}
    return {
        "claim_scope": "exact_with_sampled_key_trials",
        "check_scopes": check_scopes,
        "sampling_metadata": {
            "seed": f"0x{seed:016x}",
            "trials": num_trials,
            "rounds": num_rounds,
            "equations_per_trial": len(equations),
            "total_equation_checks": num_trials * len(equations),
        },
        "all_L_involutive": invol_all,
        "cancel_mask_dims": cancel_dims,
        "L3_uniquely_symmetric_orthogonal": all((checks["L3_only_symmetric"], checks["L3_only_orthogonal"])),
        "L3_eight_4col_islands": islands_ok,
        "super_sbox_degrees": [super_x_deg, super_z_deg],
        "latincrypt2025_blind_column_hist": blind_hist,
        "analytical_zero_sum_eq_count": len(equations),
        "island_nullities": island_nulls,
        "empirical_violations_sampled": violations,
        "mitigation_L3p_involutive_zero_cancel": all((m3p_invol, m3p_cancel_dim == 0)),
        "checks": checks,
        "passed": all(checks.values()),
    }


def _audit_colm_exact(mod128=STANDARD_COLM_MOD128, alpha_const=3):
    """Clean-room COLM GF(2^128) Rabin irreducibility, transplant & COLM_tau obstruction."""
    mod128_irred = _gf2_poly_is_irred_pow2(mod128)

    def gmul(a, b):
        return _gf2_poly_mul_mod(a, b, mod128)

    inv_alpha = _gf2_poly_inv(alpha_const, mod128)
    inv3_ok = inv_alpha is not None and gmul(alpha_const, inv_alpha) == 1

    # Standard polynomial basis powers (definitional fade/rank controls kept out of checks)
    pows = [1]
    for _ in range(130):
        pows.append(gmul(pows[-1], 2))
    fade_sum = 0
    for k in (1, 2, 3, 8, 129):
        fade_sum ^= pows[k - 1]
    rank_128 = len(_gf2_rref_pivots(pows[:128]))
    rank_129 = len(_gf2_rref_pivots(pows[:129]))

    # Transplant condition (C): deg(x^(m-1)/alpha) <= m-2 first holds at m=129
    first_m = None
    transplant_set = []
    colm_tau_blocked = False
    if inv3_ok:
        for m in range(2, 140):
            u = gmul(inv_alpha, pows[m - 1])
            deg_u = u.bit_length() - 1
            if deg_u <= m - 2:
                first_m = m
                break
        a128 = gmul(inv_alpha, pows[128])
        transplant_set = sorted([i + 1 for i in range(128) if (a128 >> i) & 1] + [129, 130])
        colm_tau_blocked = all((gmul(pows[tau], inv_alpha).bit_length() - 1) == 127 for tau in range(1, 128))

    # Literature anchor arithmetic for J. Cryptol. 2024 Theorem 2 at (q=2, s=1, a=6, m=390)
    sigma24 = 6 + 2 * 390 + 3 * (2 + 1)
    num24 = 7 * sigma24 * sigma24 + 3 * sigma24 + 2 * 1 + 3 * 1 + 2 * 1 * sigma24
    bound24 = Fraction(num24, 1 << 128)
    exceeds_2_105 = bound24 < Fraction(1, 1 << 105)

    checks = {
        "mod128_irreducible": mod128_irred,
        "inv3_exact": inv3_ok,
        "transplant_first_m_129": first_m == 129,
        "transplant_set_exact": transplant_set == [1, 3, 4, 5, 6, 7, 129, 130],
        "colm_tau_blocked": colm_tau_blocked,
    }
    return {
        "claim_scope": "exact",
        "check_scopes": {k: "exact" for k in checks},
        "mod128_irreducible": mod128_irred,
        "inv3_exact": inv3_ok,
        "transplant_first_m": first_m,
        "transplant_set": transplant_set,
        "colm_tau_1_to_127_all_blocked": colm_tau_blocked,
        "definitional_controls": {
            "scope": "definitional",
            "excluded_from_checks": True,
            "fade_sum_zero": fade_sum == 0,
            "fade_rank_128_and_129": [rank_128, rank_129],
            "note": "Fade sum is the defining polynomial x^128+x^7+x^2+x+1; ranks 128/128 hold in any polynomial basis.",
        },
        "literature_anchor": {
            "scope": "anchor",
            "excluded_from_checks": True,
            "joc2024_params": {"q": 2, "s": 1, "a": 6, "m": 390},
            "joc2024_sigma": sigma24,
            "joc2024_thm2_bound_num": num24,
            "joc2024_thm2_bound_lt_2_neg105": exceeds_2_105,
        },
        "checks": checks,
        "passed": all(checks.values()),
    }


def _audit_sbcvole_exact(
    mod257=STANDARD_SBCVOLE_MOD257,
    seed=0x202611220109ABCD,
    corrupt_v_last=0,
    corrupt_bval=0,
    zero_linear_cols=False,
):
    """Clean-room SBC-VOLE GF(2^257) irreducibility & sampled 1-signature 256-bit key recovery."""
    k_deg = 257
    mask257 = (1 << 257) - 1
    use_fast = mod257 == STANDARD_SBCVOLE_MOD257

    sq_tbl = [0] * 256
    for v_b in range(256):
        s_b = 0
        for bit_i in range(8):
            if (v_b >> bit_i) & 1:
                s_b |= 1 << (2 * bit_i)
        sq_tbl[v_b] = s_b

    def gf_reduce(prod):
        if use_fast:
            hi = prod >> 257
            prod = (prod & mask257) ^ hi ^ (hi << 12)
            hi = prod >> 257
            if hi:
                prod = (prod & mask257) ^ hi ^ (hi << 12)
            return prod
        return _gf2_poly_mod(prod, mod257)

    def gf_sq(a):
        prod = 0
        sh = 0
        while a:
            prod |= sq_tbl[a & 255] << sh
            a >>= 8
            sh += 16
        return gf_reduce(prod)

    def gf_mul(a, b):
        a1 = a
        a2 = a1 << 1
        a4 = a1 << 2
        a8 = a1 << 3
        a3 = a1 ^ a2
        a5 = a4 ^ a1
        a6 = a4 ^ a2
        a7 = a4 ^ a3
        tbl = (0, a1, a2, a3, a4, a5, a6, a7, a8, a8 ^ a1, a8 ^ a2, a8 ^ a3, a8 ^ a4, a8 ^ a5, a8 ^ a6, a8 ^ a7)
        prod = 0
        sh = 0
        while b:
            nib = b & 15
            if nib:
                prod ^= tbl[nib] << sh
            b >>= 4
            sh += 4
        return gf_reduce(prod)

    # Irreducibility of mod257 (257 is prime => degree-257 poly with f(0)=1 is irreducible iff x^(2^257) == x)
    irred_ok = False
    if mod257.bit_length() - 1 == k_deg and (mod257 & 1) == 1:
        frob = 2
        for _ in range(k_deg):
            frob = gf_sq(frob)
        irred_ok = frob == 2

    def vdot(vec, bits):
        s = 0
        for i, bit in enumerate(bits):
            if bit:
                s ^= vec[i]
        return s

    prng = _SplitMix64(seed)
    x_bits = [(prng.next_u64() >> (i & 63)) & 1 for i in range(128)]
    y_bits = [(prng.next_u64() >> (i & 63)) & 1 for i in range(128)]
    u = [prng.next_bits(k_deg) for _ in range(130)]
    v = [prng.next_bits(k_deg) for _ in range(129)]
    xp = x_bits + [1, 0]
    yp = y_bits + [0, 1]
    uxp = vdot(u, xp)
    uyp = vdot(u, yp)
    vxp = vdot(v + [0], xp)
    inv_uxp = _gf2_poly_inv(uxp, mod257)
    if inv_uxp is None:
        v_last = 0
        nsbc_planted = False
    else:
        v_last = gf_mul(gf_mul(uyp, vxp), inv_uxp) ^ vdot(v + [0], y_bits) ^ corrupt_v_last
        v.append(v_last)
        vyp = vdot(v, yp)
        nsbc_planted = gf_mul(uxp, vyp) == gf_mul(uyp, vxp)

    if len(v) < 130:
        v.append(0)
        vyp = vdot(v, yp)

    afx = [prng.next_bits(k_deg) for _ in range(128)]
    afy = [prng.next_bits(k_deg) for _ in range(128)]
    delta = prng.next_bits(k_deg) | 1
    fx = [afx[i] ^ (delta if x_bits[i] else 0) for i in range(128)]
    fy = [afy[i] ^ (delta if y_bits[i] else 0) for i in range(128)]
    ua0, va0, ub0, vb0 = 0, 0, 0, 0
    for i in range(128):
        ua0 ^= gf_mul(u[i], afx[i])
        va0 ^= gf_mul(v[i], afx[i])
        ub0 ^= gf_mul(u[i], afy[i])
        vb0 ^= gf_mul(v[i], afy[i])
    bval = (gf_mul(ua0, vyp) ^ gf_mul(uxp, vb0) ^ gf_mul(ub0, vxp) ^ gf_mul(uyp, va0)) ^ corrupt_bval

    c_u, e_v, f_u, d_v = u[128], v[128], u[129], v[129]
    ux, vx, uy, vy = 0, 0, 0, 0
    for i in range(128):
        ux ^= gf_mul(u[i], fx[i])
        vx ^= gf_mul(v[i], fx[i])
        uy ^= gf_mul(u[i], fy[i])
        vy ^= gf_mul(v[i], fy[i])
    cp = vy ^ gf_mul(delta, d_v)
    cq = uy ^ gf_mul(delta, f_u)
    cr = vx ^ gf_mul(delta, e_v)
    cs = ux ^ gf_mul(delta, c_u)
    rhs = bval ^ gf_mul(ux, d_v) ^ gf_mul(vx, f_u) ^ gf_mul(vy, c_u) ^ gf_mul(uy, e_v)
    if zero_linear_cols:
        cols = [0] * 256
    else:
        cols = [gf_mul(cp, u[i]) ^ gf_mul(cq, v[i]) for i in range(128)]
        cols.extend(gf_mul(cr, u[i]) ^ gf_mul(cs, v[i]) for i in range(128))

    piv = {}
    low_mask = (1 << 256) - 1
    for bit in range(k_deg):
        row = ((rhs >> bit) & 1) << 256
        for j, col in enumerate(cols):
            if (col >> bit) & 1:
                row |= 1 << j
        while row & low_mask:
            p = (row & low_mask).bit_length() - 1
            if p in piv:
                row ^= piv[p]
            else:
                piv[p] = row
                break
    for p in sorted(piv):
        pv = piv[p]
        for q in sorted(piv):
            if q != p and ((piv[q] >> p) & 1):
                piv[q] ^= pv

    free_cols = [j for j in range(256) if j not in piv]
    base_sol = 0
    for p, row in piv.items():
        if (row >> 256) & 1:
            base_sol |= 1 << p
    ker_vecs = []
    for fc in free_cols:
        kv = 1 << fc
        for p, row in piv.items():
            if (row >> fc) & 1:
                kv |= 1 << p
        ker_vecs.append(kv)

    recovered = None
    if len(ker_vecs) <= 12:
        for mask in range(1 << len(ker_vecs)):
            cand = base_sol
            for idx, kv in enumerate(ker_vecs):
                if (mask >> idx) & 1:
                    cand ^= kv
            xb = [(cand >> i) & 1 for i in range(128)] + [1, 0]
            yb = [(cand >> (128 + i)) & 1 for i in range(128)] + [0, 1]
            if gf_mul(vdot(u, xb), vdot(v, yb)) == gf_mul(vdot(u, yb), vdot(v, xb)):
                recovered = cand
                break
    true_bits = sum(bit << i for i, bit in enumerate(x_bits + y_bits))
    exact_recovered = recovered == true_bits

    checks = {
        "modulus_irreducible": irred_ok,
        "nsbc_planted": nsbc_planted,
        "linear_rank_ge_254": len(piv) >= 254,
        "secret_256bit_recovered_exact": exact_recovered,
    }
    check_scopes = {
        "modulus_irreducible": "exact",
        "nsbc_planted": "sampled",
        "linear_rank_ge_254": "sampled",
        "secret_256bit_recovered_exact": "sampled",
    }
    return {
        "claim_scope": "sampled",
        "check_scopes": check_scopes,
        "sampling_metadata": {
            "seed": f"0x{seed:016x}",
            "trials": 1,
            "note": (
                "gf2_linear_rank=255 and free_nullity=1 are specific to this single seeded "
                "SplitMix64 trial; other seeds frequently yield full rank 256 (free_nullity=0)."
            ),
        },
        "field_degree": k_deg,
        "modulus_irreducible": irred_ok,
        "nsbc_planted": nsbc_planted,
        "gf2_linear_rank": len(piv),
        "free_nullity": len(free_cols),
        "secret_256bit_recovered_exact": exact_recovered,
        "checks": checks,
        "passed": all(checks.values()),
    }


def _audit_blender_exact(
    iv=STANDARD_BLENDER_IV256,
    seed=0x20261122B1E4DE25,
    stream_steps=24,
    shift_list=(1, 0x13579BDF),
    truncate_unsh_vectors=None,
):
    """Clean-room Blender-256 standard-IV Theorem 2 parity stream & from-IV 2-adic SNF closure."""
    m32 = 0xFFFFFFFF

    def ror32(x, n):
        return ((x >> n) | ((x << (32 - n)) & m32)) & m32

    def rol32(x, n):
        return (((x << n) & m32) | (x >> (32 - n))) & m32

    def step256(w_arr, c1, c2, frag):
        s2 = (ror32(frag, 8) ^ w_arr[0]) + (ror32(w_arr[2], 8) ^ w_arr[4]) + c2
        t2, k2 = s2 & m32, s2 >> 32
        s1 = (frag ^ w_arr[5]) + (rol32(w_arr[3], 8) ^ w_arr[1]) + c1
        t1, k1 = s1 & m32, s1 >> 32
        rot = 7 if (k1 ^ k2) else (8 if k1 == 0 else 6)
        t1 = rol32(t1, rot)
        t2 = ror32(t2, rot)
        masks = (t2, t1)
        nw = [w_arr[i + 1] ^ masks[i & 1] for i in range(7)] + [ror32(w_arr[0], 7) ^ masks[1]]
        return nw, k1, k2

    # 1. Sampled 24-step stream from the given start state (standard IV by default)
    prng = _SplitMix64(seed)
    w_cur = list(iv)
    c1, c2 = 0, 0
    orbit = []
    for _ in range(stream_steps):
        pvec = tuple((w_cur[i] ^ w_cur[i + 2]).bit_count() & 1 for i in range(6))
        orbit.append(pvec)
        w_cur, c1, c2 = step256(w_cur, c1, c2, prng.next_u32())
    base_orbit = orbit[:8]
    thm2_period8 = all((
        len(orbit) >= 24,
        orbit[8:16] == base_orbit,
        orbit[16:24] == base_orbit,
        len(set(base_orbit)) == 8,
    ))
    thm2_permanent_invariants = all(
        all((pv[4] == (pv[0] ^ 1), pv[5] == (pv[1] ^ 1))) for pv in orbit
    )

    # 2. Clean-room 12-step entry & 8-step orbit DFS from start state
    def find_clean_orbit(shift_x):
        stack = [(list(iv), 0, 0, [])]
        while stack:
            w_s, sc1, sc2, hist = stack.pop()
            if len(hist) == 20:
                return hist[11], [[w[i] ^ w[i & 1] for i in range(8)] for w in hist[12:20]]
            kids = []
            for tgt in (shift_x, shift_x ^ m32):
                goal = w_s[1] ^ tgt
                k2_add = ror32(w_s[2], 8) ^ w_s[4]
                for rot in (6, 7, 8):
                    frag = rol32(((rol32(goal, rot) - k2_add - sc2) & m32) ^ w_s[0], 8)
                    nw, nk1, nk2 = step256(w_s, sc1, sc2, frag)
                    if nw[0] == tgt:
                        kids.append((nw, nk1, nk2))
            for nw, nk1, nk2 in reversed(kids):
                stack.append((nw, nk1, nk2, hist + [nw]))
        raise MinimaxCryptError("ORBIT_FAILED", f"no clean orbit for shift {shift_x}")

    w_entry0, d_unsh = find_clean_orbit(0)
    entry_pvec = tuple((w_entry0[i] ^ w_entry0[i + 2]).bit_count() & 1 for i in range(6))
    entry_obeys_thm2 = all((entry_pvec[4] == (entry_pvec[0] ^ 1), entry_pvec[5] == (entry_pvec[1] ^ 1)))
    entry_refutes_sec33_prose = not all(w_entry0[i] in (0, m32) for i in (0, 2, 4, 6))

    # 3. Definitional controls (kept strictly outside checks / all_gates_passed)
    issue2_even_xor_parity = all((((0).bit_count() & 1) == 0, (m32.bit_count() & 1) == 0))
    prefix_words_min = (13 + 3) // 4
    two_step_min_bytes = (prefix_words_min + 2) * 4

    # 4. From-IV 2-adic SNF subgroup closure: unshifted [0,0,1,1,2,2,3,3] -> multi-shifted [0,0,1,1,1,1,1,1]
    d_unsh_used = d_unsh[:truncate_unsh_vectors] if truncate_unsh_vectors is not None else d_unsh
    even0, odd0 = [], []
    for d_vec in d_unsh_used:
        even0.append([(-1 - 2 * d_vec[i]) & m32 for i in (0, 2, 4, 6)])
        for bit in range(32):
            sc = 1 << bit
            odd0.append([(sc * (1 - 2 * ((d_vec[i] >> bit) & 1))) & m32 for i in (1, 3, 5, 7)])
    snf_from_iv_unsh = sorted(snf_2adic_valuations_exact(even0, 32) + snf_2adic_valuations_exact(odd0, 32))

    even_m = list(even0)
    odd_m = list(odd0)
    for shift_a in shift_list:
        _, d_sh = find_clean_orbit(shift_a)
        for d_vec in d_sh:
            even_m.append([(((shift_a ^ m32) ^ d_vec[i]) - (shift_a ^ d_vec[i])) & m32 for i in (0, 2, 4, 6)])
            for bit in range(32):
                sc = 1 << bit
                odd_m.append([(sc * (1 - 2 * ((d_vec[i] >> bit) & 1))) & m32 for i in (1, 3, 5, 7)])
    snf_from_iv_multi = sorted(snf_2adic_valuations_exact(even_m, 32) + snf_2adic_valuations_exact(odd_m, 32))

    checks = {
        "thm2_period8": thm2_period8,
        "thm2_permanent_invariants": thm2_permanent_invariants,
        "entry_obeys_thm2": entry_obeys_thm2,
        "entry_refutes_sec33_prose": entry_refutes_sec33_prose,
        "snf_from_iv_unshifted_exact": snf_from_iv_unsh == [0, 0, 1, 1, 2, 2, 3, 3],
        "snf_from_iv_multi_shifted_exact": snf_from_iv_multi == [0, 0, 1, 1, 1, 1, 1, 1],
    }
    check_scopes = {
        "thm2_period8": "sampled",
        "thm2_permanent_invariants": "sampled",
        "entry_obeys_thm2": "exact",
        "entry_refutes_sec33_prose": "exact",
        "snf_from_iv_unshifted_exact": "exact",
        "snf_from_iv_multi_shifted_exact": "exact",
    }
    return {
        "claim_scope": "sampled_and_standard_iv_exact",
        "check_scopes": check_scopes,
        "sampling_metadata": {
            "start_state": "standard_blender256_iv_only",
            "seed": f"0x{seed:016x}",
            "stream_steps": stream_steps,
            "trials": 1,
            "note": (
                "Theorem 2 invariants p_4 = p_0 ^ 1, p_5 = p_1 ^ 1 are tied to the standard "
                "Blender-256 IV (arbitrary start states break them) and are checked here on "
                "one 24-step deterministic message stream."
            ),
        },
        "definitional_controls": {
            "scope": "definitional",
            "excluded_from_checks": True,
            "issue2_even_xor_parity_wt0_wt32": issue2_even_xor_parity,
            "prop6_two_step_min_bytes": two_step_min_bytes,
        },
        "thm2_iv_parity": list(base_orbit[0]),
        "thm2_period_8_and_permanent_invariants": all((thm2_period8, thm2_permanent_invariants)),
        "snf_from_iv_unshifted": snf_from_iv_unsh,
        "snf_from_iv_multi_shifted": snf_from_iv_multi,
        "checks": checks,
        "passed": all(checks.values()),
    }


def audit_fast_algebraic_and_blender_exact():
    """Pillar 2: Clean-room computational verification of ARADI, COLM, SBC-VOLE & Blender-256."""
    aradi = _audit_aradi_exact()
    colm = _audit_colm_exact()
    sbcvole = _audit_sbcvole_exact()
    blender = _audit_blender_exact()
    checks = {
        "aradi_verified": aradi["passed"],
        "colm_verified": colm["passed"],
        "sbcvole_verified": sbcvole["passed"],
        "blender_computed_verified": blender["passed"],
    }
    return {
        "aradi": aradi,
        "colm": colm,
        "sbcvole": sbcvole,
        "blender": blender,
        "checks": checks,
        "passed": all(checks.values()),
    }


# =============================================================================
# Pillar 3: Background Algebraic Identities Verified in This Audit
#           (Binary Goppa Shortening & Parity-Sublattice Gram Determinants)
# =============================================================================


def _goppa_codewords_exact(support, g_poly, m_deg, mul5, inv5, eval5):
    """Build exact binary Goppa code Gamma(support, g_poly) parity-check nullspace & full codeword set."""
    n_len = len(support)
    t_deg = len(g_poly) - 1
    hraw = [0] * (m_deg * t_deg)
    for j, z in enumerate(support):
        gv = eval5(g_poly, z)
        if gv == 0:
            return [], set()
        ig = inv5[gv]
        zp = 1
        for i in range(t_deg):
            e = mul5(zp, ig)
            for bit in range(m_deg):
                if (e >> bit) & 1:
                    hraw[m_deg * i + bit] |= 1 << j
            zp = mul5(zp, z)

    pivs = []
    rest = list(hraw)
    acc = []
    for col in range(n_len):
        bit = 1 << col
        idx = next((i for i, r in enumerate(rest) if r & bit), None)
        if idx is None:
            continue
        p_row = rest.pop(idx)
        acc = [(r ^ p_row) if (r & bit) else r for r in acc]
        rest = [(r ^ p_row) if (r & bit) else r for r in rest]
        acc.append(p_row)
        pivs.append(col)
    pset = set(pivs)
    free_cols = [c for c in range(n_len) if c not in pset]
    ker_basis = []
    for fc in free_cols:
        v = 1 << fc
        for r, pc in zip(acc, pivs):
            if (r >> fc) & 1:
                v |= 1 << pc
        ker_basis.append(v)

    codewords = {0}
    for mask in range(1, 1 << len(ker_basis)):
        cw = 0
        for idx, bv in enumerate(ker_basis):
            if (mask >> idx) & 1:
                cw ^= bv
        codewords.add(cw)
    return ker_basis, codewords


def _audit_tii_goppa_identity_exact(
    g_poly=STANDARD_GOPPA_POLY,
    n_len=24,
    short_n=21,
    support_l=None,
    verify_g_poly=None,
    short_support_override=None,
):
    """Clean-room GF(2^5) binary Goppa Theorem 1 & exact full-code primal shortening identity."""
    mod5 = 0b100101  # x^5 + x^2 + 1 irreducible over GF(2)

    def mul5(a, b):
        r = 0
        while b:
            if b & 1:
                r ^= a
            b >>= 1
            a <<= 1
            if a >> 5:
                a ^= mod5
        return r

    inv5 = [0] * 32
    for a in range(1, 32):
        for b in range(1, 32):
            if mul5(a, b) == 1:
                inv5[a] = b
                break

    def eval5(poly, z):
        acc = 0
        for coeff in reversed(poly):
            acc = mul5(acc, z) ^ coeff
        return acc

    def pmul5(p, q):
        r = [0] * (len(p) + len(q) - 1)
        for i, a in enumerate(p):
            for j, b in enumerate(q):
                r[i + j] ^= mul5(a, b)
        return r

    def pderiv5(p):
        return [p[i] if (i & 1) else 0 for i in range(1, len(p))]

    g_list = list(g_poly)
    m_deg = 5
    t_deg = len(g_list) - 1
    no_roots = all(eval5(g_list, z) != 0 for z in range(32))
    if support_l is None:
        support_l = list(range(n_len))

    ker_basis, full_codewords = _goppa_codewords_exact(support_l, g_list, m_deg, mul5, inv5, eval5)
    w_min = 2 * t_deg + 1
    min_cws = sorted(cw for cw in full_codewords if cw.bit_count() == w_min)

    # Verify Theorem 1 (sigma'_S(X) == g(X)^2, e_2(z_S) == g_{t-1}^2) on ALL min-weight codewords
    g_check = list(verify_g_poly) if verify_g_poly is not None else g_list
    g_sq = pmul5(g_check, g_check)
    gt1_sq = mul5(g_check[t_deg - 1], g_check[t_deg - 1])
    sig_derivs = []
    e2_vals = []
    for cw in min_cws:
        sup = [j for j in range(len(support_l)) if (cw >> j) & 1]
        sigma = [1]
        e2 = 0
        for ui in range(len(sup)):
            zu = support_l[sup[ui]]
            sigma = pmul5(sigma, [zu, 1])
            for vi in range(ui + 1, len(sup)):
                e2 ^= mul5(zu, support_l[sup[vi]])
        sig_derivs.append(pderiv5(sigma))
        e2_vals.append(e2)
    thm1_deriv_all = bool(min_cws) and all(sd == g_sq for sd in sig_derivs)
    thm1_e2_all = bool(min_cws) and all(e2 == gt1_sq for e2 in e2_vals)
    thm1_all = all((thm1_deriv_all, thm1_e2_all))
    pair_parity_ok = ((w_min * (w_min - 1) // 2) & 1) == (t_deg & 1)

    # Primal shortening n'=short_n: explicitly verify shortened code == Gamma(L', g) as full sets
    shortened_code_set = {cw for cw in full_codewords if (cw >> short_n) == 0}
    short_support = list(short_support_override) if short_support_override is not None else support_l[:short_n]
    direct_short_basis, direct_short_code_set = _goppa_codewords_exact(
        short_support, g_check, m_deg, mul5, inv5, eval5
    )
    shortened_equals_goppa = bool(direct_short_basis) and shortened_code_set == direct_short_code_set
    short_cws = [cw for cw in min_cws if (cw >> short_n) == 0]

    def f_quad(d):
        return 1 + d + (d * (d - 1)) // 2

    # Literature anchor arithmetic for published TII-125 and TII-250 shortening parameters
    f125_full = f_quad(507 - 9 * 7 - 1)
    f125_short = f_quad(237 - 9 * 7 - 1)
    ratio_125 = Fraction(f125_full, f125_short)

    f250_full = f_quad(1010 - 10 * 12 - 1)
    f250_short = f_quad(467 - 10 * 12 - 1)
    ratio_250 = Fraction(f250_full, f250_short)

    checks = {
        "goppa_no_roots": no_roots,
        "mini_dim_9": len(ker_basis) == 9,
        "mini_min_weight_13": len(min_cws) == 13,
        "mini_short_n21_dim_6": len(direct_short_basis) == 6 and len(shortened_code_set) == 64,
        "mini_short_n21_min_weight_6": len(short_cws) == 6,
        "shortened_equals_goppa_on_shorter_support": shortened_equals_goppa,
        "thm1_locator_deriv_square": thm1_deriv_all,
        "thm1_e2_equals_gt1_sq": thm1_e2_all,
    }
    return {
        "claim_scope": "exact",
        "check_scopes": {k: "exact" for k in checks},
        "scope_note": (
            "Background binary Goppa (GF(2) subfield subcode over GF(2^5)) algebraic identity "
            "verified in this audit; math0 code-table entries target GF(3)..GF(9), and no code "
            "in this study reads or modifies objects in other repositories."
        ),
        "mini_goppa_params": {"n": len(support_l), "m": m_deg, "t": t_deg, "k": len(ker_basis)},
        "mini_goppa_min_weight_7_count": len(min_cws),
        "mini_goppa_shortened_n21_dim": len(direct_short_basis),
        "mini_goppa_shortened_n21_codeword_count": len(shortened_code_set),
        "mini_goppa_shortened_n21_min_weight_count": len(short_cws),
        "shortened_code_equals_goppa_on_shorter_support": shortened_equals_goppa,
        "theorem1_locator_deriv_square_all_cws": thm1_all,
        "definitional_controls": {
            "scope": "definitional",
            "excluded_from_checks": True,
            "theorem2_odd_pair_parity_exact": pair_parity_ok,
        },
        "literature_anchors": {
            "scope": "anchor",
            "excluded_from_checks": True,
            "tii125_params": {"n": 507, "m": 9, "t": 7, "n_short": 237},
            "tii125_F_full_and_short": [f125_full, f125_short],
            "tii125_compression_exact": frac_str(ratio_125),
            "tii125_compression_dec6": format_exact_decimal(ratio_125),
            "tii250_params": {"n": 1010, "m": 10, "t": 12, "n_short": 467},
            "tii250_F_full_and_short": [f250_full, f250_short],
            "tii250_compression_exact": frac_str(ratio_250),
            "tii250_compression_dec6": format_exact_decimal(ratio_250),
        },
        "checks": checks,
        "passed": all(checks.values()),
    }


def _audit_hawk_lattice_identity_exact(
    b_good=None,
    u_bad=None,
    u_parity=STANDARD_HAWK_PARITY,
    h_override=None,
    u_rec_override=None,
):
    """Clean-room rank-8 parity-sublattice generation, Gram-determinant law & blind exact LLL."""
    if b_good is None:
        b_good = [
            [3, 0, 0, 0, 0, 0, 0, 0],
            [1, 3, 0, 0, 0, 0, 0, 0],
            [-1, 1, 4, 0, 0, 0, 0, 0],
            [0, -1, 1, 4, 0, 0, 0, 0],
            [1, 0, -1, 1, 5, 0, 0, 0],
            [-1, 1, 0, -1, 1, 5, 0, 0],
            [0, -1, 1, 0, -1, 1, 6, 0],
            [1, 0, -1, 1, 0, -1, 1, 6],
        ]
    if u_bad is None:
        u_bad = [[1 if i == j else 0 for j in range(8)] for i in range(8)]
        for i in range(8):
            for j in range(i):
                u_bad[i][j] = (i - j) * 7 if ((i + j) & 1) == 0 else -(i - j) * 5

    b_raw = _mat_mul_z(u_bad, b_good)
    g_raw = _mat_mul_z(b_raw, _mat_t_z(b_raw))

    # 1. Exact planted inverse recovery via triangular backward substitution (uses b_good)
    if u_rec_override is not None:
        u_rec = [list(r) for r in u_rec_override]
        exact_div_all = True
    else:
        u_rec = []
        exact_div_all = True
        for r in range(8):
            b_row = b_good[r]
            u_row = [0] * 8
            for i in range(7, -1, -1):
                acc = b_row[i] - sum(u_row[j] * b_raw[j][i] for j in range(i + 1, 8))
                if b_raw[i][i] == 0:
                    exact_div_all = False
                    u_row[i] = 0
                else:
                    q, rem = divmod(acc, b_raw[i][i])
                    if rem != 0:
                        exact_div_all = False
                    u_row[i] = q
            u_rec.append(u_row)

    u_rec_exact = all((exact_div_all, _mat_mul_z(u_rec, b_raw) == b_good))
    det_u_abs = abs(_bareiss_det_exact(u_rec))
    g_red = _mat_mul_z(_mat_mul_z(u_rec, g_raw), _mat_t_z(u_rec))
    det_raw = _bareiss_det_exact(g_raw)
    det_red = _bareiss_det_exact(g_red)
    max_diag_raw = max(g_raw[i][i] for i in range(8))
    max_diag_red = max(g_red[i][i] for i in range(8))
    diag_compression = Fraction(max_diag_raw, max_diag_red) if max_diag_red > 0 else Fraction(0, 1)

    # 2. Blind exact pure-Q LLL reduction on b_raw (does NOT receive b_good)
    b_lll, u_lll = _exact_lll_reduce(b_raw)
    g_lll = _mat_mul_z(b_lll, _mat_t_z(b_lll))
    det_u_lll_abs = abs(_bareiss_det_exact(u_lll))
    det_lll = _bareiss_det_exact(g_lll)
    lll_unimodular_exact = all((
        _mat_mul_z(u_lll, b_raw) == b_lll,
        det_u_lll_abs == 1,
        det_lll == det_raw,
        det_lll > 0,
    ))
    max_diag_lll = max(g_lll[i][i] for i in range(8))

    # 3. Parity-congruence sublattice Lambda' = 2*Z^8 + Z*u_parity (index 2^(n-1) = 128 at n=8)
    u_par = [x & 1 for x in u_parity]
    if h_override is not None:
        h_sub = [list(r) for r in h_override]
    else:
        j0 = u_par.index(1)
        h_sub = [[u_par[jj] if i == j0 else (2 if i == jj else 0) for jj in range(8)] for i in range(8)]
    det_h_abs = abs(_bareiss_det_exact(h_sub))
    zero_par = [0] * 8
    rows_in_parity_sublattice = all([x & 1 for x in row] in (zero_par, u_par) for row in h_sub)
    h_generates_parity_sublattice = all((
        any(u_par),
        rows_in_parity_sublattice,
        det_h_abs == 128,
    ))
    g_prime = _mat_mul_z(_mat_mul_z(h_sub, g_red), _mat_t_z(h_sub))
    det_g_prime = _bareiss_det_exact(g_prime)
    det_scaling_exact = det_red > 0 and det_g_prime == (1 << 14) * det_red

    # Literature anchor arithmetic (outside checks / all_gates_passed)
    beta_drops = {
        "HAWK-256": 92 - 58,
        "HAWK-512": 205 - 156,
        "HAWK-1024": 432 - 351,
    }
    hawk256_hermite_ratio = Fraction(4222, 10000)

    checks = {
        "unimodular_planted_inverse_exact": u_rec_exact,
        "abs_det_U_1": det_u_abs == 1,
        "gram_det_equal": det_raw == det_red,
        "gram_det_positive": det_red > 0,
        "max_diag_raw_31954": max_diag_raw == 31954,
        "max_diag_red_41": max_diag_red == 41,
        "lll_unimodular_and_exact": lll_unimodular_exact,
        "lll_blind_recovers_max_diag_41": max_diag_lll == 41,
        "h_generates_parity_sublattice": h_generates_parity_sublattice,
        "parity_sublattice_index_128": det_h_abs == 128,
        "gram_prime_det_scaling": det_scaling_exact,
    }
    return {
        "claim_scope": "exact",
        "check_scopes": {k: "exact" for k in checks},
        "scope_note": (
            "Background parity-sublattice and Gram-determinant identities verified in this audit "
            "(det(H G H^T) = (det H)^2 det(G) is a standard algebraic identity; h_generates_parity_sublattice "
            "additionally verifies H Z^8 = 2 Z^8 + Z u_parity, and exact LLL recovers max diagonal 41 from "
            "B_raw without B_good). No code in this study targets external quantization codebases."
        ),
        "rank_n": 8,
        "unimodular_planted_inverse_exact": u_rec_exact,
        "abs_det_U": det_u_abs,
        "gram_det_invariant": all((det_raw == det_red, det_red > 0)),
        "max_gram_diag_raw": max_diag_raw,
        "max_gram_diag_reduced": max_diag_red,
        "gram_diag_compression_exact": frac_str(diag_compression),
        "lll_blind_max_gram_diag": max_diag_lll,
        "lll_abs_det_U": det_u_lll_abs,
        "h_generates_parity_sublattice": h_generates_parity_sublattice,
        "parity_sublattice_abs_det_H": det_h_abs,
        "gram_prime_det_scales_by_2_pow_2nm1": det_scaling_exact,
        "literature_anchors": {
            "scope": "anchor",
            "excluded_from_checks": True,
            "bkz_beta_drops_published_diff": beta_drops,
            "hawk256_hermite_ratio_exact": frac_str(hawk256_hermite_ratio),
            "hawk256_hermite_ratio_lt_one": hawk256_hermite_ratio < 1,
        },
        "checks": checks,
        "passed": all(checks.values()),
    }


def audit_background_goppa_and_hawk_identities_exact():
    """Pillar 3: Background binary Goppa shortening & HAWK parity-sublattice/Gram identities."""
    tii = _audit_tii_goppa_identity_exact()
    hawk = _audit_hawk_lattice_identity_exact()
    checks = {
        "binary_goppa_shortening_identity_verified": tii["passed"],
        "hawk_parity_sublattice_and_lll_verified": hawk["passed"],
    }
    return {
        "tii_goppa_identity": tii,
        "hawk_lattice_identity": hawk,
        "checks": checks,
        "passed": all(checks.values()),
    }


# =============================================================================
# Fail-Closed Cryptographic Certification Wrapper
# =============================================================================


def certify_minimax_cryptanalysis_audit_exact(
    mode,
    live_portal_inspected,
    operator_labels,
    portal_summary_raw,
    pillar1_result,
    pillar2_result,
    pillar3_result,
    three_axis_checks,
):
    """Fail-closed certificate re-deriving Pillars 1-3 with strict recursive type equality."""
    verify_no_floats(
        {
            "mode": mode,
            "live": live_portal_inspected,
            "labels": operator_labels,
            "raw": portal_summary_raw,
            "p1": pillar1_result,
            "p2": pillar2_result,
            "p3": pillar3_result,
            "axes": three_axis_checks,
        },
        "certify",
    )
    clean_mode = require_non_empty_str(mode, "mode")
    if clean_mode not in ("live_portal_audit", "standalone_pinned_replay"):
        raise MinimaxCryptError("INVALID_MODE", f"unsupported mode {clean_mode}")
    live_flag = require_exact_bool(live_portal_inspected, "live_portal_inspected")
    if live_flag != (clean_mode == "live_portal_audit"):
        raise MinimaxCryptError("MODE_MISMATCH", "live_portal_inspected contradicts mode")

    label_guard = enforce_operator_label_hygiene(operator_labels)

    req_axes = (
        "bentsum_walsh_hadamard_and_anf",
        "fast_algebraic_and_blender_computed",
        "background_goppa_and_hawk_identities",
    )
    if type(three_axis_checks) is not dict or set(three_axis_checks.keys()) != set(req_axes):
        raise MinimaxCryptError("INVALID_AXES", "three_axis_checks keys mismatch")
    clean_axes = {ax: require_exact_bool(three_axis_checks[ax], f"axes.{ax}") for ax in req_axes}

    if (
        type(pillar1_result) is not dict
        or type(pillar2_result) is not dict
        or type(pillar3_result) is not dict
    ):
        raise MinimaxCryptError("INVALID_PILLAR", "all pillar results must be dicts")

    ps = validate_portal_summary(portal_summary_raw)
    expected_src = "live_portal_read" if live_flag else "standalone_pinned_fixture"
    if ps["diag_source"] != expected_src:
        raise MinimaxCryptError("PROVENANCE_MISMATCH", f"diag_source {ps['diag_source']} contradicts mode {clean_mode}")

    re_p1 = audit_bentsum_walsh_exact()
    if not _strict_equal(re_p1, pillar1_result):
        raise MinimaxCryptError("PILLAR_CONTRADICTION", "pillar1_result contradicts re-derivation")

    re_p2 = audit_fast_algebraic_and_blender_exact()
    if not _strict_equal(re_p2, pillar2_result):
        raise MinimaxCryptError("PILLAR_CONTRADICTION", "pillar2_result contradicts re-derivation")

    re_p3 = audit_background_goppa_and_hawk_identities_exact()
    if not _strict_equal(re_p3, pillar3_result):
        raise MinimaxCryptError("PILLAR_CONTRADICTION", "pillar3_result contradicts re-derivation")

    expected_axes = {
        "bentsum_walsh_hadamard_and_anf": re_p1["passed"],
        "fast_algebraic_and_blender_computed": re_p2["passed"],
        "background_goppa_and_hawk_identities": re_p3["passed"],
    }
    if not _strict_equal(clean_axes, expected_axes):
        raise MinimaxCryptError("AXIS_CONTRADICTION", "three_axis_checks contradicts re-derived pillars")

    all_passed = all(clean_axes.values())
    declared = build_declared_upstream_inputs(ps)
    body = {
        "schema_version": SCHEMA_VERSION,
        "study_id": STUDY_ID,
        "upstream_repo": UPSTREAM_REPO,
        "upstream_commit": ps["upstream_commit"],
        "mode": clean_mode,
        "live_portal_inspected": live_flag,
        "novelty_classification": "N0",
        "operator_label_hygiene_guard": label_guard,
        "declared_upstream_inputs": declared,
        "three_axis_audit_checks": clean_axes,
        "all_three_axes_passed": all_passed,
        "pillar1_bentsum_walsh": re_p1,
        "pillar2_fast_algebraic_and_blender": re_p2,
        "pillar3_background_goppa_and_hawk_identities": re_p3,
        "verdict": "AUDITED_MINIMAX_CRYPTANALYSIS_PORTAL" if all_passed else "REJECTED_GATE_FAILED",
        "all_gates_passed": all_passed,
    }
    body["certificate_sha256"] = canonical_sha256(body)
    return body
