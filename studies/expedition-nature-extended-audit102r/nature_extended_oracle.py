"""Track S4b (AUDIT-102): Extended Nature-Inspired Exact Operators (Pure-Q).

Five classical biological mechanisms audited strictly as pure-rational (int/Fraction)
mathematical operators with explicit must-fail controls and zero-metaphor Law-5
discipline:
  1. Hopfield (1974) / Ninio (1975) Kinetic Proofreading -> decoupled verifier gates
  2. Immune Negative Selection (Forrest et al. 1994) -> r-contiguous coverage & holes
  3. Turing (1952) Discrete Reaction-Diffusion Instability -> C_6 dispersion guard
  4. Starling Topological Flocking (Ballerini 2008 / Cavagna 2010) -> k-NN resilience
  5. Synaptic Homeostatic Scaling (Turrigiano 1998/2008) -> siliquant quant bridge

Pure Python 3 stdlib. Zero floats. Zero bare assert statements.
"""

from collections import deque
from fractions import Fraction
import hashlib
import json
import math


class NatureExtendedError(ValueError):
    """Fail-closed error raised on invalid inputs, singular solves, or bad certificates."""

    def __init__(self, code: str, detail: str):
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


SCHEMA_VERSION = "aletheia.nature_extended_audit.v1"
AUDIT_ID = "AUDIT-102"
ALETHEIA_VERSION = "2.0.0"

LAW4_N0_PRIMARY_SOURCES = (
    {
        "id": "NATX-N0-01",
        "pillar": "p1_kinetic_proofreading",
        "authors": "Hopfield, J. J.",
        "year": 1974,
        "title": "Kinetic proofreading: a new mechanism for reducing errors in biosynthetic processes requiring high specificity",
        "venue": "PNAS 71(10):4135-4139",
        "doi": "10.1073/pnas.71.10.4135",
        "novelty_class": "N0",
    },
    {
        "id": "NATX-N0-02",
        "pillar": "p1_kinetic_proofreading",
        "authors": "Ninio, J.",
        "year": 1975,
        "title": "Kinetic amplification of enzyme discrimination",
        "venue": "Biochimie 57(5):587-595",
        "doi": "10.1016/s0300-9084(75)80139-8",
        "novelty_class": "N0",
    },
    {
        "id": "NATX-N0-03",
        "pillar": "p2_immune_negative_selection",
        "authors": "Forrest, S., Perelson, A. S., Allen, L., Cherukuri, R.",
        "year": 1994,
        "title": "Self-nonself discrimination in a computer",
        "venue": "IEEE Symposium on Research in Security and Privacy, pp. 202-212",
        "doi": "10.1109/RISP.1994.296580",
        "novelty_class": "N0",
    },
    {
        "id": "NATX-N0-04",
        "pillar": "p3_turing_reaction_diffusion",
        "authors": "Turing, A. M.",
        "year": 1952,
        "title": "The chemical basis of morphogenesis",
        "venue": "Phil. Trans. R. Soc. Lond. B 237(641):37-72",
        "doi": "10.1098/rstb.1952.0012",
        "novelty_class": "N0",
    },
    {
        "id": "NATX-N0-05",
        "pillar": "p4_starling_topological_flocking",
        "authors": "Ballerini, M., Cabibbo, N., Candelier, R., Cavagna, A., Cisbani, E., Giardina, I., Lecomte, V., Orlandi, A., Parisi, G., Procaccini, A., Viale, M., Zdravkovic, V.",
        "year": 2008,
        "title": "Interaction ruling animal collective behavior depends on topological rather than metric distance: Evidence from a field study",
        "venue": "PNAS 105(4):1232-1237",
        "doi": "10.1073/pnas.0711437105",
        "novelty_class": "N0",
    },
    {
        "id": "NATX-N0-06",
        "pillar": "p4_starling_topological_flocking",
        "authors": "Cavagna, A., Cimarelli, A., Giardina, I., Parisi, G., Santagati, R., Stefanini, F., Viale, M.",
        "year": 2010,
        "title": "Scale-free correlations in starling flocks",
        "venue": "PNAS 107(26):11865-11870",
        "doi": "10.1073/pnas.1005766107",
        "novelty_class": "N0",
    },
    {
        "id": "NATX-N0-07",
        "pillar": "p5_synaptic_homeostatic_siliquant",
        "authors": "Turrigiano, G. G., Leslie, K. R., Desai, N. S., Rutherford, L. C., Nelson, S. B.",
        "year": 1998,
        "title": "Activity-dependent scaling of quantal amplitude in neocortical neurons",
        "venue": "Nature 391(6670):892-896",
        "doi": "10.1038/36103",
        "novelty_class": "N0",
    },
    {
        "id": "NATX-N0-08",
        "pillar": "p5_synaptic_homeostatic_siliquant",
        "authors": "Turrigiano, G. G.",
        "year": 2008,
        "title": "The self-tuning neuron: synaptic scaling of excitatory synapses",
        "venue": "Cell 135(3):422-435",
        "doi": "10.1016/j.cell.2008.10.008",
        "novelty_class": "N0",
    },
)

EXPECTED_SOURCE_IDS = tuple(src["id"] for src in LAW4_N0_PRIMARY_SOURCES)

EXPECTED_TOP_KEYS = frozenset({
    "schema",
    "audit_id",
    "governance",
    "law4_novelty",
    "law5_discipline",
    "primary_sources",
    "pillars",
    "summary",
    "canonical_sha256",
})

EXPECTED_PILLAR_KEYS = frozenset({
    "p1_kinetic_proofreading",
    "p2_immune_negative_selection",
    "p3_turing_reaction_diffusion",
    "p4_starling_topological_flocking",
    "p5_synaptic_homeostatic_siliquant",
})

# Default deterministic fixtures for Pillars 2, 3, 4, 5
P2_SELF_STRINGS = (
    "00000000",
    "00001111",
    "00110011",
    "00111100",
    "11000011",
    "11001100",
    "11110000",
    "11111111",
)

P3_C6_MODES = (
    (0, (1, 1, 1, 1, 1, 1)),
    (1, (2, 1, -1, -2, -1, 1)),
    (3, (2, -1, -1, 2, -1, -1)),
    (4, (1, -1, 1, -1, 1, -1)),
)

P4_FLOCK_POINTS = (
    (0, 0),
    (3, 1),
    (1, 7),
    (6, 4),
    (9, 0),
    (12, 5),
    (2, 13),
    (8, 11),
    (19, 2),
    (23, 1),
    (20, 8),
    (25, 5),
    (29, 0),
    (32, 4),
    (21, 15),
    (29, 12),
)

P5_WEIGHT_BLOCK = (
    Fraction(0, 1),
    Fraction(1, 4),
    Fraction(-3, 4),
    Fraction(5, 4),
    Fraction(-2, 1),
    Fraction(7, 4),
    Fraction(-1, 2),
    Fraction(3, 2),
)

P5_REFERENCE_VECTOR = (
    Fraction(1, 1),
    Fraction(-1, 2),
    Fraction(1, 4),
    Fraction(3, 4),
    Fraction(-1, 1),
    Fraction(1, 2),
    Fraction(0, 1),
    Fraction(1, 1),
)


# ---------------------------------------------------------------------------
# Core pure-Q helpers
# ---------------------------------------------------------------------------


def _is_strict_int(value) -> bool:
    return type(value) is int


def _is_strict_str(value) -> bool:
    return type(value) is str


def _to_fraction(value, name: str) -> Fraction:
    if isinstance(value, Fraction):
        return value
    if _is_strict_int(value):
        return Fraction(value, 1)
    raise NatureExtendedError("ERR_BAD_PARAM", f"{name} must be int or Fraction")


def _require_pos_fraction(value, name: str) -> Fraction:
    frac = _to_fraction(value, name)
    if frac <= 0:
        raise NatureExtendedError("ERR_BAD_PARAM", f"{name} must be strictly positive")
    return frac


def frac_pair(value: Fraction) -> list:
    return [value.numerator, value.denominator]


def frac_dec6(value: Fraction) -> str:
    neg = value < 0
    mag = -value if neg else value
    scaled = mag * 1_000_000
    q, rem = divmod(scaled.numerator, scaled.denominator)
    two_rem = 2 * rem
    if two_rem > scaled.denominator or (two_rem == scaled.denominator and q % 2 == 1):
        q += 1
    whole, frac = divmod(q, 1_000_000)
    prefix = "-" if neg and q != 0 else ""
    return f"{prefix}{whole}.{frac:06d}"


def round_half_even_exact(value: Fraction) -> int:
    q, rem = divmod(value.numerator, value.denominator)
    two_rem = 2 * rem
    if two_rem < value.denominator:
        return q
    if two_rem > value.denominator:
        return q + 1
    return q if q % 2 == 0 else q + 1


def canonical_json_bytes(obj) -> bytes:
    try:
        return json.dumps(
            obj,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        ).encode("utf-8")
    except (TypeError, ValueError) as exc:
        raise NatureExtendedError("ERR_CERT_JSON", f"non-canonical JSON object: {exc}") from exc


def contains_float(obj) -> bool:
    if isinstance(obj, (float, complex)):
        return True
    if isinstance(obj, dict):
        for k, v in obj.items():
            if contains_float(k) or contains_float(v):
                return True
        return False
    if isinstance(obj, (list, tuple, set, frozenset)):
        for item in obj:
            if contains_float(item):
                return True
        return False
    return False


def solve_linear_exact(matrix, rhs) -> list:
    """Exact rational Gaussian elimination with partial pivoting (zero floats)."""
    n = len(matrix)
    if n == 0 or len(rhs) != n:
        raise NatureExtendedError("ERR_BAD_MATRIX", "matrix must be non-empty square matching rhs")
    aug = []
    for row_idx in range(n):
        row = matrix[row_idx]
        if len(row) != n:
            raise NatureExtendedError("ERR_BAD_MATRIX", "non-square matrix row")
        aug.append([_to_fraction(val, "matrix") for val in row] + [_to_fraction(rhs[row_idx], "rhs")])

    for col in range(n):
        pivot = -1
        for r in range(col, n):
            if aug[r][col] != 0:
                pivot = r
                break
        if pivot == -1:
            raise NatureExtendedError("ERR_SINGULAR_MATRIX", f"singular matrix at column {col}")
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        piv_val = aug[col][col]
        for r in range(col + 1, n):
            factor = aug[r][col]
            if factor != 0:
                ratio = factor / piv_val
                aug[r][col] = Fraction(0, 1)
                for c in range(col + 1, n + 1):
                    aug[r][c] -= ratio * aug[col][c]

    sol = [Fraction(0, 1)] * n
    for r in range(n - 1, -1, -1):
        acc = aug[r][n]
        for c in range(r + 1, n):
            acc -= aug[r][c] * sol[c]
        sol[r] = acc / aug[r][r]
    return sol


# ---------------------------------------------------------------------------
# Pillar 1: Hopfield (1974) / Ninio (1975) Kinetic Proofreading
# ---------------------------------------------------------------------------


def solve_proofreading_chain_exact(d_c, d_w, k_on, w_fwd, v_cat, proofreading_steps: int) -> dict:
    """Solve exact (k+1)-state irreversible kinetic proofreading network in Q."""
    dc = _require_pos_fraction(d_c, "d_c")
    dw = _require_pos_fraction(d_w, "d_w")
    if dw <= dc:
        raise NatureExtendedError("ERR_BAD_PARAM", "d_w must exceed d_c for discrimination")
    kon = _require_pos_fraction(k_on, "k_on")
    wf = _require_pos_fraction(w_fwd, "w_fwd")
    vc = _require_pos_fraction(v_cat, "v_cat")
    if not _is_strict_int(proofreading_steps) or proofreading_steps < 0:
        raise NatureExtendedError("ERR_BAD_PARAM", "proofreading_steps must be non-negative int")

    n_states = proofreading_steps + 1

    def _flux(d_off: Fraction) -> Fraction:
        mat = [[Fraction(0, 1)] * n_states for _ in range(n_states)]
        rhs = [Fraction(0, 1)] * n_states
        rhs[0] = kon
        for m in range(n_states):
            if m > 0:
                mat[m][m - 1] = -wf
            exit_rate = vc if m == n_states - 1 else wf
            mat[m][m] = d_off + exit_rate
        steady = solve_linear_exact(mat, rhs)
        return vc * steady[n_states - 1]

    j_c = _flux(dc)
    j_w = _flux(dw)
    error_ratio = j_w / j_c
    f0 = dc / dw
    closed_form = ((dc + vc) / (dw + vc)) * (((dc + wf) / (dw + wf)) ** proofreading_steps)
    residual = error_ratio - closed_form
    thermodynamic_floor = f0 ** n_states

    return {
        "proofreading_steps": proofreading_steps,
        "discrimination_stages": n_states,
        "flux_correct": frac_pair(j_c),
        "flux_wrong": frac_pair(j_w),
        "error_ratio": frac_pair(error_ratio),
        "error_ratio_dec6": frac_dec6(error_ratio),
        "closed_form_error_ratio": frac_pair(closed_form),
        "closed_form_residual": frac_pair(residual),
        "thermodynamic_floor": frac_pair(thermodynamic_floor),
        "thermodynamic_floor_dec6": frac_dec6(thermodynamic_floor),
        "beats_f0": error_ratio < f0,
        "above_floor": error_ratio > thermodynamic_floor,
    }


def solve_equilibrium_cycle_control_exact(d_c, d_w, k_1, w_fwd, r_rev, v_cat) -> dict:
    """Must-fail control: detailed balance (delta_mu = 0) traps error rate strictly above f_0."""
    dc = _require_pos_fraction(d_c, "d_c")
    dw = _require_pos_fraction(d_w, "d_w")
    if dw <= dc:
        raise NatureExtendedError("ERR_BAD_PARAM", "d_w must exceed d_c")
    k1 = _require_pos_fraction(k_1, "k_1")
    wf = _require_pos_fraction(w_fwd, "w_fwd")
    rr = _require_pos_fraction(r_rev, "r_rev")
    vc = _require_pos_fraction(v_cat, "v_cat")

    # Thermodynamic detailed balance around cycle E+S <-> ES0 <-> ES1 <-> E+S: k1 * wf = k2 * rr
    k2 = (k1 * wf) / rr
    cycle_ratio = (k1 * wf) / (k2 * rr)

    def _flux(d_off: Fraction) -> Fraction:
        mat = [
            [d_off + wf, -rr],
            [-wf, d_off + rr + vc],
        ]
        steady = solve_linear_exact(mat, [k1, k2])
        return vc * steady[1]

    j_c = _flux(dc)
    j_w = _flux(dw)
    f_eq = j_w / j_c
    f0 = dc / dw
    return {
        "k2_detailed_balance": frac_pair(k2),
        "cycle_balance_ratio": frac_pair(cycle_ratio),
        "error_ratio": frac_pair(f_eq),
        "error_ratio_dec6": frac_dec6(f_eq),
        "strictly_worse_than_f0": f_eq > f0,
    }


def solve_coupled_gate_control_exact(d_c, d_w, k_on, w_fwd, v_cat) -> dict:
    """Must-fail control: non-independent stage 2 (d_w2 == d_c2 == d_c) yields zero amplification."""
    dc = _require_pos_fraction(d_c, "d_c")
    dw = _require_pos_fraction(d_w, "d_w")
    if dw <= dc:
        raise NatureExtendedError("ERR_BAD_PARAM", "d_w must exceed d_c")
    kon = _require_pos_fraction(k_on, "k_on")
    wf = _require_pos_fraction(w_fwd, "w_fwd")
    vc = _require_pos_fraction(v_cat, "v_cat")

    def _flux(d_stage0: Fraction) -> Fraction:
        mat = [
            [d_stage0 + wf, Fraction(0, 1)],
            [-wf, dc + vc],
        ]
        steady = solve_linear_exact(mat, [kon, Fraction(0, 1)])
        return vc * steady[1]

    f_coupled = _flux(dw) / _flux(dc)
    f0 = dc / dw
    return {
        "error_ratio": frac_pair(f_coupled),
        "error_ratio_dec6": frac_dec6(f_coupled),
        "strictly_worse_than_f0": f_coupled > f0,
    }


def audit_kinetic_proofreading_exact() -> dict:
    d_c = Fraction(1, 1)
    d_w = Fraction(10, 1)
    k_on = Fraction(1, 1)
    w_fwd = Fraction(1, 100)
    v_cat = Fraction(1, 100)
    f0 = d_c / d_w

    stages = [
        solve_proofreading_chain_exact(d_c, d_w, k_on, w_fwd, v_cat, k)
        for k in (0, 1, 2)
    ]
    eq_ctrl = solve_equilibrium_cycle_control_exact(d_c, d_w, k_on, w_fwd, Fraction(1, 100), v_cat)
    coupled_ctrl = solve_coupled_gate_control_exact(d_c, d_w, k_on, w_fwd, v_cat)

    f_s0 = Fraction(*stages[0]["error_ratio"])
    f_s1 = Fraction(*stages[1]["error_ratio"])
    f_s2 = Fraction(*stages[2]["error_ratio"])
    speedup_k1 = f_s0 / f_s1
    speedup_k2 = f_s0 / f_s2

    return {
        "operator_name": "hopfield_ninio_irreversible_kinetic_proofreading",
        "engineering_target": "aletheia decoupled @verifier gate (irreversible independent verification stage)",
        "intrinsic_f0": frac_pair(f0),
        "intrinsic_f0_dec6": frac_dec6(f0),
        "stages": stages,
        "error_reduction_k0_to_k1": frac_pair(speedup_k1),
        "error_reduction_k0_to_k1_dec6": frac_dec6(speedup_k1),
        "error_reduction_k0_to_k2": frac_pair(speedup_k2),
        "error_reduction_k0_to_k2_dec6": frac_dec6(speedup_k2),
        "monotone_exponentiation": f_s2 < f_s1 < f_s0,
        "must_fail_equilibrium_control": eq_ctrl,
        "must_fail_coupled_gate_control": coupled_ctrl,
    }


# ---------------------------------------------------------------------------
# Pillar 2: Immune Negative Selection (Forrest et al. 1994)
# ---------------------------------------------------------------------------


def _validate_binary_string(text: str, expected_len: int) -> None:
    if not _is_strict_str(text) or len(text) != expected_len:
        raise NatureExtendedError("ERR_BAD_BITSTRING", f"expected binary string of length {expected_len}")
    for ch in text:
        if ch not in ("0", "1"):
            raise NatureExtendedError("ERR_BAD_BITSTRING", f"non-binary character {ch!r}")


def r_contiguous_match(a: str, b: str, r: int) -> bool:
    if not _is_strict_str(a) or not _is_strict_str(b) or len(a) != len(b) or len(a) == 0:
        raise NatureExtendedError("ERR_BAD_BITSTRING", "inputs must be equal non-empty strings")
    _validate_binary_string(a, len(a))
    _validate_binary_string(b, len(b))
    if not _is_strict_int(r) or r < 1 or r > len(a):
        raise NatureExtendedError("ERR_BAD_PARAM", "r must be int in [1, len(a)]")
    limit = len(a) - r + 1
    for i in range(limit):
        if a[i : i + r] == b[i : i + r]:
            return True
    return False


def negative_selection_exhaustive_exact(bit_length: int, self_strings, r: int) -> dict:
    """Exact exhaustive r-contiguous negative selection & hole enumeration on {0,1}^L."""
    if not _is_strict_int(bit_length) or bit_length < 2 or bit_length > 10:
        raise NatureExtendedError("ERR_BAD_PARAM", "bit_length must be int in [2, 10]")
    if not _is_strict_int(r) or r < 1 or r > bit_length:
        raise NatureExtendedError("ERR_BAD_PARAM", "r must be int in [1, bit_length]")
    if not isinstance(self_strings, (list, tuple)) or len(self_strings) == 0:
        raise NatureExtendedError("ERR_BAD_PARAM", "self_strings must be non-empty sequence")
    for s in self_strings:
        _validate_binary_string(s, bit_length)
    self_sorted = tuple(sorted(set(self_strings)))
    self_set = frozenset(self_sorted)
    universe_size = 1 << bit_length
    if len(self_set) >= universe_size:
        raise NatureExtendedError("ERR_BAD_PARAM", "self set must be strict subset of universe")

    n_windows = bit_length - r + 1
    self_windows = [frozenset(s[i : i + r] for s in self_sorted) for i in range(n_windows)]
    universe = [format(idx, f"0{bit_length}b") for idx in range(universe_size)]
    nonself = [x for x in universe if x not in self_set]
    detectors = [
        d for d in universe if all(d[i : i + r] not in self_windows[i] for i in range(n_windows))
    ]
    det_windows = [frozenset(d[i : i + r] for d in detectors) for i in range(n_windows)]
    false_positives = sum(
        1 for s in self_sorted if any(s[i : i + r] in det_windows[i] for i in range(n_windows))
    )
    detected = [
        x for x in nonself if any(x[i : i + r] in det_windows[i] for i in range(n_windows))
    ]
    detected_set = frozenset(detected)
    holes = [x for x in nonself if x not in detected_set]
    recombinant_holes = [
        x for x in nonself if all(x[i : i + r] in self_windows[i] for i in range(n_windows))
    ]
    recomb_subset = frozenset(recombinant_holes).issubset(frozenset(holes))

    det_rate = Fraction(len(detected), len(nonself))
    hole_rate = Fraction(len(holes), len(nonself))
    det_frac = Fraction(len(detectors), universe_size)

    return {
        "r": r,
        "detector_count": len(detectors),
        "detector_universe_fraction": frac_pair(det_frac),
        "false_positive_count": false_positives,
        "detected_count": len(detected),
        "hole_count": len(holes),
        "recombinant_hole_count": len(recombinant_holes),
        "recombinant_hole_subset_holds": recomb_subset,
        "detection_rate": frac_pair(det_rate),
        "detection_rate_dec6": frac_dec6(det_rate),
        "hole_rate": frac_pair(hole_rate),
        "hole_rate_dec6": frac_dec6(hole_rate),
        "first_hole": holes[0] if holes else None,
        "first_recombinant_hole": recombinant_holes[0] if recombinant_holes else None,
    }


def uncensored_detector_control_exact(self_strings, r: int, detector: str) -> dict:
    """Must-fail control: admitting an uncensored detector causes nonzero false positives on S."""
    if not isinstance(self_strings, (list, tuple)) or len(self_strings) == 0:
        raise NatureExtendedError("ERR_BAD_PARAM", "self_strings must be non-empty sequence")
    bit_length = len(self_strings[0])
    _validate_binary_string(detector, bit_length)
    for s in self_strings:
        _validate_binary_string(s, bit_length)
    matched_self = [s for s in self_strings if r_contiguous_match(detector, s, r)]
    fp_rate = Fraction(len(matched_self), len(self_strings))
    return {
        "detector": detector,
        "r": r,
        "false_positive_count": len(matched_self),
        "false_positive_rate": frac_pair(fp_rate),
        "false_positive_rate_dec6": frac_dec6(fp_rate),
        "breaks_zero_fp_invariant": len(matched_self) > 0,
    }


def audit_immune_negative_selection_exact() -> dict:
    bit_length = 8
    sweep = [
        negative_selection_exhaustive_exact(bit_length, P2_SELF_STRINGS, r)
        for r in range(2, bit_length + 1)
    ]
    uncensored_ctrl = uncensored_detector_control_exact(P2_SELF_STRINGS, 4, "00001100")
    r2_row = sweep[0]
    r3_row = sweep[1]
    r4_row = sweep[2]
    r8_row = sweep[-1]
    return {
        "operator_name": "forrest_r_contiguous_negative_selection",
        "engineering_target": "aletheia safety-scan & warp-drive canary self/non-self separation and recombinant-hole characterization",
        "bit_length": bit_length,
        "universe_size": 1 << bit_length,
        "self_size": len(P2_SELF_STRINGS),
        "nonself_size": (1 << bit_length) - len(P2_SELF_STRINGS),
        "self_strings": list(P2_SELF_STRINGS),
        "r_sweep": sweep,
        "non_monotone_hole_witness": r4_row["hole_count"] > r3_row["hole_count"],
        "must_fail_overbroad_collapse_r2": {
            "r": 2,
            "detector_count": r2_row["detector_count"],
            "detection_rate": r2_row["detection_rate"],
            "collapsed_to_zero_detectors": r2_row["detector_count"] == 0,
        },
        "must_fail_uncensored_control": uncensored_ctrl,
        "exact_memory_limit_r8": {
            "r": 8,
            "detector_count": r8_row["detector_count"],
            "hole_count": r8_row["hole_count"],
        },
    }


# ---------------------------------------------------------------------------
# Pillar 3: Turing (1952) Discrete Reaction-Diffusion Instability on C_6
# ---------------------------------------------------------------------------


def evaluate_turing_dispersion_exact(f_u, f_v, g_u, g_v, d_u, d_v, laplacian_eigenvalues) -> dict:
    """Exact pure-Q Turing (1952) Jacobian & squared dispersion threshold audit."""
    fu = _to_fraction(f_u, "f_u")
    fv = _to_fraction(f_v, "f_v")
    gu = _to_fraction(g_u, "g_u")
    gv = _to_fraction(g_v, "g_v")
    du = _require_pos_fraction(d_u, "d_u")
    dv = _require_pos_fraction(d_v, "d_v")
    if not isinstance(laplacian_eigenvalues, (list, tuple)) or len(laplacian_eigenvalues) == 0:
        raise NatureExtendedError("ERR_BAD_PARAM", "laplacian_eigenvalues must be non-empty")

    tr_j = fu + gv
    det_j = fu * gv - fv * gu
    hom_stable = tr_j < 0 and det_j > 0
    s_term = dv * fu + du * gv
    disc = s_term * s_term - Fraction(4, 1) * du * dv * det_j
    cont_unstable = hom_stable and s_term > 0 and disc > 0

    modes = []
    any_discrete_unstable = False
    for raw_lam in laplacian_eigenvalues:
        lam = _to_fraction(raw_lam, "lambda")
        if lam < 0:
            raise NatureExtendedError("ERR_BAD_PARAM", "Laplacian eigenvalues must be non-negative")
        tr_m = tr_j - lam * (du + dv)
        det_m = du * dv * lam * lam - s_term * lam + det_j
        unstable = hom_stable and det_m < 0
        if unstable:
            any_discrete_unstable = True
        modes.append({
            "eigenvalue": frac_pair(lam),
            "trace": frac_pair(tr_m),
            "det": frac_pair(det_m),
            "unstable": unstable,
        })

    return {
        "d_u": frac_pair(du),
        "d_v": frac_pair(dv),
        "trace_j": frac_pair(tr_j),
        "det_j": frac_pair(det_j),
        "homogeneous_stable": hom_stable,
        "s_term": frac_pair(s_term),
        "turing_discriminant": frac_pair(disc),
        "continuous_turing_unstable": cont_unstable,
        "discrete_turing_unstable": any_discrete_unstable,
        "modes": modes,
    }


def verify_c6_eigenvectors_exact() -> dict:
    """Verify exact integer eigenpairs L_{C_6} v = lambda v with 0/1 max residual."""
    max_res = Fraction(0, 1)
    for lam, vec in P3_C6_MODES:
        for i in range(6):
            lv_i = Fraction(2 * vec[i] - vec[(i - 1) % 6] - vec[(i + 1) % 6], 1)
            res = abs(lv_i - Fraction(lam * vec[i], 1))
            if res > max_res:
                max_res = res
    return {
        "ring_size": 6,
        "ring_eigenvalues": [lam for lam, _ in P3_C6_MODES],
        "max_eigenvector_residual": frac_pair(max_res),
    }


def step_c6_reaction_diffusion_exact(f_u, f_v, g_u, g_v, d_u, d_v, u_amp, v_amp, mode_vec, dt, steps: int) -> dict:
    """Exact pure-Q forward-Euler evolution of 12-state reaction-diffusion ring C_6."""
    fu = _to_fraction(f_u, "f_u")
    fv = _to_fraction(f_v, "f_v")
    gu = _to_fraction(g_u, "g_u")
    gv = _to_fraction(g_v, "g_v")
    du = _require_pos_fraction(d_u, "d_u")
    dv = _require_pos_fraction(d_v, "d_v")
    ua = _to_fraction(u_amp, "u_amp")
    va = _to_fraction(v_amp, "v_amp")
    step_dt = _require_pos_fraction(dt, "dt")
    if not _is_strict_int(steps) or steps < 1:
        raise NatureExtendedError("ERR_BAD_PARAM", "steps must be positive int")
    if len(mode_vec) != 6:
        raise NatureExtendedError("ERR_BAD_PARAM", "mode_vec must have length 6")

    u = [ua * _to_fraction(x, "mode_vec") for x in mode_vec]
    v = [va * _to_fraction(x, "mode_vec") for x in mode_vec]
    init_norm_sq = sum(x * x for x in u) + sum(y * y for y in v)
    if init_norm_sq == 0:
        raise NatureExtendedError("ERR_BAD_PARAM", "initial state must be non-zero")

    for _ in range(steps):
        lu = [Fraction(2, 1) * u[i] - u[(i - 1) % 6] - u[(i + 1) % 6] for i in range(6)]
        lv = [Fraction(2, 1) * v[i] - v[(i - 1) % 6] - v[(i + 1) % 6] for i in range(6)]
        u_next = [u[i] + step_dt * (fu * u[i] + fv * v[i] - du * lu[i]) for i in range(6)]
        v_next = [v[i] + step_dt * (gu * u[i] + gv * v[i] - dv * lv[i]) for i in range(6)]
        u, v = u_next, v_next

    final_norm_sq = sum(x * x for x in u) + sum(y * y for y in v)
    ratio = final_norm_sq / init_norm_sq
    return {
        "steps": steps,
        "dt": frac_pair(step_dt),
        "initial_norm_sq": frac_pair(init_norm_sq),
        "final_norm_sq_dec6": frac_dec6(final_norm_sq),
        "norm_sq_ratio": frac_pair(ratio),
        "norm_sq_ratio_dec6": frac_dec6(ratio),
        "amplified": ratio > 1,
        "decayed": ratio < 1,
    }


def audit_turing_reaction_diffusion_exact() -> dict:
    fu, fv, gu, gv = Fraction(2, 1), Fraction(-5, 1), Fraction(2, 1), Fraction(-4, 1)
    ring_lams = tuple(lam for lam, _ in P3_C6_MODES)
    eig_cert = verify_c6_eigenvectors_exact()

    # Pass witness: D_u = 1, D_v = 10 -> mode lambda=1 unstable (det=-4), modes 0,3,4 stable
    turing_disp = evaluate_turing_dispersion_exact(fu, fv, gu, gv, 1, 10, ring_lams)
    hom_dyn = step_c6_reaction_diffusion_exact(
        fu, fv, gu, gv, 1, 10, 5, 1, P3_C6_MODES[0][1], Fraction(1, 32), 32
    )
    m1_dyn = step_c6_reaction_diffusion_exact(
        fu, fv, gu, gv, 1, 10, 5, 1, P3_C6_MODES[1][1], Fraction(1, 32), 32
    )

    # Must-fail control A: equal diffusion D_u = D_v = 1 -> Turing impossible
    eq_disp = evaluate_turing_dispersion_exact(fu, fv, gu, gv, 1, 1, ring_lams)
    eq_m1_dyn = step_c6_reaction_diffusion_exact(
        fu, fv, gu, gv, 1, 1, 5, 1, P3_C6_MODES[1][1], Fraction(1, 32), 32
    )

    # Must-fail control B: sub-threshold diffusion ratio D_u = 1, D_v = 4 (S=4 > 0, disc=-16 < 0)
    sub_disp = evaluate_turing_dispersion_exact(fu, fv, gu, gv, 1, 4, ring_lams)

    # Must-fail control C: continuous-unstable (D_u=1/3, D_v=19/10, h(2)=-2/5<0) missing discrete C_6 modes
    gap_disp = evaluate_turing_dispersion_exact(
        fu, fv, gu, gv, Fraction(1, 3), Fraction(19, 10), ring_lams
    )
    probe_lam = Fraction(2, 1)
    du_g, dv_g = Fraction(1, 3), Fraction(19, 10)
    s_g = dv_g * fu + du_g * gv
    det_j = fu * gv - fv * gu
    gap_probe_det = du_g * dv_g * probe_lam * probe_lam - s_g * probe_lam + det_j

    return {
        "operator_name": "turing_discrete_c6_reaction_diffusion_instability",
        "engineering_target": "exact symmetry-breaking instability vs discrete spectral-gap stability guard",
        "jacobian": [[2, -5], [2, -4]],
        "c6_spectrum": eig_cert,
        "turing_witness": {
            "dispersion": turing_disp,
            "homogeneous_dynamics": hom_dyn,
            "mode1_dynamics": m1_dyn,
        },
        "must_fail_equal_diffusion_control": {
            "dispersion": eq_disp,
            "mode1_dynamics": eq_m1_dyn,
        },
        "must_fail_subthreshold_ratio_control": {
            "dispersion": sub_disp,
        },
        "must_fail_discrete_spectral_gap_control": {
            "dispersion": gap_disp,
            "continuous_probe_lambda": frac_pair(probe_lam),
            "continuous_probe_det": frac_pair(gap_probe_det),
        },
    }


# ---------------------------------------------------------------------------
# Pillar 4: Starling Scale-Free Topological Flocking (Ballerini 2008 / Cavagna 2010)
# ---------------------------------------------------------------------------


def dist_sq_2d(p, q) -> int:
    dx = p[0] - q[0]
    dy = p[1] - q[1]
    return dx * dx + dy * dy


def build_topological_knn_graph(points, k: int) -> tuple:
    """Build undirected k-NN topological graph using pure-integer squared distances."""
    n = len(points)
    if not _is_strict_int(k) or k < 1 or k >= n:
        raise NatureExtendedError("ERR_BAD_PARAM", "k must be int in [1, len(points)-1]")
    edges = set()
    boundary_ties = 0
    for i in range(n):
        ranked = sorted((dist_sq_2d(points[i], points[j]), j) for j in range(n) if j != i)
        if k < len(ranked) and ranked[k - 1][0] == ranked[k][0]:
            boundary_ties += 1
        for _, j in ranked[:k]:
            edges.add((i, j) if i < j else (j, i))
    return sorted(edges), boundary_ties


def build_metric_radius_graph(points, radius_sq: int) -> list:
    """Build undirected metric radius graph (d^2 <= radius_sq) in pure integers."""
    if not _is_strict_int(radius_sq) or radius_sq < 0:
        raise NatureExtendedError("ERR_BAD_PARAM", "radius_sq must be non-negative int")
    n = len(points)
    edges = []
    for i in range(n):
        for j in range(i + 1, n):
            if dist_sq_2d(points[i], points[j]) <= radius_sq:
                edges.append((i, j))
    return edges


def graph_connectivity_and_diameter(n: int, edges, omit=None) -> tuple:
    """Exact BFS component count and graph diameter (None if disconnected)."""
    nodes = [i for i in range(n) if i != omit]
    adj = {i: [] for i in nodes}
    for u, v in edges:
        if u != omit and v != omit:
            adj[u].append(v)
            adj[v].append(u)
    visited = set()
    components = 0
    for start in nodes:
        if start not in visited:
            components += 1
            queue = deque([start])
            visited.add(start)
            while queue:
                cur = queue.popleft()
                for nxt in adj[cur]:
                    if nxt not in visited:
                        visited.add(nxt)
                        queue.append(nxt)
    if components != 1:
        return components, None
    diameter = 0
    for start in nodes:
        dist = {start: 0}
        queue = deque([start])
        while queue:
            cur = queue.popleft()
            d_next = dist[cur] + 1
            for nxt in adj[cur]:
                if nxt not in dist:
                    dist[nxt] = d_next
                    if d_next > diameter:
                        diameter = d_next
                    queue.append(nxt)
    return 1, diameter


def exact_kirchhoff_effective_resistance(n: int, edges, src: int, dst: int) -> Fraction:
    """Exact pure-Q Kirchhoff effective resistance R_eff(src, dst) on src's component."""
    if not (_is_strict_int(src) and _is_strict_int(dst)) or src == dst or not (0 <= src < n and 0 <= dst < n):
        raise NatureExtendedError("ERR_BAD_PARAM", "src and dst must be distinct node indices")
    # Restrict solve to src's connected component so unrelated disconnected nodes do not induce singularity
    adj = {i: [] for i in range(n)}
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    comp = {src}
    queue = deque([src])
    while queue:
        cur = queue.popleft()
        for nxt in adj[cur]:
            if nxt not in comp:
                comp.add(nxt)
                queue.append(nxt)
    if dst not in comp:
        raise NatureExtendedError("ERR_DISCONNECTED_ENDPOINTS", "src and dst lie in disconnected components")
    kept = sorted(i for i in comp if i != dst)
    index_of = {node: idx for idx, node in enumerate(kept)}
    size = len(kept)
    lap = [[Fraction(0, 1)] * size for _ in range(size)]
    for u, v in edges:
        if u not in comp:
            continue
        if u != dst:
            iu = index_of[u]
            lap[iu][iu] += Fraction(1, 1)
        if v != dst:
            iv = index_of[v]
            lap[iv][iv] += Fraction(1, 1)
        if u != dst and v != dst:
            iu = index_of[u]
            iv = index_of[v]
            lap[iu][iv] -= Fraction(1, 1)
            lap[iv][iu] -= Fraction(1, 1)
    rhs = [Fraction(0, 1)] * size
    rhs[index_of[src]] = Fraction(1, 1)
    potentials = solve_linear_exact(lap, rhs)
    return potentials[index_of[src]]


def audit_starling_topological_flocking_exact() -> dict:
    n = len(P4_FLOCK_POINTS)
    scales = (1, 2, 3, 4)
    k_topo = 6
    metric_r_sq = 144  # radius = 12: connected at s=1 with degree comparable to k=6

    base_topo_edges, k6_ties = build_topological_knn_graph(P4_FLOCK_POINTS, k_topo)
    base_reff = exact_kirchhoff_effective_resistance(n, base_topo_edges, 0, n - 1)

    topo_rows = []
    metric_rows = []
    all_edges_identical = True
    all_connected = True
    all_reff_identical = True

    for s in scales:
        scaled_pts = [(s * x, s * y) for x, y in P4_FLOCK_POINTS]
        t_edges, t_ties = build_topological_knn_graph(scaled_pts, k_topo)
        t_comps, t_diam = graph_connectivity_and_diameter(n, t_edges)
        t_reff = exact_kirchhoff_effective_resistance(n, t_edges, 0, n - 1)
        if t_edges != base_topo_edges:
            all_edges_identical = False
        if t_comps != 1:
            all_connected = False
        if t_reff != base_reff:
            all_reff_identical = False
        topo_rows.append({
            "scale": s,
            "area_density_factor": frac_pair(Fraction(1, s * s)),
            "edge_count": len(t_edges),
            "boundary_tie_count": t_ties,
            "components": t_comps,
            "diameter": t_diam,
            "reff_0_to_15": frac_pair(t_reff),
            "reff_0_to_15_dec6": frac_dec6(t_reff),
            "edges_identical_to_s1": t_edges == base_topo_edges,
        })

        m_edges = build_metric_radius_graph(scaled_pts, metric_r_sq)
        m_comps, m_diam = graph_connectivity_and_diameter(n, m_edges)
        m_reff = exact_kirchhoff_effective_resistance(n, m_edges, 0, n - 1) if m_comps == 1 else None
        metric_rows.append({
            "scale": s,
            "area_density_factor": frac_pair(Fraction(1, s * s)),
            "radius_sq": metric_r_sq,
            "edge_count": len(m_edges),
            "components": m_comps,
            "diameter": m_diam,
            "reff_0_to_15": frac_pair(m_reff) if m_reff is not None else None,
            "reff_0_to_15_dec6": frac_dec6(m_reff) if m_reff is not None else None,
        })

    max_ablation_comps = max(
        graph_connectivity_and_diameter(n, base_topo_edges, omit=node)[0] for node in range(n)
    )

    k1_edges, k1_ties = build_topological_knn_graph(P4_FLOCK_POINTS, 1)
    k1_comps, _ = graph_connectivity_and_diameter(n, k1_edges)

    return {
        "operator_name": "ballerini_cavagna_topological_knn_flocking",
        "engineering_target": "scale-free swarm communication graph resilience under agent-density expansion",
        "agent_count": n,
        "topological_k": k_topo,
        "metric_radius_sq": metric_r_sq,
        "scales": list(scales),
        "k6_boundary_tie_count": k6_ties,
        "k1_boundary_tie_count": k1_ties,
        "topological_scaling": topo_rows,
        "all_scale_edges_identical": all_edges_identical,
        "all_scale_connected": all_connected,
        "all_scale_reff_identical": all_reff_identical,
        "max_single_node_ablation_components": max_ablation_comps,
        "two_vertex_connected": max_ablation_comps == 1,
        "must_fail_metric_fragmentation_control": {
            "scaling": metric_rows,
            "s1_components": metric_rows[0]["components"],
            "s4_components": metric_rows[-1]["components"],
            "s4_edge_count": metric_rows[-1]["edge_count"],
            "fragments_to_singletons": metric_rows[-1]["components"] == n,
        },
        "must_fail_subcritical_k1_control": {
            "k": 1,
            "edge_count": len(k1_edges),
            "components": k1_comps,
            "disconnected": k1_comps > 1,
        },
    }


# ---------------------------------------------------------------------------
# Pillar 5: Synaptic Homeostatic Scaling (Turrigiano 1998/2008) -> siliquant
# ---------------------------------------------------------------------------


def symmetric_absmax_quantize_exact(weights, q_max: int) -> tuple:
    """Exact pure-Q symmetric per-group absmax quantization with round-half-to-even."""
    if not _is_strict_int(q_max) or q_max < 1:
        raise NatureExtendedError("ERR_BAD_PARAM", "q_max must be positive int")
    w = [_to_fraction(x, "weights") for x in weights]
    if len(w) == 0:
        raise NatureExtendedError("ERR_BAD_PARAM", "weights must be non-empty")
    absmax = max(abs(x) for x in w)
    if absmax == 0:
        raise NatureExtendedError("ERR_BAD_PARAM", "weights cannot be identically zero")
    scale = absmax / Fraction(q_max, 1)
    codes = [round_half_even_exact(x / scale) for x in w]
    dequant = [Fraction(c, 1) * scale for c in codes]
    return scale, codes, dequant


def d8_absmax_quantize_exact(weights, q_max: int) -> list:
    """Exact pure-Q scale-normalized D_8 (even-sum integer lattice) nearest-point decode.

    Preserves the all-zero block 0^8 under any positive group scale (unlike additive
    Code.centre shifts); on exact rounding-error ties during odd-parity correction,
    prefers flipping a non-zero coordinate inward toward 0 so codes stay in [-q_max, q_max].
    """
    if len(weights) != 8:
        raise NatureExtendedError("ERR_BAD_PARAM", "D8 lattice requires 8-element block")
    if not _is_strict_int(q_max) or q_max < 1:
        raise NatureExtendedError("ERR_BAD_PARAM", "q_max must be positive int")
    w = [_to_fraction(x, "weights") for x in weights]
    absmax = max(abs(x) for x in w)
    if absmax == 0:
        raise NatureExtendedError("ERR_BAD_PARAM", "weights cannot be identically zero")
    scaled = [(x * Fraction(q_max, 1)) / absmax for x in w]
    q = [round_half_even_exact(val) for val in scaled]
    if sum(q) % 2 != 0:
        best_idx = 0
        best_key = (abs(scaled[0] - Fraction(q[0], 1)), 1 if scaled[0] != 0 else 0)
        for i in range(1, 8):
            key = (abs(scaled[i] - Fraction(q[i], 1)), 1 if scaled[i] != 0 else 0)
            if key > best_key:
                best_key = key
                best_idx = i
        if scaled[best_idx] > Fraction(q[best_idx], 1):
            q[best_idx] += 1
        elif scaled[best_idx] < Fraction(q[best_idx], 1):
            q[best_idx] -= 1
        else:
            q[best_idx] += -1 if q[best_idx] > 0 else 1
    return q


def pairwise_ratio_max_drift_exact(base, transformed) -> Fraction:
    """Exact maximum |t_i/t_j - b_i/b_j| over all pairs with b_j != 0."""
    if len(base) != len(transformed) or len(base) == 0:
        raise NatureExtendedError("ERR_BAD_PARAM", "vectors must share positive length")
    b = [_to_fraction(x, "base") for x in base]
    t = [_to_fraction(x, "transformed") for x in transformed]
    max_drift = Fraction(0, 1)
    for j in range(len(b)):
        if b[j] == 0:
            continue
        if t[j] == 0:
            raise NatureExtendedError("ERR_ZERO_DENOM", f"transformed[{j}] collapsed non-zero weight to 0")
        for i in range(len(b)):
            drift = abs((t[i] / t[j]) - (b[i] / b[j]))
            if drift > max_drift:
                max_drift = drift
    return max_drift


def squared_cosine_exact(u, v) -> Fraction:
    """Exact pure-Q squared cosine similarity (u.v)^2 / ((u.u)(v.v)), zero sqrt."""
    if len(u) != len(v) or len(u) == 0:
        raise NatureExtendedError("ERR_BAD_PARAM", "vectors must share positive length")
    uu = [_to_fraction(x, "u") for x in u]
    vv = [_to_fraction(x, "v") for x in v]
    dot = sum(a * b for a, b in zip(uu, vv))
    nu = sum(a * a for a in uu)
    nv = sum(b * b for b in vv)
    if nu == 0 or nv == 0:
        raise NatureExtendedError("ERR_ZERO_NORM", "cosine requires non-zero vectors")
    return (dot * dot) / (nu * nv)


def run_multiplicative_homeostasis_exact(r0, target, eta, steps: int) -> dict:
    """Exact pure-Q discrete multiplicative homeostatic firing-rate control."""
    r = _require_pos_fraction(r0, "r0")
    r_star = _require_pos_fraction(target, "target")
    gain_eta = _require_pos_fraction(eta, "eta")
    if not _is_strict_int(steps) or steps < 1:
        raise NatureExtendedError("ERR_BAD_PARAM", "steps must be positive int")

    init_err = abs(r - r_star)
    errors = [init_err]
    gains = [Fraction(1, 1)]
    r_cur = r
    g_cur = Fraction(1, 1)
    for _ in range(steps):
        factor = Fraction(1, 1) + gain_eta * (r_star - r_cur) / r_star
        g_cur = g_cur * factor
        r_cur = r * g_cur
        errors.append(abs(r_cur - r_star))
        gains.append(g_cur)

    monotone_decay = all(errors[t + 1] < errors[t] for t in range(steps))
    return {
        "r0": frac_pair(r),
        "target": frac_pair(r_star),
        "eta": frac_pair(gain_eta),
        "steps": steps,
        "initial_error": frac_pair(init_err),
        "final_error": frac_pair(errors[-1]),
        "final_error_dec6": frac_dec6(errors[-1]),
        "final_gain": frac_pair(gains[-1]),
        "strictly_monotone_decay": monotone_decay,
        "amplified_error": errors[-1] > init_err,
        "gains": gains,
    }


def _evaluate_transform_on_siliquant_block(base_w, ref_v, transformed_w, q_max: int) -> dict:
    _, base_abs_codes, _ = symmetric_absmax_quantize_exact(base_w, q_max)
    _, trans_abs_codes, _ = symmetric_absmax_quantize_exact(transformed_w, q_max)
    base_d8 = d8_absmax_quantize_exact(base_w, q_max)
    trans_d8 = d8_absmax_quantize_exact(transformed_w, q_max)
    ratio_drift = pairwise_ratio_max_drift_exact(base_w, transformed_w)
    cos_drift = abs(squared_cosine_exact(transformed_w, ref_v) - squared_cosine_exact(base_w, ref_v))
    abs_flips = sum(1 for a, b in zip(base_abs_codes, trans_abs_codes) if a != b)
    d8_flips = sum(1 for a, b in zip(base_d8, trans_d8) if a != b)
    return {
        "max_ratio_drift": frac_pair(ratio_drift),
        "max_ratio_drift_dec6": frac_dec6(ratio_drift),
        "squared_cosine_drift": frac_pair(cos_drift),
        "squared_cosine_drift_dec6": frac_dec6(cos_drift),
        "zero_weight_after": frac_pair(transformed_w[0]),
        "absmax_codes": trans_abs_codes,
        "absmax_code_flips": abs_flips,
        "d8_codes": trans_d8,
        "d8_code_flips": d8_flips,
    }


def audit_synaptic_homeostatic_siliquant_exact() -> dict:
    q_max = 7
    _, base_abs_codes, _ = symmetric_absmax_quantize_exact(P5_WEIGHT_BLOCK, q_max)
    base_d8_codes = d8_absmax_quantize_exact(P5_WEIGHT_BLOCK, q_max)

    g_up = Fraction(7, 3)
    g_down = Fraction(3, 11)
    up_res = _evaluate_transform_on_siliquant_block(
        P5_WEIGHT_BLOCK, P5_REFERENCE_VECTOR, [g_up * x for x in P5_WEIGHT_BLOCK], q_max
    )
    up_res["gain"] = frac_pair(g_up)

    down_res = _evaluate_transform_on_siliquant_block(
        P5_WEIGHT_BLOCK, P5_REFERENCE_VECTOR, [g_down * x for x in P5_WEIGHT_BLOCK], q_max
    )
    down_res["gain"] = frac_pair(g_down)

    # Closed-loop damped multiplicative homeostasis + 1-step deadbeat
    damped = run_multiplicative_homeostasis_exact(Fraction(3, 2), Fraction(1, 1), Fraction(1, 2), 8)
    max_traj_ratio_drift = max(
        pairwise_ratio_max_drift_exact(P5_WEIGHT_BLOCK, [g * x for x in P5_WEIGHT_BLOCK])
        for g in damped["gains"]
    )
    max_traj_abs_flips = max(
        sum(
            1
            for a, b in zip(base_abs_codes, symmetric_absmax_quantize_exact([g * x for x in P5_WEIGHT_BLOCK], q_max)[1])
            if a != b
        )
        for g in damped["gains"]
    )
    damped_clean = {k: v for k, v in damped.items() if k != "gains"}
    damped_clean["max_trajectory_ratio_drift"] = frac_pair(max_traj_ratio_drift)
    damped_clean["max_trajectory_absmax_flips"] = max_traj_abs_flips

    deadbeat_gain = Fraction(1, 1) / Fraction(3, 2)
    deadbeat_post_err = abs(Fraction(3, 2) * deadbeat_gain - Fraction(1, 1))
    deadbeat = {
        "gain": frac_pair(deadbeat_gain),
        "post_step_error": frac_pair(deadbeat_post_err),
    }

    # Must-fail control A: additive shift b = 3/8 (Code.centre / siliquant#16 failure class)
    b_shift = Fraction(3, 8)
    add_res = _evaluate_transform_on_siliquant_block(
        P5_WEIGHT_BLOCK, P5_REFERENCE_VECTOR, [x + b_shift for x in P5_WEIGHT_BLOCK], q_max
    )
    add_res["additive_shift"] = frac_pair(b_shift)
    add_res["zero_floor_error_sq"] = frac_pair(b_shift * b_shift)

    # Must-fail control B: unstable gain eta = 5/2 > 2 from r0 = 21/20
    unstable = run_multiplicative_homeostasis_exact(Fraction(21, 20), Fraction(1, 1), Fraction(5, 2), 3)
    unstable_clean = {k: v for k, v in unstable.items() if k != "gains"}

    return {
        "operator_name": "turrigiano_multiplicative_homeostatic_scaling_siliquant_bridge",
        "engineering_target": "Moissanite-Labs/siliquant per-group symmetric absmax & zero-preserving D8 quantization commutation",
        "block_width": len(P5_WEIGHT_BLOCK),
        "q_max": q_max,
        "base_weights": [frac_pair(x) for x in P5_WEIGHT_BLOCK],
        "base_absmax_codes": base_abs_codes,
        "base_d8_codes": base_d8_codes,
        "multiplicative_upscaling": up_res,
        "multiplicative_downscaling": down_res,
        "damped_homeostatic_control": damped_clean,
        "deadbeat_homeostatic_control": deadbeat,
        "must_fail_additive_shift_control": add_res,
        "must_fail_unstable_gain_control": unstable_clean,
    }


# ---------------------------------------------------------------------------
# Certificate assembly & fail-closed validation
# ---------------------------------------------------------------------------


def _assemble_nature_extended_certificate() -> dict:
    p1 = audit_kinetic_proofreading_exact()
    p2 = audit_immune_negative_selection_exact()
    p3 = audit_turing_reaction_diffusion_exact()
    p4 = audit_starling_topological_flocking_exact()
    p5 = audit_synaptic_homeostatic_siliquant_exact()

    pillars_map = {
        "p1_kinetic_proofreading": p1,
        "p2_immune_negative_selection": p2,
        "p3_turing_reaction_diffusion": p3,
        "p4_starling_topological_flocking": p4,
        "p5_synaptic_homeostatic_siliquant": p5,
    }
    must_fail_count = sum(
        1 for pdata in pillars_map.values() for key in pdata if key.startswith("must_fail_")
    )

    payload = {
        "schema": SCHEMA_VERSION,
        "audit_id": AUDIT_ID,
        "governance": {
            "aletheia_version": ALETHEIA_VERSION,
            "zero_floats": True,
            "zero_bare_asserts": True,
            "strict_law4_n0_quarantine": True,
            "strict_law5_zero_metaphor": True,
            "zero_external_writes": True,
        },
        "law4_novelty": {
            "classical_mechanisms_class": "N0",
            "engineering_certifier_class": "N0",
            "primary_source_count": len(LAW4_N0_PRIMARY_SOURCES),
        },
        "law5_discipline": {
            "metaphor_claims_present": False,
            "all_mechanisms_have_must_fail_controls": True,
            "operator_scope": "exact_pure_q_operators_and_controls_only",
        },
        "primary_sources": [dict(src) for src in LAW4_N0_PRIMARY_SOURCES],
        "pillars": pillars_map,
        "summary": {
            "pillars_passed": len(pillars_map),
            "must_fail_controls_verified": must_fail_count,
            "all_passed": True,
        },
    }
    digest = hashlib.sha256(canonical_json_bytes(payload)).hexdigest()
    payload["canonical_sha256"] = digest
    return payload


def build_nature_extended_certificate() -> dict:
    payload = _assemble_nature_extended_certificate()
    validate_certificate(payload)
    return payload


_GOV_KEYS = frozenset({
    "aletheia_version", "zero_floats", "zero_bare_asserts",
    "strict_law4_n0_quarantine", "strict_law5_zero_metaphor", "zero_external_writes",
})
_LAW4_KEYS = frozenset({"classical_mechanisms_class", "engineering_certifier_class", "primary_source_count"})
_LAW5_KEYS = frozenset({"metaphor_claims_present", "all_mechanisms_have_must_fail_controls", "operator_scope"})
_SOURCE_KEYS = frozenset({"id", "pillar", "authors", "year", "title", "venue", "doi", "novelty_class"})
_SUMMARY_KEYS = frozenset({"pillars_passed", "must_fail_controls_verified", "all_passed"})

_P1_KEYS = frozenset({
    "operator_name", "engineering_target", "intrinsic_f0", "intrinsic_f0_dec6", "stages",
    "error_reduction_k0_to_k1", "error_reduction_k0_to_k1_dec6",
    "error_reduction_k0_to_k2", "error_reduction_k0_to_k2_dec6",
    "monotone_exponentiation", "must_fail_equilibrium_control", "must_fail_coupled_gate_control",
})
_P1_STAGE_KEYS = frozenset({
    "proofreading_steps", "discrimination_stages", "flux_correct", "flux_wrong",
    "error_ratio", "error_ratio_dec6", "closed_form_error_ratio", "closed_form_residual",
    "thermodynamic_floor", "thermodynamic_floor_dec6", "beats_f0", "above_floor",
})
_P1_EQ_KEYS = frozenset({"k2_detailed_balance", "cycle_balance_ratio", "error_ratio", "error_ratio_dec6", "strictly_worse_than_f0"})
_P1_CP_KEYS = frozenset({"error_ratio", "error_ratio_dec6", "strictly_worse_than_f0"})

_P2_KEYS = frozenset({
    "operator_name", "engineering_target", "bit_length", "universe_size", "self_size", "nonself_size",
    "self_strings", "r_sweep", "non_monotone_hole_witness",
    "must_fail_overbroad_collapse_r2", "must_fail_uncensored_control", "exact_memory_limit_r8",
})
_P2_ROW_KEYS = frozenset({
    "r", "detector_count", "detector_universe_fraction", "false_positive_count",
    "detected_count", "hole_count", "recombinant_hole_count", "recombinant_hole_subset_holds",
    "detection_rate", "detection_rate_dec6", "hole_rate", "hole_rate_dec6",
    "first_hole", "first_recombinant_hole",
})
_P2_R2_KEYS = frozenset({"r", "detector_count", "detection_rate", "collapsed_to_zero_detectors"})
_P2_UNC_KEYS = frozenset({"detector", "r", "false_positive_count", "false_positive_rate", "false_positive_rate_dec6", "breaks_zero_fp_invariant"})
_P2_R8_KEYS = frozenset({"r", "detector_count", "hole_count"})

_P3_KEYS = frozenset({
    "operator_name", "engineering_target", "jacobian", "c6_spectrum", "turing_witness",
    "must_fail_equal_diffusion_control", "must_fail_subthreshold_ratio_control", "must_fail_discrete_spectral_gap_control",
})
_P3_SPEC_KEYS = frozenset({"ring_size", "ring_eigenvalues", "max_eigenvector_residual"})
_P3_WIT_KEYS = frozenset({"dispersion", "homogeneous_dynamics", "mode1_dynamics"})
_P3_EQ_KEYS = frozenset({"dispersion", "mode1_dynamics"})
_P3_SUB_KEYS = frozenset({"dispersion"})
_P3_GAP_KEYS = frozenset({"dispersion", "continuous_probe_lambda", "continuous_probe_det"})
_P3_DISP_KEYS = frozenset({
    "d_u", "d_v", "trace_j", "det_j", "homogeneous_stable", "s_term",
    "turing_discriminant", "continuous_turing_unstable", "discrete_turing_unstable", "modes",
})
_P3_MODE_KEYS = frozenset({"eigenvalue", "trace", "det", "unstable"})
_P3_DYN_KEYS = frozenset({"steps", "dt", "initial_norm_sq", "final_norm_sq_dec6", "norm_sq_ratio", "norm_sq_ratio_dec6", "amplified", "decayed"})

_P4_KEYS = frozenset({
    "operator_name", "engineering_target", "agent_count", "topological_k", "metric_radius_sq",
    "scales", "k6_boundary_tie_count", "k1_boundary_tie_count", "topological_scaling",
    "all_scale_edges_identical", "all_scale_connected", "all_scale_reff_identical",
    "max_single_node_ablation_components", "two_vertex_connected",
    "must_fail_metric_fragmentation_control", "must_fail_subcritical_k1_control",
})
_P4_TOPO_KEYS = frozenset({
    "scale", "area_density_factor", "edge_count", "boundary_tie_count", "components",
    "diameter", "reff_0_to_15", "reff_0_to_15_dec6", "edges_identical_to_s1",
})
_P4_MET_KEYS = frozenset({"scaling", "s1_components", "s4_components", "s4_edge_count", "fragments_to_singletons"})
_P4_MET_ROW_KEYS = frozenset({
    "scale", "area_density_factor", "radius_sq", "edge_count", "components",
    "diameter", "reff_0_to_15", "reff_0_to_15_dec6",
})
_P4_K1_KEYS = frozenset({"k", "edge_count", "components", "disconnected"})

_P5_KEYS = frozenset({
    "operator_name", "engineering_target", "block_width", "q_max", "base_weights",
    "base_absmax_codes", "base_d8_codes", "multiplicative_upscaling", "multiplicative_downscaling",
    "damped_homeostatic_control", "deadbeat_homeostatic_control",
    "must_fail_additive_shift_control", "must_fail_unstable_gain_control",
})
_P5_MUL_KEYS = frozenset({
    "gain", "max_ratio_drift", "max_ratio_drift_dec6", "squared_cosine_drift", "squared_cosine_drift_dec6",
    "zero_weight_after", "absmax_codes", "absmax_code_flips", "d8_codes", "d8_code_flips",
})
_P5_DMP_KEYS = frozenset({
    "r0", "target", "eta", "steps", "initial_error", "final_error", "final_error_dec6", "final_gain",
    "strictly_monotone_decay", "amplified_error", "max_trajectory_ratio_drift", "max_trajectory_absmax_flips",
})
_P5_DB_KEYS = frozenset({"gain", "post_step_error"})
_P5_ADD_KEYS = frozenset({
    "additive_shift", "zero_floor_error_sq", "max_ratio_drift", "max_ratio_drift_dec6",
    "squared_cosine_drift", "squared_cosine_drift_dec6", "zero_weight_after",
    "absmax_codes", "absmax_code_flips", "d8_codes", "d8_code_flips",
})
_P5_UNST_KEYS = frozenset({
    "r0", "target", "eta", "steps", "initial_error", "final_error", "final_error_dec6",
    "final_gain", "strictly_monotone_decay", "amplified_error",
})


def _parse_frac_pair(obj, label: str) -> Fraction:
    if type(obj) is not list or len(obj) != 2:
        raise NatureExtendedError("ERR_CERT_FRAC", f"{label} must be 2-element list")
    num, den = obj[0], obj[1]
    if not _is_strict_int(num) or not _is_strict_int(den) or den <= 0:
        raise NatureExtendedError("ERR_CERT_FRAC", f"{label} must be [int, pos_int]")
    if math.gcd(abs(num), den) != 1:
        raise NatureExtendedError("ERR_CERT_FRAC", f"{label} must be reduced fraction pair")
    return Fraction(num, den)


def _req_dict(obj, label: str) -> dict:
    if type(obj) is not dict:
        raise NatureExtendedError("ERR_CERT_TYPE", f"{label} must be dict")
    return obj


def _req_exact_keys(mapping: dict, expected: frozenset, label: str) -> None:
    if frozenset(mapping.keys()) != expected:
        raise NatureExtendedError("ERR_CERT_KEYS", f"{label} key set mismatch")


def _req_bool(mapping: dict, key: str, expected: bool, label: str) -> None:
    if key not in mapping or mapping[key] is not expected:
        raise NatureExtendedError("ERR_CERT_BOOL", f"{label}.{key} must be {expected}")


def _req_nonempty_str(mapping: dict, key: str, label: str) -> str:
    if key not in mapping or not _is_strict_str(mapping[key]) or len(mapping[key].strip()) == 0:
        raise NatureExtendedError("ERR_CERT_STR", f"{label}.{key} must be non-empty str")
    return mapping[key]


def _req_int_eq(mapping: dict, key: str, expected: int, label: str) -> None:
    if key not in mapping or not _is_strict_int(mapping[key]) or mapping[key] != expected:
        raise NatureExtendedError("ERR_CERT_INT", f"{label}.{key} must equal {expected}")


def _validate_code_vec(vec, q_max: int, require_even_sum: bool, label: str) -> None:
    if type(vec) is not list or len(vec) != 8:
        raise NatureExtendedError("ERR_CERT_P5", f"{label} must be 8-element int list")
    for c in vec:
        if not _is_strict_int(c) or c < -q_max or c > q_max:
            raise NatureExtendedError("ERR_CERT_P5", f"{label} code out of [-{q_max}, {q_max}]")
    if require_even_sum and sum(vec) % 2 != 0:
        raise NatureExtendedError("ERR_CERT_P5", f"{label} must satisfy D8 even-sum parity")


def _validate_pillar1(p1: dict) -> None:
    _req_exact_keys(p1, _P1_KEYS, "p1")
    f0 = _parse_frac_pair(p1.get("intrinsic_f0"), "p1.intrinsic_f0")
    if f0 != Fraction(1, 10):
        raise NatureExtendedError("ERR_CERT_P1", "p1 intrinsic_f0 must be 1/10")
    stages = p1.get("stages")
    if type(stages) is not list or len(stages) != 3:
        raise NatureExtendedError("ERR_CERT_P1", "p1 stages must have 3 entries")
    ratios = []
    for idx, st in enumerate(stages):
        sd = _req_dict(st, f"p1.stages[{idx}]")
        _req_exact_keys(sd, _P1_STAGE_KEYS, f"p1.stages[{idx}]")
        _req_int_eq(sd, "proofreading_steps", idx, f"p1.stages[{idx}]")
        _req_bool(sd, "beats_f0", idx >= 1, f"p1.stages[{idx}]")
        _req_bool(sd, "above_floor", True, f"p1.stages[{idx}]")
        if _parse_frac_pair(sd.get("closed_form_residual"), f"p1.stages[{idx}].residual") != 0:
            raise NatureExtendedError("ERR_CERT_P1", "non-zero closed_form_residual")
        r_val = _parse_frac_pair(sd.get("error_ratio"), f"p1.stages[{idx}].error_ratio")
        if r_val <= 0:
            raise NatureExtendedError("ERR_CERT_P1", "error_ratio must be strictly positive")
        ratios.append(r_val)
    if not (ratios[2] < ratios[1] < ratios[0] and ratios[1] < f0 and ratios[2] < f0 * f0):
        raise NatureExtendedError("ERR_CERT_P1", "proofreading exponentiation invariant violated")
    if _parse_frac_pair(p1.get("error_reduction_k0_to_k1"), "p1.red_k1") != ratios[0] / ratios[1]:
        raise NatureExtendedError("ERR_CERT_P1", "error_reduction_k0_to_k1 mismatch")
    if _parse_frac_pair(p1.get("error_reduction_k0_to_k2"), "p1.red_k2") != ratios[0] / ratios[2]:
        raise NatureExtendedError("ERR_CERT_P1", "error_reduction_k0_to_k2 mismatch")
    _req_bool(p1, "monotone_exponentiation", True, "p1")

    eq = _req_dict(p1.get("must_fail_equilibrium_control"), "p1.eq_ctrl")
    _req_exact_keys(eq, _P1_EQ_KEYS, "p1.eq_ctrl")
    if _parse_frac_pair(eq.get("cycle_balance_ratio"), "p1.eq_ctrl.cycle_balance_ratio") != 1:
        raise NatureExtendedError("ERR_CERT_P1", "equilibrium detailed balance ratio must be 1/1")
    if _parse_frac_pair(eq.get("error_ratio"), "p1.eq_ctrl.error_ratio") <= f0:
        raise NatureExtendedError("ERR_CERT_P1", "equilibrium control must exceed f0")
    _req_bool(eq, "strictly_worse_than_f0", True, "p1.eq_ctrl")

    cp = _req_dict(p1.get("must_fail_coupled_gate_control"), "p1.coupled_ctrl")
    _req_exact_keys(cp, _P1_CP_KEYS, "p1.coupled_ctrl")
    if _parse_frac_pair(cp.get("error_ratio"), "p1.coupled_ctrl.error_ratio") <= f0:
        raise NatureExtendedError("ERR_CERT_P1", "coupled control must exceed f0")
    _req_bool(cp, "strictly_worse_than_f0", True, "p1.coupled_ctrl")


def _validate_pillar2(p2: dict) -> None:
    _req_exact_keys(p2, _P2_KEYS, "p2")
    _req_int_eq(p2, "bit_length", 8, "p2")
    _req_int_eq(p2, "universe_size", 256, "p2")
    _req_int_eq(p2, "self_size", 8, "p2")
    _req_int_eq(p2, "nonself_size", 248, "p2")
    sweep = p2.get("r_sweep")
    if type(sweep) is not list or len(sweep) != 7:
        raise NatureExtendedError("ERR_CERT_P2", "p2 r_sweep must have 7 entries (r=2..8)")
    by_r = {}
    for idx, row in enumerate(sweep):
        rd = _req_dict(row, f"p2.r_sweep[{idx}]")
        _req_exact_keys(rd, _P2_ROW_KEYS, f"p2.r_sweep[{idx}]")
        expected_r = idx + 2
        _req_int_eq(rd, "r", expected_r, f"p2.r_sweep[{idx}]")
        _req_int_eq(rd, "false_positive_count", 0, f"p2.r_sweep[{idx}]")
        _req_bool(rd, "recombinant_hole_subset_holds", True, f"p2.r_sweep[{idx}]")
        det_c = rd.get("detected_count")
        hole_c = rd.get("hole_count")
        dtr_c = rd.get("detector_count")
        rec_c = rd.get("recombinant_hole_count")
        if not (_is_strict_int(det_c) and _is_strict_int(hole_c)) or det_c < 0 or det_c + hole_c != 248:
            raise NatureExtendedError("ERR_CERT_P2", "detected_count + hole_count must be non-negative and sum to 248")
        if not (_is_strict_int(dtr_c) and _is_strict_int(rec_c)) or dtr_c < 0 or dtr_c > 256 or rec_c < 0 or rec_c > hole_c:
            raise NatureExtendedError("ERR_CERT_P2", "detector_count or recombinant_hole_count out of bounds")
        by_r[expected_r] = rd
    if by_r[2].get("detector_count") != 0:
        raise NatureExtendedError("ERR_CERT_P2", "r=2 must collapse to 0 detectors")
    if by_r[4].get("hole_count", 0) <= by_r[3].get("hole_count", 0):
        raise NatureExtendedError("ERR_CERT_P2", "r=4 must demonstrate non-monotone hole increase over r=3")
    if by_r[8].get("hole_count") != 0 or by_r[8].get("detector_count") != 248:
        raise NatureExtendedError("ERR_CERT_P2", "r=8 must reach full memory limit with 0 holes")
    _req_bool(p2, "non_monotone_hole_witness", True, "p2")

    r2_ctrl = _req_dict(p2.get("must_fail_overbroad_collapse_r2"), "p2.r2_ctrl")
    _req_exact_keys(r2_ctrl, _P2_R2_KEYS, "p2.r2_ctrl")
    _req_bool(r2_ctrl, "collapsed_to_zero_detectors", True, "p2.r2_ctrl")
    unc = _req_dict(p2.get("must_fail_uncensored_control"), "p2.uncensored_ctrl")
    _req_exact_keys(unc, _P2_UNC_KEYS, "p2.uncensored_ctrl")
    fp_c = unc.get("false_positive_count")
    if not _is_strict_int(fp_c) or fp_c < 1:
        raise NatureExtendedError("ERR_CERT_P2", "uncensored control must have >= 1 false positive")
    _req_bool(unc, "breaks_zero_fp_invariant", True, "p2.uncensored_ctrl")
    r8_lim = _req_dict(p2.get("exact_memory_limit_r8"), "p2.r8_lim")
    _req_exact_keys(r8_lim, _P2_R8_KEYS, "p2.r8_lim")


def _validate_c6_modes(disp: dict, expected_unstable_lams: frozenset, label: str) -> None:
    _req_exact_keys(disp, _P3_DISP_KEYS, f"{label}.disp")
    modes = disp.get("modes")
    if type(modes) is not list or len(modes) != 4:
        raise NatureExtendedError("ERR_CERT_P3", f"{label}.modes must have 4 entries")
    expected_lams = (0, 1, 3, 4)
    for idx, mode in enumerate(modes):
        md = _req_dict(mode, f"{label}.modes[{idx}]")
        _req_exact_keys(md, _P3_MODE_KEYS, f"{label}.modes[{idx}]")
        lam = _parse_frac_pair(md.get("eigenvalue"), f"{label}.modes[{idx}].lam")
        if lam != Fraction(expected_lams[idx], 1):
            raise NatureExtendedError("ERR_CERT_P3", f"{label}.modes[{idx}] eigenvalue mismatch")
        det_val = _parse_frac_pair(md.get("det"), f"{label}.modes[{idx}].det")
        want_unstable = expected_lams[idx] in expected_unstable_lams
        _req_bool(md, "unstable", want_unstable, f"{label}.modes[{idx}]")
        if want_unstable and det_val >= 0:
            raise NatureExtendedError("ERR_CERT_P3", f"{label}.modes[{idx}] unstable mode needs det < 0")
        if not want_unstable and det_val <= 0:
            raise NatureExtendedError("ERR_CERT_P3", f"{label}.modes[{idx}] stable mode needs det > 0")


def _validate_pillar3(p3: dict) -> None:
    _req_exact_keys(p3, _P3_KEYS, "p3")
    spec = _req_dict(p3.get("c6_spectrum"), "p3.c6_spectrum")
    _req_exact_keys(spec, _P3_SPEC_KEYS, "p3.c6_spectrum")
    eigs = spec.get("ring_eigenvalues")
    if type(eigs) is not list or eigs != [0, 1, 3, 4] or any(not _is_strict_int(x) for x in eigs):
        raise NatureExtendedError("ERR_CERT_P3", "ring_eigenvalues must be strict ints [0, 1, 3, 4]")
    if _parse_frac_pair(spec.get("max_eigenvector_residual"), "p3.eig_res") != 0:
        raise NatureExtendedError("ERR_CERT_P3", "C_6 eigenvector residual must be 0/1")

    wit = _req_dict(p3.get("turing_witness"), "p3.witness")
    _req_exact_keys(wit, _P3_WIT_KEYS, "p3.witness")
    wd = _req_dict(wit.get("dispersion"), "p3.witness.disp")
    _req_bool(wd, "homogeneous_stable", True, "p3.witness.disp")
    _req_bool(wd, "continuous_turing_unstable", True, "p3.witness.disp")
    _req_bool(wd, "discrete_turing_unstable", True, "p3.witness.disp")
    if _parse_frac_pair(wd.get("s_term"), "p3.witness.s") <= 0:
        raise NatureExtendedError("ERR_CERT_P3", "Turing witness s_term must be positive")
    if _parse_frac_pair(wd.get("turing_discriminant"), "p3.witness.disc") <= 0:
        raise NatureExtendedError("ERR_CERT_P3", "Turing witness discriminant must be positive")
    _validate_c6_modes(wd, frozenset({1}), "p3.witness")
    hom_d = _req_dict(wit.get("homogeneous_dynamics"), "p3.witness.hom")
    _req_exact_keys(hom_d, _P3_DYN_KEYS, "p3.witness.hom")
    m1_d = _req_dict(wit.get("mode1_dynamics"), "p3.witness.m1")
    _req_exact_keys(m1_d, _P3_DYN_KEYS, "p3.witness.m1")
    hom_ratio = _parse_frac_pair(hom_d.get("norm_sq_ratio"), "p3.hom_ratio")
    if hom_ratio <= 0 or hom_ratio >= 1:
        raise NatureExtendedError("ERR_CERT_P3", "homogeneous mode ratio must lie in (0, 1)")
    if _parse_frac_pair(m1_d.get("norm_sq_ratio"), "p3.m1_ratio") <= 1:
        raise NatureExtendedError("ERR_CERT_P3", "Turing mode 1 must amplify")

    eq = _req_dict(p3.get("must_fail_equal_diffusion_control"), "p3.eq_ctrl")
    _req_exact_keys(eq, _P3_EQ_KEYS, "p3.eq_ctrl")
    eq_d = _req_dict(eq.get("dispersion"), "p3.eq_ctrl.disp")
    _req_bool(eq_d, "continuous_turing_unstable", False, "p3.eq_ctrl.disp")
    _req_bool(eq_d, "discrete_turing_unstable", False, "p3.eq_ctrl.disp")
    _validate_c6_modes(eq_d, frozenset(), "p3.eq_ctrl")
    eq_m1 = _req_dict(eq.get("mode1_dynamics"), "p3.eq_ctrl.m1")
    _req_exact_keys(eq_m1, _P3_DYN_KEYS, "p3.eq_ctrl.m1")
    eq_ratio = _parse_frac_pair(eq_m1.get("norm_sq_ratio"), "p3.eq_m1_ratio")
    if eq_ratio <= 0 or eq_ratio >= 1:
        raise NatureExtendedError("ERR_CERT_P3", "equal-diffusion mode 1 ratio must lie in (0, 1)")

    sub = _req_dict(p3.get("must_fail_subthreshold_ratio_control"), "p3.sub_ctrl")
    _req_exact_keys(sub, _P3_SUB_KEYS, "p3.sub_ctrl")
    sub_d = _req_dict(sub.get("dispersion"), "p3.sub_ctrl.disp")
    if _parse_frac_pair(sub_d.get("s_term"), "p3.sub.s") <= 0:
        raise NatureExtendedError("ERR_CERT_P3", "subthreshold s_term must be positive")
    if _parse_frac_pair(sub_d.get("turing_discriminant"), "p3.sub.disc") >= 0:
        raise NatureExtendedError("ERR_CERT_P3", "subthreshold discriminant must be negative")
    _req_bool(sub_d, "discrete_turing_unstable", False, "p3.sub_ctrl.disp")
    _validate_c6_modes(sub_d, frozenset(), "p3.sub_ctrl")

    gap = _req_dict(p3.get("must_fail_discrete_spectral_gap_control"), "p3.gap_ctrl")
    _req_exact_keys(gap, _P3_GAP_KEYS, "p3.gap_ctrl")
    gap_d = _req_dict(gap.get("dispersion"), "p3.gap_ctrl.disp")
    _req_bool(gap_d, "continuous_turing_unstable", True, "p3.gap_ctrl.disp")
    _req_bool(gap_d, "discrete_turing_unstable", False, "p3.gap_ctrl.disp")
    _validate_c6_modes(gap_d, frozenset(), "p3.gap_ctrl")
    if _parse_frac_pair(gap.get("continuous_probe_det"), "p3.gap.probe") >= 0:
        raise NatureExtendedError("ERR_CERT_P3", "spectral gap continuous probe det must be negative")


def _validate_pillar4(p4: dict) -> None:
    _req_exact_keys(p4, _P4_KEYS, "p4")
    _req_int_eq(p4, "agent_count", 16, "p4")
    _req_int_eq(p4, "topological_k", 6, "p4")
    _req_int_eq(p4, "k6_boundary_tie_count", 0, "p4")
    _req_int_eq(p4, "k1_boundary_tie_count", 0, "p4")
    _req_int_eq(p4, "max_single_node_ablation_components", 1, "p4")
    _req_bool(p4, "all_scale_edges_identical", True, "p4")
    _req_bool(p4, "all_scale_connected", True, "p4")
    _req_bool(p4, "all_scale_reff_identical", True, "p4")
    _req_bool(p4, "two_vertex_connected", True, "p4")

    topo_rows = p4.get("topological_scaling")
    if type(topo_rows) is not list or len(topo_rows) != 4:
        raise NatureExtendedError("ERR_CERT_P4", "topological_scaling must have 4 scale rows")
    ref_reff = None
    for idx, row in enumerate(topo_rows):
        rd = _req_dict(row, f"p4.topo[{idx}]")
        _req_exact_keys(rd, _P4_TOPO_KEYS, f"p4.topo[{idx}]")
        _req_int_eq(rd, "scale", idx + 1, f"p4.topo[{idx}]")
        _req_int_eq(rd, "components", 1, f"p4.topo[{idx}]")
        _req_int_eq(rd, "boundary_tie_count", 0, f"p4.topo[{idx}]")
        _req_bool(rd, "edges_identical_to_s1", True, f"p4.topo[{idx}]")
        diam = rd.get("diameter")
        if not _is_strict_int(diam) or diam < 1:
            raise NatureExtendedError("ERR_CERT_P4", "topological diameter must be positive strict int")
        reff = _parse_frac_pair(rd.get("reff_0_to_15"), f"p4.topo[{idx}].reff")
        if reff <= 0:
            raise NatureExtendedError("ERR_CERT_P4", "topological R_eff must be positive")
        if ref_reff is None:
            ref_reff = reff
        elif reff != ref_reff:
            raise NatureExtendedError("ERR_CERT_P4", "topological R_eff must stay invariant across scales")

    met = _req_dict(p4.get("must_fail_metric_fragmentation_control"), "p4.metric_ctrl")
    _req_exact_keys(met, _P4_MET_KEYS, "p4.metric_ctrl")
    _req_int_eq(met, "s1_components", 1, "p4.metric_ctrl")
    _req_int_eq(met, "s4_components", 16, "p4.metric_ctrl")
    _req_int_eq(met, "s4_edge_count", 0, "p4.metric_ctrl")
    _req_bool(met, "fragments_to_singletons", True, "p4.metric_ctrl")
    m_rows = met.get("scaling")
    if type(m_rows) is not list or len(m_rows) != 4:
        raise NatureExtendedError("ERR_CERT_P4", "metric scaling must have 4 scale rows")
    for idx, mrow in enumerate(m_rows):
        _req_exact_keys(_req_dict(mrow, f"p4.metric[{idx}]"), _P4_MET_ROW_KEYS, f"p4.metric[{idx}]")
    _req_int_eq(m_rows[0], "components", 1, "p4.metric[0]")
    _req_int_eq(m_rows[3], "components", 16, "p4.metric[3]")
    _req_int_eq(m_rows[3], "edge_count", 0, "p4.metric[3]")

    k1 = _req_dict(p4.get("must_fail_subcritical_k1_control"), "p4.k1_ctrl")
    _req_exact_keys(k1, _P4_K1_KEYS, "p4.k1_ctrl")
    k1_c = k1.get("components")
    if not _is_strict_int(k1_c) or k1_c <= 1:
        raise NatureExtendedError("ERR_CERT_P4", "k=1 control must be disconnected")
    _req_bool(k1, "disconnected", True, "p4.k1_ctrl")


def _validate_pillar5(p5: dict) -> None:
    _req_exact_keys(p5, _P5_KEYS, "p5")
    _req_int_eq(p5, "block_width", 8, "p5")
    _req_int_eq(p5, "q_max", 7, "p5")
    _validate_code_vec(p5.get("base_absmax_codes"), 7, False, "p5.base_absmax_codes")
    _validate_code_vec(p5.get("base_d8_codes"), 7, True, "p5.base_d8_codes")
    for key in ("multiplicative_upscaling", "multiplicative_downscaling"):
        sub = _req_dict(p5.get(key), f"p5.{key}")
        _req_exact_keys(sub, _P5_MUL_KEYS, f"p5.{key}")
        _validate_code_vec(sub.get("absmax_codes"), 7, False, f"p5.{key}.absmax_codes")
        _validate_code_vec(sub.get("d8_codes"), 7, True, f"p5.{key}.d8_codes")
        if _parse_frac_pair(sub.get("max_ratio_drift"), f"p5.{key}.ratio") != 0:
            raise NatureExtendedError("ERR_CERT_P5", f"{key} must have 0/1 ratio drift")
        if _parse_frac_pair(sub.get("squared_cosine_drift"), f"p5.{key}.cos") != 0:
            raise NatureExtendedError("ERR_CERT_P5", f"{key} must have 0/1 cosine drift")
        if _parse_frac_pair(sub.get("zero_weight_after"), f"p5.{key}.zero") != 0:
            raise NatureExtendedError("ERR_CERT_P5", f"{key} must preserve 0/1 weight")
        _req_int_eq(sub, "absmax_code_flips", 0, f"p5.{key}")
        _req_int_eq(sub, "d8_code_flips", 0, f"p5.{key}")

    dmp = _req_dict(p5.get("damped_homeostatic_control"), "p5.damped")
    _req_exact_keys(dmp, _P5_DMP_KEYS, "p5.damped")
    _req_bool(dmp, "strictly_monotone_decay", True, "p5.damped")
    dmp_fin = _parse_frac_pair(dmp.get("final_error"), "p5.damped.final")
    dmp_init = _parse_frac_pair(dmp.get("initial_error"), "p5.damped.init")
    if dmp_fin < 0 or dmp_fin >= dmp_init:
        raise NatureExtendedError("ERR_CERT_P5", "damped homeostasis must strictly reduce non-negative error")
    if _parse_frac_pair(dmp.get("max_trajectory_ratio_drift"), "p5.damped.ratio") != 0:
        raise NatureExtendedError("ERR_CERT_P5", "damped homeostasis must keep 0/1 ratio drift")
    _req_int_eq(dmp, "max_trajectory_absmax_flips", 0, "p5.damped")

    db = _req_dict(p5.get("deadbeat_homeostatic_control"), "p5.deadbeat")
    _req_exact_keys(db, _P5_DB_KEYS, "p5.deadbeat")
    if _parse_frac_pair(db.get("post_step_error"), "p5.deadbeat.err") != 0:
        raise NatureExtendedError("ERR_CERT_P5", "deadbeat error must be 0/1")

    add = _req_dict(p5.get("must_fail_additive_shift_control"), "p5.add_ctrl")
    _req_exact_keys(add, _P5_ADD_KEYS, "p5.add_ctrl")
    _validate_code_vec(add.get("absmax_codes"), 7, False, "p5.add.absmax_codes")
    _validate_code_vec(add.get("d8_codes"), 7, True, "p5.add.d8_codes")
    if _parse_frac_pair(add.get("zero_weight_after"), "p5.add.zero") == 0:
        raise NatureExtendedError("ERR_CERT_P5", "additive shift must break zero weight")
    if _parse_frac_pair(add.get("max_ratio_drift"), "p5.add.ratio") <= 0:
        raise NatureExtendedError("ERR_CERT_P5", "additive shift must break pairwise ratios")
    if _parse_frac_pair(add.get("squared_cosine_drift"), "p5.add.cos") <= 0:
        raise NatureExtendedError("ERR_CERT_P5", "additive shift must break cosine similarity")
    abs_f = add.get("absmax_code_flips")
    d8_f = add.get("d8_code_flips")
    if not (_is_strict_int(abs_f) and abs_f > 0 and _is_strict_int(d8_f) and d8_f > 0):
        raise NatureExtendedError("ERR_CERT_P5", "additive shift must flip both absmax and D8 codes")

    unst = _req_dict(p5.get("must_fail_unstable_gain_control"), "p5.unstable_ctrl")
    _req_exact_keys(unst, _P5_UNST_KEYS, "p5.unstable_ctrl")
    u_fin = _parse_frac_pair(unst.get("final_error"), "p5.unstable.final")
    u_init = _parse_frac_pair(unst.get("initial_error"), "p5.unstable.init")
    if u_init <= 0 or u_fin <= u_init:
        raise NatureExtendedError("ERR_CERT_P5", "unstable gain control must amplify positive initial error")
    _req_bool(unst, "amplified_error", True, "p5.unstable_ctrl")


def validate_certificate(cert) -> None:
    """Fail-closed validation of Track S4b (AUDIT-102) certificate structure & invariants."""
    if type(cert) is not dict:
        raise NatureExtendedError("ERR_CERT_TYPE", "certificate must be a dict")
    if contains_float(cert):
        raise NatureExtendedError("ERR_CERT_FLOAT", "floats are forbidden anywhere in certificate")
    _req_exact_keys(cert, EXPECTED_TOP_KEYS, "cert")

    if _req_nonempty_str(cert, "schema", "cert") != SCHEMA_VERSION:
        raise NatureExtendedError("ERR_CERT_SCHEMA", "schema mismatch")
    if _req_nonempty_str(cert, "audit_id", "cert") != AUDIT_ID:
        raise NatureExtendedError("ERR_CERT_AUDIT_ID", "audit_id mismatch")

    gov = _req_dict(cert["governance"], "governance")
    _req_exact_keys(gov, _GOV_KEYS, "governance")
    if _req_nonempty_str(gov, "aletheia_version", "governance") != ALETHEIA_VERSION:
        raise NatureExtendedError("ERR_CERT_GOV", "aletheia_version mismatch")
    for flag in (
        "zero_floats",
        "zero_bare_asserts",
        "strict_law4_n0_quarantine",
        "strict_law5_zero_metaphor",
        "zero_external_writes",
    ):
        _req_bool(gov, flag, True, "governance")

    l4 = _req_dict(cert["law4_novelty"], "law4_novelty")
    _req_exact_keys(l4, _LAW4_KEYS, "law4_novelty")
    if _req_nonempty_str(l4, "classical_mechanisms_class", "law4_novelty") != "N0":
        raise NatureExtendedError("ERR_CERT_LAW4", "classical mechanisms must be N0")
    if _req_nonempty_str(l4, "engineering_certifier_class", "law4_novelty") != "N0":
        raise NatureExtendedError("ERR_CERT_LAW4", "engineering certifier must be N0")
    _req_int_eq(l4, "primary_source_count", len(EXPECTED_SOURCE_IDS), "law4_novelty")

    l5 = _req_dict(cert["law5_discipline"], "law5_discipline")
    _req_exact_keys(l5, _LAW5_KEYS, "law5_discipline")
    _req_bool(l5, "metaphor_claims_present", False, "law5_discipline")
    _req_bool(l5, "all_mechanisms_have_must_fail_controls", True, "law5_discipline")
    _req_nonempty_str(l5, "operator_scope", "law5_discipline")

    sources = cert["primary_sources"]
    if type(sources) is not list:
        raise NatureExtendedError("ERR_CERT_SOURCES", "primary_sources must be list")
    seen_ids = []
    for idx, src in enumerate(sources):
        sd = _req_dict(src, f"primary_sources[{idx}]")
        _req_exact_keys(sd, _SOURCE_KEYS, f"primary_sources[{idx}]")
        sid = _req_nonempty_str(sd, "id", f"primary_sources[{idx}]")
        seen_ids.append(sid)
        for field in ("pillar", "authors", "title", "venue", "doi"):
            _req_nonempty_str(sd, field, f"primary_sources[{idx}]")
        if _req_nonempty_str(sd, "novelty_class", f"primary_sources[{idx}]") != "N0":
            raise NatureExtendedError("ERR_CERT_SOURCES", "every primary source must be N0")
        yr = sd.get("year")
        if not _is_strict_int(yr) or yr < 1950 or yr > 2026:
            raise NatureExtendedError("ERR_CERT_SOURCES", "invalid primary source year")
    if tuple(seen_ids) != EXPECTED_SOURCE_IDS:
        raise NatureExtendedError("ERR_CERT_SOURCES", "primary_sources IDs mismatch")

    pillars = _req_dict(cert["pillars"], "pillars")
    if frozenset(pillars.keys()) != EXPECTED_PILLAR_KEYS:
        raise NatureExtendedError("ERR_CERT_PILLARS", "pillars key set mismatch")
    _validate_pillar1(_req_dict(pillars["p1_kinetic_proofreading"], "p1"))
    _validate_pillar2(_req_dict(pillars["p2_immune_negative_selection"], "p2"))
    _validate_pillar3(_req_dict(pillars["p3_turing_reaction_diffusion"], "p3"))
    _validate_pillar4(_req_dict(pillars["p4_starling_topological_flocking"], "p4"))
    _validate_pillar5(_req_dict(pillars["p5_synaptic_homeostatic_siliquant"], "p5"))

    actual_controls = sum(
        1 for pdata in pillars.values() for key in pdata if key.startswith("must_fail_")
    )
    summary = _req_dict(cert["summary"], "summary")
    _req_exact_keys(summary, _SUMMARY_KEYS, "summary")
    _req_int_eq(summary, "pillars_passed", len(EXPECTED_PILLAR_KEYS), "summary")
    _req_int_eq(summary, "must_fail_controls_verified", actual_controls, "summary")
    _req_bool(summary, "all_passed", True, "summary")

    digest = cert["canonical_sha256"]
    unsigned = {k: v for k, v in cert.items() if k != "canonical_sha256"}
    expected_digest = hashlib.sha256(canonical_json_bytes(unsigned)).hexdigest()
    if not _is_strict_str(digest) or digest != expected_digest:
        raise NatureExtendedError("ERR_CERT_SHA", "canonical_sha256 must be matching strict lowercase hex str")

    expected = _assemble_nature_extended_certificate()
    if canonical_json_bytes(cert) != canonical_json_bytes(expected):
        raise NatureExtendedError(
            "ERR_CERT_VALUE_MISMATCH",
            "certificate values do not match deterministic oracle recomputation",
        )
