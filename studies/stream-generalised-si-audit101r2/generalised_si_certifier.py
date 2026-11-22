#!/usr/bin/env python3
"""Track S5 (AUDIT-101): Independent Pure-Z / Pure-Q Audit & 31-Domain Certifier
for Generalised Superintelligence (https://www.generalised.si).

Zero shared code with upstream GSI verification scripts. Pure Python 3 stdlib
(`int`, `fractions.Fraction`), ZERO floats on trust paths or emitted JSON,
ZERO bare `assert`s, ZERO local host paths in certificates.

Supports two explicit modes:
  - `--live --intake-root <dir>`: parses pinned read-only sitemap/HTML/`llms-full.txt`,
    downloaded `/files/...` exact certificates, and cloned public repos
    (`vatskishan03/Hadamard`, `vatskishan03/Quantum`), verifying every public
    combinatorial/algebraic/statistical-mechanics certificate from scratch.
  - `--standalone`: runs all 8 exact pure-Z/Q verifiers offline on embedded
    known-answer witnesses with zero external files required.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import re
import sys
from typing import Any


ORG_DOMAIN_MAP: dict[str, tuple[str, str]] = {
    "hadamard-matrices": ("Foundation-0/math0", "exact Goethals-Seidel / T-matrix / Williamson PAF certificates"),
    "skew-symmetric-hadamard": ("Foundation-0/math0", "exact skew-type & symmetric Hadamard PAF certificates"),
    "two-gross-circuit-distance": ("Foundation-0/quantum", "exact 16-fault undetectable logical-error circuit witnesses on [[288,12,18]]"),
    "cyclic-difference-set-465": ("Foundation-0/math0", "exact Z_31 quotient group-ring orbit invariants (sum^2=100, PAF=0) for (465,145,45)"),
    "circulant-weighing-matrices": ("Foundation-0/math0", "exact proper CW(n,k) sparse autocorrelation & orbit-inequivalence certificates + Lean 4"),
    "good-matrices-53-55": ("Foundation-0/math0", "exact skew/symmetric Good-matrix PAF quadruples (H_212, H_220) + Lean 4"),
    "williamson-good-order-75": ("Foundation-0/math0", "exact symmetric Williamson quadruple (H_300) bitword & PAF certificate"),
    "complete-mappings-cyclic-groups": ("Foundation-0/math0", "exact enumeration counts for Z_27/Z_29/Z_31 complete mappings (OEIS A003111; unreleased)"),
    "self-dual-codes-stabilizer-states": ("Foundation-0/gfq-codes", "exact mass-formula / inequivalence counts for binary self-dual codes & stabilizer states (unreleased)"),
    "5g-nr-ldpc-minimum-distances": ("Foundation-0/gfq-codes", "exact 5G NR LDPC minimum-distance parity-check witnesses"),
    "bivariate-bicycle-circuit-distances": ("Foundation-0/quantum", "exact bivariate-bicycle schedule circuit-distance certificates"),
    "singer-relative-difference-sets": ("Foundation-0/math0", "exact RDS(364,2,243,81) difference-multiset certificate in Z_728"),
    "sat-competition-refutations": ("Proven-Commons/mcproof", "exact Farkas & GF(2)-parity unsatisfiability refutation certificates"),
    "metabolic-minimal-cut-sets": ("Foundation-0/bi0", "exact minimal cut-set enumeration on 95-reaction E. coli core stoichiometry"),
    "cluster-expansion-ground-states": ("Foundation-0/physics0", "exact integer pair-model ground-state energy certificates on 24 Ag-Pd cells"),
    "ising-3d-density-of-states": ("Foundation-0/physics0", "exact periodic 3D Ising density-of-states partition & 0th-4th moment identities"),
    "candidate-binary-codes": ("Foundation-0/gfq-codes", "exact GF(2) full-rank quasi-cyclic binary linear code generator certificates"),
    "solver-compiler-and-factory": ("Foundation-0/aletheia", "structure-detector -> solver-compiler -> verify loop architecture vs Aletheia/mcproof"),
    "superconducting-tc-ceiling": ("Foundation-0/physics0", "linearised Eliashberg T_c upper-bound white paper (0 public certificate files)"),
    "tc-ceilings-published-data": ("Foundation-0/physics0", "empirical Eliashberg ceiling screen on published electron-phonon tables (0 public files)"),
    "jellium-lower-bounds": ("Foundation-0/physics0", "computer-assisted 3D/2D jellium & Lieb-Oxford lower-bound certificates (0 public files)"),
    "dipolar-magnet-ground-states": ("Foundation-0/physics0", "certified phase diagram bounds for 2D dipolar Ising & dipolar spin ice (0 public files)"),
    "lattice-gas-ground-states": ("Foundation-0/physics0", "certified triangular/periodic lattice-gas ground-state windows (0 public files)"),
    "certified-crystal-structure-prediction": ("Foundation-0/physics0", "certified periodic ion-allocation global-minimum bounds (0 public files)"),
    "perfect-sqs-and-diffusion": ("Foundation-0/physics0", "smallest quaternary SQS cells & variational diffusion brackets (0 public files)"),
    "catalysis-limits": ("Foundation-0/bi0", "log-concave Eyring turnover-frequency volcano & OER dynamic cap bounds (0 public files)"),
    "syndrome-cycles-bivariate-bicycle-codes": ("Foundation-0/quantum", "bivariate-bicycle depth-8 syndrome-cycle distance vs logical error-rate study (0 public files)"),
    "euv-stochastic-failure-certificates": ("Foundation-0/silic0n", "Poisson shot-noise EUV contact-printing failure-probability brackets (0 public files)"),
    "steep-switch-limits": ("Foundation-0/silic0n", "Urbach-tail ballistic steep-switch on/off & switching-energy bounds (0 public files)"),
    "placement-lower-bounds": ("Foundation-0/silic0n", "ISPD 2005 half-perimeter wirelength lower-bound certificates (0 public files)"),
    "moore-bound-defect-two": ("Foundation-0/math0", "diameter-2/3 defect-2 Moore-bound non-existence & 19-comparator median-9 proof (0 public files)"),
}

SILIQUANT_BRIDGE_MAP: dict[str, dict[str, Any]] = {
    "hadamard-matrices": {
        "targets": ["Moissanite-Labs/siliquant:bounds/", "Moissanite-Labs/siliquant:shape/", "PR#24", "Issue#25"],
        "exact_operator_bridge": (
            "Non-2^m orthogonal Hadamard rotations (Goethals-Seidel, 34 T-matrices, WT47/WT83, and "
            "Paley-block / Miyamoto-block constructions in vatskishan03/Hadamard/hadamard/PALEY_BLOCKS.md "
            "& MIYAMOTO_BLOCKS.md) extending PR#24 Hadamard E8_Had outlier-flattening beyond 2^m widths "
            "with exact 1/n 1-hot squared peak ratio"
        ),
    },
    "skew-symmetric-hadamard": {
        "targets": ["Moissanite-Labs/siliquant:bounds/", "Moissanite-Labs/siliquant:shape/", "PR#24", "Issue#25"],
        "exact_operator_bridge": (
            "Skew-symmetric Hadamard & Paley skew negacyclic 4x4 block constructions "
            "(vatskishan03/Hadamard/skew/PALEY_SKEW.md) giving zero-multiply orthogonal rotations "
            "Q = H/sqrt(n) with H + H^T = 2I"
        ),
    },
    "circulant-weighing-matrices": {
        "targets": ["Moissanite-Labs/siliquant:bounds/", "Moissanite-Labs/siliquant:shape/", "PR#24", "PR#26", "Issue#25"],
        "exact_operator_bridge": (
            "Sparse {-1,0,+1} orthogonal circulant weighing rotations Q = W(n,k)/sqrt(k) "
            "(CW(120,36), CW(180,36), CW(98,16)): exact energy conservation ||Wx||_2^2 = k||x||_2^2, "
            "exact 1/k 1-hot squared outlier peak, zero multiplications, and exact n/k signed-add "
            "reduction (10/3x, 5x, 49/8x) vs dense rotations for SIMD/Pallas & TPU v5e dequant"
        ),
    },
    "good-matrices-53-55": {
        "targets": ["Moissanite-Labs/siliquant:bounds/", "Moissanite-Labs/siliquant:shape/", "PR#24", "Issue#25"],
        "exact_operator_bridge": (
            "Explicit order-53/55 Good quadruples (incl. Paley order-53 context) producing non-2^m "
            "skew-type Hadamard rotations H_212 & H_220 with exact 1/212 and 1/220 1-hot squared peak"
        ),
    },
    "williamson-good-order-75": {
        "targets": ["Moissanite-Labs/siliquant:bounds/", "Moissanite-Labs/siliquant:shape/", "PR#24", "Issue#25"],
        "exact_operator_bridge": (
            "Explicit order-75 symmetric Williamson quadruple producing non-2^m Hadamard rotation H_300 "
            "with exact 1/300 1-hot squared outlier flattening"
        ),
    },
    "self-dual-codes-stabilizer-states": {
        "targets": ["Moissanite-Labs/siliquant:lattice/", "Issue#4"],
        "exact_operator_bridge": (
            "Type II doubly-even binary self-dual codes map via Construction A "
            "Lambda(C) = (C + 2 Z^n)/sqrt(2) to even unimodular lattices generalizing E8 ([8,4,4]) "
            "and Leech Lambda_24 for Issue#4 codebook geometry (GSI counts unreleased)"
        ),
    },
    "5g-nr-ldpc-minimum-distances": {
        "targets": ["Moissanite-Labs/siliquant:lattice/", "Issue#4"],
        "exact_operator_bridge": (
            "Exact binary parity-check minimum-distance witnesses directly bound minimum Euclidean "
            "squared norm d_min/2 of Construction A lattice codebooks"
        ),
    },
    "candidate-binary-codes": {
        "targets": ["Moissanite-Labs/siliquant:lattice/", "Issue#4"],
        "exact_operator_bridge": (
            "Quasi-cyclic binary linear code generators ([111,37]..[174,58]) map via Construction A "
            "to high-dimensional lattice codebooks (exhaustive d_min lower bound still open)"
        ),
    },
    "euv-stochastic-failure-certificates": {
        "targets": ["Moissanite-Labs/siliquant:bounds/", "Issue#25"],
        "exact_operator_bridge": (
            "Physical EUV stochastic defect floor bounding SRAM/logic yield beneath Issue#25 serving "
            "roofline (0 public GSI certificate files)"
        ),
    },
    "steep-switch-limits": {
        "targets": ["Moissanite-Labs/siliquant:bounds/", "Issue#25"],
        "exact_operator_bridge": (
            "Ballistic Urbach-tail switching-energy lower bound directly constraining energy-per-op "
            "ceilings in Issue#25 dequant roofline (0 public GSI certificate files)"
        ),
    },
    "placement-lower-bounds": {
        "targets": ["Moissanite-Labs/siliquant:bounds/", "Issue#25"],
        "exact_operator_bridge": (
            "Certified wirelength lower bounds directly constraining on-chip interconnect energy & "
            "bandwidth ceilings in Issue#25 roofline (0 public GSI certificate files)"
        ),
    },
}


def _is_strict_int(value: object) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def _verify_no_floats(obj: object) -> None:
    if isinstance(obj, float):
        raise ValueError("FLOAT_FORBIDDEN")
    if isinstance(obj, dict):
        for k, v in obj.items():
            _verify_no_floats(k)
            _verify_no_floats(v)
    elif isinstance(obj, (list, tuple)):
        for item in obj:
            _verify_no_floats(item)


def _fmt_q(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}" if value.denominator != 1 else str(value.numerator)


def _canonical_sha256(obj: dict[str, Any]) -> str:
    _verify_no_floats(obj)
    return hashlib.sha256(
        json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")
    ).hexdigest()


# ---------------------------------------------------------------------------
# 1. Circulant Weighing Matrix & Orbit-Inequivalence Verifier (GSI-R-0005)
# ---------------------------------------------------------------------------


def verify_circulant_weighing_matrix(
    n: int,
    k: int,
    pos_idx: list[int],
    neg_idx: list[int],
    *,
    require_proper: bool = True,
) -> dict[str, Any]:
    """Verify exact CW(n, k) sparse periodic autocorrelation and optional properness."""
    if not _is_strict_int(n) or n < 2:
        raise ValueError("CW_INVALID_ORDER")
    if not _is_strict_int(k) or k < 1 or k > n:
        raise ValueError("CW_INVALID_WEIGHT")
    if not isinstance(pos_idx, list) or not isinstance(neg_idx, list):
        raise ValueError("CW_SUPPORT_NOT_LIST")
    if not isinstance(require_proper, bool):
        raise ValueError("CW_INVALID_PROPER_FLAG")
    if any(not _is_strict_int(x) or x < 0 or x >= n for x in pos_idx):
        raise ValueError("CW_INVALID_POS_INDEX")
    if any(not _is_strict_int(x) or x < 0 or x >= n for x in neg_idx):
        raise ValueError("CW_INVALID_NEG_INDEX")

    pset = set(pos_idx)
    nset = set(neg_idx)
    if len(pset) != len(pos_idx) or len(nset) != len(neg_idx):
        raise ValueError("CW_DUPLICATE_INDEX")
    if pset & nset:
        raise ValueError("CW_OVERLAPPING_SUPPORTS")
    if len(pos_idx) + len(neg_idx) != k:
        raise ValueError("CW_WEIGHT_MISMATCH")

    row = [0] * n
    for x in pos_idx:
        row[x] = 1
    for x in neg_idx:
        row[x] = -1
    supp = [(x, 1) for x in pos_idx] + [(x, -1) for x in neg_idx]

    for shift in range(1, n):
        acc = sum(val * row[(idx + shift) % n] for idx, val in supp)
        if acc != 0:
            raise ValueError(f"CW_NONZERO_PAF_AT_{shift}")

    base = supp[0][0]
    g = n
    for idx, _val in supp:
        g = math.gcd(g, (idx - base) % n)
    is_proper = g == 1
    if require_proper and not is_proper:
        raise ValueError("CW_NOT_PROPER")

    return {
        "valid": True,
        "n": n,
        "k": k,
        "pos_count": len(pos_idx),
        "neg_count": len(neg_idx),
        "row_sum": len(pos_idx) - len(neg_idx),
        "proper": is_proper,
        "support_gcd": g,
    }


def _cw_canonical_orbit_rep(n: int, pos_idx: list[int], neg_idx: list[int]) -> tuple[tuple[int, ...], tuple[int, ...]]:
    units = [u for u in range(1, n) if math.gcd(u, n) == 1]
    best: tuple[tuple[int, ...], tuple[int, ...]] | None = None
    for u in units:
        pu = [(u * x) % n for x in pos_idx]
        nu = [(u * x) % n for x in neg_idx]
        for shift in range(n):
            ps = tuple(sorted((x + shift) % n for x in pu))
            ns = tuple(sorted((x + shift) % n for x in nu))
            cand = (ps, ns) if (ps, ns) < (ns, ps) else (ns, ps)
            if best is None or cand < best:
                best = cand
    return best if best is not None else ((), ())


def verify_cw_class_set_inequivalent(
    n: int,
    k: int,
    classes: list[dict[str, Any]],
) -> dict[str, Any]:
    """Verify every CW(n, k) class is valid, proper, and pairwise inequivalent under shift/unit/negation."""
    if not isinstance(classes, list) or len(classes) == 0:
        raise ValueError("CW_CLASSES_EMPTY_OR_NOT_LIST")
    seen_orbits: set[tuple[tuple[int, ...], tuple[int, ...]]] = set()
    for entry in classes:
        if not isinstance(entry, dict) or set(entry.keys()) != {"P", "N"}:
            raise ValueError("CW_CLASS_SCHEMA_MISMATCH")
        verify_circulant_weighing_matrix(n, k, entry["P"], entry["N"], require_proper=True)
        rep = _cw_canonical_orbit_rep(n, entry["P"], entry["N"])
        if rep in seen_orbits:
            raise ValueError("CW_EQUIVALENT_DUPLICATE_CLASS")
        seen_orbits.add(rep)
    return {
        "valid": True,
        "n": n,
        "k": k,
        "classes_verified": len(classes),
        "distinct_orbits": len(seen_orbits),
    }


def verify_weighing_matrix_siliquant_rotation(
    n: int,
    k: int,
    pos_idx: list[int],
    neg_idx: list[int],
    input_vec: list[int],
) -> dict[str, Any]:
    """Verify exact pure-Q sparse orthogonal rotation Q = W(n,k)/sqrt(k) for Moissanite-Labs/siliquant."""
    cw = verify_circulant_weighing_matrix(n, k, pos_idx, neg_idx, require_proper=True)
    if not isinstance(input_vec, list) or len(input_vec) != n:
        raise ValueError("WROT_INVALID_INPUT_VEC")
    if any(not _is_strict_int(v) for v in input_vec):
        raise ValueError("WROT_INPUT_NON_INT")
    x_norm_sq = sum(v * v for v in input_vec)
    if x_norm_sq == 0:
        raise ValueError("WROT_ZERO_INPUT_VEC")

    y_vec = [
        sum(input_vec[(r + s) % n] for s in pos_idx) - sum(input_vec[(r + s) % n] for s in neg_idx)
        for r in range(n)
    ]
    y_norm_sq = sum(v * v for v in y_vec)
    y_inf_abs = max(abs(v) for v in y_vec)
    x_support_size = sum(1 for v in input_vec if v != 0)
    actual_peak_sq_ratio = Fraction(y_inf_abs * y_inf_abs, y_norm_sq)
    one_hot_peak_sq_ratio = Fraction(1, k)
    cs_peak_bound = Fraction(min(x_support_size, k), k)

    return {
        "valid": True,
        "n": n,
        "k": k,
        "proper": cw["proper"],
        "input_support_size": x_support_size,
        "x_norm_sq": x_norm_sq,
        "y_norm_sq": y_norm_sq,
        "energy_conserved": y_norm_sq == k * x_norm_sq,
        "y_inf_abs": y_inf_abs,
        "actual_peak_sq_ratio": _fmt_q(actual_peak_sq_ratio),
        "one_hot_peak_sq_ratio": _fmt_q(one_hot_peak_sq_ratio),
        "t_sparse_cauchy_schwarz_bound": _fmt_q(cs_peak_bound),
        "cauchy_schwarz_bound_holds": actual_peak_sq_ratio <= cs_peak_bound,
        "signed_adds_per_output": k,
        "dense_adds_per_output": n,
        "signed_add_density": _fmt_q(Fraction(k, n)),
        "dense_op_reduction_factor": _fmt_q(Fraction(n, k)),
        "zero_multiplications": True,
    }


# ---------------------------------------------------------------------------
# 2. Good / Williamson / T-Matrix / Bordered Williamson-Type Verifiers
# ---------------------------------------------------------------------------


def verify_good_or_williamson_quadruple(
    n: int,
    words: list[int],
    *,
    first_skew: bool = True,
) -> dict[str, Any]:
    """Verify Good (skew A + sym B,C,D) or Williamson (4 sym) bitwords yield sum PAF = 0."""
    if not _is_strict_int(n) or n < 3 or n % 2 == 0:
        raise ValueError("GW_INVALID_ODD_ORDER")
    if not isinstance(words, list) or len(words) != 4:
        raise ValueError("GW_WORDS_NOT_FOUR")
    if not isinstance(first_skew, bool):
        raise ValueError("GW_INVALID_SKEW_FLAG")
    half = (n - 1) // 2
    max_word = (1 << half) - 1
    if any(not _is_strict_int(w) or w < 0 or w > max_word for w in words):
        raise ValueError("GW_WORD_OUT_OF_RANGE")

    seqs: list[list[int]] = []
    for idx, w in enumerate(words):
        row = [1] * n
        for i in range(1, half + 1):
            val = -1 if ((w >> (i - 1)) & 1) else 1
            row[i] = val
            row[n - i] = -val if (idx == 0 and first_skew) else val
        seqs.append(row)

    for shift in range(1, n):
        tot = sum(sum(seq[i] * seq[(i + shift) % n] for i in range(n)) for seq in seqs)
        if tot != 0:
            raise ValueError(f"GW_NONZERO_PAF_AT_{shift}")

    row_sums = [sum(seq) for seq in seqs]
    return {
        "valid": True,
        "order": n,
        "hadamard_order": 4 * n,
        "kind": "good_matrices" if first_skew else "williamson_matrices",
        "row_sums": row_sums,
        "row_sum_sq_total": sum(r * r for r in row_sums),
    }


def verify_t_matrix_quadruple(t: int, rows: list[str]) -> dict[str, Any]:
    """Verify 4 T-matrices of order t partition Z_t with sum PAF(s) = 0 for all s != 0."""
    if not _is_strict_int(t) or t < 1:
        raise ValueError("TMAT_INVALID_ORDER")
    if not isinstance(rows, list) or len(rows) != 4:
        raise ValueError("TMAT_ROWS_NOT_FOUR")
    mp = {"+": 1, "-": -1, "0": 0}
    vecs: list[list[int]] = []
    for r in rows:
        if not isinstance(r, str) or len(r) != t:
            raise ValueError("TMAT_INVALID_ROW_LEN")
        if any(ch not in mp for ch in r):
            raise ValueError("TMAT_INVALID_ENTRY_CHAR")
        vecs.append([mp[ch] for ch in r])

    for j in range(t):
        if sum(abs(vecs[k][j]) for k in range(4)) != 1:
            raise ValueError(f"TMAT_PARTITION_VIOLATION_AT_{j}")

    for shift in range(1, t):
        tot = sum(sum(v[j] * v[(j + shift) % t] for j in range(t)) for v in vecs)
        if tot != 0:
            raise ValueError(f"TMAT_NONZERO_PAF_AT_{shift}")

    return {
        "valid": True,
        "order": t,
        "od_order": 4 * t,
        "row_sums": [sum(v) for v in vecs],
    }


def verify_bordered_williamson_type(
    order: int,
    sequences: list[str],
    expected_rowsums: list[int],
) -> dict[str, Any]:
    """Verify bordered Williamson-type core sequences of length order-1 satisfy PAF_sum == -4."""
    if not _is_strict_int(order) or order < 3 or order % 2 == 0:
        raise ValueError("BWT_INVALID_ORDER")
    if not isinstance(sequences, list) or len(sequences) != 4:
        raise ValueError("BWT_SEQUENCES_NOT_FOUR")
    if not isinstance(expected_rowsums, list) or len(expected_rowsums) != 4:
        raise ValueError("BWT_ROWSUMS_NOT_FOUR")
    if any(not _is_strict_int(r) for r in expected_rowsums):
        raise ValueError("BWT_INVALID_ROWSUM_INT")

    core_n = order - 1
    mp = {"+": 1, "-": -1}
    vecs: list[list[int]] = []
    for s in sequences:
        if not isinstance(s, str) or len(s) != core_n:
            raise ValueError("BWT_INVALID_SEQ_LEN")
        if any(ch not in mp for ch in s):
            raise ValueError("BWT_INVALID_SEQ_CHAR")
        vecs.append([mp[ch] for ch in s])

    actual_rsums = [sum(v) for v in vecs]
    if actual_rsums != expected_rowsums:
        raise ValueError("BWT_ROWSUM_MISMATCH")

    for shift in range(1, core_n):
        tot = sum(sum(v[j] * v[(j + shift) % core_n] for j in range(core_n)) for v in vecs)
        if tot != -4:
            raise ValueError(f"BWT_INVALID_CORE_PAF_AT_{shift}")

    return {
        "valid": True,
        "order": order,
        "core_length": core_n,
        "row_sums": actual_rsums,
        "core_offdiag_paf_sum": -4,
    }


# ---------------------------------------------------------------------------
# 3. Relative Difference Sets & Cyclic Difference Set Projection Orbits
# ---------------------------------------------------------------------------


def verify_relative_difference_set(
    v: int,
    n_ker: int,
    k: int,
    mu: int,
    elements: list[int],
) -> dict[str, Any]:
    """Verify cyclic (v, n_ker, k, mu) RDS in Z_{v*n_ker} with forbidden subgroup v*Z_{v*n_ker}."""
    if not _is_strict_int(v) or v < 2:
        raise ValueError("RDS_INVALID_V")
    if not _is_strict_int(n_ker) or n_ker < 2:
        raise ValueError("RDS_INVALID_N_KER")
    if not _is_strict_int(k) or k < 2:
        raise ValueError("RDS_INVALID_K")
    if not _is_strict_int(mu) or mu < 1:
        raise ValueError("RDS_INVALID_MU")
    if k * (k - 1) != n_ker * (v - 1) * mu:
        raise ValueError("RDS_COUNTING_IDENTITY_FAILED")
    if not isinstance(elements, list) or len(elements) != k:
        raise ValueError("RDS_ELEMENT_COUNT_MISMATCH")

    mod = v * n_ker
    if any(not _is_strict_int(x) or x < 0 or x >= mod for x in elements):
        raise ValueError("RDS_ELEMENT_OUT_OF_RANGE")
    if len(set(elements)) != k:
        raise ValueError("RDS_DUPLICATE_ELEMENT")

    diffs = [0] * mod
    for a in elements:
        for b in elements:
            if a != b:
                diffs[(a - b) % mod] += 1

    for d in range(mod):
        expected = 0 if (d % v == 0) else mu
        if diffs[d] != expected:
            raise ValueError(f"RDS_DIFF_MULTIPLICITY_FAILED_AT_{d}")

    return {
        "valid": True,
        "group_order": mod,
        "v": v,
        "n_ker": n_ker,
        "k": k,
        "mu": mu,
        "non_forbidden_diffs_verified": mod - n_ker,
    }


def verify_cyclic_ds_projection_orbit(
    p: int,
    abs_sum_target: int,
    sq_sum_target: int,
    vec: list[int],
) -> dict[str, Any]:
    """Verify Z_p projection orbit representative satisfies |sum|=abs_sum_target, sum(x^2)=sq_sum_target, PAF=0."""
    if not _is_strict_int(p) or p < 2:
        raise ValueError("PROJ_INVALID_P")
    if not _is_strict_int(abs_sum_target) or abs_sum_target < 0:
        raise ValueError("PROJ_INVALID_SUM_TARGET")
    if not _is_strict_int(sq_sum_target) or sq_sum_target < 1:
        raise ValueError("PROJ_INVALID_SQ_TARGET")
    if not isinstance(vec, list) or len(vec) != p:
        raise ValueError("PROJ_VECTOR_LEN_MISMATCH")
    if any(not _is_strict_int(x) for x in vec):
        raise ValueError("PROJ_VECTOR_NON_INT")
    total = sum(vec)
    if abs(total) != abs_sum_target:
        raise ValueError("PROJ_SUM_MISMATCH")
    sq_total = sum(x * x for x in vec)
    if sq_total != sq_sum_target:
        raise ValueError("PROJ_SQ_SUM_MISMATCH")
    for shift in range(1, p):
        acc = sum(vec[i] * vec[(i + shift) % p] for i in range(p))
        if acc != 0:
            raise ValueError(f"PROJ_NONZERO_PAF_AT_{shift}")
    return {
        "valid": True,
        "p": p,
        "sum": total,
        "sq_sum": sq_total,
    }


# ---------------------------------------------------------------------------
# 4. Binary Linear Code Generator Rank & Honest Upper/Lower Scope Verifier
# ---------------------------------------------------------------------------


def verify_binary_linear_code_generator(
    n: int,
    k: int,
    hex_rows: list[str],
    claimed_d: int,
) -> dict[str, Any]:
    """Verify GF(2) full rank k and generator-row weights >= claimed_d (explicitly NOT exhaustive d_min)."""
    if not _is_strict_int(n) or n < 2:
        raise ValueError("CODE_INVALID_N")
    if not _is_strict_int(k) or k < 1 or k > n:
        raise ValueError("CODE_INVALID_K")
    if not _is_strict_int(claimed_d) or claimed_d < 1 or claimed_d > n:
        raise ValueError("CODE_INVALID_CLAIMED_D")
    if not isinstance(hex_rows, list) or len(hex_rows) != k:
        raise ValueError("CODE_ROW_COUNT_MISMATCH")

    limit = 1 << n
    rows: list[int] = []
    for hr in hex_rows:
        if not isinstance(hr, str) or len(hr) == 0 or any(c not in "0123456789abcdefABCDEF" for c in hr):
            raise ValueError("CODE_INVALID_HEX_ROW")
        val = int(hr, 16)
        if val <= 0 or val >= limit:
            raise ValueError("CODE_ROW_OUT_OF_RANGE")
        rows.append(val)

    min_row_wt = min(r.bit_count() for r in rows)
    if min_row_wt < claimed_d:
        raise ValueError("CODE_GENERATOR_ROW_BELOW_CLAIMED_D")

    basis: list[int] = []
    for r in rows:
        x = r
        for b in basis:
            if (x ^ b) < x:
                x ^= b
        if x == 0:
            raise ValueError("CODE_RANK_DEFICIENT")
        basis.append(x)
        basis.sort(reverse=True)

    return {
        "valid": True,
        "n": n,
        "k": k,
        "gf2_rank": len(basis),
        "claimed_d": claimed_d,
        "min_generator_row_weight": min_row_wt,
        "exhaustive_dmin_proved": False,
        "scope_note": "generator_rank_and_row_weight_only_not_exhaustive_dmin",
    }


# ---------------------------------------------------------------------------
# 5. 3D Periodic Cubic Ising Exact Density-of-States Analytic Moment Verifier
# ---------------------------------------------------------------------------


def verify_ising_3d_dos_moments(
    dims: tuple[int, int, int],
    pairs: list[tuple[int, int]],
) -> dict[str, Any]:
    """Verify exact 0th..4th energy moments, ground-state & 1-flip degeneracies, and bipartite symmetry."""
    if not isinstance(dims, tuple) or len(dims) != 3:
        raise ValueError("ISING_INVALID_DIMS")
    if any(not _is_strict_int(L) or L < 4 for L in dims):
        raise ValueError("ISING_DIM_BELOW_4")
    if not isinstance(pairs, list) or len(pairs) == 0:
        raise ValueError("ISING_EMPTY_PAIRS")

    n_sites = dims[0] * dims[1] * dims[2]
    edges = 3 * n_sites
    pmap: dict[int, int] = {}
    for item in pairs:
        if not isinstance(item, tuple) or len(item) != 2:
            raise ValueError("ISING_PAIR_SCHEMA")
        b, c = item
        if not _is_strict_int(b) or b < 0 or b > edges:
            raise ValueError("ISING_INVALID_BROKEN_BONDS")
        if not _is_strict_int(c) or c <= 0:
            raise ValueError("ISING_NONPOSITIVE_COUNT")
        if b in pmap:
            raise ValueError("ISING_DUPLICATE_ENERGY_LEVEL")
        pmap[b] = c

    pow2 = 1 << n_sites
    m0 = sum(pmap.values())
    if m0 != pow2:
        raise ValueError("ISING_M0_SUM_MISMATCH")
    if pmap.get(0) != 2:
        raise ValueError("ISING_GROUND_STATE_DEG_MISMATCH")
    if pmap.get(6) != 2 * n_sites:
        raise ValueError("ISING_ONE_FLIP_DEG_MISMATCH")

    m1 = sum((2 * b - edges) * c for b, c in pmap.items())
    if m1 != 0:
        raise ValueError("ISING_M1_NONZERO")
    m2 = sum(((2 * b - edges) ** 2) * c for b, c in pmap.items())
    if m2 != edges * pow2:
        raise ValueError("ISING_M2_MISMATCH")
    m3 = sum(((2 * b - edges) ** 3) * c for b, c in pmap.items())
    if m3 != 0:
        raise ValueError("ISING_M3_NONZERO")

    # Exact 4-cycle count P_4 = 3*N plaquettes + wrap-around 4-cycles along any axis of length 4
    p4_wrap = sum(n_sites // L for L in dims if L == 4)
    p4_total = 3 * n_sites + p4_wrap
    exp_m4 = (edges * (3 * edges - 2) + 24 * p4_total) * pow2
    m4 = sum(((2 * b - edges) ** 4) * c for b, c in pmap.items())
    if m4 != exp_m4:
        raise ValueError("ISING_M4_MISMATCH")

    all_even = all(L % 2 == 0 for L in dims)
    bipartite_sym = all(pmap.get(edges - b) == c for b, c in pmap.items())
    if bipartite_sym != all_even:
        raise ValueError("ISING_BIPARTITE_SYMMETRY_MISMATCH")

    return {
        "valid": True,
        "dims": list(dims),
        "n_sites": n_sites,
        "n_edges": edges,
        "energy_levels": len(pmap),
        "p4_four_cycles": p4_total,
        "bipartite_symmetric": bipartite_sym,
        "ground_state_degeneracy": pmap[0],
        "one_flip_degeneracy": pmap[6],
        "moments_verified": ["m0=2^N", "m1=0", "m2=3N*2^N", "m3=0", "m4=(3N(9N-2)+24*P4)*2^N"],
    }


# ---------------------------------------------------------------------------
# 6. Cluster-Expansion Integer Pair-Model Energy & Lean 4 Purity Verifiers
# ---------------------------------------------------------------------------


def verify_cluster_expansion_pair_energy(
    dims: list[int],
    n_sites: int,
    jd_table: list[int],
    a_coeff: int,
    config_bits: str,
    expected_energy: int,
    *,
    expected_occupied: int | None = None,
) -> dict[str, Any]:
    """Verify exact integer pair-model energy E = a*|S| + (1/2) sum_{i!=j in S} Jd[coord(i)-coord(j)]."""
    if not isinstance(dims, list) or len(dims) == 0 or any(not _is_strict_int(d) or d < 1 for d in dims):
        raise ValueError("CE_INVALID_DIMS")
    prod_dims = 1
    for d in dims:
        prod_dims *= d
    if not _is_strict_int(n_sites) or n_sites != prod_dims:
        raise ValueError("CE_N_SITES_MISMATCH")
    if not isinstance(jd_table, list) or len(jd_table) != n_sites or any(not _is_strict_int(v) for v in jd_table):
        raise ValueError("CE_INVALID_JD_TABLE")
    if not _is_strict_int(a_coeff) or not _is_strict_int(expected_energy):
        raise ValueError("CE_INVALID_INT_COEFF")
    if not isinstance(config_bits, str) or len(config_bits) != n_sites or any(ch not in ("0", "1") for ch in config_bits):
        raise ValueError("CE_INVALID_CONFIG_BITS")
    if expected_occupied is not None and (not _is_strict_int(expected_occupied) or config_bits.count("1") != expected_occupied):
        raise ValueError("CE_OCCUPIED_COUNT_MISMATCH")

    def _from_idx(idx: int) -> tuple[int, ...]:
        out: list[int] = []
        rem = idx
        for d in reversed(dims):
            out.append(rem % d)
            rem //= d
        return tuple(reversed(out))

    def _to_idx(coord: tuple[int, ...]) -> int:
        acc = 0
        for v, d in zip(coord, dims):
            acc = acc * d + v
        return acc

    coords = [_from_idx(i) for i in range(n_sites)]
    ones = [i for i, ch in enumerate(config_bits) if ch == "1"]
    pair_sum = 0
    for i in ones:
        ci = coords[i]
        for j in ones:
            if i == j:
                continue
            cj = coords[j]
            diff = tuple((ci[m] - cj[m]) % dims[m] for m in range(len(dims)))
            pair_sum += jd_table[_to_idx(diff)]

    if pair_sum % 2 != 0:
        raise ValueError("CE_ODD_PAIR_SUM")
    energy = a_coeff * len(ones) + (pair_sum // 2)
    if energy != expected_energy:
        raise ValueError("CE_ENERGY_MISMATCH")

    return {
        "valid": True,
        "n_sites": n_sites,
        "occupied_count": len(ones),
        "exact_energy": energy,
    }


def _strip_lean_comments_and_strings(text: str) -> str:
    """Strip Lean 4 string literals, nested `/- ... -/` block comments, and `--` line comments."""
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_string = False
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if in_string:
            if ch == "\\" and i + 1 < n:
                i += 2
                continue
            if ch == '"':
                in_string = False
                out.append(" ")
            i += 1
            continue
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                out.append(" ")
                i += 2
                continue
            if ch == "\n":
                out.append("\n")
            i += 1
            continue
        if ch == "-" and nxt == "-":
            while i < n and text[i] != "\n":
                i += 1
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            i += 2
            continue
        if ch == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue
        out.append(ch)
        i += 1
    if in_string or block_depth != 0:
        raise ValueError("LEAN_UNCLOSED_DELIMITER")
    return "".join(out)


def verify_lean_file_purity(text: str) -> dict[str, Any]:
    """Pure-stdlib Lean 4 purity check rejecting sorry/sorryAx/admit/axiom/unsafe/native_decide outside comments/strings."""
    if not isinstance(text, str) or len(text.strip()) == 0:
        raise ValueError("LEAN_EMPTY_OR_NOT_STR")
    body = _strip_lean_comments_and_strings(text)
    banned = re.findall(
        r"\b(?:sorry|sorryAx|admit|axiom|unsafe|implemented_by|extern|native_decide|ofReduceBool)\b",
        body,
    )
    if banned:
        raise ValueError(f"LEAN_IMPURE_TOKENS:{','.join(sorted(set(banned)))}")
    return {"clean": True, "lines": len(text.splitlines()), "banned_tokens": []}


def parse_williamson_sol_line(text: str) -> list[int]:
    """Extract 4 hex words from a Williamson SOL certificate line."""
    m_sol = re.search(r"SOL\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)", text)
    if m_sol is None:
        raise ValueError("W75_SOL_NOT_FOUND")
    return [int(x, 16) for x in m_sol.groups()]


def verify_sha256sums_manifest(base_dir: Path, manifest_text: str) -> int:
    """Verify every `sha256  filename` entry in a non-empty SHA256SUMS manifest strictly confined to base_dir."""
    if not isinstance(manifest_text, str):
        raise ValueError("SHA256SUMS_NOT_STR")
    base_resolved = base_dir.resolve()
    count = 0
    for ln in manifest_text.splitlines():
        if not ln.strip():
            continue
        parts = ln.split()
        if len(parts) != 2:
            raise ValueError("SHA256SUMS_MALFORMED_LINE")
        exp_sha, rel_fn = parts
        if len(exp_sha) != 64 or any(c not in "0123456789abcdef" for c in exp_sha):
            raise ValueError("SHA256SUMS_INVALID_HEX")
        rel_path = Path(rel_fn)
        if rel_path.is_absolute() or "\\" in rel_fn or ".." in rel_path.parts:
            raise ValueError("SHA256SUMS_PATH_TRAVERSAL")
        target = (base_dir / rel_path).resolve()
        if not target.is_relative_to(base_resolved) or not target.is_file():
            raise ValueError("SHA256SUMS_TARGET_OUTSIDE_OR_MISSING")
        got_sha = hashlib.sha256(target.read_bytes()).hexdigest()
        if got_sha != exp_sha:
            raise ValueError(f"SHA256SUMS_MISMATCH:{rel_fn}")
        count += 1
    if count == 0:
        raise ValueError("SHA256SUMS_EMPTY_MANIFEST")
    return count


def verify_quantum_fault_witness(record: dict[str, Any], expected_faults: int = 16) -> dict[str, Any]:
    """Verify a two-gross circuit-distance fault witness declares and lists exact distinct fault dicts."""
    if not _is_strict_int(expected_faults) or expected_faults < 1:
        raise ValueError("QUANTUM_WITNESS_INVALID_EXPECTED")
    if not isinstance(record, dict):
        raise ValueError("QUANTUM_WITNESS_NOT_DICT")
    sector = record.get("sector")
    if sector not in ("X", "Z"):
        raise ValueError("QUANTUM_WITNESS_INVALID_SECTOR")
    n_faults = record.get("n_faults")
    faults = record.get("faults")
    if (
        not _is_strict_int(n_faults)
        or n_faults != expected_faults
        or not isinstance(faults, list)
        or len(faults) != expected_faults
    ):
        raise ValueError("QUANTUM_WITNESS_FAULT_COUNT")
    seen: set[str] = set()
    for f in faults:
        if not isinstance(f, dict) or len(f) == 0:
            raise ValueError("QUANTUM_WITNESS_INVALID_FAULT_ENTRY")
        canon = json.dumps(f, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
        if canon in seen:
            raise ValueError("QUANTUM_WITNESS_DUPLICATE_FAULT")
        seen.add(canon)
    return {"sector": sector, "n_faults": expected_faults}


# ---------------------------------------------------------------------------
# Live Intake Runner & Standalone Known-Answer Runner
# ---------------------------------------------------------------------------


def build_live_catalog(intake_root: Path) -> dict[str, Any]:
    """Parse pinned sitemap, HTML pages, and llms-full.txt into a strict zero-float 31-domain catalog."""
    raw_dir = intake_root / "raw_pages"
    sitemap_p = intake_root / "raw" / "sitemap.txt"
    llms_full_p = raw_dir / "llms-full.txt"
    llms_p = raw_dir / "llms.txt"
    if not sitemap_p.exists() or not llms_full_p.exists():
        raise ValueError("INTAKE_FILES_MISSING")

    sitemap = sitemap_p.read_text(encoding="utf-8")
    slugs = [u.split("/research/")[1] for u in re.findall(r"<loc>(https://www\.generalised\.si/research/[^<]+)</loc>", sitemap)]
    llms_full = llms_full_p.read_text(encoding="utf-8")
    idx_pn = llms_full.index("## Papers and notes")
    results_sec = llms_full[llms_full.index("## Results"):idx_pn]
    papers = re.split(r"(?=^### )", llms_full[idx_pn:], flags=re.M)[1:]
    if len(slugs) != 31 or len(papers) != 31:
        raise ValueError("CATALOG_EXPECTED_31_DOMAINS")

    ev_by_slug: dict[str, list[str]] = {}
    for m in re.finditer(r"Evidence \(([^)]+)\):.*?https://www\.generalised\.si/research/([a-z0-9-]+)", results_sec):
        ev_by_slug.setdefault(m.group(2), []).append(m.group(1))

    cat_by_slug: dict[str, str] = {}
    cur_cat = "General"
    for ln in results_sec.splitlines():
        if ln.startswith("### "):
            cur_cat = ln[4:].strip()
        for m in re.finditer(r"https://www\.generalised\.si/research/([a-z0-9-]+)", ln):
            cat_by_slug.setdefault(m.group(1), cur_cat)

    domains: list[dict[str, Any]] = []
    gsi_r_with_pub = 0
    wp_with_pub = 0
    wp_indep_labelled = 0
    total_hosted_files = 0

    for idx, (sl, ptxt) in enumerate(zip(slugs, papers), start=1):
        title = ptxt.splitlines()[0][4:].strip()
        m_code = re.search(r"GSI-R-\d{4}", ptxt)
        code = m_code.group(0) if m_code else f"WP-{idx - 18:02d}"
        is_wp = m_code is None
        html_p = raw_dir / f"research__{sl}.html"
        html_bytes = html_p.read_bytes()
        html_s = html_bytes.decode("utf-8", errors="replace")
        hosted_files = sorted(
            f
            for f in set(re.findall(r"/files/[^\"'<> \\]+\.(?:py|json|txt|csv|zip|lean|md|pdf)", html_s))
            if "$h" not in f
        )
        gsi_repos = sorted(set(re.findall(r"https://github\.com/vatskishan03/[A-Za-z0-9_.-]+", html_s)))
        has_public_artifacts = len(hosted_files) > 0 or len(gsi_repos) > 0
        total_hosted_files += len(hosted_files)
        evs = sorted(set(ev_by_slug.get(sl, [])))
        if is_wp:
            if has_public_artifacts:
                wp_with_pub += 1
            if "Independently checked" in evs:
                wp_indep_labelled += 1
        elif has_public_artifacts:
            gsi_r_with_pub += 1

        target_org, operator_bridge = ORG_DOMAIN_MAP[sl]
        domains.append(
            {
                "index": idx,
                "id": code,
                "slug": sl,
                "url": f"https://www.generalised.si/research/{sl}",
                "title": title,
                "category": cat_by_slug.get(sl, "General"),
                "series": "nov16_white_paper" if is_wp else "gsi_r_note",
                "evidence_labels": evs,
                "hosted_files_count": len(hosted_files),
                "hosted_files": hosted_files,
                "gsi_github_repos": gsi_repos,
                "has_public_artifacts": has_public_artifacts,
                "page_html_sha256": hashlib.sha256(html_bytes).hexdigest(),
                "target_org_repo": target_org,
                "law5_exact_operator_mapping": operator_bridge,
                "siliquant_exact_bridge": SILIQUANT_BRIDGE_MAP.get(sl),
                "law4_default_novelty_tier": "N0",
            }
        )

    out = {
        "schema": "aletheia.audit101.generalised_si_catalog.v1",
        "site": "https://www.generalised.si",
        "sitemap_sha256": hashlib.sha256(sitemap_p.read_bytes()).hexdigest(),
        "llms_txt_sha256": hashlib.sha256(llms_p.read_bytes()).hexdigest() if llms_p.exists() else "",
        "llms_full_txt_sha256": hashlib.sha256(llms_full_p.read_bytes()).hexdigest(),
        "total_research_domains": len(domains),
        "gsi_r_notes_count": 18,
        "gsi_r_notes_with_public_artifacts": gsi_r_with_pub,
        "nov16_white_papers_count": 13,
        "nov16_white_papers_with_public_artifacts": wp_with_pub,
        "nov16_white_papers_labelled_independently_checked": wp_indep_labelled,
        "total_hosted_download_files": total_hosted_files,
        "public_artifact_ratio": _fmt_q(Fraction(gsi_r_with_pub + wp_with_pub, len(domains))),
        "siliquant_mapped_domains_count": sum(1 for d in domains if d["siliquant_exact_bridge"] is not None),
        "domains": domains,
    }
    out["canonical_sha256"] = _canonical_sha256(out)
    return out


def run_live_audit(intake_root: Path) -> dict[str, Any]:
    """Execute independent zero-shared-code pure-Z/Q verification across all staged GSI artifacts."""
    catalog = build_live_catalog(intake_root)
    cdir = intake_root / "certificates" / "files"
    hroot = intake_root / "repos" / "Hadamard"
    qroot = intake_root / "repos" / "Quantum"

    # Pillar 1: Circulant Weighing Matrices (227/227 + 6/6 & 12/12 inequivalence + CW120_180.lean)
    cw120 = json.loads((cdir / "circulant-weighing-matrices/cw120_36_classes.json").read_text(encoding="utf-8"))
    cw180 = json.loads((cdir / "circulant-weighing-matrices/cw180_36_classes.json").read_text(encoding="utf-8"))
    cw120_res = verify_cw_class_set_inequivalent(cw120["n"], cw120["k"], cw120["classes"])
    cw180_res = verify_cw_class_set_inequivalent(cw180["n"], cw180["k"], cw180["classes"])

    lj4 = json.loads((cdir / "circulant-weighing-matrices/lj_weight4.json").read_text(encoding="utf-8"))
    lj16 = json.loads((cdir / "circulant-weighing-matrices/lj_weight16.json").read_text(encoding="utf-8"))
    lj4_count = sum(1 for nk, obj in lj4["objects"].items() if verify_circulant_weighing_matrix(int(nk), 4, obj["P"], obj["N"])["valid"])
    lj16_count = sum(1 for nk, obj in lj16["objects"].items() if verify_circulant_weighing_matrix(int(nk), 16, obj["P"], obj["N"])["valid"])
    cw_lean = verify_lean_file_purity((cdir / "circulant-weighing-matrices/CW120_180.lean").read_text(encoding="utf-8"))

    # Pillar 2: Good 53 & 55, Williamson 75, Good5355.lean, 34 T-matrices, WT47 & WT83
    good53 = verify_good_or_williamson_quadruple(53, [0x29F4DA, 0xB79910, 0x3171087, 0x3576479], first_skew=True)
    good55 = verify_good_or_williamson_quadruple(55, [0x48F51D, 0x82E36E, 0x3A9FE69, 0x41B7527], first_skew=True)
    good_lean = verify_lean_file_purity((cdir / "good-matrices-53-55/Good5355.lean").read_text(encoding="utf-8"))

    w75_txt = (cdir / "williamson-good-order-75/williamson_75_set.txt").read_text(encoding="utf-8")
    w75_res = verify_good_or_williamson_quadruple(75, parse_williamson_sol_line(w75_txt), first_skew=False)

    t_files = sorted((hroot / "t-matrices").glob("T*.txt"))
    t_orders: list[int] = []
    for tf in t_files:
        t_rows = [ln.strip() for ln in tf.read_text(encoding="utf-8").splitlines() if ln.strip() and set(ln.strip()) <= {"+", "-", "0"}]
        t_res = verify_t_matrix_quadruple(len(t_rows[0]), t_rows)
        t_orders.append(t_res["order"])

    wt_results = {}
    for wt_name in ("WT47.json", "WT83.json"):
        wtd = json.loads((hroot / "williamson-type" / wt_name).read_text(encoding="utf-8"))
        wt_results[wt_name] = verify_bordered_williamson_type(wtd["order"], wtd["sequences"], wtd["rowsums"])

    # Pillar 3: RDS(364,2,243,81), 729 L31 orbit reps for (465,145,45), 5 binary linear codes
    rds_raw = json.loads((cdir / "singer-relative-difference-sets/objects/rds_364_2_243_81.json").read_text(encoding="utf-8"))
    rds_res = verify_relative_difference_set(rds_raw["v"], rds_raw["n"], rds_raw["k"], rds_raw["mu_RDS"], rds_raw["R"])

    l31_lines = [
        [int(tok) for tok in ln.split()]
        for ln in (cdir / "cyclic-difference-set-465/data/L31_orbit_reps.txt").read_text(encoding="utf-8").splitlines()
        if ln.strip()
    ]
    l31_neg10 = 0
    l31_pos10 = 0
    for vec in l31_lines:
        pr = verify_cyclic_ds_projection_orbit(31, 10, 100, vec)
        if pr["sum"] == -10:
            l31_neg10 += 1
        else:
            l31_pos10 += 1

    code_results = []
    for cf in sorted((cdir / "candidate-binary-codes").glob("cert_*.json")):
        cd = json.loads(cf.read_text(encoding="utf-8"))
        cr = verify_binary_linear_code_generator(cd["n"], cd["k"], cd["rows"], cd["claim_d"])
        cr["file"] = cf.name
        code_results.append(cr)

    # Pillar 4: 3D Ising DoS (4x4x4 & 5x5x4), 24 Ag-Pd Cluster Expansion cells, Quantum SHA256SUMS + witnesses
    ising_results = {}
    for fn, dims in (
        ("omega_4x4x4_periodic.txt", (4, 4, 4)),
        ("omega_5x5x4_periodic.txt", (5, 5, 4)),
    ):
        pairs = [
            (int(parts[0]), int(parts[1]))
            for ln in (cdir / "ising-3d-density-of-states" / fn).read_text(encoding="utf-8").splitlines()
            if ln.strip() and len((parts := ln.split())) == 2
        ]
        ising_results[fn] = verify_ising_3d_dos_moments(dims, pairs)

    ce_insts = {x["name"]: x for x in json.loads((cdir / "cluster-expansion-ground-states/instances.json").read_text(encoding="utf-8"))}
    ce_gs = json.loads((cdir / "cluster-expansion-ground-states/ground_states.json").read_text(encoding="utf-8"))
    ce_verified = 0
    for g in ce_gs:
        inst = ce_insts[g["name"]]
        verify_cluster_expansion_pair_energy(inst["group"], inst["N"], inst["Jd"], inst["a"], g["config"], g["E"], expected_occupied=g["Pd"])
        ce_verified += 1

    q_sha_verified = verify_sha256sums_manifest(qroot, (qroot / "SHA256SUMS").read_text(encoding="utf-8"))
    q_witnesses = []
    for wf in sorted(qroot.glob("witness_*_16faults.json")):
        wd = json.loads(wf.read_text(encoding="utf-8"))
        wres = verify_quantum_fault_witness(wd, expected_faults=16)
        q_witnesses.append({"file": wf.name, "sector": wres["sector"], "n_faults": wres["n_faults"]})

    # Pillar 5: Moissanite-Labs/siliquant Sparse Weighing-Matrix Rotation Bridge (exact pure-Q witnesses)
    cw120_c0 = cw120["classes"][0]
    cw180_c0 = cw180["classes"][0]
    cw98_obj = lj16["objects"]["98"]
    vec120_1hot = [100] + [0] * 119
    vec120_2hot = [100, 25] + [0] * 118
    vec180_1hot = [100] + [0] * 179
    vec98_1hot = [100] + [0] * 97
    siliquant_bridge = {
        "siliquant_mapped_domains_count": catalog["siliquant_mapped_domains_count"],
        "cw120_36_class0_1hot": verify_weighing_matrix_siliquant_rotation(120, 36, cw120_c0["P"], cw120_c0["N"], vec120_1hot),
        "cw120_36_class0_2hot": verify_weighing_matrix_siliquant_rotation(120, 36, cw120_c0["P"], cw120_c0["N"], vec120_2hot),
        "cw180_36_class0_1hot": verify_weighing_matrix_siliquant_rotation(180, 36, cw180_c0["P"], cw180_c0["N"], vec180_1hot),
        "cw98_16_1hot": verify_weighing_matrix_siliquant_rotation(98, 16, cw98_obj["P"], cw98_obj["N"], vec98_1hot),
    }

    pinned_file_sha256s = {}
    for p in sorted(cdir.rglob("*")):
        if p.is_file():
            pinned_file_sha256s[str(p.relative_to(cdir))] = hashlib.sha256(p.read_bytes()).hexdigest()

    out = {
        "schema": "aletheia.audit101.generalised_si_certificate.v1",
        "mode": "live_artifact_verification",
        "honest_novelty_tier": "N0",
        "oracle_class": "exact",
        "catalog_summary": {
            "total_research_domains": catalog["total_research_domains"],
            "gsi_r_notes_with_public_artifacts": catalog["gsi_r_notes_with_public_artifacts"],
            "nov16_white_papers_with_public_artifacts": catalog["nov16_white_papers_with_public_artifacts"],
            "nov16_white_papers_labelled_independently_checked": catalog["nov16_white_papers_labelled_independently_checked"],
            "total_hosted_download_files": catalog["total_hosted_download_files"],
            "public_artifact_ratio": catalog["public_artifact_ratio"],
            "siliquant_mapped_domains_count": catalog["siliquant_mapped_domains_count"],
            "catalog_canonical_sha256": catalog["canonical_sha256"],
        },
        "pillar1_circulant_weighing_matrices": {
            "cw120_36": cw120_res,
            "cw180_36": cw180_res,
            "lj_weight4_verified": lj4_count,
            "lj_weight16_verified": lj16_count,
            "total_cw_verified": cw120_res["classes_verified"] + cw180_res["classes_verified"] + lj4_count + lj16_count,
            "cw120_180_lean_purity": cw_lean,
        },
        "pillar2_hadamard_good_williamson_tmatrices": {
            "good_53": good53,
            "good_55": good55,
            "good5355_lean_purity": good_lean,
            "williamson_75": w75_res,
            "hadamard_repo_t_matrices_verified": len(t_orders),
            "t_matrix_min_order": min(t_orders),
            "t_matrix_max_order": max(t_orders),
            "bordered_williamson_type": wt_results,
        },
        "pillar3_difference_sets_and_binary_codes": {
            "rds_364_2_243_81": rds_res,
            "cyclic_ds_465_l31_orbits_verified": len(l31_lines),
            "l31_sum_neg10_count": l31_neg10,
            "l31_sum_pos10_count": l31_pos10,
            "candidate_binary_codes": code_results,
        },
        "pillar4_ising_cluster_expansion_and_quantum": {
            "ising_3d_dos": ising_results,
            "agpd_cluster_expansion_cells_verified": ce_verified,
            "quantum_sha256sums_verified": q_sha_verified,
            "quantum_16fault_witnesses": q_witnesses,
        },
        "pillar5_siliquant_sparse_rotation_bridge": siliquant_bridge,
        "pinned_certificate_sha256s": pinned_file_sha256s,
    }
    out["canonical_sha256"] = _canonical_sha256(out)
    return out


def run_standalone_known_answer() -> dict[str, Any]:
    """Run all 8 zero-shared-code pure-Z/Q verifiers offline on compact known-answer witnesses."""
    cw_ok = verify_cw_class_set_inequivalent(
        7,
        4,
        [{"P": [1, 2, 4], "N": [0]}],
    )
    cw_rot = verify_weighing_matrix_siliquant_rotation(7, 4, [1, 2, 4], [0], [10, 0, 0, 0, 0, 0, 0])
    good3 = verify_good_or_williamson_quadruple(3, [0, 0, 1, 1], first_skew=True)
    will3 = verify_good_or_williamson_quadruple(3, [0, 1, 1, 1], first_skew=False)
    t3 = verify_t_matrix_quadruple(3, ["+00", "0+0", "00+", "000"])
    bwt5 = verify_bordered_williamson_type(5, ["+++-", "++--", "+-+-", "+--+"], [2, 0, 0, 0])
    rds4 = verify_relative_difference_set(4, 2, 3, 1, [0, 1, 3])
    proj5 = verify_cyclic_ds_projection_orbit(5, 2, 4, [2, 0, 0, 0, 0])
    ham74 = verify_binary_linear_code_generator(7, 4, ["47", "2b", "1d", "0e"], 3)
    ce4 = verify_cluster_expansion_pair_energy([2, 2], 4, [0, 4, 4, 2], -5, "1100", -6)
    lean_ok = verify_lean_file_purity("-- comment mentioning sorry\ntheorem t : 1 + 1 = 2 := rfl\n")

    out = {
        "schema": "aletheia.audit101.generalised_si_standalone.v1",
        "mode": "standalone_known_answer_offline",
        "honest_novelty_tier": "N0",
        "oracle_class": "exact",
        "cw_7_4": cw_ok,
        "cw_7_4_siliquant_rotation": cw_rot,
        "good_3": good3,
        "williamson_3": will3,
        "t_matrix_3": t3,
        "bordered_wt_5": bwt5,
        "rds_4_2_3_1": rds4,
        "proj_5": proj5,
        "hamming_7_4": ham74,
        "cluster_2x2": ce4,
        "lean_purity": lean_ok,
    }
    out["canonical_sha256"] = _canonical_sha256(out)
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Independent pure-Z/Q verifier for Generalised Superintelligence artifacts.")
    parser.add_argument("--standalone", action="store_true", help="Run offline known-answer self-check without intake files.")
    parser.add_argument("--live", action="store_true", help="Verify all staged live artifacts under --intake-root.")
    parser.add_argument("--intake-root", type=Path, default=Path("../intake-generalised-si"), help="Path to staged intake directory.")
    parser.add_argument("--write-catalog", type=Path, default=None, help="Optional output path to write 31-domain catalog JSON.")
    parser.add_argument("--json", action="store_true", help="Emit canonical zero-float JSON to stdout.")
    args = parser.parse_args(argv)

    if args.standalone:
        result = run_standalone_known_answer()
    else:
        intake = args.intake_root.resolve()
        if args.write_catalog is not None:
            cat = build_live_catalog(intake)
            args.write_catalog.write_text(json.dumps(cat, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        result = run_live_audit(intake)

    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(f"AUDIT-101 ({result['mode']}): OK sha256={result['canonical_sha256']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
