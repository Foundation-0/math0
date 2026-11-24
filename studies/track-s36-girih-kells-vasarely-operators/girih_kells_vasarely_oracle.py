#!/usr/bin/env python3
"""
Track S36 (Portal 33): Girih Q(phi) & E8 Elser-Sloane, Book of Kells Plait &
Kirchhoff Matrix-Tree, and Victor Vasarely Vega Metric & Plastic Alphabet.

Pure Python 3 standard library over exact Z, Q (`fractions.Fraction`), and
Q(phi) = Q[phi]/(phi^2 - phi - 1). Zero external dependencies, zero AST floats,
zero float() calls, zero bare asserts, zero .isdigit(), zero mathematical RNG.

Strict Law-4 N0/N1 honesty:
  - Classical results (Girih Q(phi) areas, Elser-Sloane 1987 E8->H4 icosians,
    Celtic plait gcd(m,n) strand count, Kirchhoff Matrix-Tree & Tait knot det,
    orthographic Beltrami metric & D4 Burnside orbits) are explicitly tagged N0.
  - Unified cross-domain exact-Q operator bridge & dual-Tait / Bareiss / Law-5
    obstruction certification is tagged N1.
"""
from __future__ import annotations

from fractions import Fraction
import hashlib
import hmac
from itertools import permutations, product
import json
import math
from typing import Any, Sequence

SCHEMA_VERSION = "aletheia.girih_kells_vasarely.certificate.v1"
TRACK_ID = "TRACK-S36-GIRIH-KELLS-VASARELY-OPERATORS"

MAX_JSON_BYTES = 1_048_576
HARD_MAX_BYTES_CAP = 64 * 1024 * 1024
MAX_JSON_DEPTH = 64
MAX_INT_BITS = 2048
MAX_INT_DIGITS = 617
MAX_RATIONAL_CHARS = 256
MAX_FORMAT_BITS = 4096

_HEX_LOWER = frozenset("0123456789abcdef")
_ASCII_DIGITS = frozenset("0123456789")
_CERT_KEYS = frozenset({"schema", "track_id", "payload_sha256", "certificate_sha256", "payload"})
_PILLAR_KEYS = (
    "pillar1_girih_qphi_e8",
    "pillar2_kells_plait_kirchhoff",
    "pillar3_vasarely_vega_alphabet",
    "pillar4_cross_domain_unification",
)
_PAYLOAD_KEYS = frozenset({
    "oracle_class",
    "novelty_classification",
    "zero_floats_exact_arithmetic",
    "all_verified",
    *_PILLAR_KEYS,
})
_ALLOWED_BOOL_KEYS = frozenset({
    "all_144_pairs_match_gcd",
    "all_areas_exact",
    "all_e8_norms_equal_2",
    "all_polygons_closed",
    "all_unit_steps_exact",
    "all_verified",
    "both_merge_distinct_components",
    "burnside_matches_bruteforce",
    "char_poly_annihilates_phi2",
    "decagon_eq_2hex_plus_2pent",
    "det_equals_inv_one_minus_rho2",
    "dual_tait_parity_all_match",
    "e8_gram_det_is_1",
    "e8_ip_histogram_exact",
    "hexagon_plus_bowtie_eq_2pentagon",
    "hyperbolic_metric_det_exact",
    "p2_kite_dart_ratio_phi",
    "p3_rhombus_ratio_phi",
    "pillar_verified",
    "radius_ratio_is_phi",
    "self_crossing_splits_and_preserves",
    "strictly_monotonic_bulging",
    "zero_floats_exact_arithmetic",
})

Q0 = Fraction(0, 1)
Q1 = Fraction(1, 1)

# ---------------------------------------------------------------------------
# Exact Non-Replay Payload Pin: 42 dict key sets / 30 list lengths / 211 leaves
# ---------------------------------------------------------------------------
# `_PAYLOAD_LEAF_PINS` maps every leaf path of the standalone payload to its exact
# expected value, so a non-replay validation can never accept a hollow payload, an
# extra nested dict key, an extra/truncated list, a flipped bool flag (True vs 1),
# an unpinned leaf mutation, a zero-denominator rational ("1/0"), or an unbounded
# int (1 << 40) tamper. Dict key sets and list lengths are derived bijectively from
# the pinned paths (string segment => dict key, int segment => list index).
_PAYLOAD_LEAF_PINS: dict[tuple[Any, ...], Any] = {
    ('all_verified',): True,
    ('novelty_classification',): 'N1_UNIFIED_PORTAL33_EXACT_OPERATORS_WITH_N0_CLASSICAL_BASE',
    ('oracle_class',): 'exact',
    ('pillar1_girih_qphi_e8', 'all_areas_exact'): True,
    ('pillar1_girih_qphi_e8', 'all_polygons_closed'): True,
    ('pillar1_girih_qphi_e8', 'all_unit_steps_exact'): True,
    ('pillar1_girih_qphi_e8', 'elser_sloane_e8_icosian_bridge', 'all_e8_norms_equal_2'): True,
    ('pillar1_girih_qphi_e8', 'elser_sloane_e8_icosian_bridge', 'e8_gram_det'): '1',
    ('pillar1_girih_qphi_e8', 'elser_sloane_e8_icosian_bridge', 'e8_gram_det_is_1'): True,
    ('pillar1_girih_qphi_e8', 'elser_sloane_e8_icosian_bridge', 'e8_ip_histogram_exact'): True,
    ('pillar1_girih_qphi_e8', 'elser_sloane_e8_icosian_bridge', 'inner_600cell_vertices'): 120,
    ('pillar1_girih_qphi_e8', 'elser_sloane_e8_icosian_bridge', 'outer_600cell_vertices'): 120,
    ('pillar1_girih_qphi_e8', 'elser_sloane_e8_icosian_bridge', 'radius_ratio_is_phi'): True,
    ('pillar1_girih_qphi_e8', 'elser_sloane_e8_icosian_bridge', 'root_inner_product_histogram', '-1'): 56,
    ('pillar1_girih_qphi_e8', 'elser_sloane_e8_icosian_bridge', 'root_inner_product_histogram', '-2'): 1,
    ('pillar1_girih_qphi_e8', 'elser_sloane_e8_icosian_bridge', 'root_inner_product_histogram', '0'): 126,
    ('pillar1_girih_qphi_e8', 'elser_sloane_e8_icosian_bridge', 'root_inner_product_histogram', '1'): 56,
    ('pillar1_girih_qphi_e8', 'elser_sloane_e8_icosian_bridge', 'root_inner_product_histogram', '2'): 1,
    ('pillar1_girih_qphi_e8', 'elser_sloane_e8_icosian_bridge', 'simple_root_count'): 8,
    ('pillar1_girih_qphi_e8', 'elser_sloane_e8_icosian_bridge', 'total_e8_roots'): 240,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'bowtie', 'area_over_sin36', 'a'): '-1',
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'bowtie', 'area_over_sin36', 'b_phi'): '2',
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'bowtie', 'interior_angles_deg', 0): 72,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'bowtie', 'interior_angles_deg', 1): 72,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'bowtie', 'interior_angles_deg', 2): 216,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'bowtie', 'interior_angles_deg', 3): 72,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'bowtie', 'interior_angles_deg', 4): 72,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'bowtie', 'interior_angles_deg', 5): 216,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'bowtie', 'n_edges'): 6,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'decagon', 'area_over_sin36', 'a'): '5',
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'decagon', 'area_over_sin36', 'b_phi'): '5',
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'decagon', 'interior_angles_deg', 0): 144,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'decagon', 'interior_angles_deg', 1): 144,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'decagon', 'interior_angles_deg', 2): 144,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'decagon', 'interior_angles_deg', 3): 144,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'decagon', 'interior_angles_deg', 4): 144,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'decagon', 'interior_angles_deg', 5): 144,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'decagon', 'interior_angles_deg', 6): 144,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'decagon', 'interior_angles_deg', 7): 144,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'decagon', 'interior_angles_deg', 8): 144,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'decagon', 'interior_angles_deg', 9): 144,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'decagon', 'n_edges'): 10,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'elongated_hexagon', 'area_over_sin36', 'a'): '2',
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'elongated_hexagon', 'area_over_sin36', 'b_phi'): '1',
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'elongated_hexagon', 'interior_angles_deg', 0): 72,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'elongated_hexagon', 'interior_angles_deg', 1): 144,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'elongated_hexagon', 'interior_angles_deg', 2): 144,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'elongated_hexagon', 'interior_angles_deg', 3): 72,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'elongated_hexagon', 'interior_angles_deg', 4): 144,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'elongated_hexagon', 'interior_angles_deg', 5): 144,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'elongated_hexagon', 'n_edges'): 6,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'pentagon', 'area_over_sin36', 'a'): '1/2',
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'pentagon', 'area_over_sin36', 'b_phi'): '3/2',
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'pentagon', 'interior_angles_deg', 0): 108,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'pentagon', 'interior_angles_deg', 1): 108,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'pentagon', 'interior_angles_deg', 2): 108,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'pentagon', 'interior_angles_deg', 3): 108,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'pentagon', 'interior_angles_deg', 4): 108,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'pentagon', 'n_edges'): 5,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'rhombus', 'area_over_sin36', 'a'): '0',
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'rhombus', 'area_over_sin36', 'b_phi'): '1',
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'rhombus', 'interior_angles_deg', 0): 72,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'rhombus', 'interior_angles_deg', 1): 108,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'rhombus', 'interior_angles_deg', 2): 72,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'rhombus', 'interior_angles_deg', 3): 108,
    ('pillar1_girih_qphi_e8', 'girih_tiles', 'rhombus', 'n_edges'): 4,
    ('pillar1_girih_qphi_e8', 'identities', 'decagon_eq_2hex_plus_2pent'): True,
    ('pillar1_girih_qphi_e8', 'identities', 'hexagon_plus_bowtie_eq_2pentagon'): True,
    ('pillar1_girih_qphi_e8', 'identities', 'p2_kite_dart_ratio_phi'): True,
    ('pillar1_girih_qphi_e8', 'identities', 'p3_rhombus_ratio_phi'): True,
    ('pillar1_girih_qphi_e8', 'inflation_matrix_phi2', 'char_poly_annihilates_phi2'): True,
    ('pillar1_girih_qphi_e8', 'inflation_matrix_phi2', 'det'): '1',
    ('pillar1_girih_qphi_e8', 'inflation_matrix_phi2', 'matrix', 0, 0): 2,
    ('pillar1_girih_qphi_e8', 'inflation_matrix_phi2', 'matrix', 0, 1): 1,
    ('pillar1_girih_qphi_e8', 'inflation_matrix_phi2', 'matrix', 1, 0): 1,
    ('pillar1_girih_qphi_e8', 'inflation_matrix_phi2', 'matrix', 1, 1): 1,
    ('pillar1_girih_qphi_e8', 'inflation_matrix_phi2', 'trace'): '3',
    ('pillar1_girih_qphi_e8', 'novelty_tag'): 'N0_CLASSICAL_LU_STEINHARDT_2007_ELSER_SLOANE_1987',
    ('pillar1_girih_qphi_e8', 'pillar_verified'): True,
    ('pillar2_kells_plait_kirchhoff', 'breakline_surgery', 'both_merge_distinct_components'): True,
    ('pillar2_kells_plait_kirchhoff', 'breakline_surgery', 'distinct_merge_2x2_H', 0): 2,
    ('pillar2_kells_plait_kirchhoff', 'breakline_surgery', 'distinct_merge_2x2_H', 1): 1,
    ('pillar2_kells_plait_kirchhoff', 'breakline_surgery', 'distinct_merge_2x2_V', 0): 2,
    ('pillar2_kells_plait_kirchhoff', 'breakline_surgery', 'distinct_merge_2x2_V', 1): 1,
    ('pillar2_kells_plait_kirchhoff', 'breakline_surgery', 'distinct_merge_4x6_V', 0): 2,
    ('pillar2_kells_plait_kirchhoff', 'breakline_surgery', 'distinct_merge_4x6_V', 1): 1,
    ('pillar2_kells_plait_kirchhoff', 'breakline_surgery', 'distinct_merge_6x6_V', 0): 6,
    ('pillar2_kells_plait_kirchhoff', 'breakline_surgery', 'distinct_merge_6x6_V', 1): 5,
    ('pillar2_kells_plait_kirchhoff', 'breakline_surgery', 'self_crossing_2x3_H_split', 0): 1,
    ('pillar2_kells_plait_kirchhoff', 'breakline_surgery', 'self_crossing_2x3_H_split', 1): 2,
    ('pillar2_kells_plait_kirchhoff', 'breakline_surgery', 'self_crossing_2x3_V_orient_flip', 0): 1,
    ('pillar2_kells_plait_kirchhoff', 'breakline_surgery', 'self_crossing_2x3_V_orient_flip', 1): 1,
    ('pillar2_kells_plait_kirchhoff', 'breakline_surgery', 'self_crossing_splits_and_preserves'): True,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'celtic_plaits_dual_tait', '2x2', 'black_vertices'): 2,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'celtic_plaits_dual_tait', '2x2', 'crossings'): 4,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'celtic_plaits_dual_tait', '2x2', 'tau_black'): 4,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'celtic_plaits_dual_tait', '2x2', 'tau_white'): 4,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'celtic_plaits_dual_tait', '2x2', 'white_vertices'): 4,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'celtic_plaits_dual_tait', '2x3', 'black_vertices'): 3,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'celtic_plaits_dual_tait', '2x3', 'crossings'): 7,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'celtic_plaits_dual_tait', '2x3', 'tau_black'): 15,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'celtic_plaits_dual_tait', '2x3', 'tau_white'): 15,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'celtic_plaits_dual_tait', '2x3', 'white_vertices'): 6,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'celtic_plaits_dual_tait', '3x3', 'black_vertices'): 5,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'celtic_plaits_dual_tait', '3x3', 'crossings'): 12,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'celtic_plaits_dual_tait', '3x3', 'tau_black'): 192,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'celtic_plaits_dual_tait', '3x3', 'tau_white'): 192,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'celtic_plaits_dual_tait', '3x3', 'white_vertices'): 9,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'celtic_plaits_dual_tait', '3x4', 'black_vertices'): 7,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'celtic_plaits_dual_tait', '3x4', 'crossings'): 17,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'celtic_plaits_dual_tait', '3x4', 'tau_black'): 2415,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'celtic_plaits_dual_tait', '3x4', 'tau_white'): 2415,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'celtic_plaits_dual_tait', '3x4', 'white_vertices'): 12,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'classic_knots_V_neg1', 'cinquefoil_5_1'): 5,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'classic_knots_V_neg1', 'figure_eight_4_1'): 5,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'classic_knots_V_neg1', 'trefoil_3_1'): 3,
    ('pillar2_kells_plait_kirchhoff', 'kirchhoff_tait_determinants', 'dual_tait_parity_all_match'): True,
    ('pillar2_kells_plait_kirchhoff', 'novelty_tag'): 'N0_CLASSICAL_CROMWELL_KIRCHHOFF_TAIT',
    ('pillar2_kells_plait_kirchhoff', 'pillar_verified'): True,
    ('pillar2_kells_plait_kirchhoff', 'plait_grid_sweep_1_to_12', 'all_144_pairs_match_gcd'): True,
    ('pillar2_kells_plait_kirchhoff', 'plait_grid_sweep_1_to_12', 'mismatches'): 0,
    ('pillar2_kells_plait_kirchhoff', 'plait_grid_sweep_1_to_12', 'single_strand_knot_pairs'): 91,
    ('pillar2_kells_plait_kirchhoff', 'plait_grid_sweep_1_to_12', 'total_pairs_traced'): 144,
    ('pillar2_kells_plait_kirchhoff', 'plait_grid_sweep_1_to_12', 'witness_strand_counts', '2x3'): 1,
    ('pillar2_kells_plait_kirchhoff', 'plait_grid_sweep_1_to_12', 'witness_strand_counts', '3x4'): 1,
    ('pillar2_kells_plait_kirchhoff', 'plait_grid_sweep_1_to_12', 'witness_strand_counts', '4x6'): 2,
    ('pillar2_kells_plait_kirchhoff', 'plait_grid_sweep_1_to_12', 'witness_strand_counts', '6x6'): 6,
    ('pillar3_vasarely_vega_alphabet', 'novelty_tag'): 'N0_CLASSICAL_BELTRAMI_BURNSIDE',
    ('pillar3_vasarely_vega_alphabet', 'pillar_verified'): True,
    ('pillar3_vasarely_vega_alphabet', 'plastic_alphabet_d4_burnside', 'burnside_matches_bruteforce'): True,
    ('pillar3_vasarely_vega_alphabet', 'plastic_alphabet_d4_burnside', 'd4_group_order'): 8,
    ('pillar3_vasarely_vega_alphabet', 'plastic_alphabet_d4_burnside', 'quad_2x2_burnside_orbits', 'k_2'): 6,
    ('pillar3_vasarely_vega_alphabet', 'plastic_alphabet_d4_burnside', 'quad_2x2_burnside_orbits', 'k_3'): 21,
    ('pillar3_vasarely_vega_alphabet', 'plastic_alphabet_d4_burnside', 'quad_2x2_burnside_orbits', 'k_6'): 231,
    ('pillar3_vasarely_vega_alphabet', 'plastic_alphabet_d4_burnside', 'single_tile_oriented_states'): 11,
    ('pillar3_vasarely_vega_alphabet', 'plastic_alphabet_d4_burnside', 'single_tile_shape_orbits'): 6,
    ('pillar3_vasarely_vega_alphabet', 'plastic_alphabet_d4_burnside', 'two_color_distinct_tile_counts', 'c_12'): 792,
    ('pillar3_vasarely_vega_alphabet', 'plastic_alphabet_d4_burnside', 'two_color_distinct_tile_counts', 'c_2'): 12,
    ('pillar3_vasarely_vega_alphabet', 'plastic_alphabet_d4_burnside', 'two_color_distinct_tile_counts', 'c_6'): 180,
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'det_equals_inv_one_minus_rho2'): True,
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'hyperbolic_metric_det_exact'): True,
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'poincare_curvature_K'): '-1',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 0, 'K_sq_decimal_4'): '1.0000',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 0, 'K_sq_det_g'): '1',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 0, 'g_metric', 0, 0): '1',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 0, 'g_metric', 0, 1): '0',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 0, 'g_metric', 1, 0): '0',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 0, 'g_metric', 1, 1): '1',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 0, 'poincare_det_g_hyp'): '16',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 0, 'rho'): '0',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 0, 'rho_sq'): '0',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 0, 'x'): '0',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 0, 'y'): '0',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 1, 'K_sq_decimal_4'): '1.1736',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 1, 'K_sq_det_g'): '169/144',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 1, 'g_metric', 0, 0): '17/16',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 1, 'g_metric', 0, 1): '1/12',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 1, 'g_metric', 1, 0): '1/12',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 1, 'g_metric', 1, 1): '10/9',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 1, 'poincare_det_g_hyp'): '815730721/26873856',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 1, 'rho'): '5/13',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 1, 'rho_sq'): '25/169',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 1, 'x'): '3/13',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 1, 'y'): '4/13',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 2, 'K_sq_decimal_4'): '1.5625',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 2, 'K_sq_det_g'): '25/16',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 2, 'g_metric', 0, 0): '25/16',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 2, 'g_metric', 0, 1): '0',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 2, 'g_metric', 1, 0): '0',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 2, 'g_metric', 1, 1): '1',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 2, 'poincare_det_g_hyp'): '390625/4096',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 2, 'rho'): '3/5',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 2, 'rho_sq'): '9/25',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 2, 'x'): '3/5',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 2, 'y'): '0',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 3, 'K_sq_decimal_4'): '2.7777',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 3, 'K_sq_det_g'): '25/9',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 3, 'g_metric', 0, 0): '25/9',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 3, 'g_metric', 0, 1): '0',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 3, 'g_metric', 1, 0): '0',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 3, 'g_metric', 1, 1): '1',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 3, 'poincare_det_g_hyp'): '6250000/6561',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 3, 'rho'): '4/5',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 3, 'rho_sq'): '16/25',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 3, 'x'): '4/5',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 3, 'y'): '0',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 4, 'K_sq_decimal_4'): '6.7600',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 4, 'K_sq_det_g'): '169/25',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 4, 'g_metric', 0, 0): '169/25',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 4, 'g_metric', 0, 1): '0',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 4, 'g_metric', 1, 0): '0',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 4, 'g_metric', 1, 1): '1',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 4, 'poincare_det_g_hyp'): '13051691536/390625',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 4, 'rho'): '12/13',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 4, 'rho_sq'): '144/169',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 4, 'x'): '12/13',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'pythagorean_samples', 4, 'y'): '0',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'sphere_curvature_K'): '1',
    ('pillar3_vasarely_vega_alphabet', 'vega_orthographic_beltrami', 'strictly_monotonic_bulging'): True,
    ('pillar4_cross_domain_unification', 'law5_honest_obstructions', 'aperiodic_vs_periodic_lattice'): 'Girih tilings live in non-crystallographic aperiodic Z[phi] (5-fold symmetry forbidden by 2D crystallographic restriction), whereas Book of Kells rectangular plaits live on periodic planar Z^2 grids.',
    ('pillar4_cross_domain_unification', 'law5_honest_obstructions', 'no_metaphor_conflation'): 'Cross-domain bridge holds strictly at the level of shared exact algebraic operators (Bareiss determinant, Q(phi) cut-and-project, finite permutation/dihedral orbits), never claiming physical or historical identity.',
    ('pillar4_cross_domain_unification', 'law5_honest_obstructions', 'positive_vs_negative_curvature'): 'Vasarely Vega orthographic projection samples positive Gaussian curvature K=+1 on S^2 (det(g)=1/(1-rho^2)) whereas Escher Circle Limit / siliquant#44 hyperbolic shells live on K=-1 Poincare disk (det(g_hyp)=16/(1-rho^2)^4).',
    ('pillar4_cross_domain_unification', 'novelty_tag'): 'N1_UNIFIED_EXACT_OPERATOR_SYNTHESIS',
    ('pillar4_cross_domain_unification', 'pillar_verified'): True,
    ('pillar4_cross_domain_unification', 'shared_exact_operators', 'bareiss_determinant_bridges', 'p1_e8_icosian_gram_det'): '1',
    ('pillar4_cross_domain_unification', 'shared_exact_operators', 'bareiss_determinant_bridges', 'p1_girih_inflation_det'): '1',
    ('pillar4_cross_domain_unification', 'shared_exact_operators', 'bareiss_determinant_bridges', 'p2_kells_3x4_kirchhoff_det'): 2415,
    ('pillar4_cross_domain_unification', 'shared_exact_operators', 'bareiss_determinant_bridges', 'p3_vasarely_rho_12_13_metric_det'): '169/25',
    ('pillar4_cross_domain_unification', 'shared_exact_operators', 'finite_group_orbits'): 'D4 Burnside orbit grammar (order 8) governs Vasarely Unite Plastique alongside S_n cycle decomposition on Celtic plait crossings.',
    ('pillar4_cross_domain_unification', 'shared_exact_operators', 'qphi_e8_bridge'): 'Elser-Sloane trace form tau(a+b*phi)=2a lifts 240 H4 icosians directly to unimodular E8 (det=1), linking siliquant E8 to Girih Q(phi).',
    ('zero_floats_exact_arithmetic',): True,
}


class GirihKellsVasarelyError(ValueError):
    """Fail-closed typed error (never stripped by python3 -O)."""

    def __init__(self, code: str, message: str) -> None:
        self.code = code
        self.message = message
        super().__init__(f"{code}: {message}")


# ---------------------------------------------------------------------------
# Zone-B Exact Type, Rational/Decimal Formatting, Iterative JSON & Digests
# ---------------------------------------------------------------------------

def require_bool(val: Any, label: str) -> bool:
    if type(val) is not bool:
        raise GirihKellsVasarelyError("INVALID_BOOL", f"{label} must be strict bool")
    return val


def require_int(
    val: Any,
    label: str,
    lo: int | None = None,
    hi: int | None = None,
) -> int:
    if type(val) is not int:
        raise GirihKellsVasarelyError("INVALID_INT", f"{label} must be strict int")
    if val.bit_length() > MAX_INT_BITS:
        raise GirihKellsVasarelyError("INT_TOO_LARGE", f"{label} exceeds {MAX_INT_BITS}-bit limit")
    if lo is not None:
        if type(lo) is not int:
            raise GirihKellsVasarelyError("INVALID_BOUND", f"{label} lo bound must be strict int")
        if val < lo:
            raise GirihKellsVasarelyError("INT_OUT_OF_RANGE", f"{label} below lower bound")
    if hi is not None:
        if type(hi) is not int:
            raise GirihKellsVasarelyError("INVALID_BOUND", f"{label} hi bound must be strict int")
        if val > hi:
            raise GirihKellsVasarelyError("INT_OUT_OF_RANGE", f"{label} above upper bound")
    return val


def require_str(val: Any, label: str, max_len: int = 4096) -> str:
    limit = require_int(max_len, f"{label}.max_len", lo=1, hi=HARD_MAX_BYTES_CAP)
    if type(val) is not str:
        raise GirihKellsVasarelyError("INVALID_STR", f"{label} must be strict str")
    if len(val) > limit:
        raise GirihKellsVasarelyError("STR_TOO_LONG", f"{label} exceeds length limit")
    try:
        val.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise GirihKellsVasarelyError("INVALID_UTF8_SURROGATE", f"{label} contains lone UTF-16 surrogate") from exc
    return val


def require_hex64(val: Any, label: str) -> str:
    s = require_str(val, label, max_len=64)
    if len(s) != 64:
        raise GirihKellsVasarelyError("INVALID_HEX64", f"{label} must be 64 lowercase ASCII hex chars")
    if any(ch not in _HEX_LOWER for ch in s):
        raise GirihKellsVasarelyError("INVALID_HEX64", f"{label} must contain only lowercase hex digits")
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


def _parse_bounded_int(token: Any, label: str = "int_token") -> int:
    """Strictly parse canonical ASCII integer rejecting '-0', '007', Unicode digits, and >MAX_INT_BITS."""
    s = require_str(token, label, max_len=HARD_MAX_BYTES_CAP)
    neg = s.startswith("-")
    digits = s[1:] if neg else s
    if len(digits) > MAX_INT_DIGITS:
        raise GirihKellsVasarelyError("INT_TOO_LARGE", f"{label} exceeds {MAX_INT_DIGITS} digits")
    if not _is_canonical_ascii_digits(digits):
        raise GirihKellsVasarelyError("INVALID_INT_TOKEN", f"{label} is not canonical ASCII integer")
    if neg and digits == "0":
        raise GirihKellsVasarelyError("INVALID_INT_TOKEN", f"{label} negative zero forbidden")
    val = -int(digits) if neg else int(digits)
    if val.bit_length() > MAX_INT_BITS:
        raise GirihKellsVasarelyError("INT_TOO_LARGE", f"{label} exceeds {MAX_INT_BITS} bits")
    return val


def parse_exact_rational(raw: Any, label: str = "rational") -> Fraction:
    """Strictly parse exact int, Fraction, or canonical ASCII rational ('p' or 'p/q')."""
    t = type(raw)
    if t is int:
        if raw.bit_length() > MAX_INT_BITS:
            raise GirihKellsVasarelyError("RATIONAL_TOO_LARGE", f"{label} exceeds bit limit")
        return Fraction(raw, 1)
    if t is Fraction:
        if raw.numerator.bit_length() > MAX_INT_BITS:
            raise GirihKellsVasarelyError("RATIONAL_TOO_LARGE", f"{label} numerator exceeds bit limit")
        if raw.denominator.bit_length() > MAX_INT_BITS:
            raise GirihKellsVasarelyError("RATIONAL_TOO_LARGE", f"{label} denominator exceeds bit limit")
        return raw
    if t is not str:
        raise GirihKellsVasarelyError("INVALID_RATIONAL_TYPE", f"{label} must be int, Fraction, or str")
    if len(raw) > MAX_RATIONAL_CHARS:
        raise GirihKellsVasarelyError("INVALID_RATIONAL_STR", f"{label} string oversized")
    parts = raw.split("/")
    if len(parts) == 1:
        num_s, den_s = parts[0], None
    elif len(parts) == 2:
        num_s, den_s = parts[0], parts[1]
    else:
        raise GirihKellsVasarelyError("INVALID_RATIONAL_STR", f"{label} contains multiple '/'")
    num_val = _parse_bounded_int(num_s, f"{label}.num")
    if den_s is None:
        return Fraction(num_val, 1)
    den_val = _parse_bounded_int(den_s, f"{label}.den")
    if den_val <= 1:
        raise GirihKellsVasarelyError("INVALID_RATIONAL_STR", f"{label} denominator must be > 1")
    if math.gcd(abs(num_val), den_val) != 1:
        raise GirihKellsVasarelyError("NON_CANONICAL_RATIONAL", f"{label} fraction is not reduced")
    return Fraction(num_val, den_val)


def format_rational(val: Any, label: str = "rational") -> str:
    if type(val) is not Fraction:
        raise GirihKellsVasarelyError("INVALID_RATIONAL_TYPE", f"{label} must be exact Fraction")
    if val.numerator.bit_length() > MAX_FORMAT_BITS:
        raise GirihKellsVasarelyError("RATIONAL_TOO_LARGE", f"{label} numerator exceeds format limit")
    if val.denominator.bit_length() > MAX_FORMAT_BITS:
        raise GirihKellsVasarelyError("RATIONAL_TOO_LARGE", f"{label} denominator exceeds format limit")
    if val.denominator == 1:
        return str(val.numerator)
    return f"{val.numerator}/{val.denominator}"


def format_decimal(val: Any, places: int = 4, label: str = "decimal") -> str:
    """Exact pure-integer truncated decimal string suppressing '-0.00'."""
    p = require_int(places, f"{label}.places", lo=0, hi=24)
    q = parse_exact_rational(val, label)
    neg = q < 0
    abs_q = -q if neg else q
    scale = 10 ** p
    scaled = (abs_q.numerator * scale) // abs_q.denominator
    if scaled == 0:
        neg = False
    sign = "-" if neg else ""
    if p == 0:
        return f"{sign}{scaled}"
    whole, frac = divmod(scaled, scale)
    return f"{sign}{whole}.{frac:0{p}d}"


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
            raise GirihKellsVasarelyError("JSON_DEPTH_EXCEEDED", f"JSON nesting exceeds {limit}")
        t = type(cur)
        if t is dict:
            cid = id(cur)
            if cid in active_ids:
                raise GirihKellsVasarelyError("JSON_CYCLE", "cyclic dict forbidden")
            active_ids.add(cid)
            stack.append((cur, depth, True))
            for k, v in cur.items():
                require_str(k, "json_key", max_len=256)
                stack.append((v, depth + 1, False))
        elif t is list:
            cid = id(cur)
            if cid in active_ids:
                raise GirihKellsVasarelyError("JSON_CYCLE", "cyclic list forbidden")
            active_ids.add(cid)
            stack.append((cur, depth, True))
            for item in cur:
                stack.append((item, depth + 1, False))
        elif t is int:
            if cur.bit_length() > MAX_INT_BITS:
                raise GirihKellsVasarelyError("INT_TOO_LARGE", "JSON int exceeds bit limit")
        elif t is str:
            require_str(cur, "json_str", max_len=65536)
        elif t is bool or cur is None:
            continue
        else:
            raise GirihKellsVasarelyError("FORBIDDEN_JSON_TYPE", f"forbidden JSON value type: {t.__name__}")


def _no_duplicate_keys_hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise GirihKellsVasarelyError("DUPLICATE_JSON_KEY", f"duplicate JSON key: {k}")
        out[k] = v
    return out


def _forbid_float(token: str) -> Any:
    raise GirihKellsVasarelyError("FLOAT_FORBIDDEN", f"float literal forbidden: {token}")


def _forbid_constant(token: str) -> Any:
    raise GirihKellsVasarelyError("NONFINITE_CONSTANT", f"non-finite JSON constant forbidden: {token}")


def parse_strict_json_text(text: Any, require_object: bool = True, max_bytes: int = MAX_JSON_BYTES) -> Any:
    require_bool(require_object, "require_object")
    cap = require_int(max_bytes, "max_bytes", lo=1, hi=HARD_MAX_BYTES_CAP)
    s = require_str(text, "json_text", max_len=cap)
    if len(s.encode("utf-8")) > cap:
        raise GirihKellsVasarelyError("JSON_TOO_LARGE", "JSON UTF-8 byte length exceeds cap")
    try:
        parsed = json.loads(
            s,
            object_pairs_hook=_no_duplicate_keys_hook,
            parse_float=_forbid_float,
            parse_int=_parse_bounded_int,
            parse_constant=_forbid_constant,
        )
    except GirihKellsVasarelyError:
        raise
    except (json.JSONDecodeError, ValueError, RecursionError) as exc:
        raise GirihKellsVasarelyError("INVALID_JSON", f"strict JSON parse failed: {type(exc).__name__}") from exc
    validate_json_tree_iterative(parsed)
    if require_object and type(parsed) is not dict:
        raise GirihKellsVasarelyError("JSON_NOT_OBJECT", "JSON root must be an object")
    return parsed


def canonical_json_bytes(obj: Any) -> bytes:
    validate_json_tree_iterative(obj)
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False).encode("ascii")


def sha256_hex(data: Any) -> str:
    if type(data) is not bytes:
        raise GirihKellsVasarelyError("INVALID_BYTES", "sha256_hex requires exact bytes")
    return hashlib.sha256(data).hexdigest()


# ---------------------------------------------------------------------------
# Exact Fraction-Free Bareiss Determinant & Q(phi) Field Arithmetic
# ---------------------------------------------------------------------------

def _require_square_qmatrix(matrix: Any, label: str = "matrix") -> list[list[Fraction]]:
    if type(matrix) not in (list, tuple):
        raise GirihKellsVasarelyError("INVALID_MATRIX", f"{label} must be list/tuple")
    n = len(matrix)
    if n == 0:
        raise GirihKellsVasarelyError("INVALID_MATRIX", f"{label} must be non-empty")
    out: list[list[Fraction]] = []
    for r_idx, row in enumerate(matrix):
        if type(row) not in (list, tuple):
            raise GirihKellsVasarelyError("INVALID_MATRIX", f"{label} row {r_idx} must be list/tuple")
        if len(row) != n:
            raise GirihKellsVasarelyError("INVALID_MATRIX", f"{label} row {r_idx} length mismatch")
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


class QPhi:
    """Exact element a + b*phi in Q(sqrt(5)) = Q[phi]/(phi^2 - phi - 1)."""

    __slots__ = ("a", "b")

    def __init__(self, a: Fraction | int, b: Fraction | int = 0) -> None:
        self.a = parse_exact_rational(a, "qphi.a")
        self.b = parse_exact_rational(b, "qphi.b")

    def __add__(self, other: QPhi) -> QPhi:
        if type(other) is not QPhi:
            raise GirihKellsVasarelyError("INVALID_QPHI_OPERAND", "__add__ requires an exact QPhi operand")
        return QPhi(self.a + other.a, self.b + other.b)

    def __sub__(self, other: QPhi) -> QPhi:
        if type(other) is not QPhi:
            raise GirihKellsVasarelyError("INVALID_QPHI_OPERAND", "__sub__ requires an exact QPhi operand")
        return QPhi(self.a - other.a, self.b - other.b)

    def __mul__(self, other: QPhi) -> QPhi:
        if type(other) is not QPhi:
            raise GirihKellsVasarelyError("INVALID_QPHI_OPERAND", "__mul__ requires an exact QPhi operand")
        return QPhi(
            self.a * other.a + self.b * other.b,
            self.a * other.b + self.b * other.a + self.b * other.b,
        )

    def __eq__(self, other: object) -> bool:
        if type(other) is not QPhi:
            return False
        return self.a == other.a and self.b == other.b

    def __hash__(self) -> int:
        return hash((self.a, self.b))

    def to_dict(self) -> dict[str, str]:
        return {"a": format_rational(self.a), "b_phi": format_rational(self.b)}


QP0 = QPhi(0, 0)
QP1 = QPhi(1, 0)
QPHI = QPhi(0, 1)
QP_HALF = QPhi(Fraction(1, 2), 0)


# ---------------------------------------------------------------------------
# Pillar 1: Girih Q(phi) Tiles, Penrose Inflation & Elser-Sloane E8 -> H4
# ---------------------------------------------------------------------------

def certify_pillar1_girih_qphi_e8() -> dict[str, Any]:
    """Certify 5 Girih tile areas from Q(phi) vertices, inflation, and E8->H4 240 icosians."""
    # Exact unit vectors e^{i k * 36 deg}: x = cos(k*36) in (1/2)Z[phi], y = sin(k*36)/sin(36) in Z[phi]
    cos36 = (
        QPhi(1, 0),
        QPhi(0, Fraction(1, 2)),
        QPhi(Fraction(-1, 2), Fraction(1, 2)),
        QPhi(Fraction(1, 2), Fraction(-1, 2)),
        QPhi(0, Fraction(-1, 2)),
        QPhi(-1, 0),
        QPhi(0, Fraction(-1, 2)),
        QPhi(Fraction(1, 2), Fraction(-1, 2)),
        QPhi(Fraction(-1, 2), Fraction(1, 2)),
        QPhi(0, Fraction(1, 2)),
    )
    sin36_over_s = (
        QPhi(0, 0), QPhi(1, 0), QPhi(0, 1), QPhi(0, 1), QPhi(1, 0),
        QPhi(0, 0), QPhi(-1, 0), QPhi(0, -1), QPhi(0, -1), QPhi(-1, 0),
    )
    sin2_36 = QPhi(Fraction(3, 4), Fraction(-1, 4))
    unit_steps_ok = all(
        cos36[k] * cos36[k] + sin36_over_s[k] * sin36_over_s[k] * sin2_36 == QP1
        for k in range(10)
    )

    tile_specs: tuple[tuple[str, tuple[int, ...], QPhi], ...] = (
        ("rhombus", (2, 3, 2, 3), QPhi(0, 1)),
        ("pentagon", (3, 3, 3, 3, 3), QPhi(Fraction(1, 2), Fraction(3, 2))),
        ("bowtie", (2, 2, 6, 2, 2, 6), QPhi(-1, 2)),
        ("elongated_hexagon", (2, 4, 4, 2, 4, 4), QPhi(2, 1)),
        ("decagon", (4,) * 10, QPhi(5, 5)),
    )

    tiles_out: dict[str, Any] = {}
    areas: dict[str, QPhi] = {}
    all_closed = True
    all_areas_exact = True
    for name, angs, expected in tile_specs:
        x, y = QP0, QP0
        direction = 0
        verts: list[tuple[QPhi, QPhi]] = [(x, y)]
        for a36 in angs:
            x = x + cos36[direction]
            y = y + sin36_over_s[direction]
            verts.append((x, y))
            direction = (direction + (5 - a36)) % 10
        closed = verts[-1] == (QP0, QP0)
        if not closed:
            all_closed = False
        shoelace = QP0
        for idx in range(len(angs)):
            x1, y1 = verts[idx]
            x2, y2 = verts[idx + 1]
            shoelace = shoelace + (x1 * y2 - y1 * x2)
        area = shoelace * QP_HALF
        if area != expected:
            all_areas_exact = False
        areas[name] = area
        tiles_out[name] = {
            "n_edges": len(angs),
            "interior_angles_deg": [a36 * 36 for a36 in angs],
            "area_over_sin36": area.to_dict(),
        }

    hex_bow_eq_2pent = areas["elongated_hexagon"] + areas["bowtie"] == QPhi(2, 0) * areas["pentagon"]
    dec_eq_2hex_2pent = (
        areas["decagon"] == QPhi(2, 0) * areas["elongated_hexagon"] + QPhi(2, 0) * areas["pentagon"]
    )

    # Penrose P3 thick/thin rhombus & P2 kite/dart area ratios (both exact phi)
    thin_rhombus_area = QP1  # 1 * 1 * sin(36) / sin(36) = 1
    p3_ratio_ok = areas["rhombus"] == QPHI * thin_rhombus_area
    # P2 kite = 2*(1/2 * phi * 1 * sin(72)) = phi^2; dart = 2*(1/2 * 1 * 1 * sin(72)) = phi -> ratio = phi
    p2_kite_area = QPHI * QPHI
    p2_dart_area = QPHI
    p2_ratio_ok = p2_kite_area == QPHI * p2_dart_area

    # Inflation matrix M = [[2,1],[1,1]] (phi^2 scaling): det=1, tr=3, lambda^2 - 3*lambda + 1 = 0
    M_inf = [[2, 1], [1, 1]]
    det_M = bareiss_det_exact(M_inf)
    tr_M = Fraction(M_inf[0][0] + M_inf[1][1], 1)
    phi2 = QPHI * QPHI
    char_poly_val = phi2 * phi2 - QPhi(tr_M, 0) * phi2 + QPhi(det_M, 0)
    char_poly_ok = char_poly_val == QP0

    # Elser-Sloane (1987) E8 -> H4 icosian cut-and-project bridge (240 roots = 2I U phi*2I)
    icos_1: set[tuple[QPhi, QPhi, QPhi, QPhi]] = set()
    for idx in range(4):
        for s in (-1, 1):
            v = [QP0, QP0, QP0, QP0]
            v[idx] = QPhi(s, 0)
            icos_1.add((v[0], v[1], v[2], v[3]))
    for signs in product((-1, 1), repeat=4):
        icos_1.add(tuple(QPhi(Fraction(s, 2), 0) for s in signs))  # type: ignore[arg-type]
    even_perms = [
        p for p in permutations(range(4))
        if sum(1 for i in range(4) for j in range(i + 1, 4) if p[i] > p[j]) % 2 == 0
    ]
    c_half = QPhi(Fraction(1, 2), 0)
    c_phi_h = QPhi(0, Fraction(1, 2))
    c_inv_h = QPhi(Fraction(-1, 2), Fraction(1, 2))
    for p in even_perms:
        for s1, s2, s3 in product((-1, 1), repeat=3):
            base = (QP0, c_half * QPhi(s1, 0), c_phi_h * QPhi(s2, 0), c_inv_h * QPhi(s3, 0))
            icos_1.add((base[p[0]], base[p[1]], base[p[2]], base[p[3]]))

    icos_phi = {(QPHI * v[0], QPHI * v[1], QPHI * v[2], QPHI * v[3]) for v in icos_1}
    all_240 = sorted(icos_1 | icos_phi, key=lambda v: tuple((c.a, c.b) for c in v))

    def _e8_dot(u: tuple[QPhi, QPhi, QPhi, QPhi], v: tuple[QPhi, QPhi, QPhi, QPhi]) -> Fraction:
        acc = QP0
        for idx in range(4):
            acc = acc + u[idx] * v[idx]
        return Fraction(2, 1) * acc.a

    inner_sq_set = {sum((c * c for c in v), QP0) for v in icos_1}
    outer_sq_set = {sum((c * c for c in v), QP0) for v in icos_phi}
    radius_ratio_ok = all((inner_sq_set == {QP1}, outer_sq_set == {phi2}))
    all_e8_norms_2 = all(_e8_dot(v, v) == Fraction(2, 1) for v in all_240)

    r0 = all_240[0]
    ip_hist: dict[str, int] = {}
    for v in all_240:
        k = str(int(_e8_dot(r0, v)))
        ip_hist[k] = ip_hist.get(k, 0) + 1
    ip_hist_ok = ip_hist == {"-2": 1, "-1": 56, "0": 126, "1": 56, "2": 1}

    # Extract 8 simple roots via generic Weyl chamber and verify unimodularity det(G8) == 1
    chamber = (100003, 7919, 3571, 1009, 521, 197, 53, 11)
    pos_roots = [
        v for v in all_240
        if sum(
            (chamber[2 * i] * v[i].a + chamber[2 * i + 1] * v[i].b for i in range(4)),
            Q0,
        ) > 0
    ]
    pos_set = set(pos_roots)
    simple_roots: list[tuple[QPhi, QPhi, QPhi, QPhi]] = []
    for r in pos_roots:
        decomposable = False
        for r1 in pos_roots:
            diff = (r[0] - r1[0], r[1] - r1[1], r[2] - r1[2], r[3] - r1[3])
            if diff in pos_set:
                decomposable = True
                break
        if not decomposable:
            simple_roots.append(r)
    gram_8 = [[_e8_dot(u, v) for v in simple_roots] for u in simple_roots]
    det_gram_8 = bareiss_det_exact(gram_8)

    pillar_ok = all((
        unit_steps_ok,
        all_closed,
        all_areas_exact,
        hex_bow_eq_2pent,
        dec_eq_2hex_2pent,
        p3_ratio_ok,
        p2_ratio_ok,
        det_M == Q1,
        tr_M == Fraction(3, 1),
        char_poly_ok,
        len(icos_1) == 120,
        len(icos_phi) == 120,
        len(all_240) == 240,
        radius_ratio_ok,
        all_e8_norms_2,
        ip_hist_ok,
        len(simple_roots) == 8,
        det_gram_8 == Q1,
    ))

    return {
        "novelty_tag": "N0_CLASSICAL_LU_STEINHARDT_2007_ELSER_SLOANE_1987",
        "pillar_verified": pillar_ok,
        "all_unit_steps_exact": unit_steps_ok,
        "all_polygons_closed": all_closed,
        "all_areas_exact": all_areas_exact,
        "girih_tiles": tiles_out,
        "identities": {
            "hexagon_plus_bowtie_eq_2pentagon": hex_bow_eq_2pent,
            "decagon_eq_2hex_plus_2pent": dec_eq_2hex_2pent,
            "p3_rhombus_ratio_phi": p3_ratio_ok,
            "p2_kite_dart_ratio_phi": p2_ratio_ok,
        },
        "inflation_matrix_phi2": {
            "matrix": M_inf,
            "det": format_rational(det_M),
            "trace": format_rational(tr_M),
            "char_poly_annihilates_phi2": char_poly_ok,
        },
        "elser_sloane_e8_icosian_bridge": {
            "inner_600cell_vertices": len(icos_1),
            "outer_600cell_vertices": len(icos_phi),
            "total_e8_roots": len(all_240),
            "radius_ratio_is_phi": radius_ratio_ok,
            "all_e8_norms_equal_2": all_e8_norms_2,
            "root_inner_product_histogram": ip_hist,
            "e8_ip_histogram_exact": ip_hist_ok,
            "simple_root_count": len(simple_roots),
            "e8_gram_det": format_rational(det_gram_8),
            "e8_gram_det_is_1": det_gram_8 == Q1,
        },
    }


# ---------------------------------------------------------------------------
# Pillar 2: Book of Kells Plait Strands, Breakline Surgery & Tait Kirchhoff
# ---------------------------------------------------------------------------

def _require_breakline_map(
    breaklines: Any,
    mm: int,
    nn: int,
) -> dict[tuple[int, int], str]:
    """Validate the exported breakline container/tuple shape: exact (xy pair, 'H'/'V') entries."""
    if type(breaklines) not in (list, tuple):
        raise GirihKellsVasarelyError("INVALID_BREAKLINES", "breaklines must be a list/tuple of (position, kind) pairs")
    breaks: dict[tuple[int, int], str] = {}
    for idx, item in enumerate(breaklines):
        if type(item) not in (list, tuple) or len(item) != 2:
            raise GirihKellsVasarelyError("INVALID_BREAKLINE", f"breakline {idx} must be a (position, kind) pair")
        kind = item[1]
        if type(kind) is not str or kind not in ("H", "V"):
            raise GirihKellsVasarelyError("INVALID_BREAKLINE", "breakline kind must be 'H' or 'V'")
        pos = item[0]
        if type(pos) not in (list, tuple) or len(pos) != 2:
            raise GirihKellsVasarelyError("INVALID_BREAKLINE", f"breakline {idx} position must be a 2-element list/tuple")
        bx = require_int(pos[0], "bx", lo=1, hi=2 * mm - 1)
        by = require_int(pos[1], "by", lo=1, hi=2 * nn - 1)
        breaks[(bx, by)] = kind
    return breaks


def _require_edge_pairs(edges: Any, nv: int, label: str = "edges") -> list[tuple[int, int]]:
    """Validate the exported edge container/tuple shape: exact 2-endpoint pairs inside [0, nv-1]."""
    if type(edges) not in (list, tuple):
        raise GirihKellsVasarelyError("INVALID_EDGES", f"{label} must be a list/tuple of 2-endpoint pairs")
    pairs: list[tuple[int, int]] = []
    for idx, edge in enumerate(edges):
        if type(edge) not in (list, tuple) or len(edge) != 2:
            raise GirihKellsVasarelyError("INVALID_EDGES", f"{label}[{idx}] must be a 2-element list/tuple")
        u = require_int(edge[0], f"{label}[{idx}].u", lo=0, hi=nv - 1)
        v = require_int(edge[1], f"{label}[{idx}].v", lo=0, hi=nv - 1)
        pairs.append((u, v))
    return pairs


def trace_celtic_plait_strands(
    m: int,
    n: int,
    breaklines: Sequence[tuple[tuple[int, int], str]] = (),
) -> dict[str, int]:
    """Explicit permutation-cycle tracer on the [0, 2m] x [0, 2n] rectangular Celtic plait."""
    mm = require_int(m, "m", lo=1, hi=16)
    nn = require_int(n, "n", lo=1, hi=16)
    breaks = _require_breakline_map(breaklines, mm, nn)

    edges: list[tuple[int, int, int, int]] = []
    for x in range(2 * mm + 1):
        for y in range(2 * nn + 1):
            if (x + y) % 2 != 1:
                continue
            for dx in (-1, 1):
                for dy in (-1, 1):
                    nx, ny = x + dx, y + dy
                    if 0 <= nx <= 2 * mm and 0 <= ny <= 2 * nn:
                        edges.append((x, y, dx, dy))

    nxt: dict[tuple[int, int, int, int], tuple[int, int, int, int]] = {}
    for x, y, dx, dy in edges:
        nx, ny = x + dx, y + dy
        ndx, ndy = dx, dy
        if nx == 0 or nx == 2 * mm:
            ndx = -ndx
        if ny == 0 or ny == 2 * nn:
            ndy = -ndy
        b = breaks.get((nx, ny))
        if b == "V":
            ndx = -ndx
        elif b == "H":
            ndy = -ndy
        nxt[(x, y, dx, dy)] = (nx, ny, ndx, ndy)

    seen: set[tuple[int, int, int, int]] = set()
    dir_cycles = 0
    for e in edges:
        if e in seen:
            continue
        cur = e
        while cur not in seen:
            seen.add(cur)
            cur = nxt[cur]
        dir_cycles += 1
    crossings = 2 * mm * nn - mm - nn - len(breaks)
    return {
        "m": mm,
        "n": nn,
        "strand_count": dir_cycles // 2,
        "crossing_count": crossings,
    }


def kirchhoff_spanning_trees_exact(n_verts: int, edges: Sequence[tuple[int, int]]) -> int:
    """Exact Kirchhoff Matrix-Tree determinant det(L_0) via fraction-free Bareiss."""
    nv = require_int(n_verts, "n_verts", lo=1, hi=64)
    pairs = _require_edge_pairs(edges, nv)
    if nv == 1:
        return 1
    L = [[Q0] * nv for _ in range(nv)]
    for u, v in pairs:
        L[u][u] += Q1
        L[v][v] += Q1
        L[u][v] -= Q1
        L[v][u] -= Q1
    L0 = [row[:-1] for row in L[:-1]]
    return int(bareiss_det_exact(L0))


def _celtic_dual_tait_graphs(m: int, n: int) -> tuple[int, list[tuple[int, int]], int, list[tuple[int, int]]]:
    """Build both White (P_m x P_n) and Black planar-dual Tait checker-graphs of an m x n plait."""
    w_edges: list[tuple[int, int]] = []
    for r in range(m):
        for c in range(n):
            u = r * n + c
            if c + 1 < n:
                w_edges.append((u, r * n + (c + 1)))
            if r + 1 < m:
                w_edges.append((u, (r + 1) * n + c))

    def _bid(i: int, j: int) -> int:
        if i == 0 or i == m or j == 0 or j == n:
            return 0
        return 1 + (i - 1) * (n - 1) + (j - 1)

    b_nv = 1 + (m - 1) * (n - 1)
    b_edges: list[tuple[int, int]] = []
    for i in range(m):
        for j in range(1, n):
            b_edges.append((_bid(i, j), _bid(i + 1, j)))
    for i in range(1, m):
        for j in range(n):
            b_edges.append((_bid(i, j), _bid(i, j + 1)))
    return m * n, w_edges, b_nv, b_edges


def certify_pillar2_kells_plait_kirchhoff() -> dict[str, Any]:
    """Certify 12x12 Celtic plait gcd(m,n) theorem, breakline surgery, and Tait Kirchhoff dets."""
    # Exact permutation-cycle sweep over all 144 pairs (m, n) in [1..12]^2
    mismatches = 0
    single_knot_pairs = 0
    witness_pairs: dict[str, int] = {}
    for m in range(1, 13):
        for n in range(1, 13):
            res = trace_celtic_plait_strands(m, n)
            g = math.gcd(m, n)
            if res["strand_count"] != g:
                mismatches += 1
            if g == 1:
                single_knot_pairs += 1
            if (m, n) in ((2, 3), (3, 4), (4, 6), (6, 6)):
                witness_pairs[f"{m}x{n}"] = res["strand_count"]

    # Breakline surgery witnesses (distinct-component merge vs self-crossing split/orient-flip)
    b_22_base = trace_celtic_plait_strands(2, 2)["strand_count"]
    b_22_v = trace_celtic_plait_strands(2, 2, [((1, 2), "V")])["strand_count"]
    b_22_h = trace_celtic_plait_strands(2, 2, [((1, 2), "H")])["strand_count"]
    b_46_base = trace_celtic_plait_strands(4, 6)["strand_count"]
    b_46_v = trace_celtic_plait_strands(4, 6, [((1, 2), "V")])["strand_count"]
    b_66_base = trace_celtic_plait_strands(6, 6)["strand_count"]
    b_66_v = trace_celtic_plait_strands(6, 6, [((1, 2), "V")])["strand_count"]

    b_23_base = trace_celtic_plait_strands(2, 3)["strand_count"]
    b_23_h = trace_celtic_plait_strands(2, 3, [((1, 2), "H")])["strand_count"]
    b_23_v = trace_celtic_plait_strands(2, 3, [((1, 2), "V")])["strand_count"]

    both_merge_ok = all((
        b_22_base == 2,
        b_22_v == 1,
        b_22_h == 1,
        b_46_base == 2,
        b_46_v == 1,
        b_66_base == 6,
        b_66_v == 5,
    ))
    self_split_ok = all((b_23_base == 1, b_23_h == 2, b_23_v == 1))

    # Classic alternating knot determinants |V_K(-1)| = det(L_0) (Jones polynomial determinant identity)
    classic_knots = {
        "trefoil_3_1": kirchhoff_spanning_trees_exact(3, ((0, 1), (1, 2), (2, 0))),
        "figure_eight_4_1": kirchhoff_spanning_trees_exact(3, ((0, 1), (0, 1), (1, 2), (2, 0))),
        "cinquefoil_5_1": kirchhoff_spanning_trees_exact(5, ((0, 1), (1, 2), (2, 3), (3, 4), (4, 0))),
    }

    # Alternating Celtic plait dual Tait Kirchhoff determinants tau(G_white) == tau(G_black)
    plait_dets: dict[str, Any] = {}
    dual_ok = True
    for m, n in ((2, 2), (2, 3), (3, 3), (3, 4)):
        wnv, we, bnv, be = _celtic_dual_tait_graphs(m, n)
        dw = kirchhoff_spanning_trees_exact(wnv, we)
        db = kirchhoff_spanning_trees_exact(bnv, be)
        if dw != db:
            dual_ok = False
        plait_dets[f"{m}x{n}"] = {
            "crossings": len(we),
            "white_vertices": wnv,
            "black_vertices": bnv,
            "tau_white": dw,
            "tau_black": db,
        }

    pillar_ok = all((
        mismatches == 0,
        single_knot_pairs == 91,
        both_merge_ok,
        self_split_ok,
        classic_knots == {"trefoil_3_1": 3, "figure_eight_4_1": 5, "cinquefoil_5_1": 5},
        dual_ok,
        plait_dets["2x2"]["tau_white"] == 4,
        plait_dets["2x3"]["tau_white"] == 15,
        plait_dets["3x3"]["tau_white"] == 192,
        plait_dets["3x4"]["tau_white"] == 2415,
    ))

    return {
        "novelty_tag": "N0_CLASSICAL_CROMWELL_KIRCHHOFF_TAIT",
        "pillar_verified": pillar_ok,
        "plait_grid_sweep_1_to_12": {
            "total_pairs_traced": 144,
            "mismatches": mismatches,
            "single_strand_knot_pairs": single_knot_pairs,
            "all_144_pairs_match_gcd": mismatches == 0,
            "witness_strand_counts": witness_pairs,
        },
        "breakline_surgery": {
            "distinct_merge_2x2_V": [b_22_base, b_22_v],
            "distinct_merge_2x2_H": [b_22_base, b_22_h],
            "distinct_merge_4x6_V": [b_46_base, b_46_v],
            "distinct_merge_6x6_V": [b_66_base, b_66_v],
            "self_crossing_2x3_H_split": [b_23_base, b_23_h],
            "self_crossing_2x3_V_orient_flip": [b_23_base, b_23_v],
            "both_merge_distinct_components": both_merge_ok,
            "self_crossing_splits_and_preserves": self_split_ok,
        },
        "kirchhoff_tait_determinants": {
            "classic_knots_V_neg1": classic_knots,
            "celtic_plaits_dual_tait": plait_dets,
            "dual_tait_parity_all_match": dual_ok,
        },
    }


# ---------------------------------------------------------------------------
# Pillar 3: Victor Vasarely Vega Orthographic Beltrami & Plastic Alphabet D4
# ---------------------------------------------------------------------------

def certify_pillar3_vasarely_vega_alphabet() -> dict[str, Any]:
    """Certify exact Beltrami orthographic metric det(g)=1/(1-rho^2) and D4 Plastic Alphabet orbits."""
    # Exact Pythagorean rational sample points ordered strictly by radius rho
    samples: tuple[tuple[Fraction, Fraction, Fraction], ...] = (
        (Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)),
        (Fraction(3, 13), Fraction(4, 13), Fraction(5, 13)),
        (Fraction(3, 5), Fraction(0, 1), Fraction(3, 5)),
        (Fraction(4, 5), Fraction(0, 1), Fraction(4, 5)),
        (Fraction(12, 13), Fraction(0, 1), Fraction(12, 13)),
    )
    vega_rows: list[dict[str, Any]] = []
    prev_k2: Fraction | None = None
    monotonic = True
    all_det_ok = True
    all_hyp_ok = True
    for x, y, rho in samples:
        r2 = x * x + y * y
        denom = Q1 - r2
        # First fundamental form of z = sqrt(1 - x^2 - y^2): g_ij = delta_ij + x_i x_j / (1 - rho^2)
        g = [
            [Q1 + (x * x) / denom, (x * y) / denom],
            [(x * y) / denom, Q1 + (y * y) / denom],
        ]
        det_g = bareiss_det_exact(g)
        expected_k2 = Q1 / denom
        if det_g != expected_k2:
            all_det_ok = False
        if prev_k2 is not None and det_g <= prev_k2:
            monotonic = False
        prev_k2 = det_g
        # Hyperbolic Poincare disk contrast (K = -1): g_hyp = (4 / (1 - rho^2)^2) * I_2
        c_hyp = Fraction(4, 1) / (denom * denom)
        det_hyp = bareiss_det_exact([[c_hyp, Q0], [Q0, c_hyp]])
        if det_hyp != Fraction(16, 1) / (denom ** 4):
            all_hyp_ok = False
        vega_rows.append({
            "x": format_rational(x),
            "y": format_rational(y),
            "rho": format_rational(rho),
            "rho_sq": format_rational(r2),
            "g_metric": [[format_rational(v) for v in row] for row in g],
            "K_sq_det_g": format_rational(det_g),
            "K_sq_decimal_4": format_decimal(det_g, 4),
            "poincare_det_g_hyp": format_rational(det_hyp),
        })

    # Plastic Alphabet (1955 Unite Plastique): D4 (order 8) Burnside orbit grammar
    # 1) Single-tile 6 geometric forms (3 D4-invariant + 2 D2-invariant + 1 C2-invariant = 11 oriented states)
    # Explicit D4 action on the 11 oriented form states:
    #   0: circle (fixed by all 8)
    #   1: square (fixed by all 8)
    #   2: rhombus (fixed by all 8)
    #   3,4: ellipse (+45, -45) -> swap under r90/r270/h_ref/v_ref, fixed by e/r180/d1/d2
    #   5,6: rectangle (horiz, vert) -> swap under r90/r270/d1/d2, fixed by e/r180/h_ref/v_ref
    #   7,8,9,10: right-triangle (4 corners NW,NE,SE,SW) -> rotated by r90, each diag ref fixes 2
    d4_single_perms: tuple[tuple[int, ...], ...] = (
        (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10),   # e
        (0, 1, 2, 4, 3, 6, 5, 8, 9, 10, 7),   # r90
        (0, 1, 2, 3, 4, 5, 6, 9, 10, 7, 8),   # r180
        (0, 1, 2, 4, 3, 6, 5, 10, 7, 8, 9),   # r270
        (0, 1, 2, 4, 3, 5, 6, 8, 7, 10, 9),   # h_ref (left-right)
        (0, 1, 2, 4, 3, 5, 6, 10, 9, 8, 7),   # v_ref (top-bottom)
        (0, 1, 2, 3, 4, 6, 5, 7, 10, 9, 8),   # d1_ref (NW-SE diag)
        (0, 1, 2, 3, 4, 6, 5, 9, 8, 7, 10),   # d2_ref (NE-SW diag)
    )
    single_fix_sum = sum(sum(1 for i, img in enumerate(perm) if img == i) for perm in d4_single_perms)
    single_orbits = single_fix_sum // 8

    # 2) 2x2 Unite Plastique quad-block under D4 acting on 4 cells (0:NW, 1:NE, 2:SE, 3:SW)
    d4_quad_perms: tuple[tuple[int, int, int, int], ...] = (
        (0, 1, 2, 3),  # e
        (1, 2, 3, 0),  # r90
        (2, 3, 0, 1),  # r180
        (3, 0, 1, 2),  # r270
        (1, 0, 3, 2),  # h_ref
        (3, 2, 1, 0),  # v_ref
        (0, 3, 2, 1),  # d1_ref
        (2, 1, 0, 3),  # d2_ref
    )
    quad_orbits: dict[str, int] = {}
    burnside_ok = True
    for k in (2, 3, 6):
        formula = (k ** 4 + 2 * (k ** 3) + 3 * (k ** 2) + 2 * k) // 8
        # Brute-force canonical orbit enumeration verifying Burnside exactness
        orbits_set: set[tuple[int, int, int, int]] = set()
        for state in product(range(k), repeat=4):
            canon = min(tuple(state[p[i]] for i in range(4)) for p in d4_quad_perms)
            orbits_set.add(canon)  # type: ignore[arg-type]
        if len(orbits_set) != formula:
            burnside_ok = False
        quad_orbits[f"k_{k}"] = len(orbits_set)

    # Distinct two-color (bg != fg) Plastic Alphabet counts: 6 * c * (c - 1)
    color_counts = {f"c_{c}": single_orbits * c * (c - 1) for c in (2, 6, 12)}

    pillar_ok = all((
        all_det_ok,
        monotonic,
        all_hyp_ok,
        single_orbits == 6,
        burnside_ok,
        quad_orbits == {"k_2": 6, "k_3": 21, "k_6": 231},
        color_counts == {"c_2": 12, "c_6": 180, "c_12": 792},
    ))

    return {
        "novelty_tag": "N0_CLASSICAL_BELTRAMI_BURNSIDE",
        "pillar_verified": pillar_ok,
        "vega_orthographic_beltrami": {
            "sphere_curvature_K": "1",
            "poincare_curvature_K": "-1",
            "det_equals_inv_one_minus_rho2": all_det_ok,
            "strictly_monotonic_bulging": monotonic,
            "hyperbolic_metric_det_exact": all_hyp_ok,
            "pythagorean_samples": vega_rows,
        },
        "plastic_alphabet_d4_burnside": {
            "d4_group_order": 8,
            "single_tile_oriented_states": 11,
            "single_tile_shape_orbits": single_orbits,
            "two_color_distinct_tile_counts": color_counts,
            "quad_2x2_burnside_orbits": quad_orbits,
            "burnside_matches_bruteforce": burnside_ok,
        },
    }


# ---------------------------------------------------------------------------
# Pillar 4: Cross-Domain Exact-Operator Unification & Honest Law-5 Obstructions
# ---------------------------------------------------------------------------

def certify_pillar4_unification(
    p1: dict[str, Any],
    p2: dict[str, Any],
    p3: dict[str, Any],
) -> dict[str, Any]:
    """Synthesize algebraic operators uniting P1-P3 and certify explicit Law-5 obstructions."""
    e8_det = p1["elser_sloane_e8_icosian_bridge"]["e8_gram_det"]
    tau_3x4 = p2["kirchhoff_tait_determinants"]["celtic_plaits_dual_tait"]["3x4"]["tau_white"]
    k2_12_13 = p3["vega_orthographic_beltrami"]["pythagorean_samples"][-1]["K_sq_det_g"]
    pillar_ok = all((
        p1["pillar_verified"],
        p2["pillar_verified"],
        p3["pillar_verified"],
        e8_det == "1",
        tau_3x4 == 2415,
        k2_12_13 == "169/25",
    ))
    return {
        "novelty_tag": "N1_UNIFIED_EXACT_OPERATOR_SYNTHESIS",
        "pillar_verified": pillar_ok,
        "shared_exact_operators": {
            "bareiss_determinant_bridges": {
                "p1_e8_icosian_gram_det": e8_det,
                "p1_girih_inflation_det": p1["inflation_matrix_phi2"]["det"],
                "p2_kells_3x4_kirchhoff_det": tau_3x4,
                "p3_vasarely_rho_12_13_metric_det": k2_12_13,
            },
            "qphi_e8_bridge": "Elser-Sloane trace form tau(a+b*phi)=2a lifts 240 H4 icosians directly to unimodular E8 (det=1), linking siliquant E8 to Girih Q(phi).",
            "finite_group_orbits": "D4 Burnside orbit grammar (order 8) governs Vasarely Unite Plastique alongside S_n cycle decomposition on Celtic plait crossings.",
        },
        "law5_honest_obstructions": {
            "aperiodic_vs_periodic_lattice": "Girih tilings live in non-crystallographic aperiodic Z[phi] (5-fold symmetry forbidden by 2D crystallographic restriction), whereas Book of Kells rectangular plaits live on periodic planar Z^2 grids.",
            "positive_vs_negative_curvature": "Vasarely Vega orthographic projection samples positive Gaussian curvature K=+1 on S^2 (det(g)=1/(1-rho^2)) whereas Escher Circle Limit / siliquant#44 hyperbolic shells live on K=-1 Poincare disk (det(g_hyp)=16/(1-rho^2)^4).",
            "no_metaphor_conflation": "Cross-domain bridge holds strictly at the level of shared exact algebraic operators (Bareiss determinant, Q(phi) cut-and-project, finite permutation/dihedral orbits), never claiming physical or historical identity.",
        },
    }


# ---------------------------------------------------------------------------
# Certificate Construction & Fail-Closed Validation (`full_replay` True/False)
# ---------------------------------------------------------------------------

def build_standalone_payload() -> dict[str, Any]:
    p1 = certify_pillar1_girih_qphi_e8()
    p2 = certify_pillar2_kells_plait_kirchhoff()
    p3 = certify_pillar3_vasarely_vega_alphabet()
    p4 = certify_pillar4_unification(p1, p2, p3)
    all_ok = all((
        p1["pillar_verified"],
        p2["pillar_verified"],
        p3["pillar_verified"],
        p4["pillar_verified"],
    ))
    return {
        "oracle_class": "exact",
        "novelty_classification": "N1_UNIFIED_PORTAL33_EXACT_OPERATORS_WITH_N0_CLASSICAL_BASE",
        "zero_floats_exact_arithmetic": True,
        "all_verified": all_ok,
        "pillar1_girih_qphi_e8": p1,
        "pillar2_kells_plait_kirchhoff": p2,
        "pillar3_vasarely_vega_alphabet": p3,
        "pillar4_cross_domain_unification": p4,
    }


def build_standalone_certificate() -> dict[str, Any]:
    payload = build_standalone_payload()
    payload_sha = sha256_hex(canonical_json_bytes(payload))
    outer = {
        "schema": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": payload_sha,
        "payload": payload,
    }
    cert_sha = sha256_hex(canonical_json_bytes(outer))
    return {
        "schema": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": payload_sha,
        "certificate_sha256": cert_sha,
        "payload": payload,
    }


def _validate_payload_structure(payload: Any) -> None:
    """Strict structural & bool-allowlist validator closing hollow/bool-for-int forgeries in non-replay mode."""
    if type(payload) is not dict:
        raise GirihKellsVasarelyError("INVALID_PAYLOAD_TYPE", "payload must be strict dict")
    if frozenset(payload.keys()) != _PAYLOAD_KEYS:
        raise GirihKellsVasarelyError("INVALID_PAYLOAD_KEYS", "payload key set mismatch")
    if payload["oracle_class"] != "exact":
        raise GirihKellsVasarelyError("INVALID_ORACLE_CLASS", "oracle_class must be 'exact'")
    if payload["zero_floats_exact_arithmetic"] is not True:
        raise GirihKellsVasarelyError("INVALID_ZERO_FLOAT_FLAG", "zero_floats_exact_arithmetic must be True")
    if payload["all_verified"] is not True:
        raise GirihKellsVasarelyError("ALL_VERIFIED_FALSE", "payload.all_verified must be True")
    for pkey in _PILLAR_KEYS:
        pillar = payload[pkey]
        if type(pillar) is not dict:
            raise GirihKellsVasarelyError("INVALID_PILLAR_TYPE", f"{pkey} must be strict dict")
        if pillar.get("pillar_verified") is not True:
            raise GirihKellsVasarelyError("PILLAR_NOT_VERIFIED", f"{pkey}.pillar_verified must be True")
    # Walk payload iteratively ensuring every bool occurs ONLY under an explicitly allowlisted boolean key
    stack: list[tuple[str | None, Any]] = [(None, payload)]
    while stack:
        key, cur = stack.pop()
        t = type(cur)
        if t is dict:
            for k, v in cur.items():
                stack.append((k, v))
        elif t is list:
            for item in cur:
                if type(item) is bool:
                    raise GirihKellsVasarelyError("UNEXPECTED_BOOL_IN_LIST", "bool forbidden inside JSON list")
                stack.append((None, item))
        elif t is bool and key not in _ALLOWED_BOOL_KEYS:
            raise GirihKellsVasarelyError("UNEXPECTED_BOOL_FIELD", f"bool forbidden for key: {key}")


def _derive_pin_index(
    pins: dict[tuple[Any, ...], Any],
) -> tuple[dict[tuple[Any, ...], frozenset[Any]], dict[tuple[Any, ...], int]]:
    """Derive exact per-dict key sets and per-list lengths from the pinned leaf paths."""
    dict_keys: dict[tuple[Any, ...], set[Any]] = {(): set()}
    list_lens: dict[tuple[Any, ...], int] = {}
    for path in pins:
        for depth in range(1, len(path) + 1):
            parent = path[: depth - 1]
            seg = path[depth - 1]
            if type(seg) is int:
                prev = list_lens.get(parent, 0)
                length = seg + 1
                list_lens[parent] = length if length > prev else prev
            else:
                dict_keys.setdefault(parent, set()).add(seg)
    return {k: frozenset(v) for k, v in dict_keys.items()}, list_lens


_PAYLOAD_PIN_DICT_KEYS, _PAYLOAD_PIN_LIST_LENS = _derive_pin_index(_PAYLOAD_LEAF_PINS)


def _pin_path_label(path: tuple[Any, ...]) -> str:
    return "/".join(str(seg) for seg in path) if path else "<root>"


def pin_payload_exact(payload: Any) -> None:
    """Enforce exact dict key sets, exact list lengths, and bijective leaf pinning.

    Every one of the 42 nested dicts must match its exact frozenset of keys, every one
    of the 30 lists must match its exact length, and every one of the 211 leaves must be
    type-identical (bool is never an int) and value-identical to the pinned expectation.
    """
    if type(payload) is not dict:
        raise GirihKellsVasarelyError("PIN_ROOT_TYPE", "payload must be strict dict")
    dict_keys = _PAYLOAD_PIN_DICT_KEYS
    list_lens = _PAYLOAD_PIN_LIST_LENS
    pins = _PAYLOAD_LEAF_PINS
    stack: list[tuple[tuple[Any, ...], Any]] = [((), payload)]
    while stack:
        path, cur = stack.pop()
        if path in dict_keys:
            if type(cur) is not dict:
                raise GirihKellsVasarelyError("PIN_CONTAINER_TYPE", f"{_pin_path_label(path)} must be strict dict")
            if frozenset(cur.keys()) != dict_keys[path]:
                raise GirihKellsVasarelyError("PIN_DICT_KEYS", f"{_pin_path_label(path)} key set mismatch")
            for key, val in cur.items():
                stack.append((path + (key,), val))
        elif path in list_lens:
            if type(cur) is not list:
                raise GirihKellsVasarelyError("PIN_CONTAINER_TYPE", f"{_pin_path_label(path)} must be strict list")
            if len(cur) != list_lens[path]:
                raise GirihKellsVasarelyError("PIN_LIST_LEN", f"{_pin_path_label(path)} length mismatch")
            for idx, val in enumerate(cur):
                stack.append((path + (idx,), val))
        else:
            expected = pins[path]
            if type(cur) is not type(expected):
                raise GirihKellsVasarelyError("PIN_LEAF_TYPE", f"{_pin_path_label(path)} leaf type mismatch")
            if cur != expected:
                raise GirihKellsVasarelyError("PIN_LEAF_VALUE", f"{_pin_path_label(path)} leaf value mismatch")


def _invoke_secondary_audit(payload: Any) -> dict[str, Any]:
    """Invoke the Zone-B secondary auditor (audit module) without a static import cycle."""
    try:
        from girih_kells_vasarely_audit import secondary_audit_payload as _secondary
    except ImportError as exc:
        raise GirihKellsVasarelyError(
            "SECONDARY_AUDIT_UNAVAILABLE", "secondary auditor module is not importable"
        ) from exc
    return _secondary(payload)


def validate_certificate_payload(cert: Any, full_replay: bool = True) -> dict[str, Any]:
    """Fail-closed Zone-B certificate validator supporting full_replay=True and full_replay=False."""
    require_bool(full_replay, "full_replay")
    if type(cert) is not dict:
        raise GirihKellsVasarelyError("NON_OBJECT_CERT", "certificate must be strict dict")
    validate_json_tree_iterative(cert)
    if frozenset(cert.keys()) != _CERT_KEYS:
        raise GirihKellsVasarelyError("INVALID_CERT_KEYS", "certificate top-level keys mismatch")
    if cert["schema"] != SCHEMA_VERSION:
        raise GirihKellsVasarelyError("INVALID_SCHEMA", "unexpected certificate schema")
    if cert["track_id"] != TRACK_ID:
        raise GirihKellsVasarelyError("INVALID_TRACK_ID", "unexpected certificate track_id")

    p_sha = require_hex64(cert["payload_sha256"], "payload_sha256")
    c_sha = require_hex64(cert["certificate_sha256"], "certificate_sha256")
    payload = cert["payload"]
    _validate_payload_structure(payload)

    recomputed_p_sha = sha256_hex(canonical_json_bytes(payload))
    if not constant_time_hex64_equal(p_sha, recomputed_p_sha, "payload_sha256"):
        raise GirihKellsVasarelyError("PAYLOAD_SHA_MISMATCH", "payload_sha256 mismatch")

    outer = {
        "schema": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": p_sha,
        "payload": payload,
    }
    recomputed_c_sha = sha256_hex(canonical_json_bytes(outer))
    if not constant_time_hex64_equal(c_sha, recomputed_c_sha, "certificate_sha256"):
        raise GirihKellsVasarelyError("CERT_SHA_MISMATCH", "certificate_sha256 mismatch")

    secondary: dict[str, Any] | None = None
    if full_replay:
        expected = build_standalone_certificate()
        if canonical_json_bytes(cert) != canonical_json_bytes(expected):
            raise GirihKellsVasarelyError("ORACLE_REPLAY_MISMATCH", "certificate diverges from exact oracle replay")
    else:
        # Non-replay mode carries the full second-audit burden: algebraic re-derivation,
        # entry-point JSON-tree exactness, and the 42-dict/30-list/211-leaf exact pin.
        secondary = _invoke_secondary_audit(payload)

    result: dict[str, Any] = {
        "valid": True,
        "schema": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": p_sha,
        "certificate_sha256": c_sha,
        "full_replay": full_replay,
    }
    if secondary is not None:
        result["secondary_audit"] = secondary
    return result
