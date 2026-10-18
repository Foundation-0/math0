"""Open minimum-distance checker for linear codes over GF(q), q in 3..9
(plus GF(2)).  See gfq.distance for methods, gfq.cli for the CLI."""
from .field import GF, SUPPORTED_Q
from .distance import MinDistanceResult, min_distance, brute_force_min_distance, bz_min_distance
from .matrix import parse_matrix

__all__ = ["GF", "SUPPORTED_Q", "MinDistanceResult", "min_distance",
           "brute_force_min_distance", "bz_min_distance", "parse_matrix"]
__version__ = "0.1.0"
