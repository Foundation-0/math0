"""Command-line minimum-distance checker.

Usage:
    python -m gfq --q 3 examples/golay11.txt
    python -m gfq --q 4 --method bz --json matrix.txt
    cat matrix.txt | python -m gfq --q 3 -

Exit codes: 0 = exact distance (with certificate codeword printed);
2 = enumeration budget exhausted, only bounds are claimed;
1 = input/usage error.
"""
from __future__ import annotations

import argparse
import json
import sys

from .field import GF
from .matrix import parse_matrix, row_space_contains, weight
from .distance import min_distance


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        prog="gfq-check",
        description="Exact minimum distance of a linear code over GF(q) "
                    "from a generator matrix.")
    ap.add_argument("matrix", help="generator-matrix file, or - for stdin")
    ap.add_argument("--q", type=int, required=True,
                    help="field order: one of 2,3,4,5,7,8,9")
    ap.add_argument("--method", choices=["auto", "brute", "bz"], default="auto")
    ap.add_argument("--max-enum", type=int, default=2_000_000,
                    help="Brouwer-Zimmermann enumeration budget (default 2000000)")
    ap.add_argument("--brute-limit", type=int, default=400_000,
                    help="auto: use brute force at or below this many codewords")
    ap.add_argument("--json", action="store_true", help="machine-readable output")
    args = ap.parse_args(argv)

    try:
        F = GF(args.q)
        text = sys.stdin.read() if args.matrix == "-" else open(args.matrix).read()
        G = parse_matrix(text, F)
        res = min_distance(G, F, method=args.method,
                           brute_limit=args.brute_limit, max_enum=args.max_enum)
    except (ValueError, OSError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 1

    # Certificate sanity: the printed codeword really is in the row space
    # and really has the claimed weight.  This is a cheap independent check
    # of the *upper* bound (the lower bound rests on the enumeration).
    cert_ok = (row_space_contains(G, F, res.codeword)
               and weight(res.codeword) == res.upper_bound)

    if args.json:
        print(json.dumps({
            "q": args.q, "n": res.n, "k": res.k,
            "d": res.d, "lower_bound": res.lower_bound,
            "upper_bound": res.upper_bound, "complete": res.complete,
            "codeword_certificate": res.codeword,
            "certificate_checked": cert_ok,
            "method": res.method, "enumerated": res.enumerated,
            "num_info_sets": res.num_info_sets,
        }, indent=2))
    else:
        print(res.params())
        print(f"field: GF({args.q})  method: {res.method}"
              + (f"  disjoint info sets: {res.num_info_sets}" if res.method == "bz" else "")
              + f"  combinations enumerated: {res.enumerated}")
        label = ("minimum-weight codeword" if res.complete
                 else "lightest codeword found (upper-bound certificate only)")
        print(f"{label} (certificate, weight {res.upper_bound}): "
              + " ".join(str(a) for a in res.codeword))
        print(f"certificate in row space with claimed weight: {cert_ok}")
        if not res.complete:
            print("status: INCOMPLETE - enumeration budget exhausted; "
                  "only the stated bounds are claimed, not an exact d.")
    if not cert_ok:  # pragma: no cover - would indicate an internal bug
        print("error: internal certificate check failed", file=sys.stderr)
        return 1
    return 0 if res.complete else 2


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
