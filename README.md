# math0
Math explorations.

## gfq: minimum-distance checker for linear codes over GF(q)

`gfq/` is an open checker for the first step in [AREAS.md](AREAS.md) §1:
given a generator matrix over GF(q), compute the exact minimum distance
and print a minimum-weight codeword as a certificate that anyone can
re-check. It makes no claims about new code records.

**Fields.** q ∈ {2, 3, 4, 5, 7, 8, 9}. Prime fields are residues mod p.
GF(4), GF(8) and GF(9) use explicit polynomial tables
(GF(2)[x]/(x²+x+1), GF(2)[x]/(x³+x+1), GF(3)[x]/(x²+1)); elements are the
integers 0..q−1 encoding polynomial coefficients in base p. There is no
field GF(6), and q=6 is rejected. Zero dependencies (Python ≥ 3.10).

**Use.**

```
python3 -m gfq --q 3 examples/golay11.txt          # prints [11,6,5] + certificate
python3 -m gfq --q 4 --method bz --json matrix.txt # machine-readable
cat matrix.txt | python3 -m gfq --q 3 -            # stdin
pip install .                                      # optional: provides `gfq-check`
```

Matrix files: one row per line, entries separated by spaces or commas
(brackets as pasted from Magma/Sage also work), compact digit strings
such as `20121` work for q ≤ 9, `#` comments are ignored, and an optional
leading `q k n` header is accepted. Exit codes: 0 exact, 2 budget
exhausted (only bounds claimed), 1 input error. The printed certificate
is checked to lie in the row space with the claimed weight before it is
reported.

**Methods and limits.** `--method brute` enumerates all
(q^k−1)/(q−1) normalised codewords: exact, feasible only for small q^k
(`auto` uses it up to 400,000 by default). `--method bz` is a
Brouwer–Zimmermann-style enumeration: in g disjoint information sets it
enumerates message weights s = 1, 2, …, which proves
d ≥ min(upper bound, g·(s+1)) at each level, and stops when the bounds
meet (exact) or the `--max-enum` budget runs out (then it reports an
honest interval and exit code 2, never a guessed d). Cost per level is
about g·C(k,s)·(q−1)^(s−1) codewords, so it is strong when d is small
relative to k or several disjoint information sets exist, and weak for
large-k codes with large d — those need the budget raised or a stronger
implementation (bitsets/GPU, better information sets). Finite
enumerations here are labelled VERIFIED, not "proved"; expected values
in the tests are KNOWN theorems.

**Tests.** `python3 -m unittest discover -s tests` validates the field
axioms exhaustively for every supported q, and the distance against
known codes: ternary Golay [11,6,5] and [12,6,6], Hamming codes over
GF(3)/GF(4)/GF(8)/GF(9) (including [21,18,3] and [40,36,3] cases where
brute force is infeasible), Reed–Solomon examples over
GF(5)/GF(7)/GF(8)/GF(9), and brute-vs-BZ agreement on small random codes.

**Attacking the smallest open codetables entries next.** The census in
[data/codetables/](data/codetables/) counts 80,652 open non-binary
entries. A sane order: (1) re-run `python3 data/codetables/census.py
--csv entries.csv` and sort open entries by gap, then by n — single-gap,
small-n entries first, remembering AREAS.md's caution that large GF(7)
gaps mostly reflect weak upper bounds; (2) for a target [n,k] over GF(q),
fetch the record construction's generator matrix from codetables.de and
re-verify its d with this checker before searching (a construction that
cannot be re-checked is not a baseline); (3) search where Grassl's
quasi-cyclic index-2 sweep has not: quasi-twisted codes of index 3–4,
constacyclic shifts, and one-column extensions of record codes, using
this checker (BZ mode, budget set explicitly) to certify every candidate
before believing it; (4) only then consider submitting a verified
improvement, generator matrix included, to codes@codetables.de. No
search or submission has been done in this repository yet.
