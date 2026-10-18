# Codetables attack: 15 smallest-gap entries over GF(3)/GF(4)/GF(5)

**Headline result: no improvement.** None of the 15 attacked entries yielded
a code beating the table lower bound. On 10 entries the search constructed
codes *matching* the recorded lower bound (independent constructions of
known parameters, all gfq-verified); on 5 it fell 1 short. This file reports
search coverage per entry so the negative result is usable. Nothing here is
a proof that any lower bound is optimal.

Claim labels follow this repo's convention: finite exhaustive checks are
VERIFIED, not "proved"; table values are KNOWN (Grassl's compilation);
nothing below is labelled PROVEN and no CONJECTURE is asserted.

## Targets (KNOWN: table values)

Census regenerated live on 2026-10-18 (see Reproduction): counts identical
to the committed `data/codetables/census-2026-10-18.json` (80,652 open
non-binary entries; no entry moved since the snapshot the same day).
Targets are the smallest-`n` gap-1 entries per field with `k <= 10`, 5 per
field — a code with `d = lb+1` would close the entry. GF(5) `[18,9]`
replaces `[18,7]` so the double-circulant family (`n=2k`) is exercised.
Only these 15 `(q,n,k,lb,ub)` entries are committed (in
`search.py: TARGETS` and `results.json`); Grassl's full tables are not.

| GF(q) | [n,k] | table lb–ub (2026-10-18) | best found d (VERIFIED) | beats lb |
|---|---|---|---|---|
| 3 | [22,8] | 9–10 | 9 | no |
| 3 | [23,8] | 10–11 | 10 | no |
| 3 | [23,9] | 9–10 | 9 | no |
| 3 | [24,9] | 10–11 | 9 | no |
| 3 | [24,10] | 9–10 | 8 | no |
| 4 | [19,8] | 8–9 | 8 | no |
| 4 | [20,9] | 8–9 | 7 | no |
| 4 | [22,6] | 12–13 | 12 | no |
| 4 | [23,7] | 12–13 | 11 | no |
| 4 | [24,8] | 12–13 | 11 | no |
| 5 | [16,5] | 9–10 | 9 | no |
| 5 | [16,6] | 8–9 | 8 | no |
| 5 | [17,6] | 9–10 | 9 | no |
| 5 | [17,7] | 8–9 | 8 | no |
| 5 | [18,9] | 7–8 | 7 | no |

Every "best found d" is VERIFIED twice: `gfq.min_distance` in-process and
the gfq CLI (`complete=true`, certificate codeword checked in the row
space; 14 by brute force, GF(5)[18,9] by Brouwer–Zimmermann). Generator
matrices and CLI outputs are in `best/q*_n*_k*_d*.{txt,gfq.json}`. These
are certificates for the stated `d` of those specific matrices only.
Because no code beats a table lower bound, there is nothing to submit and
no submission note was drafted; nobody was contacted.

## Search coverage per entry

Families (see `search.py` docstring for details):

1. **random**: random projective column multisets (≤200 samples or ~3 s).
2. **greedy+anneal**: greedy column augmentation, then simulated-annealing
   column swaps scored on the exact weight spectrum over all messages
   (spectrum min = exact d of the column multiset when columns span;
   reported candidates always re-verified with gfq). Pass 1: 25 s/target,
   seed 20261018, 2,375,086 steps total. Pass 2 (`--second-pass`): 45 s/
   target from the recorded best + a fresh greedy start, seed 777001,
   3,496,168 steps total, **no target improved**.
3. **cyclic+constacyclic**: exhaustive over all monic check polynomials h
   of degree k (`h | x^n − λ` for some λ≠0), so the best (consta)cyclic d
   below is VERIFIED-exhaustive for that family. `divisors 0` means no
   (consta)cyclic [n,k] code exists at all. Validated on GF(3)[11,6]:
   finds 4 divisors, best d=5 (the ternary Golay parameters), gfq-confirmed.
4. **double-circulant QC** `[I | Circ(a)]`: only applicable for n=2k.
5. **derivations**: shorten/puncture/parity-extend (1–2 coordinates) of
   (a) every `gfq.codes` seed — 65/67/72 seeds for q=3/4/5, of which **0**
   are within derivation reach of any target by parameter arithmetic
   (seeds have n≤13 or wrong k; targets have n≥16), so 0 candidates; and
   (b) phase 2: all such derivations of the 15 best-found codes that land
   on another target — 791 matrices, each gfq-verified.

| GF(q)[n,k] | random (samples→best) | anneal steps p1+p2 (restarts) | cyclic: polys / divisors → best d | DC-QC | phase-2 derivations in → max d |
|---|---|---|---|---|---|
| 3[22,8] | 200→8 | 186,498+386,827 (6) | 6,561 / 0 → none | n=2k only | 322 → 9 |
| 3[23,8] | 200→8 | 178,215+393,494 (6) | 6,561 / 0 → none | n=2k only | 25 → 9 |
| 3[23,9] | 200→8 | 46,278+119,601 (5) | 19,683 / 0 → none | n=2k only | 48 → 8 |
| 3[24,9] | 200→8 | 39,719+106,541 (5) | 19,683 / 76 → 8 | n=2k only | 1 → 9 |
| 3[24,10] | 37→7 | 9,745+39,021 (4) | 59,049 / 84 → 6 | n=2k only | 0 |
| 4[19,8] | 169→7 | 20,306+58,418 (5) | 65,536 / 0 → none | n=2k only | 20 → 7 |
| 4[20,9] | 40→7 | 4,623+13,165 (4) | 262,144 / 27 → 6 | n=2k only | 0 |
| 4[22,6] | 200→11 | 484,957+871,450 (6) | 4,096 / 6 → 10 | n=2k only | 299 → 11 |
| 4[23,7] | 200→10 | 133,245+215,471 (6) | 16,384 / 0 → none | n=2k only | 24 → 11 |
| 4[24,8] | 179→10 | 27,351+36,179 (5) | 65,536 / 45 → 6 | n=2k only | 0 |
| 5[16,5] | 200→8 | 821,863+795,984 (6) | 3,125 / 20 → 6 | n=2k only | 17 → 9 |
| 5[16,6] | 200→7 | 191,915+218,065 (6) | 15,625 / 24 → 4 | n=2k only | 34 → 8 |
| 5[17,6] | 200→8 | 195,904+177,863 (6) | 15,625 / 0 → none | n=2k only | 1 → 9 |
| 5[17,7] | 200→7 | 33,498+61,954 (5) | 78,125 / 0 → none | n=2k only | 0 |
| 5[18,9] | 9→6 | 969+2,135 (5) | skipped: 5^9=1,953,125 > budget 600,000 | 51 samples→7 | 0 |

Full machine-readable record (per-restart stats, all 791 phase-2 records,
best generators, gfq outputs): `results.json`.

## Reproduction (exact commands)

```sh
# from the repo root, on top of agent/wave1-gfq-checker
python3 -m unittest discover -s tests            # 24 tests, OK (no pytest on this machine)

# census regeneration as actually run (direct urllib failed, see below):
mkdir -p /tmp/codetables_pages
for spec in "2 256" "3 243" "4 256" "5 130" "7 100" "8 130" "9 130"; do
  set -- $spec
  curl -sL --max-time 240 -A "foundation0-census" \
    "https://www.codetables.de/BKLC/Tables_color.php?q=$1&n0=1&n1=$2&k0=1&k1=$2" \
    -o /tmp/codetables_pages/q$1.html
done
cd /tmp && python3 /path/to/math0/data/codetables/census.py \
  --from-dir /tmp/codetables_pages --csv /tmp/entries.csv   # csv NOT committed

# the search (pass 1: 7m55s wall; pass 2: 11m38s wall, this machine)
python3 results/codetables/search.py --seconds 25 --seed 20261018
python3 results/codetables/search.py --second-pass --seconds 45 --seed 777001

# re-verify any certificate, e.g.:
python3 -m gfq --q 5 --json results/codetables/best/q5_n16_k5_d9.txt
python3 -m gfq --q 3 examples/golay11.txt        # checker sanity: [11,6,5]
```

Randomness: both passes are seeded, but wall-clock budgets make step
counts machine-dependent; re-runs should reproduce the *conclusions*
(best d per target), not bit-identical matrices.

## What was NOT done

- No upper-bound work (LP/Delsarte, etc.): this track attacked lower
  bounds by construction only. Failure to find `d=lb+1` says nothing
  about whether such codes exist.
- Quasi-cyclic search beyond double-circulant (n=2k) random sampling and
  the exhaustive cyclic/constacyclic sweep: no general QC index-3/4 or
  quasi-twisted search (AREAS.md's suggestion), no BCH/algebraic-geometry
  constructions, no ILP/SAT-based column search.
- Cyclic sweep skipped for GF(5)[18,9] (budget above); its anneal coverage
  is also the thinnest (spectrum of 488,281 messages ⇒ ~35 ms/step).
- GF(7)/GF(8)/GF(9) entries, larger n/k, and "constructions missing"
  entries were out of scope for this run.
- No contact with the table maintainer (nothing to submit).

## Failed attempts / deviations

- `python3 census.py` live mode failed on this machine
  (`SSL: CERTIFICATE_VERIFY_FAILED` in urllib). Workaround: fetch the same
  URLs with curl and run `census.py --from-dir` (commands above). The
  regenerated counts are identical to the committed snapshot, so target
  values are unaffected.
- First cyclic design enumerated generator polynomials directly
  (`q^(n−k)` candidates, infeasible for every target). Replaced by the
  check-polynomial enumeration (`q^k`), validated on the Golay parameters
  before use.
- The annealer did not even reach the table lower bound on 5 targets
  (GF(3)[24,9], GF(3)[24,10], GF(4)[20,9], GF(4)[23,7], GF(4)[24,8]) in
  either pass; on those, coverage is weaker than on the 10 where it
  matched lb from multiple restarts. CONJECTURE (unlabelled, not claimed):
  none — we draw no conclusion about optimality from this.
