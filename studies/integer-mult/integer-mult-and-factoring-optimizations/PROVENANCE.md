# Provenance and status: integer-mult-and-factoring-optimizations

**Status: claimed, pending review.** No maintainer of math0, CrocSwap/integer-mult-bounds or
1337isnot1337/integer-factoring has reviewed these files, and nothing has been submitted upstream.

## What it is

Two small exact-arithmetic studies, as received:

- `integer-mult-bounds/`: five 3-query dyadic cubic-repair witnesses at odd-S arities r = 14, 18, 55, 71, 82 for
  [CrocSwap/integer-mult-bounds](https://github.com/CrocSwap/integer-mult-bounds), with a Python verifier, its JSON
  output and a C++ search tool.
- `integer-factoring/`: a tighter divisor-count exponent bound `q_**(n)` for
  [1337isnot1337/integer-factoring](https://github.com/1337isnot1337/integer-factoring), with a Python script and its
  JSON benchmarks.

The README and every other file except this one are unchanged.

## Source

| Item | Value |
|---|---|
| Drive file | `2026-11-13_integer-mult-and-factoring-optimizations.zip`, id `1iokcshlFzw-CfJ3l2jo0jYnn0Adv1Em_` |
| Drive created and modified | 2026-11-13T21:47:08Z |
| Zip size and SHA-256 | 10,799 bytes, `67403d27494245b4f6dcdf5b210cd1a311223215ece0232155689c0753489db7` |
| Inner manifest | `SHA256SUMS` from the zip; `sha256sum -c SHA256SUMS` passes on all 6 listed files |
| Author | An AI agent working for Ahraz Arifuddin (Aska Digital), per the Drive owner |

## What was run

On Linux x86_64, Python 3.13.5, 14 November 2026, from each subfolder:

| Command | Result |
|---|---|
| `python3 -B odd_s_general_frame_breakthroughs.py` | exit 0, about 14 s; output byte-identical to `odd_s_cubic_witnesses.json` |
| `python3 -B -m unittest odd_s_general_frame_breakthroughs` | 1 test, OK (14.2 s) |
| `python3 -B ramanujan_shell_divisor_bound.py` | exit 0; output byte-identical to `ramanujan_shell_benchmarks.json` |
| `python3 -B -m unittest ramanujan_shell_divisor_bound` | 2 tests, OK (0.12 s) |
| `odd_s_general_frame_search.cpp` | not compiled: this machine has no C++ compiler |

The divisor-bound unit tests compare the bound with an exact divisor sieve for every N below 2^18 and with primorial
and colossally abundant candidates.

## Claims that are not yet checked

- **"Refutes the odd-S non-monic impossibility conjecture."** The script checks that each of the five row triples
  solves the cubic-repair equations exactly and that monic frames fail at those arities by a finite odd-divisor
  search. Whether that search covers every monic frame, and whose conjecture this answers, needs a reader. The
  related upstream pull requests (#6653 merged; #7475, #7479 and #7506 open as of 14 November 2026) have not been
  compared with these witnesses.
- **"Strictly new" arities.** Not checked against the upstream catalogue or the open pull requests.
- **The divisor-count bound for all N below 2^n.** The tests cover n up to 18 exhaustively. The 29.4% to 59.3%
  reductions up to n = 65536 come from the script's own formula and are as strong as its proof, which is a docstring
  sketch.
- **A missing file.** The README asks to "also copy" `fast_cubic_unlock.cpp`; the zip has
  `odd_s_general_frame_search.cpp` instead, and no file of the first name.
- **Both scripts check with `assert`** (9 and 5 statements), so `python3 -O` skips those checks.

## Next steps

Compile and run the C++ search, compare the five witnesses with CrocSwap #7475, #7479 and #7506, and ask each
upstream maintainer before opening a pull request there.
