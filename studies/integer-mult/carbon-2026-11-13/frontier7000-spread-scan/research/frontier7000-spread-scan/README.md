# `research/frontier7000-spread-scan` — Exact Mean-Preserving Contraction Audit of Frontier `#7000`

Scoped research and formal-certificate package for [`CrocSwap/integer-mult-bounds`](https://github.com/CrocSwap/integer-mult-bounds) auditing the exact `117,612` paid-call (`P`) and `23,392` productive-target (`T`) histograms of Selected Frontier `#7000` ([`FULL-RESULT.json`](https://github.com/CrocSwap/integer-mult-bounds/blob/main/research/shared-wire-split-composition/FULL-RESULT.json), [`CLAIM.json`](https://github.com/CrocSwap/integer-mult-bounds/blob/main/certificates/frontier7000/CLAIM.json)).

## Summary of Certified Results

- **Exact 30-Digit Root & 3-Stratum Decomposition**: Verifies `T` (`23,392` fields, mass `321,364`), `P` (`117,612` calls = `18 × 6,310` native `MOVE`s + `416` `QUERY` leaves + `3,616` `8Z`-locked whole-idles, mass `319,844`, surplus `S = 1,520`), and reproduces `gate.raw_bracket` (`0.00363005817468836708593357676489...`) in pure `fractions.Fraction` arithmetic.
- **Hotspot Identification (`99.07%` in `r ∈ {2, 3, 4, 5}`)**: Ranks all 12 legal symmetric spreads $(r, r) \to (r-d, r+d)$ inside the 9-slot native rank cap $r \le 8$:
  - Highest single-pair leverage: `(4, 4) -> (1, 7)` (`+3.9482e-7` per local pair) and `(5, 5) -> (2, 8)` (`+3.0033e-7` per local pair; uniquely immune to naive coalescing since $5 + 5 = 10 > 9$).
  - Highest total bucket headroom: `r = 3` (`811` local calls, `(3, 3) -> (1, 5)` giving `+9.4419e-5` symmetric or `+1.9418e-4` on `[1, 8]` balayage) and `r = 2` (`828` local calls).
- **BIT Ceiling Crossings**: Spreading `440` local pairs (`7920` global pairs) across `r ∈ {3, 4, 5}` lifts $\kappa$ to `0.003766795470`, crossing `complex_BIT_premise = 0.00376669`; full `[1, 8]` Bauer–Karamata balayage (`{1: 5645, 5: 1, 8: 664}`) bounds all count-and-mass-preserving native spreads at $\kappa_{\text{bal}} = 0.004141907509$ (`+14.10%`).
- **Physical Reversibility Gate**: Supplies exact `18 × 18` `GL_9(Z)` witnesses separating legal commuting-spectator flag re-pivoting (`(5, 5) -> (2, 8)`) from coupled-contact / mod-4 phase obstructions. No new selected global $\kappa$ is claimed prior to replay against `data/final.json.gz`.

## Reproduction

```bash
python3 -W error -B research/frontier7000-spread-scan/verify.py --check
python3 -W error -B -m unittest discover -s research/frontier7000-spread-scan/tests -p 'test_*.py' -v
```

## Open next questions

1. Parse the `71,261` native events in `research/shared-wire-split-composition/data/final.json.gz` to enumerate consecutive per-owner `MOVE` pairs in buckets `r ∈ {3, 4, 5}` whose intervening contacts commute on $d \ge 1$ quotient axes (`C S = S C`) and preserve mod-4 boundary phase polynomials.
2. Once legal native itineraries lift Complex saving past `complex_BIT_premise = 0.00376669`, pair with an updated BIT cover audit up to `admitted_BIT_saving = 0.00385248`.
3. Kernel-check `formal/Frontier7000SpreadBounds.lean` via `lake env lean` in CI.
