# `research/conservation-quotient-bounds` — Base-Mathematics Unification & Exact Checkers

Scoped research and formal-certificate package for [`CrocSwap/integer-mult-bounds`](https://github.com/CrocSwap/integer-mult-bounds) (`main` at `e545235`, Priority Revision 8, Selected Frontier [`#7000`](https://github.com/CrocSwap/integer-mult-bounds/blob/main/certificates/selected-result.json)).

## Scope & Summary of Results

1. **Search-Free Cut-Rank & Picard–Queyranne Lattice Checker (`Theorem 1`)**: Certifies $\operatorname{rank}_{\mathbb{F}}(M) \le c(U, \bar{U})$ via explicit factorization $M = A_{\bar{U}} B_U$, canonical source-minimal / sink-minimal cut lattice $[U_{\min}, U_{\max}]$, and $O(|V| + |E|)$ edge-deletion BFS without trusting max-flow solvers.
2. **Indefinite Reverse-Frame & Closed-Form `Helper300` Post-Decoder (`Theorems 2A & 2B`)**: Certifies Gram nondegeneracy $\det(B^T H B) \neq 0$ and reverse complement nesting $U_w^{\perp_H} \subseteq U_z^{\perp_H}$ on indefinite forms ([`docs/research/cross-point-sharing.md`](https://github.com/CrocSwap/integer-mult-bounds/blob/main/docs/research/cross-point-sharing.md)), exhibits an explicit isotropic counterexample, and derives an unconditional closed-form $\mathbb{Z}[\frac{1}{4}]$ left-inverse decoder $L \begin{bmatrix} P_{\text{persist}} \\ C_{\text{cache}} \end{bmatrix} = I$ closing the 8-field persistent kernel in [Discussion `#5470`](https://github.com/CrocSwap/integer-mult-bounds/discussions/5470).
3. **Zero-Float Power-Sum Enclosures, Karamata Pruning Rule, & Farkas Ceiling (`Theorems 3A & 3B`)**: Encloses $(r/m)^{1-a}$ in pure `fractions.Fraction` arithmetic (`< 10^-32` width), reproduces all 18 published digits of `PR #450`, `Aska PR #464`, and `Aska PR #469` ([`fdn0.org/research/integer-multiplication/`](https://fdn0.org/research/integer-multiplication/)), proves that the `(-99, +198, -99)` sub-move on `$\{5, 6, 7\}$` in `PR #469` paid a strict Jensen concavity penalty (`6^12 < 5^5 * 7^7`), and certifies an exact rational Farkas dual ceiling (`0.001467442448`).
4. **Triple Independent Verification + Core Lean 4 Module**: Checked by `check_certificate.py` (pure `fractions.Fraction`), `c11_base_verifier.c` (`gcc -std=c11 -O2 -Wall -Wextra -Werror` `__int128`), 18 re-hashed semantic tamper controls in `verify.py`, and `formal/BaseMathConvergence.lean` (zero-`sorry` Core Lean 4, audited by a 12-vector surface scanner).

No new selected global $\kappa$ above Frontier `#7000` (`363005817/100000000000`) or complete Lean multiplication-machine proof is claimed.

## Reproduction

Run with assertions enabled (`-O` and nonzero `PYTHONOPTIMIZE` are rejected fail-closed per [`CONTRIBUTING.md`](https://github.com/CrocSwap/integer-mult-bounds/blob/main/CONTRIBUTING.md)):

```bash
python3 -W error -B research/conservation-quotient-bounds/verify.py --check
python3 -W error -B -m unittest discover -s research/conservation-quotient-bounds/tests -p 'test_*.py' -v
```

*Unrun environment note*: `formal/BaseMathConvergence.lean` uses Core Lean 4 (`Int`/`Nat`/`List`) with zero `sorry` or `axiom` declarations; `lake env lean` was not executed in the build container because `lean` was not installed there.

## Open next questions

1. **Frontier `#7000` Retiming Scan for Mean-Preserving Contractions**: Audit the `117,612` paid calls across the `3,057`-map native catalogue in Frontier `#7000` for any zero-count-change, mass-preserving contractions $(r-\delta, r+\delta) \to (r, r)$ that can be reversed into spreads without violating frame nesting.
2. **Binding Closed-Form Decoder $L$ to Selected `#5413`/`#7000` Paid Repair Invoices**: Instantiate $L = \begin{bmatrix} I & I - \frac{1}{4} M M^T & 0 & -\frac{1}{4} M \\ 0 & I & 0 & 0 \\ 0 & B^T M^T & I_m & B^T \end{bmatrix}$ directly against the emitted `Helper300` suffix word and price the exact adapter/restoration bill.
3. **Kernel-Checking `BaseMathConvergence.lean` in CI**: Bind `formal/BaseMathConvergence.lean` into `formal/` under the pinned Lean toolchain and connect rational interval bounds via `Rat`.

## Attribution & License

Builds on [`CrocSwap/integer-mult-bounds`](https://github.com/CrocSwap/integer-mult-bounds) maintained by Douglas Colkitt (`@Mister-Meeseeks`), OpenAI's #109 framework (`openai/math @ adc7f12`), Jerry Chen / `@CubeJerry` (`#7000`/`#7001`), DreamingOfClouds (`#450`), `@apoursh` and `@JoyboyBrian` ([Discussion `#5470`](https://github.com/CrocSwap/integer-mult-bounds/discussions/5470)), Ali Romman ([Discussion `#6458`](https://github.com/CrocSwap/integer-mult-bounds/discussions/6458)), and cross-repository mathematical synthesis from [`ahrazzle/soko`](https://github.com/ahrazzle/soko), [`Moissanite-Labs/weft`](https://github.com/Moissanite-Labs/weft), and [`Foundation-0/project-asma`](https://github.com/Foundation-0/project-asma) by Ahraz Arifuddin (`@ahrazzle` / Aska Digital) with Gemini automated mathematical synthesis. Licensed under Apache-2.0.
