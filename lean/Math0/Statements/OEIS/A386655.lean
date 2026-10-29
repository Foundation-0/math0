/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A386655: residues mod 6 of the e.g.f. coefficients of `∑ (2^n x + LambertW(x))^n / n!`

Source: https://oeis.org/A386655, _Paul D. Hanna_, Aug 23 2025. Verbatim:
> Conjecture: for n >= 6, a(n) (mod 6) equals [1, 0, 3, 0, 3, 2] repeating.

The entry's definition (offset 0): "E.g.f.: Sum_{n>=0} (2^n*x + LambertW(x))^n / n!", i.e.
`a(n) = n! [x^n] ∑_{m ≥ 0} (2^m x + W(x))^m / m!`, where `W(x) = LambertW(x)` is the power
series with `W(0) = 0` and `W(x) e^{W(x)} = x`.

## Encoding

* `a n` is the explicit formula listed in the entry (formula section; the first PARI program
  is this formula):
  `a(n) = Sum_{k=0..n} binomial(n,k) * 2^(k*(k+1)) * (2^k - (n-k))^(n-k-1)`.
  For `k = n` the exponent is `-1` and the summand is `2^(n(n+1)) * (2^n)^(-1) = 2^(n^2)`
  (as PARI evaluates it); `term n n` is this value `2^(n*n)`. For `k < n` the exponent
  `n-k-1` is a natural number, the base `2^k - (n-k)` is an integer that may be negative, and
  `0^0 = 1` (the case `n = 1`, `k = 0`), again as in PARI. So `a : ℕ → ℤ`; the sequence is
  nonnegative (keyword `nonn`), and the conjecture is read with the residue `a n % 6` in
  `{0, …, 5}` (`Int.emod`).
* The formula follows from the e.g.f. via `(2^m x + W)^m/m! = ∑_j 2^(m j) x^j/j! · W^(m-j)/(m-j)!`
  (giving the entry's form `∑_j 2^(j^2) e^{2^j W} x^j/j!`) and the classical expansion
  `e^{c W(x)} = ∑_k c (c-k)^(k-1) x^k/k!`; it is not a conjectured formula. This equivalence
  is not proved in Lean here (Mathlib has neither the Lambert `W` series nor Lagrange
  inversion). Instead, the definition is cross-checked in the kernel against a direct, literal
  evaluation of the e.g.f. (`egf`): `W` is obtained from its defining equation
  `W = x e^{-W}` by fixed-point iteration (`lambertW`, with `lambertW_spec` checking
  `W e^W = x`), and `∑_m (2^m x + W)^m/m!` is evaluated with truncated e.g.f. arithmetic over
  `ℤ` (coefficient lists of `x^i/i!`; `F^m/m!` is computed as `((F^(m-1)/(m-1)!) · F) / m`,
  where every division is exact since `F` has zero constant term). Only `m ≤ N` contributes to
  the coefficients of `x^0, …, x^N`, because `2^m x + W = O(x)`. `a_eq_egf` checks
  `a n = egf` coefficient for `n = 0..16`, beyond the 13 listed terms.
* `a_data` checks all 13 terms listed in the entry (`n = 0..12`).
* The conjecture: for every `n ≥ 6`, `a(n) mod 6` is the `((n - 6) mod 6)`-th entry
  (0-based) of `[1, 0, 3, 0, 3, 2]`, i.e. `a(6) ≡ 1`, `a(7) ≡ 0`, `a(8) ≡ 3`, `a(9) ≡ 0`,
  `a(10) ≡ 3`, `a(11) ≡ 2`, `a(12) ≡ 1`, … (mod 6). `statement_data` confirms this reading
  agrees with the listed terms `n = 6..12`.
-/

namespace Math0.Statements.A386655

/-! ### The explicit formula -/

/-- Binomial coefficient via descending factorials (fast in the kernel); equals `Nat.choose`. -/
def binom (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

theorem binom_eq_choose (n k : ℕ) : binom n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm

/-- The `k`-th summand `binomial(n,k) * 2^(k*(k+1)) * (2^k - (n-k))^(n-k-1)` of the explicit
formula; for `k = n` (exponent `-1`) it is `2^(n(n+1)) / 2^n = 2^(n^2)`. -/
def term (n k : ℕ) : ℤ :=
  if k = n then 2 ^ (n * n)
  else (binom n k : ℤ) * 2 ^ (k * (k + 1)) * ((2 : ℤ) ^ k - ((n - k : ℕ) : ℤ)) ^ (n - k - 1)

/-- A386655: `a n = n! [x^n] ∑_{m ≥ 0} (2^m x + LambertW(x))^m / m!`, given by the entry's
explicit formula `a(n) = ∑_{k=0..n} binomial(n,k) 2^(k(k+1)) (2^k - (n-k))^(n-k-1)`. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), term n k

/-- The definition reproduces the first terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 13).map (fun i => a (i + 0)) =
    [1, 3, 23, 708, 82677, 39043808, 75384175459, 594418947869568, 19030890530555146281,
      2460681168464503636482816, 1280084112577610436036966382815,
      2672769582069469500760580570122074560,
      22366167041278673568399013569832022272725469] := by
  decide +kernel

/-! ### Cross-check: direct evaluation of the e.g.f. -/

/-- A truncated e.g.f. is a list `f` standing for `∑_i f[i] x^i / i!`; `coef f i = f[i]`. -/
def coef (f : List ℤ) (i : ℕ) : ℤ := f.getD i 0

/-- Sum of e.g.f.s, truncated after `x^N`. -/
def eadd (N : ℕ) (f g : List ℤ) : List ℤ :=
  (List.range (N + 1)).map fun n => coef f n + coef g n

/-- Product of e.g.f.s, truncated after `x^N`: `(f g)_n = ∑_k C(n,k) f_k g_(n-k)`. -/
def emul (N : ℕ) (f g : List ℤ) : List ℤ :=
  (List.range (N + 1)).map fun n =>
    ((List.range (n + 1)).map fun k => (binom n k : ℤ) * coef f k * coef g (n - k)).sum

/-- `x · f`, truncated after `x^N`: `(x f)_n = n f_(n-1)`. -/
def xmul (N : ℕ) (f : List ℤ) : List ℤ :=
  (List.range (N + 1)).map fun (n : ℕ) => (n : ℤ) * coef f (n - 1)

/-- The e.g.f. `1`, truncated after `x^N`. -/
def eone (N : ℕ) : List ℤ := 1 :: List.replicate N 0

/-- `F^m / m!`, truncated after `x^N`, for `F` with zero constant term (the division by `m`
is exact, as `F^m/m!` has integral e.g.f. coefficients). -/
def powDivFact (N : ℕ) (F : List ℤ) : ℕ → List ℤ
  | 0 => eone N
  | m + 1 => (emul N (powDivFact N F m) F).map (· / ((m + 1 : ℕ) : ℤ))

/-- The pair `(F^j/j!, ∑_{i ≤ j} F^i/i!)`, truncated after `x^N`. -/
def expAux (N : ℕ) (F : List ℤ) : ℕ → List ℤ × List ℤ
  | 0 => (eone N, eone N)
  | j + 1 =>
    let p := expAux N F j
    let q := (emul N p.1 F).map (· / ((j + 1 : ℕ) : ℤ))
    (q, eadd N p.2 q)

/-- `exp F = ∑_{j ≤ N} F^j/j!`, truncated after `x^N`, for `F` with zero constant term. -/
def eexp (N : ℕ) (F : List ℤ) : List ℤ := (expAux N F N).2

/-- Fixed-point iteration `W ↦ x e^{-W}` from `W = 0`; after `i` steps the coefficients of
`x^0, …, x^(i-1)` agree with those of `LambertW(x)`. -/
def lambertWIter (N : ℕ) : ℕ → List ℤ
  | 0 => List.replicate (N + 1) 0
  | i + 1 => xmul N (eexp N ((lambertWIter N i).map (- ·)))

/-- `LambertW(x)`, the solution of `W = x e^{-W}` (i.e. `W e^W = x`), truncated after `x^N`. -/
def lambertW (N : ℕ) : List ℤ := lambertWIter N (N + 1)

/-- `n! [x^n] ∑_{m ≥ 0} (2^m x + LambertW(x))^m / m!` for `n = 0..N` (only `m ≤ N`
contributes). -/
def egf (N : ℕ) : List ℤ :=
  (List.range (N + 1)).foldl
    (fun acc m => eadd N acc (powDivFact N (eadd N (lambertW N) [0, 2 ^ m]) m))
    (List.replicate (N + 1) 0)

/-- Sanity check of `lambertW`: `W e^W = x` up to `x^16`, and its first coefficients are
`(-k)^(k-1)` as in the entry's example. -/
theorem lambertW_spec :
    emul 16 (lambertW 16) (eexp 16 (lambertW 16)) = eadd 16 [] [0, 1] ∧
      (lambertW 16).take 8 = [0, 1, -2, 9, -64, 625, -7776, 117649] := by
  decide +kernel

/-- The explicit formula agrees with the direct evaluation of the e.g.f. for `n = 0..16`. -/
theorem a_eq_egf : (List.range 17).map a = egf 16 := by
  decide +kernel

/-- Hanna's conjecture (A386655): for `n ≥ 6`, `a(n) mod 6` runs through `[1, 0, 3, 0, 3, 2]`
periodically, starting with `1` at `n = 6`. -/
def statement : Prop :=
  ∀ n : ℕ, 6 ≤ n → a n % 6 = ([1, 0, 3, 0, 3, 2] : List ℤ).getD ((n - 6) % 6) 0

/-- The reading of `statement` agrees with the listed terms `n = 6..12` (not a proof). -/
theorem statement_data :
    ∀ n ∈ List.range' 6 7, a n % 6 = ([1, 0, 3, 0, 3, 2] : List ℤ).getD ((n - 6) % 6) 0 := by
  decide +kernel

end Math0.Statements.A386655
