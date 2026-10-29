/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A265649: two closed forms for the triangle `T(n,k) = T(n-1,k-1) + (2n-1+k) T(n-1,k)`

Source: https://oeis.org/A265649, _Werner Schulte_, Dec 11 2015 (FORMULA section). Verbatim:
> Conjecture: T(n,k) = 2^(n-k)*(n-k)!*binomial(n,k)*(Sum_{j=0..n-k} (-1/4)^j*
> binomial(2*j+k,j)*binomial(n,j+k)).
> Conjecture: T(n,k) = (-1)^k*Sum_{j=0..n-1} A001497(n-1,j)*A021009(j+1,k).

The entry (_Werner Schulte_, Dec 11 2015, offset `0`, keyword `tabl`) is "Triangle of
coefficients T(n,k) of polynomials p(n,x) = Sum_{k=0..n} T(n,k)*x^k where T(0,0) = 1, and
T(n,k) = 0 for k < 0 or k > n, and T(n,k) = T(n-1,k-1) + (2*n-1+k)*T(n-1,k) for n > 0 and
0 <= k <= n."

## Encoding

* *The triangle.* `T : ℕ → ℕ → ℕ` is defined by the recurrence of the entry's name, written for
  row `n + 1`: `T(0,0) = 1`, `T(0,k) = 0` for `k ≥ 1`, `T(n+1,0) = (2(n+1)-1+0)·T(n,0)` (the term
  `T(n,-1)` is `0`), and `T(n+1,k+1) = T(n,k) + (2(n+1)-1+(k+1))·T(n,k+1)`. The definition
  applies the recurrence also for `k + 1 > n + 1`; `T_eq_zero_of_lt` proves that this gives
  `T(n,k) = 0` for all `k > n`, as the entry requires, so `T` is exactly the entry's triangle
  (extended by `0` outside `0 ≤ k ≤ n`).
* *The sequence.* `a m` is the `m`-th term (offset `0`) of the triangle read by rows.
  `a_data` checks all 55 listed terms (rows `n = 0, …, 9`) in the kernel; `T_data` checks the
  same terms row by row.
* *The referenced triangles.* `A001497 m j` is the Bessel-polynomial triangle, through its
  closed form from that entry, `a(n,m) = (2n-m)!/(m!(n-m)!2^(n-m))` for `n ≥ m ≥ 0`, else `0`;
  `A021009 m k` is the (signed) Laguerre triangle `n!·L_n(x)`, through the closed form from that
  entry, `a(n,m) = (-1)^m·n!·binomial(n,m)/m!` for `n ≥ m`, else `0`. Both are computed in `ℚ`
  (so no exactness of a natural-number division is assumed); `A001497_data` and
  `A021009_data` check them against all terms listed in those entries.
* *Conjecture 1* (`statement₁`): for every entry of the triangle (`n ≥ 0`, `0 ≤ k ≤ n`),
  `T(n,k) = 2^(n-k)·(n-k)!·C(n,k)·∑_{j=0}^{n-k} (-1/4)^j·C(2j+k,j)·C(n,j+k)`, an identity in `ℚ`
  (`n - k` is a genuine difference since `k ≤ n`).
* *Conjecture 2* (`statement₂`): for every `n ≥ 1` and `0 ≤ k ≤ n`,
  `T(n,k) = (-1)^k·∑_{j=0}^{n-1} A001497(n-1,j)·A021009(j+1,k)`, an identity in `ℚ`. The range
  `n ≥ 1` is forced by the formula: `A001497` has offset `0`, so `A001497(n-1,j)` only exists for
  `n ≥ 1` (and for `n = 0` the sum would be empty). The terms with `j + 1 < k` vanish since then
  `A021009(j+1,k) = 0`.
* *Reading choices.* Both conjectures are read on the entries of the triangle (`0 ≤ k ≤ n`);
  for `k > n` both sides would be `0` anyway (`C(n,k) = 0`, resp. `A021009(j+1,k) = 0`).
  `statement` is the conjunction of the two conjectures. `statement₁_check` and
  `statement₂_check` verify them for `n ≤ 12` in the kernel (a sanity check of the transcription,
  not a proof).
-/

namespace Math0.Statements.A265649

/-- A265649 as a triangle: `T(0,0) = 1`, `T(0,k) = 0` for `k > 0`, and for `n ≥ 0`
`T(n+1,k) = T(n,k-1) + (2(n+1)-1+k)·T(n,k)` (with `T(n,-1) = 0`). -/
def T : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => (2 * (n + 1) - 1 + 0) * T n 0
  | n + 1, k + 1 => T n k + (2 * (n + 1) - 1 + (k + 1)) * T n (k + 1)

/-- `T(n,k) = 0` for `k > n`, as in the entry. -/
theorem T_eq_zero_of_lt {n k : ℕ} (h : n < k) : T n k = 0 := by
  induction n generalizing k with
  | zero =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rfl
  | succ n ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [T, ih (by omega), ih (by omega), zero_add, mul_zero]

/-- The recurrence of the entry, for `n > 0` and `1 ≤ k ≤ n`
(`T(n,k) = T(n-1,k-1) + (2n-1+k)·T(n-1,k)`), written with `n + 1`, `k + 1`. -/
theorem T_succ_succ (n k : ℕ) :
    T (n + 1) (k + 1) = T n k + (2 * (n + 1) - 1 + (k + 1)) * T n (k + 1) := by
  rw [T]

/-- A265649 read by rows (offset `0`): the `m`-th term is `T(n,k)` for the `m`-th pair `(n,k)`,
`0 ≤ k ≤ n`, in the order `(0,0), (1,0), (1,1), (2,0), …`. -/
def a (m : ℕ) : ℕ :=
  let p := ((List.range (m + 1)).flatMap fun n => (List.range (n + 1)).map fun k => (n, k)).getD
    m (0, 0)
  T p.1 p.2

/-- The definition reproduces all 55 terms listed in OEIS (rows `0, …, 9`; kernel-checked). -/
theorem a_data : (List.range 55).map (fun i => a (i + 0)) =
    [1, 1, 1, 3, 5, 1, 15, 33, 12, 1, 105, 279, 141, 22, 1, 945, 2895, 1830, 405, 35, 1, 10395,
      35685, 26685, 7500, 930, 51, 1, 135135, 509985, 435960, 146685, 23310, 1848, 70, 1,
      2027025, 8294895, 7921305, 3076290, 589575, 60270, 3318, 92, 1, 34459425, 151335135,
      158799690, 69447105, 15457365, 1915515, 136584, 5526, 117, 1] := by
  decide +kernel

/-- The same 55 listed terms, read off `T` row by row (kernel-checked). -/
theorem T_data : (List.range 10).flatMap (fun n => (List.range (n + 1)).map (fun k => T n k)) =
    [1, 1, 1, 3, 5, 1, 15, 33, 12, 1, 105, 279, 141, 22, 1, 945, 2895, 1830, 405, 35, 1, 10395,
      35685, 26685, 7500, 930, 51, 1, 135135, 509985, 435960, 146685, 23310, 1848, 70, 1,
      2027025, 8294895, 7921305, 3076290, 589575, 60270, 3318, 92, 1, 34459425, 151335135,
      158799690, 69447105, 15457365, 1915515, 136584, 5526, 117, 1] := by
  decide +kernel

/-! ### The referenced triangles A001497 and A021009 -/

/-- A001497 (coefficients of the Bessel polynomials): `a(n,m) = (2n-m)!/(m!(n-m)!2^(n-m))` for
`n ≥ m ≥ 0`, else `0`. -/
def A001497 (n m : ℕ) : ℚ :=
  if m ≤ n then
    ((2 * n - m).factorial : ℚ) / ((m.factorial : ℚ) * ((n - m).factorial : ℚ) * 2 ^ (n - m))
  else 0

/-- A021009 (coefficients of `n!·L_n(x)`, rising powers of `x`):
`a(n,m) = (-1)^m·n!·binomial(n,m)/m!` for `n ≥ m`, else `0`. -/
def A021009 (n m : ℕ) : ℚ :=
  if m ≤ n then
    (-1) ^ m * (n.factorial : ℚ) * (n.choose m : ℚ) / (m.factorial : ℚ)
  else 0

/-- `A001497` reproduces all 55 terms listed in that entry (rows `0, …, 9`; kernel-checked). -/
theorem A001497_data :
    (List.range 10).flatMap (fun n => (List.range (n + 1)).map (fun m => A001497 n m)) =
    [1, 1, 1, 3, 3, 1, 15, 15, 6, 1, 105, 105, 45, 10, 1, 945, 945, 420, 105, 15, 1, 10395,
      10395, 4725, 1260, 210, 21, 1, 135135, 135135, 62370, 17325, 3150, 378, 28, 1,
      2027025, 2027025, 945945, 270270, 51975, 6930, 630, 36, 1, 34459425, 34459425, 16216200,
      4729725, 945945, 135135, 13860, 990, 45, 1] := by
  decide +kernel

/-- `A021009` reproduces all 47 terms listed in that entry (rows `0, …, 8` and the first two
terms of row `9`; kernel-checked). -/
theorem A021009_data :
    (List.range 9).flatMap (fun n => (List.range (n + 1)).map (fun m => A021009 n m)) ++
      [A021009 9 0, A021009 9 1] =
    [1, 1, -1, 2, -4, 1, 6, -18, 9, -1, 24, -96, 72, -16, 1, 120, -600, 600, -200, 25, -1, 720,
      -4320, 5400, -2400, 450, -36, 1, 5040, -35280, 52920, -29400, 7350, -882, 49, -1,
      40320, -322560, 564480, -376320, 117600, -18816, 1568, -64, 1, 362880, -3265920] := by
  decide +kernel

/-! ### The conjectures -/

/-- The right-hand side of the first conjecture:
`2^(n-k)·(n-k)!·C(n,k)·∑_{j=0}^{n-k} (-1/4)^j·C(2j+k,j)·C(n,j+k)`. -/
def rhs₁ (n k : ℕ) : ℚ :=
  2 ^ (n - k) * ((n - k).factorial : ℚ) * (n.choose k : ℚ) *
    ∑ j ∈ Finset.range (n - k + 1),
      (-1 / 4 : ℚ) ^ j * ((2 * j + k).choose j : ℚ) * (n.choose (j + k) : ℚ)

/-- The right-hand side of the second conjecture:
`(-1)^k·∑_{j=0}^{n-1} A001497(n-1,j)·A021009(j+1,k)`. -/
def rhs₂ (n k : ℕ) : ℚ :=
  (-1) ^ k * ∑ j ∈ Finset.range n, A001497 (n - 1) j * A021009 (j + 1) k

/-- First conjecture (Werner Schulte, A265649): for all `0 ≤ k ≤ n`,
`T(n,k) = 2^(n-k)·(n-k)!·C(n,k)·∑_{j=0}^{n-k} (-1/4)^j·C(2j+k,j)·C(n,j+k)`. -/
def statement₁ : Prop :=
  ∀ n k : ℕ, k ≤ n → (T n k : ℚ) = rhs₁ n k

/-- Second conjecture (Werner Schulte, A265649): for all `n ≥ 1` and `0 ≤ k ≤ n`,
`T(n,k) = (-1)^k·∑_{j=0}^{n-1} A001497(n-1,j)·A021009(j+1,k)`. -/
def statement₂ : Prop :=
  ∀ n k : ℕ, 1 ≤ n → k ≤ n → (T n k : ℚ) = rhs₂ n k

/-- Sanity check of the first conjecture for `n ≤ 12` (kernel-checked; not a proof). -/
theorem statement₁_check :
    (List.range 13).all (fun n => (List.range (n + 1)).all
      (fun k => decide ((T n k : ℚ) = rhs₁ n k))) = true := by
  decide +kernel

/-- Sanity check of the second conjecture for `1 ≤ n ≤ 12` (kernel-checked; not a proof). -/
theorem statement₂_check :
    (List.range 12).all (fun i => (List.range (i + 2)).all
      (fun k => decide ((T (i + 1) k : ℚ) = rhs₂ (i + 1) k))) = true := by
  decide +kernel

/-- Both conjectures of Werner Schulte (A265649, Dec 11 2015): for all `0 ≤ k ≤ n`,
`T(n,k) = 2^(n-k)·(n-k)!·C(n,k)·∑_{j=0}^{n-k} (-1/4)^j·C(2j+k,j)·C(n,j+k)`, and for all
`n ≥ 1`, `0 ≤ k ≤ n`, `T(n,k) = (-1)^k·∑_{j=0}^{n-1} A001497(n-1,j)·A021009(j+1,k)`. -/
def statement : Prop :=
  (∀ n k : ℕ, k ≤ n →
      (T n k : ℚ) = 2 ^ (n - k) * ((n - k).factorial : ℚ) * (n.choose k : ℚ) *
        ∑ j ∈ Finset.range (n - k + 1),
          (-1 / 4 : ℚ) ^ j * ((2 * j + k).choose j : ℚ) * (n.choose (j + k) : ℚ)) ∧
    (∀ n k : ℕ, 1 ≤ n → k ≤ n →
      (T n k : ℚ) = (-1) ^ k * ∑ j ∈ Finset.range n, A001497 (n - 1) j * A021009 (j + 1) k)

/-- `statement` is the conjunction of the two conjectures. -/
theorem statement_iff : statement ↔ statement₁ ∧ statement₂ := Iff.rfl

end Math0.Statements.A265649
