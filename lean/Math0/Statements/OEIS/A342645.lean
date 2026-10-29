/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A342645: diagonals of the eventual Mahonian-column polynomials

Source: https://oeis.org/A342645, _Peter Kagey_, Mar 17 2021 (COMMENTS and FORMULA sections).
Verbatim:
> Conjecture: For each m, T(n,n-m) is a polynomial of degree 2m whose leading coefficient is
> abs(A290030(m)/A053657(m+1)).

and
> Conjectures:
> T(n,n)   = 1.
> T(n,n-1) = (-3n + n^2)/2.
> T(n,n-2) = (-2n + 21n^2 - 22n^3 + 3n^4)/24.
> T(n,n-3) = (96n - 134n^2 + 13n^3 + 37n^4 - 13n^5 + n^6)/48.

The entry (offset `0`, keywords `sign,tabl`) is "Triangle read by rows: T(n,k) gives n! times
the coefficient of x^k in the polynomial that describes the number of permutations on x letters
with major index n", with the comment "This n-th row describes a polynomial that eventually
agrees with the n-th column of A008302."

## Encoding

* *Mahonian numbers.* `mahonianPoly x = ∏_{i=0}^{x-1} (1 + q + ⋯ + q^i) ∈ ℕ[q]` is the generating
  polynomial of row `x` of A008302 ("Triangle of Mahonian numbers T(n,k): coefficients in
  expansion of Product_{i=0..n-1} (1 + x + ... + x^i)"). `mahonian x n` computes its coefficient
  of `q^n` by a row recursion (multiply the previous row by `1 + q + ⋯ + q^x`), and
  `coeff_mahonianPoly` proves `(mahonianPoly x).coeff n = mahonian x n` for all `x, n`. By
  MacMahon's theorem this is the number of permutations of `x` letters with major index `n`;
  `mahonian_eq_majCount` checks this in the kernel against a literal count (`majCount`: the
  arrangements `List.permutations' [0, …, x-1]`, with major index `maj` = sum of the 1-based
  positions `i` with `w_i > w_{i+1}`) for all `x ≤ 6` and `n ≤ 15`.
* *The polynomial of column `n`.* For `x ≥ n` the number `mahonian x n` is a polynomial in `x`
  of degree `n`: modulo `q^(n+1)`, `∏_{i=1}^{x} (1 - q^i)` does not depend on `x` once `x ≥ n`,
  so `mahonian x n = [q^n] ∏_{i=1}^{x} (1 - q^i) / (1 - q)^x = ∑_{j ≤ n} e_j · C(x+n-j-1, n-j)`
  with `x`-independent `e_j` (this is Mike Earnest's MSE answer linked from the entry). So "the
  polynomial that describes" column `n` is the unique polynomial `P_n` of degree `≤ n` through
  the `n + 1` points `(x, mahonian x n)`, `x = n, …, 2n`. (The entry's Mathematica program
  interpolates the same column on `x = n, …, 2n+2`.) `Trow n` is the coefficient list of
  `n! · P_n`, computed in `ℤ` by Newton's forward-difference formula
  `n! · P_n(x) = ∑_{j=0}^{n} Δ^j · (n!/j!) · (x - n)(x - n - 1)⋯(x - n - j + 1)`,
  where `Δ^j` is the `j`-th forward difference of `x ↦ mahonian x n` at `x = n`
  (`column`, `diffHeads`, `fallingFrom`, `newton`). `T n k` is the coefficient of `x^k`.
  `rowPoly_agrees` checks in the kernel, for every `n ≤ 9`, that
  `∑_k T(n,k) x^k = n! · mahonian x n` for all `x = n, …, 3n+2`, i.e. also beyond the
  interpolation nodes.
* *Data.* `T_data` checks all 55 listed terms (rows `n = 0, …, 9`) row by row, and `a_data`
  checks them again for `a`, the triangle read by rows (the OEIS sequence itself, offset `0`).
* *A290030* is "Leading coefficients of numerators of Norlund's B_{nu}^(n) polynomials", with
  Mathematica program `NorlundB[n, x] // Together // Numerator // Coefficient[#, x, n]`. The
  Nørlund polynomial is `B_n^(x) = n! [t^n] (t/(e^t - 1))^x`. We compute
  `G = t/(e^t - 1)` as the reciprocal of `(e^t - 1)/t = ∑_k t^k/(k+1)!` (`bernG`), and then use the
  binomial series: with `H = G - 1` (no constant term), `[t^n] G^x = ∑_{j=0}^{n} C(x, j) [t^n] H^j`
  as polynomials in `x` (both sides are polynomials in `x` that agree at every natural number
  `x`, by the binomial theorem). So `norlund n`, the coefficient list of `B_n^(x)` in `x`, is
  `∑_{j=0}^{n} (n!/j!) · [t^n] H^j · x(x-1)⋯(x-j+1)`; `norlund_check` compares it in the kernel
  with `n! [t^n] G^x` computed by repeated multiplication, for `n ≤ 6`, `x ≤ 8`. Writing a
  polynomial with rational coefficients over the least common multiple `L` of their
  denominators (as `Together` does; `L · B_n^(x)` then has integer coefficients with no factor
  in common with `L`, so nothing cancels), its numerator is `L · B_n^(x)`, and A290030(n) is the
  coefficient of `x^n` there: `A290030 n = L · [x^n] B_n^(x)` (an integer, since the denominator
  of `[x^n] B_n^(x)` divides `L`). `A290030_data` checks the first 26 listed terms.
* *A053657* is defined by its name, `a(n) = Product_{p prime} p^{Sum_{k>=0}
  floor((n-1)/((p-1)p^k))}` (offset `1`); only primes `p ≤ n` and exponents `k < n` can
  contribute, since otherwise `(p-1)p^k > n - 1`. `A053657_data` checks all 19 listed terms.
* *The conjecture.* `statementDiagonals`: for every `m ≥ 0` there is `Q ∈ ℚ[X]` of degree exactly
  `2m` with leading coefficient `|A290030(m)/A053657(m+1)|` (computed in `ℚ`) such that
  `T(n, n-m) = Q(n)` for every `n ≥ m`, i.e. for every row in which `T(n, n-m)` is an entry of
  the triangle. (The weaker reading "for all sufficiently large `n`" is implied.)
  `statementFormulas`: the four FORMULA identities, each for all `n` with `T(n, n-m)` an entry
  (`n ≥ m` for `m = 0, 1, 2, 3`), with exact rational division. `statement` is the conjunction.
  `formulas_check` and `leading_check` are sanity checks of the transcription, not proofs: the
  four formulas hold for `n ≤ 12`, and `|A290030(m)/A053657(m+1)| = 1/(2^m m!)` for `m ≤ 9`,
  which matches the leading coefficients `1, 1/2, 3/24, 1/48` of the four formulas.
-/

namespace Math0.Statements.A342645

open Polynomial

/-! ### Mahonian numbers (A008302) -/

/-- The generating polynomial `∏_{i=0}^{x-1} (1 + q + ⋯ + q^i)` of row `x` of A008302. -/
noncomputable def mahonianPoly (x : ℕ) : ℕ[X] :=
  ∏ i ∈ Finset.range x, ∑ j ∈ Finset.range (i + 1), (X : ℕ[X]) ^ j

/-- Coefficientwise sum of two coefficient lists (lowest degree first). -/
def addN : List ℕ → List ℕ → List ℕ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addN p q

/-- Multiply a coefficient list by `1 + q + ⋯ + q^(m-1)`. -/
def mulOnes (m : ℕ) (r : List ℕ) : List ℕ :=
  r.foldr (fun a acc => addN (List.replicate m a) (0 :: acc)) []

/-- The coefficient list of `mahonianPoly x`. -/
def mahonianRow : ℕ → List ℕ
  | 0 => [1]
  | x + 1 => mulOnes (x + 1) (mahonianRow x)

/-- The Mahonian number A008302`(x, n)`: the number of permutations of `x` letters with major
index (equivalently, with inversion number) `n`. -/
def mahonian (x n : ℕ) : ℕ := (mahonianRow x).getD n 0

/-- The polynomial with coefficient list `l` (lowest degree first). -/
noncomputable def toPoly : List ℕ → ℕ[X]
  | [] => 0
  | a :: l => C a + X * toPoly l

theorem coeff_toPoly (l : List ℕ) (k : ℕ) : (toPoly l).coeff k = l.getD k 0 := by
  induction l generalizing k with
  | nil => simp [toPoly]
  | cons a l ih =>
    cases k with
    | zero => simp [toPoly]
    | succ k => simp [toPoly, coeff_X_mul, ih]

theorem toPoly_addN (p q : List ℕ) : toPoly (addN p q) = toPoly p + toPoly q := by
  induction p generalizing q with
  | nil => simp [addN, toPoly]
  | cons a p ih =>
    cases q with
    | nil => simp [addN, toPoly]
    | cons b q => simp only [addN, toPoly, ih, map_add]; ring

theorem toPoly_replicate (m a : ℕ) :
    toPoly (List.replicate m a) = C a * ∑ j ∈ Finset.range m, (X : ℕ[X]) ^ j := by
  induction m with
  | zero => simp [toPoly]
  | succ m ih =>
    have hs : ∑ j ∈ Finset.range (m + 1), (X : ℕ[X]) ^ j =
        1 + X * ∑ j ∈ Finset.range m, (X : ℕ[X]) ^ j := by
      rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
      simp [pow_succ']
    rw [List.replicate_succ, toPoly, ih, hs]
    ring

theorem toPoly_mulOnes (m : ℕ) (r : List ℕ) :
    toPoly (mulOnes m r) = toPoly r * ∑ j ∈ Finset.range m, (X : ℕ[X]) ^ j := by
  induction r with
  | nil => simp [mulOnes, toPoly]
  | cons a r ih =>
    have h : mulOnes m (a :: r) = addN (List.replicate m a) (0 :: mulOnes m r) := rfl
    rw [h, toPoly_addN, toPoly_replicate, toPoly, toPoly, ih, map_zero]
    ring

theorem mahonianPoly_eq (x : ℕ) : mahonianPoly x = toPoly (mahonianRow x) := by
  induction x with
  | zero => simp [mahonianPoly, mahonianRow, toPoly]
  | succ x ih =>
    rw [mahonianPoly, Finset.prod_range_succ, ← mahonianPoly, ih, mahonianRow, toPoly_mulOnes]

/-- `mahonian x n` is the coefficient of `q^n` in `∏_{i=0}^{x-1} (1 + q + ⋯ + q^i)`. -/
theorem coeff_mahonianPoly (x n : ℕ) : (mahonianPoly x).coeff n = mahonian x n := by
  rw [mahonianPoly_eq, coeff_toPoly, mahonian]

/-- The major index of a word `w`: the sum of the (1-based) positions `i` with `w_i > w_{i+1}`. -/
def maj (w : List ℕ) : ℕ :=
  ((List.range (w.length - 1)).map fun i =>
    if w.getD (i + 1) 0 < w.getD i 0 then i + 1 else 0).sum

/-- The number of permutations of the `x` letters `0, …, x-1` with major index `n` (literal
count). -/
def majCount (x n : ℕ) : ℕ := ((List.range x).permutations'.filter fun w => maj w = n).length

/-- Sanity check (MacMahon): `mahonian x n` counts the permutations of `x` letters with major
index `n`, for `x ≤ 6` (all `n ≤ 15 = 6·5/2`). -/
theorem mahonian_eq_majCount : ∀ x < 7, ∀ n < 16, majCount x n = mahonian x n := by
  decide +kernel

/-! ### The triangle -/

/-- Forward differences: `diffHeads k v = [Δ^0 v (0), Δ^1 v (0), …, Δ^(k-1) v (0)]`, where
`(Δ v)(i) = v(i+1) - v(i)`. -/
def diffHeads : ℕ → List ℤ → List ℤ
  | 0, _ => []
  | k + 1, v => v.headD 0 :: diffHeads k (List.zipWith (· - ·) v.tail v)

/-- Coefficientwise sum of two integer coefficient lists (lowest degree first). -/
def addZ : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addZ p q

/-- Multiply a coefficient list by `x - c`. -/
def mulXsub (c : ℤ) (p : List ℤ) : List ℤ := addZ (0 :: p) (p.map fun a => -c * a)

/-- The coefficient list of `(x - c)(x - c - 1)⋯(x - c - j + 1)`. -/
def fallingFrom (c : ℕ) : ℕ → List ℤ
  | 0 => [1]
  | j + 1 => mulXsub ((c + j : ℕ) : ℤ) (fallingFrom c j)

/-- Column `n` of A008302 at the interpolation nodes: `[mahonian n n, …, mahonian (2n) n]`. -/
def column (n : ℕ) : List ℤ := (List.range (n + 1)).map fun i => (mahonian (n + i) n : ℤ)

/-- Newton's forward-difference sum `∑_{i} d_i · (n!/(j+i)!) · fallingFrom n (j+i)`, for the
list of differences `[d_0, d_1, …]` starting at index `j`. -/
def newton (n : ℕ) : ℕ → List ℤ → List ℤ
  | _, [] => []
  | j, d :: ds =>
    addZ ((fallingFrom n j).map fun a => d * ((n.factorial / j.factorial : ℕ) : ℤ) * a)
      (newton n (j + 1) ds)

/-- Row `n` of the triangle: the coefficient list of `n! · P_n(x)`, where `P_n` is the polynomial
of degree `≤ n` through `(x, mahonian x n)`, `x = n, …, 2n` (Newton's formula). -/
def Trow (n : ℕ) : List ℤ := newton n 0 (diffHeads (n + 1) (column n))

/-- A342645: `T(n, k)` is `n!` times the coefficient of `x^k` in the polynomial that describes
the number of permutations on `x` letters with major index `n` (for `x ≥ n`). -/
def T (n k : ℕ) : ℤ := (Trow n).getD k 0

/-- Evaluate an integer coefficient list (lowest degree first) at `x`. -/
def evalZ (l : List ℤ) (x : ℤ) : ℤ := l.foldr (fun a acc => a + x * acc) 0

/-- Sanity check: for `n ≤ 9`, `∑_k T(n,k) x^k = n! · mahonian x n` for all `x = n, …, 3n+2`,
and row `n` has exactly `n + 1` entries. -/
theorem rowPoly_agrees : ∀ n < 10, (Trow n).length = n + 1 ∧ ∀ i < 2 * n + 3,
    evalZ (Trow n) ((n + i : ℕ) : ℤ) = (n.factorial : ℤ) * (mahonian (n + i) n : ℤ) := by
  decide +kernel

/-- The definition reproduces all 55 terms listed in OEIS, rows `n = 0, …, 9` (kernel-checked). -/
theorem T_data : (List.range 10).map (fun n => (List.range (n + 1)).map (T n)) =
    [[1],
     [-1, 1],
     [-2, -1, 1],
     [0, -7, 0, 1],
     [0, -14, -13, 2, 1],
     [120, -46, -65, -15, 5, 1],
     [0, 516, -356, -165, -5, 9, 1],
     [5040, 1392, 266, -1421, -280, 28, 14, 1],
     [0, 46320, 3772, -5740, -3871, -280, 98, 20, 1],
     [0, 215280, 212724, -26272, -31437, -7791, 126, 222, 27, 1]] := by
  decide +kernel

/-- A342645 as a sequence (offset `0`): the triangle `T` read by rows. Entry `i` lies in the row
`n` with `n(n+1)/2 ≤ i < (n+1)(n+2)/2`, at column `i - n(n+1)/2`. -/
def a (i : ℕ) : ℤ :=
  let n := Nat.findGreatest (fun n => n * (n + 1) / 2 ≤ i) i
  T n (i - n * (n + 1) / 2)

/-- The definition reproduces all 55 terms listed in OEIS, `a 0, …, a 54` (kernel-checked). -/
theorem a_data : (List.range 55).map (fun i => a (i + 0)) =
    [1, -1, 1, -2, -1, 1, 0, -7, 0, 1, 0, -14, -13, 2, 1, 120, -46, -65, -15, 5, 1, 0, 516, -356,
      -165, -5, 9, 1, 5040, 1392, 266, -1421, -280, 28, 14, 1, 0, 46320, 3772, -5740, -3871, -280,
      98, 20, 1, 0, 215280, 212724, -26272, -31437, -7791, 126, 222, 27, 1] := by
  decide +kernel

/-! ### A290030 and A053657 -/

/-- `revG k = [G_k, G_{k-1}, …, G_0]`, where `t/(e^t - 1) = ∑ G_k t^k`, computed as the
reciprocal of `(e^t - 1)/t = ∑_k t^k/(k+1)!`: `G_0 = 1` and
`G_{k+1} = -∑_{i=0}^{k} G_{k-i}/(i+2)!`. -/
def revG : ℕ → List ℚ
  | 0 => [1]
  | k + 1 => (-(List.zipWith (fun g i => g / ((i + 2).factorial : ℚ)) (revG k)
      (List.range (k + 1))).sum) :: revG k

/-- The coefficients `[G_0, …, G_n]` of `t/(e^t - 1)`. -/
def bernG (n : ℕ) : List ℚ := (revG n).reverse

/-- Coefficientwise sum of two rational coefficient lists (lowest degree first). -/
def addQ : List ℚ → List ℚ → List ℚ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addQ p q

/-- Product of two rational coefficient lists. -/
def mulQ (p q : List ℚ) : List ℚ := p.foldr (fun a acc => addQ (q.map (a * ·)) (0 :: acc)) []

/-- `H = t/(e^t - 1) - 1`, truncated after `t^n`. -/
def Hser (n : ℕ) : List ℚ := 0 :: (bernG n).tail

/-- `powsH n H k P = [[t^n] P, [t^n] P·H, …, [t^n] P·H^(k-1)]` (power series truncated after
`t^n`). -/
def powsH (n : ℕ) (H : List ℚ) : ℕ → List ℚ → List ℚ
  | 0, _ => []
  | k + 1, P => P.getD n 0 :: powsH n H k ((mulQ P H).take (n + 1))

/-- The coefficient list of `x(x-1)⋯(x-j+1)`. -/
def descQ : ℕ → List ℚ
  | 0 => [1]
  | j + 1 => addQ (0 :: descQ j) ((descQ j).map fun a => -(j : ℚ) * a)

/-- `∑_{i} (n!/(j+i)!) · c_i · x(x-1)⋯(x-(j+i)+1)` for the list `[c_0, c_1, …]` starting at
index `j`. -/
def norlundAux (n : ℕ) : ℕ → List ℚ → List ℚ
  | _, [] => []
  | j, c :: cs => addQ ((descQ j).map fun a => (n.factorial : ℚ) * c / (j.factorial : ℚ) * a)
      (norlundAux n (j + 1) cs)

/-- The coefficient list (in `x`, lowest degree first) of Nørlund's polynomial
`B_n^(x) = n! [t^n] (t/(e^t - 1))^x = n! ∑_{j=0}^{n} C(x, j) [t^n] H^j`. -/
def norlund (n : ℕ) : List ℚ := norlundAux n 0 (powsH n (Hser n) (n + 1) [1])

/-- Evaluate a rational coefficient list (lowest degree first) at `x`. -/
def evalQ (l : List ℚ) (x : ℚ) : ℚ := l.foldr (fun a acc => a + x * acc) 0

/-- `(t/(e^t - 1))^x`, truncated after `t^n`, by repeated multiplication. -/
def powG (n : ℕ) : ℕ → List ℚ
  | 0 => [1]
  | x + 1 => (mulQ (powG n x) (bernG n)).take (n + 1)

/-- Sanity check of the binomial-series step: `B_n^(x) = n! [t^n] (t/(e^t - 1))^x` for `n ≤ 6`
and `x ≤ 8`. -/
theorem norlund_check : ∀ n < 7, ∀ x : ℕ, x < 9 →
    evalQ (norlund n) (x : ℚ) = (n.factorial : ℚ) * (powG n x).getD n 0 := by
  decide +kernel

/-- The least common multiple of the denominators of a list of rationals. -/
def lcmDen (l : List ℚ) : ℕ := (l.map (·.den)).foldr Nat.lcm 1

/-- A290030: the leading coefficient (coefficient of `x^n`) of the numerator `L · B_n^(x)` of
Nørlund's polynomial `B_n^(x)`, where `L` is the least common denominator of its coefficients.
-/
def A290030 (n : ℕ) : ℤ := ((lcmDen (norlund n) : ℚ) * (norlund n).getD n 0).num

/-- The definition reproduces the first 26 terms listed in OEIS, `a(0), …, a(25)`
(kernel-checked). -/
theorem A290030_data : (List.range 26).map A290030 =
    [1, -1, 3, -1, 15, -3, 63, -9, 135, -15, 99, -9, 12285, -945, 405, -27, 6885, -405, 161595,
      -8505, 1403325, -66825, 419175, -18225, 24877125, -995085] := by
  decide +kernel

/-- A053657 (offset `1`): `a(n) = ∏_{p prime} p^(∑_{k ≥ 0} ⌊(n-1)/((p-1) p^k)⌋)`; only primes
`p ≤ n` and `k < n` contribute. -/
def A053657 (n : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
    p ^ (∑ k ∈ Finset.range n, (n - 1) / ((p - 1) * p ^ k))

/-- The definition reproduces all 19 terms listed in OEIS, `a(1), …, a(19)` (kernel-checked). -/
theorem A053657_data : (List.range 19).map (fun i => A053657 (i + 1)) =
    [1, 2, 24, 48, 5760, 11520, 2903040, 5806080, 1393459200, 2786918400, 367873228800,
      735746457600, 24103053950976000, 48206107901952000, 578473294823424000,
      1156946589646848000, 9440684171518279680000, 18881368343036559360000,
      271211974879377138647040000] := by
  decide +kernel

/-! ### The conjecture -/

/-- Kagey's conjecture (COMMENTS): for each `m ≥ 0`, `n ↦ T(n, n-m)` (`n ≥ m`) is a polynomial
in `n` of degree `2m` whose leading coefficient is `|A290030(m)/A053657(m+1)|`. -/
def statementDiagonals : Prop :=
  ∀ m : ℕ, ∃ Q : ℚ[X], Q.degree = ((2 * m : ℕ) : WithBot ℕ) ∧
    Q.leadingCoeff = |(A290030 m : ℚ) / (A053657 (m + 1) : ℚ)| ∧
    ∀ n : ℕ, m ≤ n → (T n (n - m) : ℚ) = Q.eval (n : ℚ)

/-- Kagey's conjectured formulas (FORMULA): `T(n,n) = 1`, `T(n,n-1) = (-3n + n^2)/2`,
`T(n,n-2) = (-2n + 21n^2 - 22n^3 + 3n^4)/24` and
`T(n,n-3) = (96n - 134n^2 + 13n^3 + 37n^4 - 13n^5 + n^6)/48`, each for every `n` such that the
left side is an entry of the triangle. -/
def statementFormulas : Prop :=
  (∀ n : ℕ, T n n = 1) ∧
  (∀ n : ℕ, 1 ≤ n → (T n (n - 1) : ℚ) = (-3 * (n : ℚ) + (n : ℚ) ^ 2) / 2) ∧
  (∀ n : ℕ, 2 ≤ n → (T n (n - 2) : ℚ) =
    (-2 * (n : ℚ) + 21 * (n : ℚ) ^ 2 - 22 * (n : ℚ) ^ 3 + 3 * (n : ℚ) ^ 4) / 24) ∧
  (∀ n : ℕ, 3 ≤ n → (T n (n - 3) : ℚ) =
    (96 * (n : ℚ) - 134 * (n : ℚ) ^ 2 + 13 * (n : ℚ) ^ 3 + 37 * (n : ℚ) ^ 4
      - 13 * (n : ℚ) ^ 5 + (n : ℚ) ^ 6) / 48)

/-- The conjectures of A342645 (COMMENTS and FORMULA sections). -/
def statement : Prop := statementDiagonals ∧ statementFormulas

/-- Sanity check of the transcription (not a proof): the four formulas hold for `n ≤ 12`. -/
theorem formulas_check : ∀ n < 13,
    T n n = 1 ∧
    (1 ≤ n → (T n (n - 1) : ℚ) = (-3 * (n : ℚ) + (n : ℚ) ^ 2) / 2) ∧
    (2 ≤ n → (T n (n - 2) : ℚ) =
      (-2 * (n : ℚ) + 21 * (n : ℚ) ^ 2 - 22 * (n : ℚ) ^ 3 + 3 * (n : ℚ) ^ 4) / 24) ∧
    (3 ≤ n → (T n (n - 3) : ℚ) =
      (96 * (n : ℚ) - 134 * (n : ℚ) ^ 2 + 13 * (n : ℚ) ^ 3 + 37 * (n : ℚ) ^ 4
        - 13 * (n : ℚ) ^ 5 + (n : ℚ) ^ 6) / 48) := by
  decide +kernel

/-- Sanity check (not part of the conjecture): `|A290030(m)/A053657(m+1)| = 1/(2^m m!)` for
`m ≤ 9`. -/
theorem leading_check : ∀ m < 10,
    |(A290030 m : ℚ) / (A053657 (m + 1) : ℚ)| = 1 / (2 ^ m * (m.factorial : ℚ)) := by
  decide +kernel

end Math0.Statements.A342645
