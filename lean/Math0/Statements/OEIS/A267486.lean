/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A267486: Gaussian polynomials in the basis `(1+q^2)^k q^(g-k)` via Chebyshev products

Source: https://oeis.org/A267486, Stephen O'Sullivan, Jan 15 2016 (COMMENTS section, text as of
revision #23, May 30 2026). Verbatim:
> Conjecture: More generally, the Gaussian polynomial [2*n+m+1-(m mod 2),m]_q =
> Sum_{k=0..g(m;n)} a(m;n,k)*(1+q^2)^k*q^(g(m;n)-k), for m >= 0, n >= 0, where g(m;n) = m*n if
> m is odd and (2*n+1)*m/2 if m is even, and the tabf array entries a(m;n,k) are the
> coefficients of the g.f. for the row n polynomials G(m;n,x) = (d^m/dt^m)G(m;n,t,x)/m!|_{t=0},
> with G(m;n,t,x) = (1+t)*Product_{k=1..n+(m - m (mod 2))/2}(1 + t^2 + 2*t*T(k,x/2)
> (Chebyshev's T-polynomials). Hence a(m;n,k) = [x^k]G(m;n,x), for k=0..g(m;n). The present
> entry is the instance m = 2. (Thanks to _Wolfdieter Lang_ for clarifying the text on the
> general prescription of a(m;n,k).)

The entry itself (offset `0`, keyword `tabf`) is "Triangle of coefficients of Gaussian
polynomials [2n+7,6]_q represented as finite sum of terms (1+q^2)^k*q^(g-k), where
k = 0,1,...,g with g=6n+3": row `n ≥ 0` lists `a(n,k)`, `k = 0..6n+3`, with
`[2n+7,6]_q = Sum_{k=0..g} a(n,k)*(1+q^2)^k*q^(g-k)`, and the sequence is the rows read in
order. (The representation is unique: `(1+q^2)^k*q^(g-k) = q^g*(q+1/q)^k`, and the powers of
`q+1/q` are linearly independent.)

## Encoding

* **The sequence `a`.** The terms are signed, so `a : ℕ → ℤ`. It is computed from the entry's
  definition, not from the conjectured Chebyshev formula: `gaussL N m` is the coefficient list
  of the Gaussian polynomial `[N,m]_q` (lowest degree first), computed by the q-Pascal rule
  `[r+1,k+1]_q = [r,k]_q + q^(k+1)*[r,k+1]_q` (the same rule that defines `gaussBinom` below),
  and `reprAux` peels off the basis elements from the top: `(1+q^2)^k*q^(g-k)` has degree
  `g+k` and leading coefficient `1`, so for `k = g, g-1, …, 0` the coefficient of `q^(g+k)` in
  the current remainder is the coefficient of `(1+q^2)^k*q^(g-k)`. This triangular elimination
  returns the unique representation coefficients; `row_exact` checks (kernel) that the final
  remainder is zero for every listed row, i.e. that the computed coefficients really represent
  `[2n+7,6]_q`. `a i` finds the row `n` and position `k` of index `i` (row `n` has length
  `6n+4`) and returns `a(n,k)`. `a_data` checks all 80 listed terms (rows `n = 0..4`).
* **The conjecture** is about every `m ≥ 0`, `n ≥ 0`, with `q` an indeterminate.
  - `gaussBinom N m : ℤ[X]` is the Gaussian polynomial `[N,m]_q`, defined by the q-Pascal
    rule with `[N,0]_q = 1` and `[0,m+1]_q = 0`; sanity lemmas `gaussBinom_four_two` and
    `gaussBinom_five_two_mul` check it against the explicit value / the product formula
    `[N,m]_q * Prod_{i=1..m}(1-q^i) = Prod_{i=0..m-1}(1-q^(N-i))`.
  - `g m n` is `m*n` for odd `m` and `(2*n+1)*m/2` for even `m` (an exact division).
  - `chebHalf k = T(k, x/2)`, Mathlib's Chebyshev polynomial of the first kind composed with
    `x/2`, over `ℚ` (so that `x/2` makes sense).
  - `Gt m n : ℚ[x][t]` is `G(m;n,t,x) = (1+t)*Prod_{k=1..n+(m - m mod 2)/2}(1+t^2+2t*T(k,x/2))`
    as a polynomial in `t` with coefficients in `ℚ[x]`; the upper limit is written literally.
  - `G m n : ℚ[x]` is `(d^m/dt^m) G(m;n,t,x) / m!` evaluated at `t = 0`, written literally with
    Mathlib's iterated `derivative` (`G_eq_coeff` shows it is the `t^m`-coefficient).
  - `a(m;n,k) = [x^k] G(m;n,x)` is `(G m n).coeff k : ℚ`.
  - The Gaussian polynomial `[2*n+m+1-(m mod 2), m]_q` is mapped into `ℚ[q]` and compared with
    `Sum_{k=0..g} C(a(m;n,k)) * (1+q^2)^k * q^(g-k)` (here `q` is `X : ℚ[X]`, and `g - k` is a
    true difference since `k ≤ g`).
  - The text also says that the row `n` entries `a(m;n,k)`, `k = 0..g(m;n)`, are the
    coefficients of the generating function `G(m;n,x)` of row `n`; we therefore also state
    `natDegree (G m n) ≤ g m n` (the row polynomial has no terms beyond `k = g(m;n)`).
    Without this conjunct the identity alone would say nothing about the coefficients of `G`
    beyond `x^g`.
* **Reading notes on the entry.** The comment says "The present entry is the instance m = 2",
  but the entry's name, data and Maple program are the instance `m = 6`
  (`[2n+7,6]_q`, `g = 6n+3`, product up to `n+3`); likewise the `%F` line and the Mathematica
  program (copied from A267120) use `Product_{i=1..n+1}`, which is the `m = 6` instance only
  with `n+3`. These slips do not affect the general conjecture, which is formalized as written.
  `G_six_zero` checks that the formal `G 6 0` is `-1 - 2x + x^2 + x^3`, i.e. row 0 of the data,
  and `G_two_zero` checks `G 2 0 = 1 + x` (`[3,2]_q = q + (1+q^2)`).
-/

namespace Math0.Statements.A267486

open Polynomial

/-! ### The sequence (computable, from the entry's definition) -/

/-- Coefficientwise sum of two coefficient lists (lowest degree first). -/
def addL : List ℤ → List ℤ → List ℤ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: addL p q

/-- Multiplication of a coefficient list by `q ^ s`. -/
def shiftL (s : ℕ) (p : List ℤ) : List ℤ := List.replicate s 0 ++ p

/-- One q-Pascal step: from the list `[[r,0]_q, …, [r,m]_q]` of coefficient lists to
`[[r+1,0]_q, …, [r+1,m]_q]`, using `[r+1,0]_q = 1` and
`[r+1,k+1]_q = [r,k]_q + q^(k+1) [r,k+1]_q`. -/
def pascalStep (m : ℕ) (prev : List (List ℤ)) : List (List ℤ) :=
  (List.range (m + 1)).map fun k =>
    match k with
    | 0 => [1]
    | k + 1 => addL (prev.getD k []) (shiftL (k + 1) (prev.getD (k + 1) []))

/-- `[[r,0]_q, …, [r,m]_q]`, starting from `[0,0]_q = 1`, `[0,k+1]_q = 0`. -/
def gaussRows (m : ℕ) : ℕ → List (List ℤ)
  | 0 => [1] :: List.replicate m []
  | r + 1 => pascalStep m (gaussRows m r)

/-- Coefficient list (lowest degree first) of the Gaussian polynomial `[N,m]_q`. -/
def gaussL (N m : ℕ) : List ℤ := (gaussRows m N).getD m []

/-- Coefficient list of `(1+q^2)^k`. -/
def onePlusSqPow : ℕ → List ℤ
  | 0 => [1]
  | k + 1 => addL (onePlusSqPow k) (shiftL 2 (onePlusSqPow k))

/-- Coefficient list of the basis element `(1+q^2)^k * q^(g-k)`. -/
def basisL (g k : ℕ) : List ℤ := shiftL (g - k) (onePlusSqPow k)

/-- Triangular elimination in the basis `(1+q^2)^k q^(g-k)`: `reprAux g j r acc` treats
`k = j-1, j-2, …, 0` in turn, taking as coefficient of `(1+q^2)^k q^(g-k)` the coefficient of
`q^(g+k)` in the remainder `r` and subtracting that multiple of the basis element. It returns
the coefficients (prepended to `acc`, so in the order `k = 0, 1, …`) and the final remainder. -/
def reprAux (g : ℕ) : ℕ → List ℤ → List ℤ → List ℤ × List ℤ
  | 0, r, acc => (acc, r)
  | j + 1, r, acc =>
    reprAux g j (addL r ((basisL g j).map fun x => -(r.getD (g + j) 0 * x)))
      (r.getD (g + j) 0 :: acc)

/-- Row `n` of A267486: the coefficients `a(n,0), …, a(n,6n+3)` of
`[2n+7,6]_q = Sum_{k=0..g} a(n,k) (1+q^2)^k q^(g-k)`, `g = 6n+3`. -/
def row (n : ℕ) : List ℤ := (reprAux (6 * n + 3) (6 * n + 4) (gaussL (2 * n + 7) 6) []).1

/-- Position `(n, k)` in the triangle of the flat index `i` (row `n` has length `6n+4`);
`fuel = i + 1` always suffices since each step lowers `i` by at least `4`. -/
def locate : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, n, i => (n, i)
  | fuel + 1, n, i => if i < 6 * n + 4 then (n, i) else locate fuel (n + 1) (i - (6 * n + 4))

/-- A267486 (offset `0`): the triangle `a(n,k)` of coefficients of `(1+q^2)^k q^(g-k)`,
`g = 6n+3`, in the Gaussian polynomial `[2n+7,6]_q`, read by rows. -/
def a (i : ℕ) : ℤ := (row (locate (i + 1) 0 i).1).getD (locate (i + 1) 0 i).2 0

/-- The definition reproduces all 80 terms listed in OEIS (rows `n = 0..4`; kernel-checked). -/
theorem a_data : (List.range 80).map (fun i => a (i + 0)) =
    [-1, -2, 1, 1, 0, 2, -2, -15, 7, 17, -5, -7, 1, 1, -2, -6, 25, 71, -80, -218, 126, 284,
      -106, -190, 48, 69, -11, -13, 1, 1, 0, 6, -12, -137, 196, 945, -811, -2745, 1602,
      4163, -1780, -3711, 1193, 2059, -493, -722, 123, 156, -17, -19, 1, 1, -3, -12, 94, 358,
      -952, -3430, 4699, 15615, -13467, -39946, 24494, 63168, -29535, -65638, 24206, 46512,
      -13652, -22891, 5294, 7834, -1386, -1831, 234, 279, -23, -25, 1, 1] := by
  decide +kernel

/-- For the listed rows the elimination leaves remainder `0`, so the computed coefficients
represent `[2n+7,6]_q` exactly; rows have length `6n+4` (kernel-checked). -/
theorem row_exact : ∀ n < 5,
    (reprAux (6 * n + 3) (6 * n + 4) (gaussL (2 * n + 7) 6) []).2.all (· = 0) = true ∧
      (row n).length = 6 * n + 4 := by
  decide +kernel

/-! ### The conjecture -/

/-- The Gaussian polynomial (q-binomial coefficient) `[N, m]_q ∈ ℤ[q]`, by the q-Pascal rule
`[N+1, m+1]_q = [N, m]_q + q^(m+1) [N, m+1]_q`, `[N, 0]_q = 1`, `[0, m+1]_q = 0`. -/
noncomputable def gaussBinom : ℕ → ℕ → ℤ[X]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | N + 1, m + 1 => gaussBinom N m + X ^ (m + 1) * gaussBinom N (m + 1)

theorem gaussBinom_four_two : gaussBinom 4 2 = 1 + X + 2 * X ^ 2 + X ^ 3 + X ^ 4 := by
  simp [gaussBinom]; ring

theorem gaussBinom_five_two_mul :
    gaussBinom 5 2 * ((1 - X) * (1 - X ^ 2)) = (1 - X ^ 5) * (1 - X ^ 4) := by
  simp [gaussBinom]; ring

/-- `g(m;n) = m*n` if `m` is odd and `(2*n+1)*m/2` if `m` is even. -/
def g (m n : ℕ) : ℕ := if m % 2 = 1 then m * n else (2 * n + 1) * m / 2

theorem g_six (n : ℕ) : g 6 n = 6 * n + 3 := by
  simp [g]; omega

/-- `T(k, x/2) ∈ ℚ[x]`, with `T` the Chebyshev polynomials of the first kind. -/
noncomputable def chebHalf (k : ℕ) : ℚ[X] := (Chebyshev.T ℚ k).comp (C (1 / 2 : ℚ) * X)

/-- `G(m;n,t,x) = (1+t) * Prod_{k=1..n+(m - m mod 2)/2} (1 + t^2 + 2*t*T(k,x/2))`, a polynomial
in `t` (the outer variable) with coefficients in `ℚ[x]`. -/
noncomputable def Gt (m n : ℕ) : ℚ[X][X] :=
  (1 + X) * ∏ k ∈ Finset.Icc 1 (n + (m - m % 2) / 2), (1 + X ^ 2 + 2 * X * C (chebHalf k))

/-- `G(m;n,x) = (d^m/dt^m) G(m;n,t,x) / m! |_{t=0}`. -/
noncomputable def G (m n : ℕ) : ℚ[X] :=
  C ((m.factorial : ℚ)⁻¹) * (derivative^[m] (Gt m n)).eval 0

/-- `G(m;n,x)` is the coefficient of `t^m` in `G(m;n,t,x)`. -/
theorem G_eq_coeff (m n : ℕ) : G m n = (Gt m n).coeff m := by
  rw [G, ← coeff_zero_eq_eval_zero, coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
    nsmul_eq_mul, ← mul_assoc]
  have h : (m.factorial : ℚ[X]) = C (m.factorial : ℚ) := by simp
  rw [h, ← C_mul, inv_mul_cancel₀ (by exact_mod_cast m.factorial_ne_zero), C_1, one_mul]

theorem two_chebHalf_one : 2 * chebHalf 1 = X := by
  apply Polynomial.funext; intro r
  simp [chebHalf]

theorem two_chebHalf_two : 2 * chebHalf 2 = X ^ 2 - 2 := by
  apply Polynomial.funext; intro r
  simp [chebHalf, Chebyshev.T_two]; ring

theorem two_chebHalf_three : 2 * chebHalf 3 = X ^ 3 - 3 * X := by
  have h3 : Chebyshev.T ℚ 3 = 2 * X * (2 * X ^ 2 - 1) - X := by
    have := Chebyshev.T_add_two ℚ 1
    norm_num at this
    rw [this, Chebyshev.T_two]
  apply Polynomial.funext; intro r
  simp [chebHalf, h3]; ring

/-- Sanity check: `G(2;0,x) = 1 + x` (and indeed `[3,2]_q = 1 + q + q^2 = q + (1+q^2)`). -/
theorem G_two_zero : G 2 0 = 1 + X := by
  rw [G_eq_coeff]
  have h1 : (1 + X : ℚ[X][X]) * (1 + X ^ 2 + 2 * X * C (chebHalf 1)) =
      1 + X + X ^ 2 * (1 + C (2 * chebHalf 1)) + X ^ 3 + X * C (2 * chebHalf 1) := by
    rw [C_mul, C_ofNat]; ring
  simp only [Gt, Nat.reduceMod, Nat.sub_zero, Nat.reduceDiv, zero_add, Finset.Icc_self,
    Finset.prod_singleton]
  rw [h1, two_chebHalf_one]
  simp [coeff_X, coeff_one, coeff_X_pow, coeff_X_pow_mul']

theorem coeff_six_aux (a b c : ℚ[X]) :
    ((1 + X) * ((1 + X ^ 2 + X * C a) * ((1 + X ^ 2 + X * C b) * (1 + X ^ 2 + X * C c)))).coeff 6
      = 1 + a + b + c := by
  ring_nf
  simp [coeff_mul_C, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, coeff_X, coeff_one]

/-- Sanity check: `G(6;0,x) = -1 - 2x + x^2 + x^3`, i.e. row 0 of A267486 (`-1, -2, 1, 1`). -/
theorem G_six_zero : G 6 0 = -1 - 2 * X + X ^ 2 + X ^ 3 := by
  rw [G_eq_coeff]
  have hI : Finset.Icc 1 (0 + (6 - 6 % 2) / 2) = {1, 2, 3} := by decide
  have hf : ∀ k : ℕ, (1 + X ^ 2 + 2 * X * C (chebHalf k) : ℚ[X][X]) =
      1 + X ^ 2 + X * C (2 * chebHalf k) := by
    intro k; rw [C_mul, C_ofNat]; ring
  rw [Gt, hI, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton, hf, hf, hf, coeff_six_aux, two_chebHalf_one, two_chebHalf_two,
    two_chebHalf_three]
  ring

/-- O'Sullivan's conjecture: for all `m ≥ 0`, `n ≥ 0`, the row polynomial
`G(m;n,x) = Sum_{k=0..g(m;n)} a(m;n,k) x^k` (so of degree at most `g(m;n)`), and the Gaussian
polynomial satisfies `[2n+m+1-(m mod 2), m]_q = Sum_{k=0..g(m;n)} a(m;n,k) (1+q^2)^k q^(g(m;n)-k)`
with `a(m;n,k) = [x^k] G(m;n,x)`. -/
def statement : Prop :=
  ∀ m n : ℕ,
    (G m n).natDegree ≤ g m n ∧
      (gaussBinom (2 * n + m + 1 - m % 2) m).map (Int.castRingHom ℚ) =
        ∑ k ∈ Finset.range (g m n + 1), C ((G m n).coeff k) * (1 + X ^ 2) ^ k * X ^ (g m n - k)

end Math0.Statements.A267486
