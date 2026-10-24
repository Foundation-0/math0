/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A341761: leading coefficient of the subword complexity polynomial

Source: https://oeis.org/A341761, Shiyao Guo, Feb 19 2021 (COMMENTS section). Verbatim:
> Conjecture: the coefficient of x^n in S(n,x) is n*(n+1)/2.

The entry (offset `0`, keywords `sign,tabl`) is "Triangle read by rows in which row n is the
coefficients of the subword complexity polynomial S(n,x)." Its comments explain: "S(n,x) is the
sum of subword complexities (number of nonempty distinct subwords) of all words of length n and an
alphabet with size x", and "The degree of S(n,x) is n." The example (`S(3,2) = 36`: the words
`aaa, aab, …, bbb` have `3, 5, 5, 5, 5, 5, 5, 3` distinct nonempty subwords) and the Mathematica
program (which takes all `Subsequences`, i.e. contiguous pieces) confirm that "subword" means a
*factor* (contiguous subword), and that the coefficients are listed constant term first.

## Encoding

* *Factors.* `factors w` is the finite set of distinct nonempty factors of the word `w`, computed
  as the nonempty prefixes of the suffixes of `w`; `mem_factors` proves
  `u ∈ factors w ↔ u ≠ [] ∧ u <:+: w` (`<:+:` is Mathlib's "is a contiguous infix of").
  `complexity w = (factors w).card` is the subword complexity of `w`.
* *`S(n, x)`.* `S n x = ∑ w : Fin n → Fin x, complexity (List.ofFn w)`: the words of length `n`
  over an alphabet of size `x` are the maps `Fin n → Fin x`. (For `x = 0, n ≥ 1` there are no
  words and `S n 0 = 0`; for `n = 0` there is one, empty, word with complexity `0`.) For
  evaluation, `words x n` lists the same words as lists and `S_eq_Sw` proves
  `S n x = Sw n x := ((words x n).map complexity).sum`.
* *The polynomial and the conjecture.* "The polynomial `S(n,x)`" is read as a polynomial
  `P : ℚ[X]` with `P(x) = S(n, x)` for every `x ∈ ℕ`. Such a `P` is unique when it exists, since
  two polynomials agreeing on the infinite set `ℕ` coincide (`poly_unique`). `statement` says: for
  every `n ≥ 0` there is such a polynomial `P` and its coefficient of `x^n` is `n(n+1)/2`. The
  entry asserts, as a fact, that `S(n, x)` is a polynomial in `x` of degree `n`; the existential
  in `statement` includes the polynomiality part. Rational coefficients are allowed, so no
  integrality is assumed.
* *The triangle.* Row `n` lists the `n + 1` coefficients of `x^0, …, x^n` (the triangle shape
  encodes the degree `n` stated in the entry). Since a polynomial of degree `≤ n` is determined by
  its values at `x = 0, …, n`, `row n` computes these coefficients from `S(n,0), …, S(n,n)` by
  Newton's forward-difference formula `P(x) = ∑_{k ≤ n} Δ^k S(n,·)(0) · C(x, k)` (`interp`),
  working in `ℚ`. This reproduces the coefficients of `S(n,x)` exactly when `S(n,·)` is a
  polynomial of degree `≤ n`, as the entry states. `a` is the triangle read by rows (offset `0`):
  `a m` is entry `k` of row `n`, where `m = n(n+1)/2 + k`, `0 ≤ k ≤ n` (`rowCol`). It is
  `ℚ`-valued because the interpolation is done over `ℚ`; the data check confirms the listed terms
  are the integers given in OEIS.
* *Data.* `S(n, x)` is computed by brute force over all `x^n` words, so the kernel can only reach
  small rows: `rows_data` checks rows `n = 0, …, 5`, and `a_data` the corresponding first `21`
  terms `a 0, …, a 20` (row `6` would need the `46656` words of length `6` over `6` letters).
-/

namespace Math0.Statements.A341761

open Polynomial

/-! ### Factors, subword complexity and `S(n, x)` -/

/-- The distinct nonempty factors (contiguous subwords) of the word `w`: the nonempty prefixes of
the suffixes of `w` (see `mem_factors`). -/
def factors {α : Type*} [DecidableEq α] (w : List α) : Finset (List α) :=
  (w.tails.flatMap fun t => t.inits.tail).toFinset

theorem mem_inits_tail {α : Type*} (u : List α) :
    ∀ t : List α, u ∈ t.inits.tail ↔ u ≠ [] ∧ u <+: t
  | [] => by simp
  | a :: l => by
    simp only [List.inits_cons, List.tail_cons, List.mem_map, List.mem_inits]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨List.cons_ne_nil _ _, List.prefix_cons_inj _ |>.2 hv⟩
    · rintro ⟨hu, hp⟩
      rcases u with _ | ⟨b, v⟩
      · exact absurd rfl hu
      · obtain ⟨rfl, hv⟩ := List.cons_prefix_cons.1 hp
        exact ⟨v, hv, rfl⟩

/-- `factors w` is exactly the set of nonempty contiguous subwords of `w`. -/
theorem mem_factors {α : Type*} [DecidableEq α] (w u : List α) :
    u ∈ factors w ↔ u ≠ [] ∧ u <:+: w := by
  simp only [factors, List.mem_toFinset, List.mem_flatMap, List.mem_tails, mem_inits_tail,
    List.infix_iff_prefix_suffix]
  constructor
  · rintro ⟨t, ht, hu, hp⟩
    exact ⟨hu, t, hp, ht⟩
  · rintro ⟨hu, t, hp, ht⟩
    exact ⟨t, ht, hu, hp⟩

/-- The subword complexity of `w`: the number of distinct nonempty factors of `w`. -/
def complexity {α : Type*} [DecidableEq α] (w : List α) : ℕ := (factors w).card

/-- `S(n, x)`: the sum of the subword complexities of all `x^n` words of length `n` over an
alphabet of size `x` (the words are the maps `Fin n → Fin x`). -/
def S (n x : ℕ) : ℕ := ∑ w : Fin n → Fin x, complexity (List.ofFn w)

/-- Two polynomials over `ℚ` that agree at every natural number are equal; so "the polynomial
`S(n, x)`" is well defined whenever one exists. -/
theorem poly_unique (P Q : ℚ[X]) (h : ∀ x : ℕ, P.eval (x : ℚ) = Q.eval (x : ℚ)) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem (f := fun x : ℕ => (x : ℚ)) Nat.cast_injective
  intro x
  exact h x

/-! ### Evaluating `S(n, x)` -/

/-- All words of length `n` over the alphabet `Fin x`, as lists. -/
def words (x : ℕ) : ℕ → List (List (Fin x))
  | 0 => [[]]
  | n + 1 => (List.finRange x).flatMap fun c => (words x n).map (c :: ·)

theorem sum_map_flatMap {β γ : Type*} (l : List β) (f : β → List γ) (g : γ → ℕ) :
    ((l.flatMap f).map g).sum = (l.map fun b => ((f b).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem sum_ofFn_eq (x : ℕ) : ∀ (n : ℕ) (g : List (Fin x) → ℕ),
    ∑ w : Fin n → Fin x, g (List.ofFn w) = ((words x n).map g).sum
  | 0, g => by simp [words]
  | n + 1, g => by
    rw [← (Fin.consEquiv (fun _ => Fin x)).sum_comp, Fintype.sum_prod_type, Fin.sum_univ_def,
      words, sum_map_flatMap]
    congr 1
    refine List.map_congr_left fun c _ => ?_
    rw [List.map_map, ← sum_ofFn_eq x n (g ∘ fun l => c :: l)]
    simp [Fin.consEquiv_apply, List.ofFn_succ]

/-- `S(n, x)` summed over the list `words x n`. -/
def Sw (n x : ℕ) : ℕ := ((words x n).map complexity).sum

theorem S_eq_Sw : S = Sw := by
  funext n x
  exact sum_ofFn_eq x n complexity

/-! ### The triangle -/

/-- One step of forward differences: `[v₀, v₁, v₂, …] ↦ [v₁ - v₀, v₂ - v₁, …]`. -/
def diff (v : List ℚ) : List ℚ := List.zipWith (fun a b => b - a) v v.tail

/-- Multiply the polynomial with coefficient list `p` (constant term first) by `X - c`. -/
def mulXSub (c : ℚ) (p : List ℚ) : List ℚ :=
  List.zipWith (· + ·) (0 :: p) (p.map (fun a => -c * a) ++ [0])

/-- The coefficients (constant term first) of `C(X, k) = X (X - 1) ⋯ (X - k + 1) / k!`. -/
def binomCoeffs (k : ℕ) : List ℚ :=
  ((List.range k).foldl (fun p i => mulXSub i p) [1]).map (· / k.factorial)

/-- The coefficients `[c₀, …, cₙ]` (constant term first) of the polynomial of degree `≤ n` that
takes the values `v = [v₀, …, vₙ]` at `x = 0, …, n`, by Newton's forward-difference formula
`P(x) = ∑_{k ≤ n} Δ^k v₀ · C(x, k)`. -/
def interp (v : List ℚ) : List ℚ :=
  (List.range v.length).map fun j =>
    ((List.range v.length).map fun k => (diff^[k] v).headD 0 * (binomCoeffs k).getD j 0).sum

/-- Row `n` of the triangle: the coefficients of `x^0, …, x^n` in `S(n, x)`, interpolated from
the values `S(n, 0), …, S(n, n)`. -/
def row (n : ℕ) : List ℚ := interp ((List.range (n + 1)).map fun x => (S n x : ℚ))

/-- The position `m` of a triangle read by rows is entry `k` of row `n`, where
`m = n(n+1)/2 + k` and `0 ≤ k ≤ n`; `rowCol m = (n, k)`. -/
def rowCol (m : ℕ) : ℕ × ℕ :=
  let n := (List.range (m + 1)).foldl (fun acc i => if i * (i + 1) / 2 ≤ m then i else acc) 0
  (n, m - n * (n + 1) / 2)

/-- A341761: the triangle read by rows whose row `n` lists the coefficients (of `x^0, …, x^n`)
of the subword complexity polynomial `S(n, x)`. -/
def a (m : ℕ) : ℚ := (row (rowCol m).1).getD (rowCol m).2 0

/-! ### Data -/

/-- `row` with `S` replaced by its list evaluation `Sw`. -/
def rowW (n : ℕ) : List ℚ := interp ((List.range (n + 1)).map fun x => (Sw n x : ℚ))

theorem row_eq_rowW : row = rowW := by
  funext n
  simp only [row, rowW, S_eq_Sw]

set_option maxRecDepth 100000 in
/-- Rows `n = 0, …, 5` of the triangle, as listed in OEIS (kernel-checked). -/
theorem rows_data : (List.range 6).map row =
    [[0], [0, 1], [0, -1, 3], [0, 0, -3, 6], [0, -1, 1, -6, 10], [0, 2, -6, 4, -10, 15]] := by
  rw [row_eq_rowW]
  decide +kernel

theorem a_eq_getD (N m : ℕ) (h : (rowCol m).1 < N) :
    a m = (((List.range N).map row).getD (rowCol m).1 []).getD (rowCol m).2 0 := by
  simp [a, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]

/-- The definition reproduces the first `21` terms listed in OEIS (rows `0`–`5`;
kernel-checked through `rows_data`). -/
theorem a_data : (List.range 21).map (fun i => a (i + 0)) =
    [0, 0, 1, 0, -1, 3, 0, 0, -3, 6, 0, -1, 1, -6, 10, 0, 2, -6, 4, -10, 15] := by
  have hlt : ∀ m ∈ List.range 21, (rowCol m).1 < 6 := by decide
  rw [List.map_congr_left fun m hm => a_eq_getD 6 (m + 0) (hlt m hm), rows_data]
  decide +kernel

/-! ### The conjecture -/

/-- Conjecture (Shiyao Guo): for every `n ≥ 0`, the subword complexity polynomial `S(n, x)` (a
polynomial `P` with `P(x) = S(n, x)` for all `x ∈ ℕ`, unique by `poly_unique`) has coefficient
`n(n+1)/2` at `x^n`. -/
def statement : Prop :=
  ∀ n : ℕ, ∃ P : ℚ[X], (∀ x : ℕ, P.eval (x : ℚ) = (S n x : ℚ)) ∧
    P.coeff n = (n : ℚ) * (n + 1) / 2

end Math0.Statements.A341761
