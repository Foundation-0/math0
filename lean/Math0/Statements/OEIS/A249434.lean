/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A249434: `A249151(k) = k` exactly when `k + 1` is prime

Source: https://oeis.org/A249434, Antti Karttunen, Nov 02 2014 (COMMENTS section). Verbatim:
> It seems that A006093 gives all those k for which A249151(k) = k. If that is true, then this
> is a disjoint union of A006093 and A249429.

The same claim appears in A249151 ("A006093 seems to give all such k, that a(k) = k"), and the
cross-references of A249434 list "Subsequences: A006093 (conjectured)".

## The sequences involved

* A249434 (offset `1`): "Integers m such that m! divides the product of elements on row m of
  Pascal's triangle." Data: `0, 1, 2, 4, 6, 10, 12, 16, 18, 22, …`.
* A249151 (offset `0`): "Largest m such that m! divides the product of elements on row n of
  Pascal's triangle."
* A006093 (offset `1`): `a(n) = prime(n) - 1`, i.e. `1, 2, 4, 6, 10, 12, …`. So a natural number
  `k` lies in A006093 iff `k + 1` is prime.

## Encoding

* `rowProd n = ∏_{j = 0..n} C(n, j)` is the product of the elements of row `n` of Pascal's
  triangle (A001142).
* `IsTerm m := m ! ∣ rowProd m` is the defining property of A249434, and
  `a n = Nat.nth IsTerm (n - 1)` (offset `1`) lists its terms in increasing order. `Nat.nth` is
  noncomputable (finiteness of the gaps is not known in Lean), so `a` is noncomputable; the
  predicate `IsTerm` itself is decidable. `a_data` checks all `81` listed terms `a 1, …, a 81`
  (all terms `≤ 256`) through a kernel scan over `m < 257`. For speed, the kernel computes
  `rowProd m` by the recurrence `rowProd (n+1) * (n+1)! = rowProd n * (n+1)^(n+1)`
  (`rowProd_succ_mul`), proved here.
* `A249151 n` is computed by an upward search (the set `{m | m ! ∣ rowProd n}` is downward closed
  since `j ! ∣ m !` for `j ≤ m`, and bounded since `rowProd n ≥ 1`). `A249151_isGreatest` proves
  that `A249151 n` is the greatest `m` with `m ! ∣ rowProd n`, and `A249151_data` checks the
  first `81` listed terms of A249151.
* "A006093 gives all those k for which A249151(k) = k" is read as the set equality
  `{k | A249151(k) = k} = A006093` (both inclusions: the follow-up "this is a disjoint union of
  A006093 and A249429" and the cross-reference "Subsequences: A006093 (conjectured)" both need
  `A006093 ⊆ {k | A249151(k) = k}` as well). So `statement` is: for every `k ≥ 0`,
  `k` is the largest `m` with `m ! ∣ rowProd k` iff `k + 1` is prime. `statement_iff` restates
  it with the function `A249151`.
-/

namespace Math0.Statements.A249434

open Finset Nat

/-! ### The row products of Pascal's triangle -/

/-- The product of the elements of row `n` of Pascal's triangle, `∏_{j=0..n} C(n, j)`
(A001142). -/
def rowProd (n : ℕ) : ℕ := ∏ j ∈ range (n + 1), n.choose j

theorem rowProd_pos (n : ℕ) : 0 < rowProd n :=
  Finset.prod_pos fun j hj => Nat.choose_pos (by simp at hj; omega)

/-- `∏_{j < N} (N - j) = N!`. -/
theorem prod_range_sub_eq_factorial (N : ℕ) : ∏ j ∈ range N, (N - j) = N ! := by
  rw [← Finset.prod_range_add_one_eq_factorial, ← Finset.prod_range_reflect (fun j => j + 1) N]
  refine Finset.prod_congr rfl fun j hj => ?_
  simp at hj
  omega

/-- The recurrence `P(n+1) * (n+1)! = P(n) * (n+1)^(n+1)` for the row products. -/
theorem rowProd_succ_mul (n : ℕ) : rowProd (n + 1) * (n + 1)! = rowProd n * (n + 1) ^ (n + 1) := by
  have h1 : rowProd (n + 1) = ∏ j ∈ range (n + 1), (n + 1).choose j := by
    rw [rowProd, Finset.prod_range_succ, Nat.choose_self, mul_one]
  have h2 : (n + 1) ^ (n + 1) = ∏ _j ∈ range (n + 1), (n + 1) := by simp
  rw [h1, ← prod_range_sub_eq_factorial, ← Finset.prod_mul_distrib, rowProd, h2,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Nat.choose_mul_succ_eq]

/-- Kernel-friendly computation of `(rowProd n, n !)`. -/
def rowProdFact : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 =>
    match rowProdFact n with
    | (p, f) => (p * (n + 1) ^ (n + 1) / (f * (n + 1)), f * (n + 1))

theorem rowProdFact_eq (n : ℕ) : rowProdFact n = (rowProd n, n !) := by
  induction n with
  | zero => simp [rowProdFact, rowProd]
  | succ n ih =>
    rw [rowProdFact, ih]
    simp only [Prod.mk.injEq]
    have hf : n ! * (n + 1) = (n + 1)! := by rw [Nat.factorial_succ, mul_comm]
    rw [hf]
    refine ⟨?_, rfl⟩
    exact Nat.div_eq_of_eq_mul_left (Nat.factorial_pos _) (rowProd_succ_mul n).symm

/-! ### A249434 -/

/-- The defining property of A249434: `m !` divides the product of row `m` of Pascal's
triangle. -/
def IsTerm (m : ℕ) : Prop := m ! ∣ rowProd m

theorem isTerm_iff_check (m : ℕ) :
    IsTerm m ↔ (rowProdFact m).1 % (rowProdFact m).2 = 0 := by
  rw [rowProdFact_eq, IsTerm, Nat.dvd_iff_mod_eq_zero]

instance : DecidablePred IsTerm := fun m => decidable_of_iff _ (isTerm_iff_check m).symm

/-- A249434: the `n`-th smallest (offset `1`) integer `m ≥ 0` such that `m !` divides the
product of the elements on row `m` of Pascal's triangle. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- The elements `< N` satisfying `p`, in increasing order, are `nth p 0, nth p 1, …`. -/
theorem filter_range_eq (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    (List.range N).filter (fun k => decide (p k)) =
      (List.range (Nat.count p N)).map (Nat.nth p) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, ih, Nat.count_succ]
    by_cases h : p N
    · simp [h, List.range_succ, Nat.nth_count h]
    · simp [h]

theorem map_nth_eq_of_filter {p : ℕ → Prop} [DecidablePred p] {N K : ℕ} {L : List ℕ}
    (h : (List.range N).filter (fun k => decide (p k)) = L) (hK : L.length = K) :
    (List.range K).map (Nat.nth p) = L := by
  rw [filter_range_eq] at h
  subst h
  simp only [List.length_map, List.length_range] at hK
  rw [hK]

/-- The definition reproduces all 81 terms listed in OEIS (all terms `≤ 256`; kernel-checked). -/
theorem a_data : (List.range 81).map (fun i => a (i + 1)) =
    [0, 1, 2, 4, 6, 10, 12, 16, 18, 22, 28, 30, 35, 36, 39, 40, 42, 46, 52, 58, 60, 62, 66, 70,
      72, 78, 79, 82, 83, 88, 89, 96, 100, 102, 104, 106, 107, 108, 112, 126, 130, 131, 136,
      138, 143, 148, 149, 150, 153, 156, 159, 162, 164, 166, 167, 172, 174, 175, 178, 179, 180,
      181, 190, 192, 194, 196, 197, 198, 199, 207, 209, 210, 219, 222, 226, 228, 232, 238, 240,
      250, 256] := by
  have : (fun i => a (i + 1)) = Nat.nth IsTerm := funext fun i => by simp [a]
  rw [this]
  exact map_nth_eq_of_filter (N := 257) (by decide +kernel) rfl

/-! ### A249151 -/

/-- Upward search: starting from `m` with `m ! ∣ P`, step up while `(m + 1)! ∣ P`, with `fuel`
steps at most. -/
def lastFact (P : ℕ) : ℕ → ℕ → ℕ
  | 0, m => m
  | f + 1, m => if (m + 1)! ∣ P then lastFact P f (m + 1) else m

theorem lastFact_spec (P : ℕ) (hP : 0 < P) (f m : ℕ) (hm : m ! ∣ P) (hf : P ≤ m + f) :
    (lastFact P f m)! ∣ P ∧ ¬ (lastFact P f m + 1)! ∣ P := by
  induction f generalizing m with
  | zero =>
    refine ⟨hm, fun h => ?_⟩
    have h1 := Nat.le_of_dvd hP h
    have h2 := Nat.self_le_factorial (m + 1)
    simp only [lastFact] at h1 h2
    omega
  | succ f ih =>
    rw [lastFact]
    split_ifs with h
    · exact ih (m + 1) h (by omega)
    · exact ⟨hm, h⟩

/-- A249151: the largest `m` such that `m !` divides the product of the elements on row `n` of
Pascal's triangle. -/
def A249151 (n : ℕ) : ℕ := lastFact (rowProd n) (rowProd n) 0

/-- `A249151 n` is the greatest `m` with `m ! ∣ rowProd n`. -/
theorem A249151_isGreatest (n : ℕ) : IsGreatest {m : ℕ | m ! ∣ rowProd n} (A249151 n) := by
  obtain ⟨h1, h2⟩ := lastFact_spec (rowProd n) (rowProd_pos n) (rowProd n) 0 (by simp)
    (by omega)
  refine ⟨h1, fun m hm => ?_⟩
  by_contra hlt
  exact h2 ((Nat.factorial_dvd_factorial (by unfold A249151 at *; omega)).trans hm)

theorem A249151_eq_iff (n k : ℕ) : A249151 n = k ↔ IsGreatest {m : ℕ | m ! ∣ rowProd n} k :=
  ⟨fun h => h ▸ A249151_isGreatest n, fun h => (A249151_isGreatest n).unique h⟩

/-- Kernel-friendly version of `A249151`. -/
def A249151' (n : ℕ) : ℕ := lastFact (rowProdFact n).1 (rowProdFact n).1 0

theorem A249151'_eq (n : ℕ) : A249151' n = A249151 n := by
  simp [A249151', A249151, rowProdFact_eq]

/-- The definition of `A249151` reproduces its first 81 listed terms (kernel-checked). -/
theorem A249151_data : (List.range 81).map A249151 =
    [1, 1, 2, 1, 4, 2, 6, 1, 2, 4, 10, 7, 12, 6, 4, 1, 16, 2, 18, 4, 6, 10, 22, 11, 4, 12, 2, 6,
      28, 25, 30, 1, 10, 16, 6, 36, 36, 18, 12, 40, 40, 6, 42, 10, 23, 22, 46, 19, 6, 4, 16, 12,
      52, 2, 10, 35, 18, 28, 58, 47, 60, 30, 63, 1, 12, 10, 66, 16, 22, 49, 70, 41, 72, 36, 4,
      18, 10, 12, 78, 80, 2] := by
  have : A249151 = A249151' := funext fun n => (A249151'_eq n).symm
  rw [this]
  decide +kernel

/-! ### The conjecture -/

/-- Conjecture (Karttunen, A249434 / A249151): A006093 (the numbers `prime(n) - 1`) is exactly
the set of `k` with `A249151(k) = k`. That is, for every `k ≥ 0`, `k` is the largest `m` such
that `m !` divides the product of the elements on row `k` of Pascal's triangle if and only if
`k + 1` is prime. -/
def statement : Prop :=
  ∀ k : ℕ, IsGreatest {m : ℕ | m ! ∣ rowProd k} k ↔ (k + 1).Prime

/-- The same statement phrased with the function `A249151`. -/
theorem statement_iff : statement ↔ ∀ k : ℕ, A249151 k = k ↔ (k + 1).Prime := by
  simp only [statement, A249151_eq_iff]

end Math0.Statements.A249434
