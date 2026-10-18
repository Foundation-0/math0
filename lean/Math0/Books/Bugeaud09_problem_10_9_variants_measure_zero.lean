/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_9
import Math0.Audit

/-!
# Mahler's Z-numbers form a null set (Bugeaud, Problem 10.9, measure-zero variant)

A Z-number is a real `ξ > 0` with `{ξ (3/2)^n} ∈ [0, 1/2)` for every `n ≥ 1`; Mahler [Mah68]
asked whether any exist (Bugeaud, *Distribution modulo one and Diophantine approximation*,
Problem 10.9). We prove exactly the formal statement
`Bugeaud09.problem_10_9.variants.measure_zero`: the set of Z-numbers has Lebesgue measure zero.
Following Mahler, put `g_n = ⌊ξ (3/2)^n⌋`. Since `{ξ (3/2)^n} < 1/2` for all `n ≥ 1`, we get
`3 g_n ≤ 2 g_{n+1} ≤ 3 g_n + 1`, so `g_{n+1}` is determined by `g_n`. Hence two Z-numbers with
the same `g_1` have all `g_n` equal, so `|ξ - η| (3/2)^n < 1` for all `n` and `ξ = η`. Thus
`ξ ↦ ⌊3ξ/2⌋` is injective on Z-numbers, the set is countable, and countable sets are null.
-/

namespace Math0.Bugeaud09

/-- Mahler's recurrence: for a Z-number `ξ` and `n ≥ 1`, with `g_n = ⌊ξ (3/2)^n⌋`,
we have `3 g_n ≤ 2 g_{n+1} ≤ 3 g_n + 1`. -/
lemma floor_step {ξ : ℝ} (hξ : IsZNumber ξ) {n : ℕ} (hn : 1 ≤ n) :
    3 * ⌊ξ * (3 / 2 : ℝ) ^ n⌋ ≤ 2 * ⌊ξ * (3 / 2 : ℝ) ^ (n + 1)⌋ ∧
    2 * ⌊ξ * (3 / 2 : ℝ) ^ (n + 1)⌋ ≤ 3 * ⌊ξ * (3 / 2 : ℝ) ^ n⌋ + 1 := by
  have h1 := hξ.2 n hn
  have h2 := hξ.2 (n + 1) (by omega)
  have hx' : ξ * (3 / 2 : ℝ) ^ (n + 1) = 3 / 2 * (ξ * (3 / 2 : ℝ) ^ n) := by
    rw [pow_succ]; ring
  rw [hx'] at h2 ⊢
  generalize ξ * (3 / 2 : ℝ) ^ n = x at h1 h2 ⊢
  have ha := Int.floor_le x
  have hb := Int.floor_le (3 / 2 * x)
  rw [Int.fract] at h1 h2
  constructor
  · have h : ((3 * ⌊x⌋ : ℤ) : ℝ) < ((2 * ⌊3 / 2 * x⌋ + 1 : ℤ) : ℝ) := by
      push_cast; linarith
    have := Int.cast_lt.mp h
    omega
  · have h : ((2 * ⌊3 / 2 * x⌋ : ℤ) : ℝ) < ((3 * ⌊x⌋ + 2 : ℤ) : ℝ) := by
      push_cast; linarith
    have := Int.cast_lt.mp h
    omega

/-- Two Z-numbers with the same `⌊ξ (3/2)⌋` have the same `⌊ξ (3/2)^n⌋` for every `n ≥ 1`. -/
lemma floor_eq_of_floor_one_eq {ξ η : ℝ} (hξ : IsZNumber ξ) (hη : IsZNumber η)
    (h1 : ⌊ξ * (3 / 2 : ℝ) ^ 1⌋ = ⌊η * (3 / 2 : ℝ) ^ 1⌋) :
    ∀ n, 1 ≤ n → ⌊ξ * (3 / 2 : ℝ) ^ n⌋ = ⌊η * (3 / 2 : ℝ) ^ n⌋ := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact h1
  | succ n hn ih =>
    have := floor_step hξ hn
    have := floor_step hη hn
    omega

/-- Mahler: a Z-number is determined by `⌊ξ (3/2)⌋`. -/
lemma injOn_floor :
    Set.InjOn (fun ξ : ℝ => ⌊ξ * (3 / 2 : ℝ) ^ 1⌋) {ξ : ℝ | IsZNumber ξ} := by
  intro ξ hξ η hη h1
  have hall := floor_eq_of_floor_one_eq hξ hη h1
  by_contra hne
  have hpos : 0 < |ξ - η| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / |ξ - η|) (by norm_num : (1 : ℝ) < 3 / 2)
  have hle : (3 / 2 : ℝ) ^ n ≤ (3 / 2 : ℝ) ^ (n + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
  have hlt := Int.abs_sub_lt_one_of_floor_eq_floor (hall (n + 1) (by omega))
  rw [← sub_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (3 / 2) ^ (n + 1))] at hlt
  have : 1 < |ξ - η| * (3 / 2 : ℝ) ^ (n + 1) := by
    rw [div_lt_iff₀ hpos] at hn
    nlinarith
  linarith

/-- The set of Z-numbers is countable. -/
lemma countable_zNumbers : {ξ : ℝ | IsZNumber ξ}.Countable :=
  (Set.mapsTo_univ _ _).countable_of_injOn injOn_floor Set.countable_univ

/-- Mahler (1968): the set of Z-numbers has Lebesgue measure zero. -/
theorem measure_zero : type_of% @Bugeaud09.problem_10_9.variants.measure_zero :=
  countable_zNumbers.measure_zero _

end Math0.Bugeaud09

#math0_proves Math0.Bugeaud09.measure_zero Bugeaud09.problem_10_9.variants.measure_zero
