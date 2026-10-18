/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_9
import Math0.Audit

/-!
# Z-numbers form a set of Hausdorff dimension zero

Problem 10.9 of Bugeaud's *Distribution modulo one and Diophantine approximation* concerns
Mahler's Z-numbers: reals `ξ > 0` with `{ξ (3/2)^n} ∈ [0, 1/2)` for all `n ≥ 1`. The variant
`dimH_lt_one` records the theorem of Flatto, Lagarias and Pollington that the set of Z-numbers
has Hausdorff dimension `< 1`. We prove the (much stronger) classical fact, going back to
Mahler, that the set of Z-numbers is countable, hence of Hausdorff dimension `0 < 1`.
The key point: if `g_n = ⌊ξ (3/2)^n⌋` then the Z-number condition forces
`3 g_n ≤ 2 g_{n+1} ≤ 3 g_n + 1`, so `g_{n+1}` is determined by `g_n`; hence all `g_n` are
determined by `g_1`, and since `|ξ - η| (3/2)^n < 1/2` whenever `g_n(ξ) = g_n(η)`, the map
`ξ ↦ ⌊3ξ/2⌋` is injective on Z-numbers.
-/

namespace Math0.Bugeaud09

/-- If `x` and `3x/2` both have fractional part `< 1/2`, then `3⌊x⌋ ≤ 2⌊3x/2⌋ ≤ 3⌊x⌋ + 1`. -/
private lemma floor_bounds (x : ℝ) (hx : Int.fract x < 1 / 2) (hx' : Int.fract (x * (3 / 2)) < 1 / 2) :
    3 * ⌊x⌋ ≤ 2 * ⌊x * (3 / 2)⌋ ∧ 2 * ⌊x * (3 / 2)⌋ ≤ 3 * ⌊x⌋ + 1 := by
  rw [Int.fract] at hx hx'
  have h1 := Int.floor_le x
  have h2 := Int.floor_le (x * (3 / 2))
  constructor
  · have : ((3 * ⌊x⌋ - 2 * ⌊x * (3 / 2)⌋ : ℤ) : ℝ) < 1 := by push_cast; linarith
    have : (3 * ⌊x⌋ - 2 * ⌊x * (3 / 2)⌋ : ℤ) < 1 := by exact_mod_cast this
    omega
  · have : ((2 * ⌊x * (3 / 2)⌋ - 3 * ⌊x⌋ : ℤ) : ℝ) < 2 := by push_cast; linarith
    have : (2 * ⌊x * (3 / 2)⌋ - 3 * ⌊x⌋ : ℤ) < 2 := by exact_mod_cast this
    omega

/-- For two Z-numbers, the floors of `ξ (3/2)^n` agree for all `n ≥ 1` as soon as they agree
for `n = 1`. -/
private lemma floor_eq_of_floor_eq {ξ η : ℝ} (hξ : IsZNumber ξ) (hη : IsZNumber η)
    (h : ⌊ξ * (3 / 2)⌋ = ⌊η * (3 / 2)⌋) (m : ℕ) :
    ⌊ξ * (3 / 2) ^ (m + 1)⌋ = ⌊η * (3 / 2) ^ (m + 1)⌋ := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    have e1 : ξ * (3 / 2 : ℝ) ^ (m + 1 + 1) = ξ * (3 / 2) ^ (m + 1) * (3 / 2) := by ring
    have e2 : η * (3 / 2 : ℝ) ^ (m + 1 + 1) = η * (3 / 2) ^ (m + 1) * (3 / 2) := by ring
    have a := floor_bounds (ξ * (3 / 2) ^ (m + 1)) (hξ.2 _ (by omega)) (e1 ▸ hξ.2 _ (by omega))
    have b := floor_bounds (η * (3 / 2) ^ (m + 1)) (hη.2 _ (by omega)) (e2 ▸ hη.2 _ (by omega))
    rw [e1, e2]
    omega

/-- The map `ξ ↦ ⌊3ξ/2⌋` is injective on Z-numbers. -/
private lemma injOn_floor : Set.InjOn (fun ξ : ℝ => ⌊ξ * (3 / 2)⌋) {ξ : ℝ | IsZNumber ξ} := by
  intro ξ hξ η hη h
  change IsZNumber ξ at hξ
  change IsZNumber η at hη
  by_contra hne
  have hpos : 0 < |ξ - η| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (2 * |ξ - η|)) (by norm_num : (1 : ℝ) < 3 / 2)
  have hf := floor_eq_of_floor_eq hξ hη h n
  have fx := hξ.2 (n + 1) (by omega)
  have fy := hη.2 (n + 1) (by omega)
  rw [Int.fract] at fx fy
  have lx := Int.floor_le (ξ * (3 / 2) ^ (n + 1))
  have ly := Int.floor_le (η * (3 / 2) ^ (n + 1))
  rw [hf] at fx lx
  have hd : |ξ - η| * (3 / 2 : ℝ) ^ (n + 1) < 1 / 2 := by
    rw [← abs_of_pos (by positivity : (0 : ℝ) < (3 / 2) ^ (n + 1)), ← abs_mul, abs_lt, sub_mul]
    constructor <;> linarith
  have hpow : (3 / 2 : ℝ) ^ n ≤ (3 / 2) ^ (n + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  rw [div_lt_iff₀ (by positivity)] at hn
  nlinarith

/-- The set of Z-numbers is countable. -/
private lemma countable_zNumbers : {ξ : ℝ | IsZNumber ξ}.Countable :=
  (Set.mapsTo_univ _ _).countable_of_injOn injOn_floor Set.countable_univ

/-- The set of Z-numbers has Hausdorff dimension `< 1` (indeed `= 0`, being countable). -/
theorem dimH_lt_one : type_of% @Bugeaud09.problem_10_9.variants.dimH_lt_one := by
  rw [countable_zNumbers.dimH_zero]
  exact zero_lt_one

end Math0.Bugeaud09

#math0_proves Math0.Bugeaud09.dimH_lt_one Bugeaud09.problem_10_9.variants.dimH_lt_one
