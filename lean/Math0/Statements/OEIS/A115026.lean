/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A115026: no limiting value of the digit-power iteration exceeds 370

Source: https://oeis.org/A115026, Harvey P. Dale, Jun 08 2022 (COMMENTS section). Verbatim:
> Conjecture: no term is greater than 370. - _Harvey P. Dale_, Jun 08 2022

The sequence (offset `1`, by Sergio Pimentel) is "Limiting value of n under iteration of
"sum of the digits raised to the power of the number of digits of n" (A101337)", with the
comment "Iterate A101337 starting at n until reaching a constant value (like 370) or a cycle
(like 160, 217, 352, 160, ...). In the latter case, a(n) takes the smallest value in the cycle
(e.g., a(59) = 160)."

## Encoding

* `F m` is A101337: the sum of `d ^ L` over the decimal digits `d` of `m`, where `L` is the
  number of decimal digits of `m` (`Nat.digits 10 m`, so `F 0 = 0`; only `m ≥ 1` matters).
* The cycle that the orbit `n, F n, F (F n), …` ends in is `limitCycle n`: the values
  `F^[k] n` of the orbit that are periodic points of `F` (`F^[p] m = m` for some `p > 0`).
  A fixed point ("constant value") is a cycle of length one. `a n` is the smallest element of
  `limitCycle n`, as in the entry.
* `a` is computed by Floyd's cycle-finding loop (`meet`), which returns a periodic point `y` of
  the orbit, followed by a walk around the cycle of `y` that records its minimum (`cycleMin`).
  Both loops take a fuel argument `fuel n`. The fuel never runs out: every value of the orbit is
  at most `max n C` with `C = 70 * 9 ^ 70` (`iterate_le`, because `F m < m` once `m` has at
  least `70` digits), so by pigeonhole the orbit repeats within `max n C + 2` steps
  (`exists_meet`). The theorem `a_spec` proves, for every `n`, that `a n ∈ limitCycle n` and
  `a n ≤ m` for every `m ∈ limitCycle n`; so `a n` is exactly the OEIS definition.
  `a_data` checks all 65 listed terms `a 1, …, a 65`.
* The conjecture is about all terms of the sequence, i.e. all `n ≥ 1` (the offset is `1`):
  `∀ n ≥ 1, a n ≤ 370`.
-/

namespace Math0.Statements.A115026

/-- A101337: the sum of the decimal digits of `m`, each raised to the power (number of decimal
digits of `m`). -/
def F (m : ℕ) : ℕ := ((Nat.digits 10 m).map (· ^ (Nat.digits 10 m).length)).sum

/-- The cycle that the iteration of `F` starting at `n` eventually enters: the elements of the
orbit of `n` that are periodic points of `F`. -/
def limitCycle (n : ℕ) : Set ℕ :=
  {m | (∃ k, F^[k] n = m) ∧ ∃ p, 0 < p ∧ F^[p] m = m}

/-- Floyd's tortoise-and-hare loop: from `x = F^[k] n`, `z = F^[2k] n`, step `k ↦ k + 1` until
`x = z`, and return `x` (a periodic point of the orbit). -/
def meet : ℕ → ℕ → ℕ → ℕ
  | 0, x, _ => x
  | fuel + 1, x, z => if x = z then x else meet fuel (F x) (F (F z))

/-- Walk from `cur` along the orbit until `y` is reached again, keeping the running minimum `m`. -/
def cycleMin (y : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, m => m
  | fuel + 1, cur, m => if cur = y then m else cycleMin y fuel (F cur) (min m cur)

/-- A bound for `F` on numbers with fewer than `70` digits. -/
def C : ℕ := 70 * 9 ^ 70

/-- Enough fuel for both loops (see `exists_meet`). -/
def fuel (n : ℕ) : ℕ := (max n C + 2) ^ 2

/-- A115026: the smallest value of the cycle that the iteration of A101337 starting at `n`
ends in (see `a_spec`). -/
def a (n : ℕ) : ℕ :=
  let y := meet (fuel n) (F n) (F (F n))
  cycleMin y (fuel n) (F y) y

/-- The definition reproduces all 65 terms listed in OEIS, `a 1, …, a 65` (kernel-checked). -/
theorem a_data : (List.range 65).map (fun i => a (i + 1)) =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 5, 1, 370, 370, 370, 370, 370, 1, 4, 5, 8, 1, 4, 370, 370,
      370, 1, 370, 9, 1, 1, 370, 370, 370, 370, 370, 370, 370, 370, 370, 4, 370, 1, 370, 370,
      370, 370, 1, 370, 370, 370, 370, 370, 370, 370, 370, 370, 160, 370, 370, 370, 370, 370,
      370] := by
  decide +kernel

/-! ### `a n` is the smallest element of the limit cycle of `n` -/

/-- `F m ≤ L * 9 ^ L`, where `L` is the number of digits of `m`. -/
theorem F_le (m : ℕ) : F m ≤ (Nat.digits 10 m).length * 9 ^ (Nat.digits 10 m).length := by
  unfold F
  have h := List.sum_le_card_nsmul ((Nat.digits 10 m).map (· ^ (Nat.digits 10 m).length))
    (9 ^ (Nat.digits 10 m).length) (by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨d, hd, rfl⟩ := hx
      have := Nat.digits_lt_base (by norm_num) hd
      exact Nat.pow_le_pow_left (by omega) _)
  simpa using h

theorem key_ineq (L : ℕ) (hL : 70 ≤ L) : 10 * (L * 9 ^ L) < 10 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    have h1 : 9 * (L + 1) * 9 ^ L ≤ 10 * L * 9 ^ L := Nat.mul_le_mul_right _ (by omega)
    rw [pow_succ, pow_succ]
    nlinarith

/-- `F m ≤ max m C`. -/
theorem F_le_max (m : ℕ) : F m ≤ max m C := by
  have h1 := F_le m
  by_cases hm : (Nat.digits 10 m).length < 70
  · apply le_max_of_le_right
    calc F m ≤ (Nat.digits 10 m).length * 9 ^ (Nat.digits 10 m).length := h1
      _ ≤ 70 * 9 ^ 70 :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) (by omega))
  · apply le_max_of_le_left
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hm
    have h2 := Nat.base_pow_length_digits_le 10 m (by norm_num) hm0
    have h3 := key_ineq (Nat.digits 10 m).length (by omega)
    omega

/-- Every value of the orbit of `n` is at most `max n C`. -/
theorem iterate_le (n : ℕ) : ∀ k, F^[k] n ≤ max n C := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    calc F (F^[k] n) ≤ max (F^[k] n) C := F_le_max _
      _ ≤ max n C := max_le (le_trans ih le_rfl) (le_max_right _ _)

theorem meet_of_repeat (n i j : ℕ) (hij : i < j) (h : F^[i] n = F^[j] n) :
    F^[(j - i) * (i + 1)] n = F^[2 * ((j - i) * (i + 1))] n := by
  have hw : Function.IsPeriodicPt F (j - i) (F^[i] n) := by
    show F^[j - i] (F^[i] n) = F^[i] n
    rw [← Function.iterate_add_apply, show j - i + i = j by omega]
    exact h.symm
  have hK := hw.mul_const (i + 1)
  have hiK : i ≤ (j - i) * (i + 1) := by
    have : 1 ≤ j - i := by omega
    nlinarith
  have e1 : F^[(j - i) * (i + 1)] n = F^[(j - i) * (i + 1) - i] (F^[i] n) := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hiK]
  have e2 : F^[2 * ((j - i) * (i + 1))] n =
      F^[(j - i) * (i + 1) - i] (F^[(j - i) * (i + 1)] (F^[i] n)) := by
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
    congr 1
    omega
  rw [e1, e2, hK.eq]

/-- By pigeonhole, Floyd's loop meets within `fuel n` steps. -/
theorem exists_meet (n : ℕ) : ∃ K, 1 ≤ K ∧ K ≤ fuel n ∧ F^[K] n = F^[2 * K] n := by
  obtain ⟨i, hi, j, hj, hij, h⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (max n C + 2)) (t := Finset.range (max n C + 1))
    (f := fun k => F^[k] n) (by simp) (by
      intro k _
      simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (iterate_le n k))
  simp only [Finset.mem_range] at hi hj
  have bound : ∀ i j : ℕ, i < j → j < max n C + 2 →
      1 ≤ (j - i) * (i + 1) ∧ (j - i) * (i + 1) ≤ fuel n := by
    intro i j hij hj
    refine ⟨Nat.mul_pos (by omega) (by omega), ?_⟩
    unfold fuel
    rw [sq]
    exact Nat.mul_le_mul (by omega) (by omega)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact ⟨_, (bound i j hlt hj).1, (bound i j hlt hj).2, meet_of_repeat n i j hlt h⟩
  · exact ⟨_, (bound j i hlt hi).1, (bound j i hlt hi).2, meet_of_repeat n j i hlt h.symm⟩

theorem meet_spec (n : ℕ) : ∀ (f k K : ℕ), 1 ≤ k → k ≤ K → K - k < f →
    F^[K] n = F^[2 * K] n →
    ∃ k', 1 ≤ k' ∧ k' ≤ K ∧ meet f (F^[k] n) (F^[2 * k] n) = F^[k'] n ∧
      F^[k'] (F^[k'] n) = F^[k'] n := by
  intro f
  induction f with
  | zero => intro k K _ _ h; omega
  | succ f ih =>
    intro k K hk hkK hf hK
    simp only [meet]
    split_ifs with h
    · refine ⟨k, hk, hkK, rfl, ?_⟩
      rw [← Function.iterate_add_apply, ← two_mul]
      exact h.symm
    · have hkK' : k + 1 ≤ K := by
        rcases eq_or_lt_of_le hkK with rfl | h'
        · exact absurd hK h
        · exact h'
      obtain ⟨k', h1, h2, h3, h4⟩ := ih (k + 1) K (by omega) hkK' (by omega) hK
      have e1 : F^[k + 1] n = F (F^[k] n) := Function.iterate_succ_apply' _ _ _
      have e2 : F^[2 * (k + 1)] n = F (F (F^[2 * k] n)) := by
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Function.iterate_succ_apply',
          Function.iterate_succ_apply']
      rw [e1, e2] at h3
      exact ⟨k', h1, h2, h3, h4⟩

theorem cycleMin_spec (y p : ℕ) (hy : F^[p] y = y) : ∀ (f t m : ℕ), 1 ≤ t → t ≤ p →
    p - t < f → (∃ s, F^[s] y = m) → (∀ s < t, m ≤ F^[s] y) →
    (∃ s, F^[s] y = cycleMin y f (F^[t] y) m) ∧
      ∀ s, cycleMin y f (F^[t] y) m ≤ F^[s] y := by
  intro f
  induction f with
  | zero => intros; omega
  | succ f ih =>
    intro t m ht htp hf hm hmin
    simp only [cycleMin]
    split_ifs with h
    · refine ⟨hm, fun s => ?_⟩
      have hper : Function.IsPeriodicPt F t y := h
      rw [← hper.iterate_mod_apply]
      exact hmin _ (Nat.mod_lt _ (by omega))
    · have htp' : t + 1 ≤ p := by
        rcases eq_or_lt_of_le htp with rfl | h'
        · exact absurd hy h
        · exact h'
      have e : F (F^[t] y) = F^[t + 1] y := (Function.iterate_succ_apply' _ _ _).symm
      rw [e]
      apply ih (t + 1) (min m (F^[t] y)) (by omega) htp' (by omega)
      · rcases le_total m (F^[t] y) with hle | hle
        · rw [min_eq_left hle]
          exact hm
        · rw [min_eq_right hle]
          exact ⟨t, rfl⟩
      · intro s hs
        rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
        · exact le_trans (min_le_left _ _) (hmin s hs)
        · exact min_le_right _ _

/-- `a n` is the smallest element of the cycle that the iteration of `F` from `n` ends in. -/
theorem a_spec (n : ℕ) : a n ∈ limitCycle n ∧ ∀ m ∈ limitCycle n, a n ≤ m := by
  obtain ⟨K, hK1, hKf, hK⟩ := exists_meet n
  obtain ⟨k, hk1, hkK, hy, hper⟩ := meet_spec n (fuel n) 1 K le_rfl hK1 (by omega) hK
  have hy' : meet (fuel n) (F n) (F (F n)) = F^[k] n := hy
  obtain ⟨⟨s, hs⟩, hmin⟩ := cycleMin_spec (F^[k] n) k hper (fuel n) 1 (F^[k] n) le_rfl hk1
    (by omega) ⟨0, rfl⟩ (by
      intro s hs
      rw [show s = 0 by omega]
      exact le_rfl)
  have ha : a n = cycleMin (F^[k] n) (fuel n) (F^[1] (F^[k] n)) (F^[k] n) := by
    simp only [a, hy']
    rfl
  rw [ha]
  refine ⟨⟨⟨s + k, ?_⟩, k, hk1, ?_⟩, ?_⟩
  · rw [Function.iterate_add_apply, hs]
  · rw [← hs, ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hper]
  · rintro m ⟨⟨i, hi⟩, q, hq, hqm⟩
    have hm' : Function.IsPeriodicPt F (q * k) m :=
      (show Function.IsPeriodicPt F q m from hqm).mul_const k
    have hkq : k ≤ q * k := Nat.le_mul_of_pos_left k hq
    have : m = F^[q * k + i - k] (F^[k] n) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega), Function.iterate_add_apply,
        hi, hm'.eq]
    rw [this]
    exact hmin _

/-- Conjecture (Harvey P. Dale, 2022): no term of A115026 is greater than `370`, i.e. for every
`n ≥ 1`, the smallest value of the cycle that the iteration of A101337 starting at `n` enters is
at most `370`. -/
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → a n ≤ 370

end Math0.Statements.A115026
