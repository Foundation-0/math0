/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A097154: 0 and 89 are the only fixed points of reverse(x) - maxdigit(x)

Source: https://oeis.org/A097154, Jason Earls, Aug 01 2004 (COMMENTS section). Verbatim:
> a(89)=-1 because 89 is the first number that will not reach zero: 98-9=89. It is conjectured
> that 0 and 89 are the only fixed points of f.

The entry's name: "Number of iterations of f(x) = reverse(x) - maxdigit(x) needed to reach zero,
or -1 if zero is never reached, where maxdig(n) is the largest digit of n." Offset `1`; keyword
`sign` (the value `-1` occurs). The same conjecture is repeated in A097155 and A097157.

## Encoding

* `rev x` is the decimal reversal of `x`: `Nat.ofDigits 10 (Nat.digits 10 x).reverse`, so
  trailing zeros of `x` become dropped leading zeros (`rev 120 = 21`) and `rev 0 = 0`.
* `maxDigit x` is the largest decimal digit of `x` (`maxDigit 0 = 0`, the digit of `0`).
* `f x = rev x - maxDigit x`. This is truncated subtraction on `ℕ`, but it never truncates:
  `maxDigit_le_rev` proves `maxDigit x ≤ rev x`, and `f_eq_int` restates `f` with integer
  subtraction. So `f` is the entry's map on the nonnegative integers (with `f 0 = 0`).
* The sequence (offset `1`, values in `ℤ` because of `-1`): `a n` is the least `k` with
  `f^[k] n = 0`, or `-1` if there is none. To keep `a` computable it searches only
  `k ≤ 10 ^ d`, where `d` is the number of digits of `n`. `a_spec` proves this is no restriction:
  `a n = if h : ∃ k, f^[k] n = 0 then Nat.find h else -1`. The reason is that `f` maps
  `[0, 10^d)` into itself, and the iterates before the first `0` are pairwise distinct.
  `a_data` kernel-checks all 127 listed terms `a 1, …, a 127`, including `a 89 = -1`.
* The conjecture: for every `x ≥ 0`, `f x = x` holds iff `x = 0` or `x = 89`.
-/

namespace Math0.Statements.A097154

/-- `reverse(x)`: the number whose decimal digits are those of `x` in reverse order
(`rev 120 = 21`, `rev 0 = 0`). -/
def rev (x : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 x).reverse

/-- `maxdigit(x)`: the largest decimal digit of `x` (`maxDigit 0 = 0`). -/
def maxDigit (x : ℕ) : ℕ := (Nat.digits 10 x).foldr max 0

/-- `f(x) = reverse(x) - maxdigit(x)`. (The subtraction never truncates; see
`maxDigit_le_rev`.) -/
def f (x : ℕ) : ℕ := rev x - maxDigit x

theorem le_ofDigits_of_mem : ∀ (l : List ℕ) (d : ℕ), d ∈ l → d ≤ Nat.ofDigits 10 l
  | [], d, h => by simp at h
  | e :: l, d, h => by
    rw [Nat.ofDigits_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := le_ofDigits_of_mem l d h
      omega

theorem foldr_max_le : ∀ (l : List ℕ) (c : ℕ), (∀ d ∈ l, d ≤ c) → l.foldr max 0 ≤ c
  | [], c, _ => Nat.zero_le c
  | e :: l, c, h => by
    simp only [List.foldr_cons]
    exact max_le (h e List.mem_cons_self)
      (foldr_max_le l c fun d hd => h d (List.mem_cons_of_mem e hd))

/-- The largest digit never exceeds the reversal, so `f` is an honest subtraction. -/
theorem maxDigit_le_rev (x : ℕ) : maxDigit x ≤ rev x :=
  foldr_max_le _ _ fun d hd => le_ofDigits_of_mem _ d (List.mem_reverse.2 hd)

/-- `f x = reverse(x) - maxdigit(x)` as an integer. -/
theorem f_eq_int (x : ℕ) : (f x : ℤ) = (rev x : ℤ) - (maxDigit x : ℤ) := by
  have := maxDigit_le_rev x
  simp only [f]
  omega

/-- The entry's example `12 → 19 → 82 → 20 → 0`, and the fixed points `0` and `89`
(`98 - 9 = 89`). -/
theorem f_examples :
    f 12 = 19 ∧ f 19 = 82 ∧ f 82 = 20 ∧ f 20 = 0 ∧ f 0 = 0 ∧ rev 89 = 98 ∧ maxDigit 89 = 9 ∧
      f 89 = 89 := by
  decide +kernel

/-- `search x k fuel` follows the orbit `x, f x, f (f x), …` for at most `fuel` steps. It returns
`k + j` for the least `j ≤ fuel` with `f^[j] x = 0`, and `-1` if there is no such `j`. -/
def search : ℕ → ℕ → ℕ → ℤ
  | x, k, 0 => if x = 0 then (k : ℤ) else -1
  | x, k, fuel + 1 => if x = 0 then (k : ℤ) else search (f x) (k + 1) fuel

/-- A097154 (offset `1`): the number of iterations of `f` needed to reach zero, or `-1` if zero
is never reached. The search bound `10 ^ (number of digits of n)` loses nothing (`a_spec`). -/
def a (n : ℕ) : ℤ := search n 0 (10 ^ (Nat.digits 10 n).length)

/-- The definition reproduces all 127 terms listed in OEIS, `a 1, …, a 127` (kernel-checked). -/
theorem a_data : (List.range 127).map (fun i => a (i + 1)) =
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 5, 3, 3, 3, 3, 1, 2, 2, 4, 4, 6, 5, 3, 3, 3, 1, 2,
      2, 2, 4, 4, 7, 3, 3, 3, 1, 2, 2, 2, 2, 4, 4, 5, 3, 3, 1, 2, 2, 2, 2, 2, 4, 6, 3, 3, 1, 2, 2,
      2, 2, 2, 2, 4, 5, 3, 1, 2, 2, 2, 2, 2, 2, 2, 4, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, -1, 1, 2, 2, 2,
      2, 2, 2, 2, 2, 2, 1, 2, 6, 6, 9, 7, 8, 8, 10, 7, 2, 3, 10, 7, 8, 9, 3, 3, 3, 3, 4, 4, 4, 4,
      4, 8, 4, 4] := by
  decide +kernel

/-! ### The search bound is no restriction -/

theorem search_of_zero : ∀ (fuel x k j : ℕ), j ≤ fuel → f^[j] x = 0 →
    (∀ i < j, f^[i] x ≠ 0) → search x k fuel = ((k + j : ℕ) : ℤ) := by
  intro fuel
  induction fuel with
  | zero =>
    intro x k j hj hz _
    obtain rfl : j = 0 := by omega
    simp only [Function.iterate_zero, id_eq] at hz
    simp [search, hz]
  | succ fuel ih =>
    intro x k j hj hz hmin
    by_cases hx : x = 0
    · have hj0 : j = 0 := by
        by_contra hne
        exact hmin 0 (Nat.pos_of_ne_zero hne) (by simpa using hx)
      subst hj0
      simp [search, hx]
    · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := by
        rcases j with _ | j
        · simp at hz
          exact absurd hz hx
        · exact ⟨j, rfl⟩
      rw [search, if_neg hx]
      rw [Function.iterate_succ_apply] at hz
      rw [ih (f x) (k + 1) j (by omega) hz fun i hi => by
        have := hmin (i + 1) (by omega)
        rwa [Function.iterate_succ_apply] at this]
      push_cast
      ring

theorem search_of_ne : ∀ (fuel x k : ℕ), (∀ i ≤ fuel, f^[i] x ≠ 0) → search x k fuel = -1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro x k h
    have := h 0 le_rfl
    simp only [Function.iterate_zero, id_eq] at this
    simp [search, this]
  | succ fuel ih =>
    intro x k h
    have hx := h 0 (Nat.zero_le _)
    simp only [Function.iterate_zero, id_eq] at hx
    rw [search, if_neg hx]
    exact ih (f x) (k + 1) fun i hi => by
      have := h (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this

theorem f_lt {x L : ℕ} (h : x < 10 ^ L) : f x < 10 ^ L := by
  have h1 : rev x < 10 ^ (Nat.digits 10 x).length := by
    have := Nat.ofDigits_lt_base_pow_length (b := 10) (l := (Nat.digits 10 x).reverse)
      (by norm_num) (fun d hd => Nat.digits_lt_base (by norm_num) (List.mem_reverse.1 hd))
    simpa [rev] using this
  have h2 : (Nat.digits 10 x).length ≤ L := (Nat.digits_length_le_iff (by norm_num) x).2 h
  have h3 : 10 ^ (Nat.digits 10 x).length ≤ 10 ^ L := Nat.pow_le_pow_right (by norm_num) h2
  unfold f
  omega

theorem iterate_lt {x L : ℕ} (h : x < 10 ^ L) : ∀ i, f^[i] x < 10 ^ L
  | 0 => h
  | i + 1 => by
    rw [Function.iterate_succ_apply']
    exact f_lt (iterate_lt h i)

/-- If the orbit of `n` reaches `0`, it does so within `10 ^ (number of digits of n)` steps. -/
theorem find_lt {n : ℕ} (h : ∃ k, f^[k] n = 0) :
    Nat.find h < 10 ^ (Nat.digits 10 n).length := by
  have hn : n < 10 ^ (Nat.digits 10 n).length := Nat.lt_base_pow_length_digits (by norm_num)
  have hk0 : f^[Nat.find h] n = 0 := Nat.find_spec h
  have key : ∀ i j, i < j → j ≤ Nat.find h → f^[i] n = f^[j] n → False := by
    intro i j hij hj he
    have e : f^[Nat.find h] n = f^[Nat.find h - j + i] n := by
      rw [show Nat.find h = Nat.find h - j + j by omega, Function.iterate_add_apply, ← he,
        ← Function.iterate_add_apply]
      congr 1
      omega
    exact Nat.find_min h (m := Nat.find h - j + i) (by omega) (e ▸ hk0)
  have hcard := Finset.card_le_card_of_injOn (fun i => f^[i] n)
    (s := Finset.range (Nat.find h + 1)) (t := Finset.range (10 ^ (Nat.digits 10 n).length))
    (fun i _ => by
      simp only [Finset.coe_range, Set.mem_Iio]
      exact iterate_lt hn i)
    (by
      intro i hi j hj hij
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact key i j hlt (by omega) hij
      · exact key j i hlt (by omega) hij.symm)
  simp only [Finset.card_range] at hcard
  omega

open Classical in
/-- `a` is the OEIS definition: the least `k` with `f^[k] n = 0`, or `-1` if there is none. -/
theorem a_spec (n : ℕ) : a n = if h : ∃ k, f^[k] n = 0 then (Nat.find h : ℤ) else -1 := by
  unfold a
  split_ifs with h
  · rw [search_of_zero _ n 0 (Nat.find h) (find_lt h).le (Nat.find_spec h)
      fun i hi => Nat.find_min h hi]
    simp
  · simp only [not_exists] at h
    exact search_of_ne _ n 0 fun i _ => h i

/-- The conjecture (Earls): `0` and `89` are the only fixed points of
`f(x) = reverse(x) - maxdigit(x)` on the nonnegative integers. -/
def statement : Prop :=
  ∀ x : ℕ, f x = x ↔ x = 0 ∨ x = 89

end Math0.Statements.A097154
