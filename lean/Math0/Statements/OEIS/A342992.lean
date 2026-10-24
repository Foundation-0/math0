/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A342992: smallest multiple of `n` with only prime digits

Source: https://oeis.org/A342992, _Metin Sariyar_, Apr 13 2021 (COMMENTS section). Verbatim:
> Conjecture: a(n) > 0 for all n that are not divisible by 5.

The entry's name: "Smallest k such that k*n contains only prime digits, or 0 if no such k
exists." Offset `1`. Data: `2, 1, 1, 8, 1, 12, 1, 4, 3, 0, 2, 6, …` (81 terms, `n = 1, …, 81`).

## Encoding

* *Prime digits.* `PrimeDigits m`: `m > 0` and every decimal digit of `m` (`Nat.digits 10 m`)
  is a prime, i.e. lies in `{2, 3, 5, 7}`. The condition `m > 0` is needed because
  `Nat.digits 10 0 = []` would make `0` satisfy the digit condition vacuously, while `0`
  (written "0") has the non-prime digit `0`. In particular `k = 0` never qualifies, so the
  "smallest k" is automatically a positive integer, as in the entry (whose PARI program starts
  the search at `k = 1`).
* *The sequence.* `a n` is the least `k` with `PrimeDigits (k * n)` (`Nat.find`) if such `k`
  exists, and `0` otherwise. Existence is not decidable from the definition as written (it is
  an unbounded search), so `a` is noncomputable. `a_pos_iff` records that `0 < a n` holds
  exactly when some `k` with `PrimeDigits (k * n)` exists.
* *Data check.* The computable `aSearch n B` returns `some 0` when `n > 0` and `10 ∣ n` (then
  every positive multiple of `n` ends in the digit `0`, so no `k` exists), and otherwise the
  least `k < B` with `PrimeDigits (k * n)` (tested by the Boolean `primeDigitsB`), if any.
  `a_eq_of_aSearch` proves that `aSearch n B = some v` implies `a n = v`. `a_data` checks all 81
  listed terms (`n = 1, …, 81`) this way with `B = 100` (the largest listed term is `93`).
* *The conjecture.* `statement`: for every `n ≥ 1` (the entry's offset) with `5 ∤ n`,
  `a n > 0`. (The hypothesis `n ≥ 1` is the entry's range; it is redundant since `5 ∣ 0`.)
-/

namespace Math0.Statements.A342992

/-! ### Definitions -/

/-- `m` is positive and all its decimal digits are prime. -/
def PrimeDigits (m : ℕ) : Prop := 0 < m ∧ ∀ d ∈ Nat.digits 10 m, d.Prime

instance : DecidablePred PrimeDigits := fun m => by unfold PrimeDigits; infer_instance

open Classical in
/-- A342992: the smallest `k` such that `k * n` contains only prime digits, or `0` if no such
`k` exists (offset `1`). -/
noncomputable def a (n : ℕ) : ℕ :=
  if h : ∃ k, PrimeDigits (k * n) then Nat.find h else 0

/-- `a n > 0` exactly when some multiple `k * n` has only prime digits. -/
theorem a_pos_iff (n : ℕ) : 0 < a n ↔ ∃ k, PrimeDigits (k * n) := by
  constructor
  · intro h
    by_contra hne
    rw [a, dif_neg hne] at h
    exact lt_irrefl 0 h
  · intro h
    rw [a, dif_pos h]
    by_contra h0
    have h0' : Nat.find h = 0 := by omega
    have := Nat.find_spec h
    rw [h0', zero_mul] at this
    exact lt_irrefl 0 this.1

/-! ### Computable certificates -/

/-- Boolean version of `PrimeDigits` (see `primeDigitsB_iff`). -/
def primeDigitsB (m : ℕ) : Bool :=
  decide (0 < m) && (Nat.digits 10 m).all fun d => d == 2 || d == 3 || d == 5 || d == 7

theorem prime_iff_of_lt_ten {d : ℕ} (hd : d < 10) :
    d.Prime ↔ (d == 2 || d == 3 || d == 5 || d == 7) = true := by
  interval_cases d <;> norm_num

theorem primeDigitsB_iff (m : ℕ) : primeDigitsB m = true ↔ PrimeDigits m := by
  simp only [primeDigitsB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, PrimeDigits]
  refine and_congr Iff.rfl (forall₂_congr fun d hd => ?_)
  exact (prime_iff_of_lt_ten (Nat.digits_lt_base (by norm_num) hd)).symm

/-- If `n > 0` and `10 ∣ n`, then no multiple of `n` has only prime digits. -/
theorem not_exists_of_ten_dvd {n : ℕ} (h10 : 10 ∣ n) : ¬ ∃ k, PrimeDigits (k * n) := by
  rintro ⟨k, hpos, hd⟩
  have hmem : (k * n) % 10 ∈ Nat.digits 10 (k * n) := by
    rw [Nat.digits_def' (by norm_num) hpos]
    exact List.mem_cons_self
  have h0 : (k * n) % 10 = 0 := Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left h10 k)
  have := hd _ hmem
  rw [h0] at this
  exact Nat.not_prime_zero this

/-- `some 0` if `n > 0` and `10 ∣ n`; otherwise the least `k < B` such that `k * n` has only
prime digits, if there is one. -/
def aSearch (n B : ℕ) : Option ℕ :=
  if 0 < n ∧ n % 10 = 0 then some 0 else (List.range B).find? fun k => primeDigitsB (k * n)

theorem a_eq_of_aSearch {n B v : ℕ} (h : aSearch n B = some v) : a n = v := by
  unfold aSearch at h
  split_ifs at h with h10
  · rw [Option.some.injEq] at h
    subst h
    rw [a, dif_neg (not_exists_of_ten_dvd (Nat.dvd_of_mod_eq_zero h10.2))]
  · rw [List.find?_range_eq_some] at h
    obtain ⟨hv, -, hlt⟩ := h
    have hv' : PrimeDigits (v * n) := (primeDigitsB_iff _).1 hv
    have hex : ∃ k, PrimeDigits (k * n) := ⟨v, hv'⟩
    rw [a, dif_pos hex, Nat.find_eq_iff]
    refine ⟨hv', fun j hj hjP => ?_⟩
    have := hlt j hj
    rw [(primeDigitsB_iff _).2 hjP] at this
    exact absurd this (by decide)

theorem map_a_eq_of_aSearch {B : ℕ} :
    ∀ {l D : List ℕ}, l.map (fun i => aSearch i B) = D.map some → l.map a = D
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | i :: l, d :: D, h => by
    simp only [List.map_cons, List.cons.injEq] at h ⊢
    exact ⟨a_eq_of_aSearch h.1, map_a_eq_of_aSearch h.2⟩

/-- The entry's example: `a(4) = 8`, since `8 * 4 = 32`. -/
theorem a_four : a 4 = 8 := a_eq_of_aSearch (B := 9) (by decide +kernel)

/-- The definition reproduces all 81 terms listed in OEIS (`n = 1, …, 81`, kernel-checked). -/
theorem a_data : (List.range 81).map (fun i => a (i + 1)) =
    [2, 1, 1, 8, 1, 12, 1, 4, 3, 0, 2, 6, 4, 18, 5, 2, 15, 4, 3, 0, 12, 1, 1, 3, 1, 2, 1, 9, 8,
      0, 12, 1, 1, 8, 1, 2, 1, 14, 7, 0, 13, 6, 54, 8, 5, 7, 5, 49, 15, 0, 5, 1, 1, 43, 1, 42, 1,
      4, 43, 0, 12, 6, 4, 43, 5, 42, 5, 4, 8, 0, 5, 1, 1, 3, 1, 7, 1, 74, 3, 0, 93] := by
  rw [show (fun i => a (i + 1)) = a ∘ (fun i => i + 1) from rfl, ← List.map_map]
  exact map_a_eq_of_aSearch (B := 100) (by decide +kernel)

/-! ### The conjecture -/

/-- Conjecture (Sariyar, A342992): `a(n) > 0` for every `n ≥ 1` not divisible by `5`, i.e. every
such `n` has a positive multiple all of whose decimal digits are prime. -/
def statement : Prop := ∀ n : ℕ, 1 ≤ n → ¬ 5 ∣ n → 0 < a n

end Math0.Statements.A342992
