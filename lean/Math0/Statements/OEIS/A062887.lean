/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A062887: multiples of `2n+1` with odd digits descending by 2 (mod 10)

Source: https://oeis.org/A062887, Sean A. Irvine, Apr 14 2023 (COMMENTS section). Verbatim:
> Conjecture: The only numbers n for which a(n)=0 are those for which 2*n+1 is divisible by 125.

The entry (Amarnath Murthy, Jun 28 2001, offset `0`) is "Smallest multiple of 2n+1 with the
property that its digits are odd and each digit is two less (mod 10) than the previous digit, or
0 if no such number exists." Data: `1, 3, 5, 7, 9, 319, 975, 75, 7531, 19, 197531975319, …`
(26 terms, `n = 0, …, 25`).

## Encoding

* *The digit property.* `IsDesc2 N`: `N > 0`, every decimal digit of `N` is odd, and, reading
  the digits from left to right (most significant first, `(Nat.digits 10 N).reverse`), each
  digit `next` is two less (mod 10) than the previous digit `prev`, i.e.
  `next + 2 ≡ prev [MOD 10]`. Examples: `975`, `75`, `319`, `1`, `9753197`. The condition
  `N > 0` is needed because `Nat.digits 10 0 = []` would make `0` satisfy the digit conditions
  vacuously, while `0` (written "0") does not have odd digits; it is also not a meaningful
  "smallest multiple".
* *The sequence.* `a n` is the least `N` with `IsDesc2 N` and `2n+1 ∣ N` if such `N` exists
  (`Nat.find`), and `0` otherwise. Existence is not known to be decidable from the definition,
  so `a` is noncomputable as written.
* *Data check.* `gen x L` is the little-endian digit list `[x, x+2, x+4, …] (mod 10)` of length
  `L`. We prove that the numbers with `IsDesc2` are exactly the `Nat.ofDigits 10 (gen x L)` with
  `x ∈ {1,3,5,7,9}`, `L ≥ 1` (`isDesc2_ofDigits_gen`, `exists_gen_of_isDesc2`). The computable
  `aSearch n B` takes the least multiple of `2n+1` among these numbers with at most `B` digits;
  `a_eq_of_aSearch` shows that whenever it returns `some v`, `a n = v` (any smaller element has
  at most as many digits). `a_data` checks all 26 listed terms (`n = 0, …, 25`) this way, with
  `B = 18` (the largest listed term has 18 digits).
* *The conjecture.* "The only numbers `n` for which `a(n) = 0` are those for which `2n+1` is
  divisible by `125`" is read as the set equality `{n | a n = 0} = {n | 125 ∣ 2n+1}`:
  `statement` is `∀ n, a n = 0 ↔ 125 ∣ 2 * n + 1`, over the entry's full range `n ≥ 0`.
-/

namespace Math0.Statements.A062887

/-! ### Definitions -/

/-- `N` is positive, its decimal digits are odd, and (reading from left to right) each digit is
two less (mod 10) than the previous digit. -/
def IsDesc2 (N : ℕ) : Prop :=
  0 < N ∧ (∀ d ∈ Nat.digits 10 N, Odd d) ∧
    (Nat.digits 10 N).reverse.IsChain (fun prev next => next + 2 ≡ prev [MOD 10])

instance : DecidablePred IsDesc2 := fun N => by unfold IsDesc2; infer_instance

open Classical in
/-- A062887: the smallest multiple of `2n+1` whose digits are odd and each digit is two less
(mod 10) than the previous digit, or `0` if no such number exists (offset `0`). -/
noncomputable def a (n : ℕ) : ℕ :=
  if h : ∃ N, IsDesc2 N ∧ 2 * n + 1 ∣ N then Nat.find h else 0

/-! ### Computable description of the numbers with the digit property -/

/-- The little-endian digit list `[x, x+2, x+4, …]` (mod 10) of length `L`. -/
def gen : ℕ → ℕ → List ℕ
  | _, 0 => []
  | x, L + 1 => x :: gen ((x + 2) % 10) L

theorem length_gen (x L : ℕ) : (gen x L).length = L := by
  induction L generalizing x with
  | zero => rfl
  | succ L ih => simp [gen, ih]

theorem gen_lt (x L : ℕ) (hx : x < 10) : ∀ d ∈ gen x L, d < 10 := by
  induction L generalizing x with
  | zero => simp [gen]
  | succ L ih =>
    intro d hd
    simp only [gen, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact hx
    · exact ih _ (Nat.mod_lt _ (by norm_num)) d hd

theorem gen_odd (x L : ℕ) (hx : Odd x) : ∀ d ∈ gen x L, Odd d := by
  induction L generalizing x with
  | zero => simp [gen]
  | succ L ih =>
    intro d hd
    simp only [gen, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact hx
    · refine ih _ ?_ d hd
      rw [Nat.odd_iff] at hx ⊢
      omega

theorem gen_chain (x L : ℕ) :
    (gen x L).IsChain (fun p q => p + 2 ≡ q [MOD 10]) := by
  induction L generalizing x with
  | zero => simp [gen]
  | succ L ih =>
    cases L with
    | zero => simp [gen]
    | succ L =>
      simp only [gen] at ih ⊢
      rw [List.isChain_cons_cons]
      exact ⟨(Nat.mod_modEq _ _).symm, ih _⟩

theorem gen_of_chain : ∀ (l : List ℕ) (x : ℕ), (∀ d ∈ x :: l, d < 10) →
    (x :: l).IsChain (fun p q => p + 2 ≡ q [MOD 10]) → x :: l = gen x (l.length + 1)
  | [], x, _, _ => rfl
  | y :: l, x, hlt, hc => by
    rw [List.isChain_cons_cons] at hc
    have hy : y = (x + 2) % 10 := by
      have h1 : (x + 2) % 10 = y % 10 := hc.1
      have h2 : y < 10 := hlt y (by simp)
      rw [Nat.mod_eq_of_lt h2] at h1
      exact h1.symm
    have ih := gen_of_chain l y (fun d hd => hlt d (List.mem_cons_of_mem _ hd)) hc.2
    subst hy
    rw [List.length_cons, gen, ← ih]

theorem digits_ofDigits_gen (x L : ℕ) (hx : x < 10) (hodd : Odd x) :
    Nat.digits 10 (Nat.ofDigits 10 (gen x L)) = gen x L := by
  apply Nat.digits_ofDigits 10 (by norm_num) _ (gen_lt x L hx)
  intro h hz
  have := gen_odd x L hodd _ (List.getLast_mem h)
  rw [hz] at this
  exact absurd this (by decide)

/-- Every `Nat.ofDigits 10 (gen x L)` with `x` an odd digit and `L ≥ 1` has the digit
property. -/
theorem isDesc2_ofDigits_gen (x L : ℕ) (hx : x < 10) (hodd : Odd x) (hL : 1 ≤ L) :
    IsDesc2 (Nat.ofDigits 10 (gen x L)) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    have : 1 ≤ x := by rw [Nat.odd_iff] at hodd; omega
    simp only [gen, Nat.ofDigits_cons]
    omega
  · rw [digits_ofDigits_gen x L hx hodd]
    exact gen_odd x L hodd
  · rw [digits_ofDigits_gen x L hx hodd, List.isChain_reverse]
    exact gen_chain x L

/-- Every number with the digit property is `Nat.ofDigits 10 (gen x L)` with `x` an odd digit,
where `L ≥ 1` is its number of digits. -/
theorem exists_gen_of_isDesc2 {N : ℕ} (h : IsDesc2 N) :
    ∃ x L, x < 10 ∧ Odd x ∧ 1 ≤ L ∧ Nat.digits 10 N = gen x L := by
  obtain ⟨hpos, hodd, hc⟩ := h
  rw [List.isChain_reverse] at hc
  have hlt : ∀ d ∈ Nat.digits 10 N, d < 10 := fun d hd => Nat.digits_lt_base (by norm_num) hd
  cases hds : Nat.digits 10 N with
  | nil => exact absurd hds (Nat.digits_ne_nil_iff_ne_zero.2 (by omega))
  | cons x l =>
    rw [hds] at hc hlt hodd
    refine ⟨x, l.length + 1, hlt x (by simp), hodd x (by simp), by omega, ?_⟩
    exact gen_of_chain l x hlt hc

/-- All numbers with the digit property and at most `B` digits. -/
def cands (B : ℕ) : List ℕ :=
  (List.range B).flatMap fun L => [1, 3, 5, 7, 9].map fun x => Nat.ofDigits 10 (gen x (L + 1))

/-- The least multiple of `2n+1` among the numbers with the digit property and at most `B`
digits, if there is one. -/
def aSearch (n B : ℕ) : Option ℕ :=
  ((cands B).filter fun c => c % (2 * n + 1) == 0).min?

theorem mem_cands {B c : ℕ} :
    c ∈ cands B ↔ ∃ L < B, ∃ x ∈ [1, 3, 5, 7, 9], Nat.ofDigits 10 (gen x (L + 1)) = c := by
  simp only [cands, List.mem_flatMap, List.mem_range, List.mem_map]

theorem a_eq_of_aSearch {n B v : ℕ} (h : aSearch n B = some v) : a n = v := by
  rw [aSearch, List.min?_eq_some_iff] at h
  obtain ⟨hv, hmin⟩ := h
  rw [List.mem_filter, mem_cands] at hv
  obtain ⟨⟨L, hL, x, hx, rfl⟩, hdvd⟩ := hv
  have hx' : x < 10 ∧ Odd x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
  have hdvd' : 2 * n + 1 ∣ Nat.ofDigits 10 (gen x (L + 1)) :=
    Nat.dvd_of_mod_eq_zero (by simpa using hdvd)
  have hex : ∃ N, IsDesc2 N ∧ 2 * n + 1 ∣ N :=
    ⟨_, isDesc2_ofDigits_gen x (L + 1) hx'.1 hx'.2 (by omega), hdvd'⟩
  rw [a, dif_pos hex, Nat.find_eq_iff]
  refine ⟨⟨isDesc2_ofDigits_gen x (L + 1) hx'.1 hx'.2 (by omega), hdvd'⟩, ?_⟩
  rintro k hk ⟨hkD, hkdvd⟩
  obtain ⟨y, M, hy, hyodd, hM, hdk⟩ := exists_gen_of_isDesc2 hkD
  have hlen : M ≤ L + 1 := by
    have := Nat.le_length_digits_le 10 k _ hk.le
    rw [hdk, digits_ofDigits_gen x (L + 1) hx'.1 hx'.2, length_gen, length_gen] at this
    exact this
  have hkeq : Nat.ofDigits 10 (gen y M) = k := by rw [← hdk, Nat.ofDigits_digits]
  have hy' : y ∈ [1, 3, 5, 7, 9] := by
    have : ∀ y < 10, Odd y → y ∈ [1, 3, 5, 7, 9] := by decide
    exact this y hy hyodd
  have hkmem : k ∈ (cands B).filter fun c => c % (2 * n + 1) == 0 := by
    rw [List.mem_filter, mem_cands]
    refine ⟨⟨M - 1, by omega, y, hy', ?_⟩, ?_⟩
    · rw [Nat.sub_add_cancel hM, hkeq]
    · simpa using Nat.mod_eq_zero_of_dvd hkdvd
  have := hmin k hkmem
  omega

theorem map_a_eq_of_aSearch {B : ℕ} :
    ∀ {l D : List ℕ}, l.map (fun i => aSearch i B) = D.map some → l.map a = D
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | i :: l, d :: D, h => by
    simp only [List.map_cons, List.cons.injEq] at h ⊢
    exact ⟨a_eq_of_aSearch h.1, map_a_eq_of_aSearch h.2⟩

/-- The entry's example: `975 = 13 · 75` has the digit property. -/
theorem example_975 : IsDesc2 975 ∧ 13 ∣ 975 := by
  refine ⟨?_, by norm_num⟩
  have := isDesc2_ofDigits_gen 5 3 (by norm_num) (by decide) (by norm_num)
  simpa [gen, Nat.ofDigits] using this

/-- The definition reproduces all 26 terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 26).map (fun i => a (i + 0)) =
    [1, 3, 5, 7, 9, 319, 975, 75, 7531, 19, 197531975319, 3197, 75, 5319, 319, 31,
      3197531975319, 53197531975, 1975319, 975, 531975, 1975319753197, 19753197531975,
      75319753197531, 319753197531975319, 753197531975319753] := by
  simp only [Nat.add_zero]
  exact map_a_eq_of_aSearch (B := 18) (by decide +kernel)

/-! ### The conjecture -/

/-- Conjecture (Irvine, A062887): `a(n) = 0` exactly for those `n` with `125 ∣ 2n+1`. -/
def statement : Prop := ∀ n : ℕ, a n = 0 ↔ 125 ∣ 2 * n + 1

end Math0.Statements.A062887
