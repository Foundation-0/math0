/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A116184: `n` with `37^3` dividing the numerator of `∑_{k=1}^{36} 1/k^n`

Source: https://oeis.org/A116184, _Alexander Adamchuk_, Apr 08 2007. Verbatim (COMMENTS
section):
> Conjecture: All terms of the arithmetic progression 3+36k belong to a(n). Prime terms in a(n)
> are {3, 37, 73, 443, 739, 887, 1109, ...}. It appears that all primes in a(n) that are greater
> than 37 are of the form 37k-1.

The sequence (offset `1`) is "Numbers n such that 37^3 divides the numerator of generalized
harmonic number H(36,n) = Sum[ 1/k^n, {k,1,36} ]." The entry's Mathematica program scans
`n = 1, …, 1000`.

## Encoding

* `H n : ℚ` is the generalized harmonic number `H(36, n) = ∑_{k=1}^{36} 1/k^n`, computed exactly
  in `ℚ`; its numerator is `(H n).num` (Mathlib's `Rat.num`, in lowest terms; `H n > 0`).
* `IsTerm n`: `37^3 ∣ (H n).num`, i.e. `n` is a term of A116184. (`n = 0` is not a term:
  `H 0 = 36`; see `not_isTerm_zero`. So the terms are exactly the positive `n` with the
  property, as in the entry.)
* `a n = Nat.nth IsTerm (n - 1)` is the `n`-th smallest term (offset `1`), noncomputable as
  written. `exists_a_eq_iff` shows that a positive integer `x` occurs as some `a m` (`m ≥ 1`)
  iff `IsTerm x`, so "belongs to a(n)" / "primes in a(n)" are expressed with `IsTerm`.
* *Decidability.* Since `37` is prime and `37 > 36`, `H n = S / 36!^n` with
  `S = ∑_{k=1}^{36} (36!/k)^n` and `gcd(37, 36!^n) = 1`, so `37^3 ∣ (H n).num ↔ 37^3 ∣ S`
  (`isTerm_iff_check`); `S mod 37^3` is computed from the residues `36!/k mod 37^3`. This gives a
  `DecidablePred IsTerm` instance, and `a_data` checks all 53 listed terms (all members `≤ 975`)
  by a kernel-checked `List.filter`.
* *The conjecture* (both claims of the comment): `statement` is the conjunction of
  (a) `IsTerm (3 + 36k)` for every `k ≥ 0` (the progression `3, 39, 75, …` starts at the term
  `3`), and (b) every prime term `p > 37` is of the form `37k - 1`, written `p = 37 * k - 1` for
  some `k : ℕ` (natural subtraction is harmless: `k = 0` gives `0`, and for `k ≥ 1` this is
  `37 ∣ p + 1`). The list of prime terms quoted in between is a data example, not part of the
  claim.
-/

namespace Math0.Statements.A116184

/-! ### Definitions -/

/-- The generalized harmonic number `H(36, n) = ∑_{k=1}^{36} 1/k^n`, computed exactly in `ℚ`. -/
def H (n : ℕ) : ℚ := ∑ k ∈ Finset.Icc (1 : ℕ) 36, 1 / ((k : ℚ) ^ n)

/-- `n` is a term of A116184: `37^3` divides the numerator of `H(36, n)`. -/
def IsTerm (n : ℕ) : Prop := (37 ^ 3 : ℤ) ∣ (H n).num

/-! ### A fast decision procedure -/

/-- The residues `36!/k mod 37^3` for `k = 1, …, 36` (`37^3 = 50653`). -/
def coeffs : List ℕ :=
  [23531, 37092, 24728, 18546, 35098, 12364, 25070, 9273, 25127, 17549, 6744, 6182, 21292, 12535,
    45468, 29963, 46078, 37890, 25232, 34101, 25241, 3372, 7630, 3091, 47542, 10646, 25260, 31594,
    13038, 22734, 4027, 40308, 2248, 23039, 5014, 18945]

theorem coeffs_eq :
    coeffs = (List.range 36).map (fun i => Nat.factorial 36 / (i + 1) % 50653) := by
  decide +kernel

/-- `∑_{k=1}^{36} (36!/k)^n ≡ 0 (mod 37^3)`, computed with small residues. -/
def check (n : ℕ) : Bool := (coeffs.map (fun c => c ^ n % 50653)).sum % 50653 == 0

theorem sum_range_eq_list_sum (f : ℕ → ℕ) (N : ℕ) :
    ∑ i ∈ Finset.range N, f i = ((List.range N).map f).sum := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]
    simp

theorem sum_Icc_eq_list_sum (g : ℕ → ℕ) :
    ∑ k ∈ Finset.Icc 1 36, g k = ((List.range 36).map (fun i => g (i + 1))).sum := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, sum_range_eq_list_sum]
  simp [Nat.add_comm 1]

/-- `H(36, n) = (∑_{k=1}^{36} (36!/k)^n) / 36!^n`. -/
theorem H_eq (n : ℕ) :
    H n = ((∑ k ∈ Finset.Icc 1 36, (Nat.factorial 36 / k) ^ n : ℕ) : ℚ) /
      ((Nat.factorial 36 ^ n : ℕ) : ℚ) := by
  have hF : ((Nat.factorial 36 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [H, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hk36⟩ := Finset.mem_Icc.mp hk
  have hkd : k ∣ Nat.factorial 36 := Nat.dvd_factorial hk1 hk36
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_div hkd hk0, div_pow]
  field_simp

/-- If `q = s / b` with `b` coprime to `37`, then `37^3 ∣ q.num ↔ 37^3 ∣ s`. -/
theorem dvd_num_iff (q : ℚ) (s b : ℕ) (hb : b ≠ 0) (hcop : Nat.Coprime (37 ^ 3) b)
    (hq : q = (s : ℚ) / (b : ℚ)) :
    (37 ^ 3 : ℤ) ∣ q.num ↔ (37 ^ 3 : ℤ) ∣ (s : ℤ) := by
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  -- `q.num * b = s * q.den`
  have key : q.num * (b : ℤ) = (s : ℤ) * (q.den : ℤ) := by
    have h1 : (q.num : ℚ) / (q.den : ℚ) = (s : ℚ) / (b : ℚ) := by rw [Rat.num_div_den, hq]
    have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    rw [div_eq_div_iff hd hb'] at h1
    exact_mod_cast h1
  -- `q.den ∣ b`
  have hden : (q.den : ℤ) ∣ (b : ℤ) := by
    have : q = Rat.divInt (s : ℤ) (b : ℤ) := by
      rw [hq, Rat.divInt_eq_div]; push_cast; rfl
    have h := Rat.den_dvd (s : ℤ) (b : ℤ)
    rwa [← this] at h
  have hcopZ : IsCoprime ((37 ^ 3 : ℕ) : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  push_cast at hcopZ
  have hcopD : IsCoprime (37 ^ 3 : ℤ) (q.den : ℤ) := hcopZ.of_isCoprime_of_dvd_right hden
  constructor
  · intro h
    have : (37 ^ 3 : ℤ) ∣ (s : ℤ) * (q.den : ℤ) := key ▸ dvd_mul_of_dvd_left h _
    exact hcopD.dvd_of_dvd_mul_right this
  · intro h
    have : (37 ^ 3 : ℤ) ∣ q.num * (b : ℤ) := key ▸ dvd_mul_of_dvd_left h _
    exact hcopZ.dvd_of_dvd_mul_right this

theorem isTerm_iff_check (n : ℕ) : IsTerm n ↔ check n = true := by
  have h37 : Nat.Coprime 37 (Nat.factorial 36) :=
    (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr
      (by rw [Nat.Prime.dvd_factorial (by norm_num)]; norm_num)
  have hcop : Nat.Coprime (37 ^ 3) (Nat.factorial 36 ^ n) := Nat.Coprime.pow 3 n h37
  rw [IsTerm, dvd_num_iff (H n) _ _ (by positivity) hcop (H_eq n)]
  rw [show ((37 : ℤ) ^ 3) = ((37 ^ 3 : ℕ) : ℤ) by norm_num, Int.natCast_dvd_natCast,
    Nat.dvd_iff_mod_eq_zero, Finset.sum_nat_mod]
  simp only [Nat.pow_mod (Nat.factorial 36 / _)]
  rw [sum_Icc_eq_list_sum, check, coeffs_eq, List.map_map]
  simp [Function.comp_def]

instance : DecidablePred IsTerm := fun n => decidable_of_iff _ (isTerm_iff_check n).symm

/-! ### The sequence -/

/-- A116184: the `n`-th smallest (offset `1`) number `m` such that `37^3` divides the numerator
of `H(36, m) = ∑_{k=1}^{36} 1/k^m`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- `0` is not a term (`H(36, 0) = 36`). -/
theorem not_isTerm_zero : ¬ IsTerm 0 := by decide +kernel

/-- A positive integer occurs in the sequence iff it satisfies the defining property. -/
theorem exists_a_eq_iff {x : ℕ} (hx : x ≠ 0) : (∃ m, 1 ≤ m ∧ a m = x) ↔ IsTerm x := by
  constructor
  · rintro ⟨m, -, hm⟩
    have h : Nat.nth IsTerm (m - 1) ≠ 0 := by rw [← a, hm]; exact hx
    have := Nat.nth_mem_of_ne_zero h
    rwa [← a, hm] at this
  · intro h
    exact ⟨Nat.count IsTerm x + 1, by omega, by simp [a, Nat.nth_count h]⟩

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

/-- The definition reproduces all 53 terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 53).map (fun i => a (i + 1)) =
    [3, 37, 39, 73, 75, 111, 147, 148, 183, 185, 219, 221, 255, 259, 291, 295, 327, 333, 363,
      369, 399, 407, 435, 443, 471, 481, 507, 517, 543, 555, 579, 591, 615, 629, 651, 665, 687,
      703, 723, 739, 759, 777, 795, 813, 831, 851, 867, 887, 903, 925, 939, 961, 975] := by
  have : (fun i => a (i + 1)) = Nat.nth IsTerm := funext fun i => by simp [a]
  rw [this]
  exact map_nth_eq_of_filter (N := 976) (by decide +kernel) rfl

/-! ### The conjecture -/

/-- Conjecture (Adamchuk, A116184): (a) every term `3 + 36k` (`k ≥ 0`) of the arithmetic
progression belongs to the sequence, and (b) every prime term greater than `37` is of the form
`37k - 1`. -/
def statement : Prop :=
  (∀ k : ℕ, IsTerm (3 + 36 * k)) ∧
    (∀ p : ℕ, p.Prime → 37 < p → IsTerm p → ∃ k : ℕ, p = 37 * k - 1)

end Math0.Statements.A116184
