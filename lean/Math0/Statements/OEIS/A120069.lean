/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A120069: denominators of `∑_{k=1}^{n} C(k)/4^(k-1)` (Groux's and Staunton's conjectures)

Source: https://oeis.org/A120069, _Groux Roland_, Dec 11 2010 and _Alexander Staunton_,
Feb 28 2026 (FORMULA section). Verbatim:
> Conjecture: a(n) = denominator(Catalan(n)/4^(n-1)). - _Groux Roland_, Dec 11 2010
>
> Conjecture: a(n) = 2^(A283208(n)-2). - _Alexander Staunton_, Feb 28 2026

The sequence (offset `1`, by _Wolfdieter Lang_) is "Denominators of partial sums of a convergent
series involving scaled Catalan numbers A000108", where (COMMENTS/FORMULA) "The partial sums
r(n) = Sum_{k=1..n} C(k)/2^(2*(k-1)) are rationals (written in lowest terms)", `C = ` A000108
(Catalan numbers), and "a(n) = denominator(r(n))".

A283208 (offset `0`) is defined in its COMMENTS section: "a(n) is the least nonnegative integer
such that 2^a(n) (2n+1)/(n+1) c(2n) is a nonnegative integer, where c(2n) = c(2n-1) =
Pochhammer(1/2,n)/(n!)" (Vietoris' numbers).

## Encoding

* `r n : ℚ` is `∑_{k=1}^{n} C(k)/2^(2(k-1))` computed exactly in `ℚ` with Mathlib's `catalan`
  (`k ≥ 1`, so `k - 1` is exact). Mathlib's `Rat` is always in lowest terms with positive
  denominator, so `a n = (r n).den` is A120069's `a(n)` for `n ≥ 1`. (`a 0 = 1`, the denominator
  of the empty sum, is not a term of the sequence and plays no role.) For the kernel, `catalan` is
  replaced by the provably equal `catFast` (`catFast_eq`), and `a_data` checks all 27 listed
  terms `a 1, …, a 27`.
* `pochhammer x n = x (x+1) ⋯ (x+n-1)` is the rising factorial (Mathematica's `Pochhammer`);
  `pochhammer_eq_ascPochhammer` shows it is Mathlib's `ascPochhammer ℚ n` evaluated at `x`.
  `vietoris n = Pochhammer(1/2, n)/n!` is `c(2n)`, and `w n = (2n+1)/(n+1) · c(2n)`.
* `IsNatExp n e` says `2^e · (2n+1)/(n+1) · c(2n)` is a nonnegative integer (literally: equals
  `(m : ℚ)` for some `m : ℕ`). It is decidable (`exists_natCast_iff`), it holds for `e = 2n`
  (`isNatExp_two_mul`, via `4^n c(2n) = C(2n, n)` and `(n+1) ∣ C(2n, n)`), so
  `A283208 n = Nat.find …` is the least such `e`, exactly A283208's definition. `A283208_data`
  checks all 63 listed terms `A283208 0, …, A283208 62` (kernel-checked through
  `A283208_eq_of`, which uses that `IsNatExp n` is upward closed).
* *The conjecture.* Both conjectures are about the terms of A120069, i.e. `n ≥ 1`. Groux:
  `a n = (C(n)/4^(n-1)).den` (with `n - 1` exact for `n ≥ 1`). Staunton:
  `a(n) = 2^(A283208(n) - 2)`, stated in `ℚ` with an integer exponent,
  `(a n : ℚ) = 2 ^ ((A283208 n : ℤ) - 2)`, so that no truncated natural subtraction is involved.
  `statement` is the conjunction of the two, for every `n ≥ 1`.
-/

namespace Math0.Statements.A120069

open Finset

/-! ### A120069 -/

/-- The partial sum `r(n) = ∑_{k=1}^{n} C(k)/2^(2(k-1))`, `C(k)` the Catalan numbers (A000108),
computed exactly in `ℚ`. -/
def r (n : ℕ) : ℚ := ∑ k ∈ Finset.Icc 1 n, (catalan k : ℚ) / 2 ^ (2 * (k - 1))

/-- A120069 (offset `1`): `a(n)` is the denominator of `r(n) = ∑_{k=1}^{n} C(k)/2^(2(k-1))`
(in lowest terms). -/
def a (n : ℕ) : ℕ := (r n).den

/-- Catalan numbers by the recursion `C(k+1) = 2(2k+1) C(k)/(k+2)` (fast in the kernel). -/
def catFast : ℕ → ℕ
  | 0 => 1
  | k + 1 => catFast k * (2 * (2 * k + 1)) / (k + 2)

theorem succ_succ_mul_catalan (k : ℕ) :
    (k + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
  have h1 := succ_mul_catalan_eq_centralBinom (k + 1)
  have h2 := succ_mul_catalan_eq_centralBinom k
  have h3 := Nat.succ_mul_centralBinom_succ k
  apply Nat.eq_of_mul_eq_mul_left (show 0 < k + 1 by omega)
  calc (k + 1) * ((k + 2) * catalan (k + 1)) = (k + 1) * (k + 1).centralBinom := by
        rw [← h1]
    _ = 2 * (2 * k + 1) * ((k + 1) * catalan k) := by rw [h3, h2]
    _ = (k + 1) * (2 * (2 * k + 1) * catalan k) := by ring

theorem catFast_eq : ∀ k : ℕ, catFast k = catalan k
  | 0 => by simp [catFast]
  | k + 1 => by
    rw [catFast, catFast_eq k, Nat.mul_comm, ← succ_succ_mul_catalan,
      Nat.mul_div_cancel_left _ (by omega)]

/-- `r` computed with `catFast`. -/
def rFast (n : ℕ) : ℚ := ∑ k ∈ Finset.Icc 1 n, (catFast k : ℚ) / 2 ^ (2 * (k - 1))

theorem r_eq_rFast (n : ℕ) : r n = rFast n := by
  simp [r, rFast, catFast_eq]

/-- The definition reproduces all 27 terms listed in OEIS (`n = 1, …, 27`; kernel-checked). -/
theorem a_data : (List.range 27).map (fun i => a (i + 1)) =
    [1, 2, 16, 32, 128, 256, 4096, 8192, 32768, 65536, 524288, 1048576, 4194304, 8388608,
      268435456, 536870912, 2147483648, 4294967296, 34359738368, 68719476736, 274877906944,
      549755813888, 8796093022208, 17592186044416, 70368744177664, 140737488355328,
      1125899906842624] := by
  have : a = fun n => (rFast n).den := funext fun n => by simp [a, r_eq_rFast]
  rw [this]
  decide +kernel

/-! ### A283208 -/

/-- The rising factorial (Pochhammer symbol) `(x)_n = x (x+1) ⋯ (x+n-1)`. -/
def pochhammer (x : ℚ) (n : ℕ) : ℚ := ∏ i ∈ Finset.range n, (x + i)

/-- `pochhammer` is Mathlib's `ascPochhammer`. -/
theorem pochhammer_eq_ascPochhammer (x : ℚ) (n : ℕ) :
    pochhammer x n = (ascPochhammer ℚ n).eval x := by
  induction n with
  | zero => simp [pochhammer]
  | succ n ih => rw [pochhammer, Finset.prod_range_succ, ← pochhammer, ih, ascPochhammer_succ_eval]

/-- Vietoris' number `c(2n) = c(2n-1) = Pochhammer(1/2, n)/n!`. -/
def vietoris (n : ℕ) : ℚ := pochhammer (1 / 2) n / (n.factorial : ℚ)

/-- `(2n+1)/(n+1) · c(2n)`. -/
def w (n : ℕ) : ℚ := (2 * n + 1) / (n + 1) * vietoris n

/-- `2^e · (2n+1)/(n+1) · c(2n)` is a nonnegative integer. -/
def IsNatExp (n e : ℕ) : Prop := ∃ m : ℕ, (2 : ℚ) ^ e * w n = m

theorem exists_natCast_iff (q : ℚ) : (∃ m : ℕ, q = m) ↔ q.den = 1 ∧ 0 ≤ q := by
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨Rat.den_natCast m, Nat.cast_nonneg m⟩
  · rintro ⟨h1, h2⟩
    refine ⟨q.num.toNat, ?_⟩
    have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr h2
    have hq : (q.num : ℚ) = q := Rat.coe_int_num_of_den_eq_one h1
    rw [← hq]
    have : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg hnum
    exact_mod_cast this.symm

instance (n : ℕ) : DecidablePred (IsNatExp n) := fun e =>
  decidable_of_iff _ (exists_natCast_iff ((2 : ℚ) ^ e * w n)).symm

/-- `4^n c(2n) = C(2n, n)`. -/
theorem four_pow_mul_vietoris (n : ℕ) : (4 : ℚ) ^ n * vietoris n = n.centralBinom := by
  induction n with
  | zero => simp [vietoris, pochhammer]
  | succ n ih =>
    have h3 := Nat.succ_mul_centralBinom_succ n
    have hcb : ((n + 1).centralBinom : ℚ) = 2 * (2 * n + 1) * n.centralBinom / (n + 1) := by
      rw [eq_div_iff (by positivity)]
      exact_mod_cast (by rw [mul_comm]; exact h3 :
        (n + 1).centralBinom * (n + 1) = 2 * (2 * n + 1) * n.centralBinom)
    rw [hcb, ← ih]
    simp only [vietoris, pochhammer, Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_succ, pow_succ]
    field_simp
    ring

theorem isNatExp_two_mul (n : ℕ) : IsNatExp n (2 * n) := by
  refine ⟨(2 * n + 1) * (n.centralBinom / (n + 1)), ?_⟩
  rw [Nat.cast_mul, Nat.cast_div (Nat.succ_dvd_centralBinom n) (by positivity), w, pow_mul,
    show ((2 : ℚ) ^ 2) = 4 by norm_num, ← four_pow_mul_vietoris]
  push_cast
  field_simp

/-- A283208 (offset `0`): the least nonnegative integer `e` such that `2^e (2n+1)/(n+1) c(2n)`
is a nonnegative integer, `c(2n) = Pochhammer(1/2, n)/n!`. -/
def A283208 (n : ℕ) : ℕ := Nat.find ⟨2 * n, isNatExp_two_mul n⟩

theorem isNatExp_succ {n e : ℕ} (h : IsNatExp n e) : IsNatExp n (e + 1) := by
  obtain ⟨m, hm⟩ := h
  exact ⟨2 * m, by rw [pow_succ, mul_comm ((2 : ℚ) ^ e), mul_assoc, hm]; push_cast; ring⟩

theorem isNatExp_mono {n e f : ℕ} (h : IsNatExp n e) (hef : e ≤ f) : IsNatExp n f := by
  induction f, hef using Nat.le_induction with
  | base => exact h
  | succ f _ ih => exact isNatExp_succ ih

theorem A283208_eq_of {n v : ℕ} (h1 : IsNatExp n v) (h2 : v = 0 ∨ ¬ IsNatExp n (v - 1)) :
    A283208 n = v := by
  rw [A283208, Nat.find_eq_iff]
  refine ⟨h1, fun m hm hP => ?_⟩
  rcases h2 with h2 | h2
  · omega
  · exact h2 (isNatExp_mono hP (by omega))

/-- Boolean check that `v` is the least exponent for `n`. -/
def checkA283208 (n v : ℕ) : Bool :=
  decide (IsNatExp n v) && (v == 0 || !decide (IsNatExp n (v - 1)))

theorem A283208_eq_of_check {n v : ℕ} (h : checkA283208 n v = true) : A283208 n = v := by
  simp only [checkA283208, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true', decide_eq_false_iff_not] at h
  exact A283208_eq_of h.1 h.2

theorem map_eq_of_check {f : ℕ → ℕ} {c : ℕ → ℕ → Bool} (hc : ∀ n v, c n v = true → f n = v)
    {N : ℕ} {L : List ℕ} (hN : L.length = N) (h : ∀ i < L.length, c i (L.getD i 0) = true) :
    (List.range N).map f = L := by
  subst hN
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_map, List.getElem_range]
  have := h i h2
  rw [List.getD_eq_getElem _ _ h2] at this
  exact hc _ _ this

/-- The definition of A283208 reproduces all 63 terms listed in OEIS (`n = 0, …, 62`;
kernel-checked). -/
theorem A283208_data : (List.range 63).map A283208 =
    [0, 2, 3, 6, 7, 9, 10, 14, 15, 17, 18, 21, 22, 24, 25, 30, 31, 33, 34, 37, 38, 40, 41, 45, 46,
      48, 49, 52, 53, 55, 56, 62, 63, 65, 66, 69, 70, 72, 73, 77, 78, 80, 81, 84, 85, 87, 88, 93,
      94, 96, 97, 100, 101, 103, 104, 108, 109, 111, 112, 115, 116, 118, 119] := by
  refine map_eq_of_check (c := checkA283208) (fun _ _ h => A283208_eq_of_check h) rfl ?_
  decide +kernel

/-! ### The conjecture -/

/-- Conjectures (Groux 2010, Staunton 2026, A120069): for every `n ≥ 1`,
`a(n) = denominator(Catalan(n)/4^(n-1))` and `a(n) = 2^(A283208(n) - 2)`. -/
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    a n = ((catalan n : ℚ) / 4 ^ (n - 1)).den ∧
      (a n : ℚ) = (2 : ℚ) ^ ((A283208 n : ℤ) - 2)

end Math0.Statements.A120069
