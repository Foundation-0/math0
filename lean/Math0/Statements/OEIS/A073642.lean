/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A073642: sum of the positions of the 1-bits of `n` (Yanev's identity)

Source: https://oeis.org/A073642, Velin Yanev, Sep 09 2017 (FORMULA section). Verbatim:
> Conjecture: a(n) = (3*A011371(n) - Sum_{k=1..n} A007814(k)^2)/2 for n > 0.

The sequence (offset `0`, Benoit Cloitre, Aug 29 2002) is "Replace 2^k in the binary
representation of n with k (i.e., if n = 2^b + 2^c + 2^d + ... then a(n) = b + c + d + ...)."
The two sequences referred to in the conjecture are
* A011371 (offset `0`): "a(n) = n minus (number of 1's in binary expansion of n). Also highest
  power of 2 dividing n!.";
* A007814 (offset `1`): "Exponent of highest power of 2 dividing n, a.k.a. the binary carry
  sequence, the ruler sequence, or the 2-adic valuation of n."

## Encoding

* `a n` is the sum of `Nat.bitIndices n`, the list of exponents `b < c < d < ⋯` with
  `n = 2^b + 2^c + 2^d + ⋯` (Mathlib: `Nat.sum_map_two_pow_bitIndices`,
  `Nat.mem_bitIndices`). `a_sum_two_pow` proves that `a` is exactly the OEIS definition: for
  every finite set `s` of exponents, `a (∑ i ∈ s, 2 ^ i) = ∑ i ∈ s, i` (every `n` has exactly
  one such representation). `a_data` checks all 88 listed terms `a 0, …, a 87`.
* `A011371 n = n - (number of 1's among the binary digits Nat.digits 2 n)` is the primary OEIS
  definition of A011371; `A011371_eq_padicValNat_factorial` proves that it also equals
  `padicValNat 2 n!` (the second description, Legendre's formula). `A011371_data` checks all
  73 listed terms of A011371 (`n = 0, …, 72`).
* `A007814 k = padicValNat 2 k` is the 2-adic valuation; it is only used for `k ≥ 1`, where it
  is the exponent of the highest power of `2` dividing `k`. `A007814_data` checks all 111
  listed terms of A007814 (`k = 1, …, 111`).
* The conjecture is stated for every `n > 0`, as in the entry. The right-hand side is read
  literally as a rational number, `(3 * A011371(n) - ∑_{k=1}^{n} A007814(k)^2) / 2` computed in
  `ℚ` (so neither the subtraction nor the division is truncated, and the claim includes that
  this number is the natural number `a(n)`).
* `rhs_data` is a sanity check of the encoding (not part of the statement): for `n = 1, …, 87`
  the integer `3 * A011371(n) - ∑_{k=1}^{n} A007814(k)^2` equals twice the listed term `a(n)`.
-/

namespace Math0.Statements.A073642

/-- A073642: replace `2^k` in the binary representation of `n` with `k`, i.e. if
`n = 2^b + 2^c + 2^d + ⋯` (distinct exponents) then `a(n) = b + c + d + ⋯`. Here
`Nat.bitIndices n` is the increasing list of these exponents. -/
def a (n : ℕ) : ℕ := (Nat.bitIndices n).sum

/-- A011371: `n` minus the number of 1's in the binary expansion of `n`. -/
def A011371 (n : ℕ) : ℕ := n - (Nat.digits 2 n).count 1

/-- A007814: the exponent of the highest power of `2` dividing `n` (the 2-adic valuation). -/
def A007814 (n : ℕ) : ℕ := padicValNat 2 n

/-! ### The definitions match the OEIS definitions -/

/-- The OEIS definition of A073642: if `n = ∑ i ∈ s, 2 ^ i` for a finite set `s` of exponents,
then `a(n) = ∑ i ∈ s, i`. -/
theorem a_sum_two_pow (s : Finset ℕ) : a (∑ i ∈ s, 2 ^ i) = ∑ i ∈ s, i := by
  have h := Finset.toFinset_bitIndices_sum_two_pow s
  conv_rhs => rw [← h]
  rw [List.sum_toFinset _ Nat.bitIndices_sorted.nodup, List.map_id']
  rfl

/-- Binary digits are `0` or `1`, so their sum is the number of 1's. -/
theorem count_one_digits_two (n : ℕ) : (Nat.digits 2 n).count 1 = (Nat.digits 2 n).sum := by
  have h : ∀ L : List ℕ, (∀ x ∈ L, x < 2) → L.count 1 = L.sum := by
    intro L
    induction L with
    | nil => simp
    | cons x L ih =>
      intro hL
      have hx := hL x (by simp)
      rw [List.count_cons, List.sum_cons, ih (fun y hy => hL y (by simp [hy]))]
      interval_cases x <;> (simp; try omega)
  exact h _ (fun x hx => Nat.digits_lt_base (by norm_num) hx)

/-- The second description of A011371: it is the exponent of the highest power of `2`
dividing `n!`. -/
theorem A011371_eq_padicValNat_factorial (n : ℕ) : A011371 n = padicValNat 2 n.factorial := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  rw [show (2 - 1) = 1 from rfl, one_mul] at h
  rw [A011371, count_one_digits_two, h]

/-! ### Data checks -/

/-- The definition reproduces all 88 terms listed in OEIS, `a 0, …, a 87` (kernel-checked). -/
theorem a_data : (List.range 88).map (fun i => a (i + 0)) =
    [0, 0, 1, 1, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 6, 6, 4, 4, 5, 5, 6, 6, 7, 7, 7, 7, 8, 8, 9, 9,
      10, 10, 5, 5, 6, 6, 7, 7, 8, 8, 8, 8, 9, 9, 10, 10, 11, 11, 9, 9, 10, 10, 11, 11, 12, 12,
      12, 12, 13, 13, 14, 14, 15, 15, 6, 6, 7, 7, 8, 8, 9, 9, 9, 9, 10, 10, 11, 11, 12, 12, 10,
      10, 11, 11, 12, 12, 13, 13] := by
  decide +kernel

/-- `A011371` reproduces all 73 terms listed in OEIS A011371, `n = 0, …, 72` (kernel-checked). -/
theorem A011371_data : (List.range 73).map (fun i => A011371 (i + 0)) =
    [0, 0, 1, 1, 3, 3, 4, 4, 7, 7, 8, 8, 10, 10, 11, 11, 15, 15, 16, 16, 18, 18, 19, 19, 22, 22,
      23, 23, 25, 25, 26, 26, 31, 31, 32, 32, 34, 34, 35, 35, 38, 38, 39, 39, 41, 41, 42, 42, 46,
      46, 47, 47, 49, 49, 50, 50, 53, 53, 54, 54, 56, 56, 57, 57, 63, 63, 64, 64, 66, 66, 67, 67,
      70] := by
  decide +kernel

/-- `A007814` reproduces all 111 terms listed in OEIS A007814, `k = 1, …, 111`
(kernel-checked). -/
theorem A007814_data : (List.range 111).map (fun i => A007814 (i + 1)) =
    [0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,
      5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1,
      0, 6, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0,
      1, 0, 5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] := by
  decide +kernel

/-- Sanity check of the encoding of the right-hand side: for `n = 1, …, 87`, the integer
`3 * A011371(n) - ∑_{k=1}^{n} A007814(k)^2` is twice the listed term `a(n)` (kernel-checked). -/
theorem rhs_data : (List.range 87).map (fun i =>
      3 * (A011371 (i + 1) : ℤ) - ∑ k ∈ Finset.Icc 1 (i + 1), (A007814 k : ℤ) ^ 2) =
    ([0, 1, 1, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 6, 6, 4, 4, 5, 5, 6, 6, 7, 7, 7, 7, 8, 8, 9, 9,
      10, 10, 5, 5, 6, 6, 7, 7, 8, 8, 8, 8, 9, 9, 10, 10, 11, 11, 9, 9, 10, 10, 11, 11, 12, 12,
      12, 12, 13, 13, 14, 14, 15, 15, 6, 6, 7, 7, 8, 8, 9, 9, 9, 9, 10, 10, 11, 11, 12, 12, 10,
      10, 11, 11, 12, 12, 13, 13] : List ℤ).map (2 * ·) := by
  decide +kernel

/-! ### The conjecture -/

/-- Conjecture (Velin Yanev, 2017): for every `n > 0`,
`a(n) = (3 * A011371(n) - ∑_{k=1}^{n} A007814(k)^2) / 2`. -/
def statement : Prop :=
  ∀ n : ℕ, 0 < n →
    (a n : ℚ) = (3 * (A011371 n : ℚ) - ∑ k ∈ Finset.Icc 1 n, (A007814 k : ℚ) ^ 2) / 2

end Math0.Statements.A073642
