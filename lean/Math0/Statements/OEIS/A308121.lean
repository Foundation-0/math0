/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A308121: row 2n is row n with its halves swapped, for odd n

Source: https://oeis.org/A308121, Charlie Neder, Jun 05 2019 (COMMENTS section). Verbatim:
> Conjecture: If n is odd, then row 2n can be obtained from row n by interchanging the first and
> second halves.

The entry (Jamie Morken, May 13 2019; offset `1`, keywords `sign,tabf`) is the "Irregular
triangle read by rows: T(n,k) = A109395(n)*k-A076512(n)*A038566(n,k)", with the comment "Row n has
length A000010(n)."

## Encoding

* `totatives n` is row `n` of A038566 ("triangle in which n-th row gives phi(n) numbers between 1
  and n that are relatively prime to n"): the numbers `r` with `1 ≤ r ≤ n` and `gcd(r, n) = 1`, in
  increasing order. For `n = 1` this is `[1]`, matching A038566's first row; for `n ≥ 2` it is the
  list of totatives in `[1, n-1]`.
* `A109395 n` is the denominator and `A076512 n` the numerator of the reduced fraction
  `phi(n)/n`, computed literally as `Rat.den` and `Rat.num` of `(Nat.totient n : ℚ) / n`
  (as in the names of A109395 and A076512).
* `T n k = A109395(n) * k - A076512(n) * A038566(n, k)` in `ℤ` (the sequence is signed), for
  `n ≥ 1` and `1 ≤ k ≤ phi(n)`; `A038566(n, k)` is the `k`-th entry of `totatives n` (1-based).
* `row n` is the list `[T(n,1), …, T(n, phi(n))]` (row `n` has length `A000010(n)`).
* `a_data` checks, in the kernel, that rows `1..15` concatenated are exactly the 72 listed terms
  (`%S`, `%T`, `%U`), i.e. `a(1), …, a(72)` of the flattened sequence. `T_210_2` checks the
  worked example `T(210,2) = -18` from the entry.
* *The conjecture.* "Row 2n can be obtained from row n by interchanging the first and second
  halves" is encoded as: there are lists `A`, `B` of equal length with `row n = A ++ B` (the first
  and second halves of row `n`) and `row (2n) = B ++ A`.
* *Reading choice (range of `n`).* For `n = 1`, row 1 is `[0]`, which has odd length 1 and so has
  no first and second halves; the conjecture is only meaningful when row `n` has halves. For odd
  `n ≥ 3`, `phi(n)` is even. We therefore quantify over odd `n` with `n > 1`. (Under any reading
  that included `n = 1`, the claim would be false there: row 2 is `[1]`, not a rearrangement of
  `[0]`.) `statement_check_7` and `statement_check_15` illustrate the claim for `n = 7` and
  `n = 15` (sanity checks of the transcription, not a proof).
-/

namespace Math0.Statements.A308121

/-- Row `n` of A038566: the numbers `r` with `1 ≤ r ≤ n` and `gcd(r, n) = 1`, increasing. -/
def totatives (n : ℕ) : List ℕ :=
  (List.range' 1 n).filter (fun r => Nat.Coprime r n)

/-- A109395: the denominator of `phi(n)/n`. -/
def A109395 (n : ℕ) : ℕ := ((Nat.totient n : ℚ) / n).den

/-- A076512: the numerator of `phi(n)/n` (as an integer). -/
def A076512 (n : ℕ) : ℤ := ((Nat.totient n : ℚ) / n).num

/-- `T(n,k) = A109395(n)*k - A076512(n)*A038566(n,k)`, where `A038566(n,k)` is the `k`-th
(1-based) number in `[1, n]` coprime to `n`; meaningful for `n ≥ 1`, `1 ≤ k ≤ phi(n)`. -/
def T (n k : ℕ) : ℤ :=
  (A109395 n : ℤ) * k - A076512 n * ((totatives n).getD (k - 1) 0 : ℕ)

/-- Row `n` of the triangle: `[T(n,1), …, T(n, phi(n))]`. -/
def row (n : ℕ) : List ℤ :=
  (List.range (Nat.totient n)).map (fun i => T n (i + 1))

/-- The definition reproduces the 72 listed terms of OEIS (rows `1..15`, kernel-checked). -/
theorem a_data : (List.range 15).flatMap (fun i => row (i + 1)) =
    [0, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 4, 5, 6, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4,
      1, 2, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 2, 1, 2, 1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12,
      4, 5, 6, 1, 2, 3, 7, 14, 13, 4, 11, 2, 1, 8] := by
  decide +kernel

/-- The worked example of the entry: `T(210,2) = 35*2 - 8*11 = -18`. -/
theorem T_210_2 : T 210 2 = -18 := by
  decide +kernel

/-- Charlie Neder's conjecture: for odd `n > 1` (so that row `n` has two halves), row `2n` is row
`n` with its first and second halves interchanged. -/
def statement : Prop :=
  ∀ n : ℕ, Odd n → 1 < n →
    ∃ A B : List ℤ, row n = A ++ B ∧ A.length = B.length ∧ row (2 * n) = B ++ A

/-- Sanity check for `n = 7`: row 7 is `[1,2,3,4,5,6]` and row 14 is `[4,5,6,1,2,3]`. -/
theorem statement_check_7 :
    row 7 = [1, 2, 3] ++ [4, 5, 6] ∧ row 14 = [4, 5, 6] ++ [1, 2, 3] := by
  decide +kernel

/-- Sanity check for `n = 15`: row 15 is `[7,14,13,4,11,2,1,8]`, row 30 is `[11,2,1,8,7,14,13,4]`. -/
theorem statement_check_15 :
    row 15 = [7, 14, 13, 4] ++ [11, 2, 1, 8] ∧ row 30 = [11, 2, 1, 8] ++ [7, 14, 13, 4] := by
  decide +kernel

end Math0.Statements.A308121
