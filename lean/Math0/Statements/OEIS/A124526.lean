/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A124526: Hanna's product formula for partitions with `k` mixed-parity blocks

Source: https://oeis.org/A124526, Paul D. Hanna, Nov 08 2006 (COMMENTS section). Verbatim:
> A124418(n,k) = k!*T(n,k) (conjecture).

The same conjecture is recorded in the FORMULA section of https://oeis.org/A124418, also by
Paul D. Hanna, Nov 08 2006:
> Conjecture: T(n,k) = k!*A049020([n/2],k)*A049020([(n+1)/2],k) where
> A049020(n,k)=Sum_{i=0..n} S2(n,i)*C(i,k) and S2(n,k)=(1/k!)*Sum_{j=0..k} (-1)^(k-j)*C(k,j)*j^n
> (the Stirling numbers of 2nd kind).

## Encoding

* *A124526* (offset `0`, keyword `tabf`) is the triangle "read by rows, where
  `T(n,k) = A049020([n/2],k)*A049020([(n+1)/2],k)`"; "Row n has 1+floor(n/2) terms", i.e.
  `0 ≤ k ≤ ⌊n/2⌋`. Here `[x]` is the floor, so `[n/2] = n / 2` and `[(n+1)/2] = (n + 1) / 2`
  (natural-number division).
* *A049020* is encoded by the formula given in A124526 (and A049020):
  `A049020(m,k) = ∑_{i=0}^{m} S2(m,i) · C(i,k)`, where `S2` is Mathlib's `Nat.stirlingSecond`
  (the Stirling numbers of the second kind; the explicit alternating sum quoted in the entry is a
  standard closed form of the same numbers).
* `T n k` is A124526's `T(n,k)`; `a` is the triangle read by rows (the OEIS sequence itself,
  offset `0`). `T_data` checks all 16 listed rows `n = 0, …, 15` and `a_data` checks all 72 listed
  terms `a 0, …, a 71` (both kernel-checked).
* *A124418* (Emeric Deutsch, offset `0`): "Triangle read by rows: T(n,k) is the number of
  partitions of the set {1,2,...,n} having exactly k blocks that contain both odd and even
  entries (0<=k<=floor(n/2))." A partition of `{1, …, n}` is a Mathlib
  `Finpartition (Finset.Icc 1 n)` (a finite set of nonempty, pairwise disjoint blocks whose union is
  `{1, …, n}`; two partitions are equal iff they have the same blocks). A block `b` is *mixed*
  (`IsMixed b`) if it contains an odd entry and an even entry. `A124418 n k` counts the partitions
  of `{1, …, n}` with exactly `k` mixed blocks (`A124418_eq_card` restates it as the cardinality of
  a subtype). For `n = 0` the unique (empty) partition of `∅` has no mixed block.
  The definition is decidable, but Mathlib's enumeration of `Finpartition`s is doubly
  exponential (it filters the powerset of the powerset), so the kernel can only evaluate it for
  `n ≤ 3`: `A124418_data` checks the listed rows `n = 0, 1, 2, 3` of A124418
  (`1; 1; 1, 1; 2, 3`). Separately, `rhs_data` checks that `k! · T(n,k)` reproduces all 49 listed
  terms of A124418 (rows `0, …, 12`); this only sanity-checks the transcription of the right-hand
  side and proves nothing about the conjecture.
* *The conjecture.* `statement`: for all `n ≥ 0` and all `k` with `0 ≤ k ≤ ⌊n/2⌋` (the index range
  of both triangles), `A124418(n,k) = k! · T(n,k)`.
-/

namespace Math0.Statements.A124526

open Finset

/-- A049020: `A049020(m,k) = ∑_{i=0}^{m} S2(m,i) · C(i,k)`, the number of set partitions of an
`m`-set in which exactly `k` of the blocks have been distinguished (`S2` = Stirling numbers of the
second kind, `Nat.stirlingSecond`). -/
def A049020 (m k : ℕ) : ℕ :=
  ∑ i ∈ range (m + 1), Nat.stirlingSecond m i * Nat.choose i k

/-- A124526 as a triangle: `T(n,k) = A049020([n/2],k) * A049020([(n+1)/2],k)`
(`0 ≤ k ≤ ⌊n/2⌋`). -/
def T (n k : ℕ) : ℕ := A049020 (n / 2) k * A049020 ((n + 1) / 2) k

/-- A124526 as a sequence (offset `0`): the triangle `T` read by rows, row `n` being
`T(n,0), …, T(n,⌊n/2⌋)`. (Rows `0, …, i` contain at least `i + 1` entries, so the `i`-th entry of
the concatenation lies among them.) -/
def a (i : ℕ) : ℕ :=
  ((List.range (i + 1)).flatMap fun n => (List.range (n / 2 + 1)).map (T n)).getD i 0

/-- The definition reproduces the 16 rows `n = 0, …, 15` listed in OEIS (kernel-checked). -/
theorem T_data : (List.range 16).map (fun n => (List.range (n / 2 + 1)).map (T n)) =
    [[1],
     [1],
     [1, 1],
     [2, 3],
     [4, 9, 1],
     [10, 30, 6],
     [25, 100, 36, 1],
     [75, 370, 186, 10],
     [225, 1369, 961, 100, 1],
     [780, 5587, 4960, 750, 15],
     [2704, 22801, 25600, 5625, 225, 1],
     [10556, 101774, 136960, 39000, 2325, 21],
     [41209, 454276, 732736, 270400, 24025, 441, 1],
     [178031, 2199262, 4110512, 1849120, 217000, 6027, 28],
     [769129, 10647169, 23059204, 12645136, 1960000, 82369, 784, 1],
     [3630780, 55493841, 136074274, 87570056, 16787400, 944230, 13720, 36]] := by
  decide +kernel

/-- The definition reproduces all 72 terms listed in OEIS, `a 0, …, a 71` (kernel-checked). -/
theorem a_data : (List.range 72).map (fun i => a (i + 0)) =
    [1, 1, 1, 1, 2, 3, 4, 9, 1, 10, 30, 6, 25, 100, 36, 1, 75, 370, 186, 10, 225, 1369, 961, 100,
      1, 780, 5587, 4960, 750, 15, 2704, 22801, 25600, 5625, 225, 1, 10556, 101774, 136960, 39000,
      2325, 21, 41209, 454276, 732736, 270400, 24025, 441, 1, 178031, 2199262, 4110512, 1849120,
      217000, 6027, 28, 769129, 10647169, 23059204, 12645136, 1960000, 82369, 784, 1, 3630780,
      55493841, 136074274, 87570056, 16787400, 944230, 13720, 36] := by
  decide +kernel

/-! ### A124418: partitions of `{1, …, n}` by the number of mixed-parity blocks -/

/-- A block is *mixed* if it contains both an odd and an even entry. -/
def IsMixed (b : Finset ℕ) : Prop := (∃ x ∈ b, Odd x) ∧ (∃ x ∈ b, Even x)

instance : DecidablePred IsMixed := fun b => by unfold IsMixed; infer_instance

/-- A124418: `T(n,k)` is the number of partitions of the set `{1, 2, …, n}` having exactly `k`
blocks that contain both odd and even entries. -/
def A124418 (n k : ℕ) : ℕ :=
  (univ.filter fun P : Finpartition (Icc 1 n) => (P.parts.filter IsMixed).card = k).card

/-- `A124418 n k` is the number of partitions of `{1, …, n}` with exactly `k` mixed blocks. -/
theorem A124418_eq_card (n k : ℕ) :
    A124418 n k =
      Fintype.card {P : Finpartition (Icc 1 n) // (P.parts.filter IsMixed).card = k} := by
  rw [A124418, Fintype.card_subtype]

/-- The definition of A124418 reproduces its listed rows `n = 0, 1, 2, 3` (kernel-checked; the
enumeration of partitions is doubly exponential, so larger rows are out of reach). -/
theorem A124418_data : (List.range 4).map (fun n => (List.range (n / 2 + 1)).map (A124418 n)) =
    [[1], [1], [1, 1], [2, 3]] := by
  decide +kernel

/-- Sanity check of the transcription of the right-hand side (not a proof of the conjecture):
`k! · T(n,k)` reproduces all 49 listed terms of A124418 (rows `n = 0, …, 12`). -/
theorem rhs_data : (List.range 13).flatMap
      (fun n => (List.range (n / 2 + 1)).map (fun k => k.factorial * T n k)) =
    [1, 1, 1, 1, 2, 3, 4, 9, 2, 10, 30, 12, 25, 100, 72, 6, 75, 370, 372, 60, 225, 1369, 1922,
      600, 24, 780, 5587, 9920, 4500, 360, 2704, 22801, 51200, 33750, 5400, 120, 10556, 101774,
      273920, 234000, 55800, 2520, 41209, 454276, 1465472, 1622400, 576600, 52920, 720] := by
  decide +kernel

/-! ### The conjecture -/

/-- Conjecture (Paul D. Hanna, 2006): for all `n ≥ 0` and `0 ≤ k ≤ ⌊n/2⌋`, the number
A124418(n,k) of partitions of `{1, …, n}` with exactly `k` blocks containing both odd and even
entries equals `k! · T(n,k)`, where `T(n,k) = A049020([n/2],k) · A049020([(n+1)/2],k)` is
A124526. -/
def statement : Prop :=
  ∀ n k : ℕ, k ≤ n / 2 → A124418 n k = k.factorial * T n k

end Math0.Statements.A124526
