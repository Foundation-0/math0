/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A188474: the row sums of a generalized Deutsch triangle are A137398

Source: https://oeis.org/A188474, Paul Barry, Apr 01 2011 (COMMENTS section). Verbatim:
> Row sums are A137398(n+1) (conjecture). Diagonal sums are A188476.

Only the first sentence is the conjecture. The second refers to A188476, which is defined as the
diagonal sums of this triangle; it is not part of the conjecture and is not formalized.

The entry (offset `0`, keyword `tabl`) is named "A generalized Deutsch triangle." Its comment
says: "Member r=2 of the family of "Pascal-like" triangles with
T(n,k)=sum{j=0..n-k+1, (j/(n+2-j))*C(n+2-j,n-k+1)*C(n+2-j,k+1)*r^(j-1)}". Its formula is
"T(n,k)=sum{j=0..n-k+1, (j/(n+2-j))*C(n+2-j,n-k+1)*C(n+2-j,k+1)*2^(j-1)}", for `0 ≤ k ≤ n`.

A137398 (Gordon Beavers, G. Starling and W. Li, Apr 11 2008; offset `1`) is named: "Let S be a
strictly monotonic sequence of length 2n and let p and q be subsequences of S each of length n
such that the least element belongs to p and every element of S belongs to either p or q. The
number of ways to select p such that for any index i the exchange of p(i) and q(i) makes at least
one of p and q non-monotonic, is given by a(n)." Its data begin `0, 1, 2, 7, 22, 74, 252, …`,
with `a(1) = 0`.

## Encoding

* *The triangle.* `T n k : ℚ` is the formula above with `r = 2`, computed exactly in `ℚ`. The
  sum runs over `j = 0, …, n-k+1`, i.e. `j ∈ range (n-k+2)`. `j/(n+2-j)` is a rational quotient.
  Its denominator `n+2-j` is computed in `ℚ`, and it is `≥ k+1 ≥ 1` for `j ≤ n-k+1`. The
  binomial coefficients are Mathlib's `Nat.choose` of `n+2-j`. That natural-number subtraction is
  exact, since `j ≤ n-k+1 ≤ n+1`. `2^(j-1)` is an integer power in `ℚ`. It is `1/2` for `j = 0`,
  but that term vanishes anyway because of the factor `j`. The individual terms are not obviously
  integers, so `T` is `ℚ`-valued. Only `0 ≤ k ≤ n` is used.
* *The sequence.* `row n = [T(n,0), …, T(n,n)]`, and `a i` is the triangle read by rows (the
  OEIS sequence itself, offset `0`). `a_data` checks all `66` listed terms `a 0, …, a 65`
  (rows `0, …, 10`).
* *A137398.* Only the relative order of the elements of `S` matters, so the `m`-th term uses
  `S = [0, 1, …, 2m-1]` (`List.range (2 * m)`).
  - `p` runs over the subsequences of `S` of length `m`. These are `List.sublistsLen m S`, which
    lists each of them exactly once (Mathlib's `List.mem_sublistsLen`, `List.nodup_sublistsLen`).
  - `q` is then forced. Every element of `S` lies in `p` or in `q`, and `|p| + |q| = 2m = |S|`,
    so `q` consists of the elements of `S` not in `p`, in the order of `S`:
    `q = S.filter (· ∉ p)`. Counting the ways to select `p` is counting these `p`.
  - "The least element belongs to p" is `0 ∈ p`.
  - `p(i)` and `q(i)` are the `i`-th entries of `p` and `q` (`i = 0, …, m-1`, 0-based; both
    lists have length `m`, so the default value of `getD` is never used). Exchanging them gives
    the lists `p.set i q(i)` and `q.set i p(i)`.
  - "Monotonic" is read as increasing, i.e. in the direction of `S`: `List.Pairwise (· < ·)`.
    For `m ≥ 3` this is the only possible reading. Each exchanged list still contains `m - 1 ≥ 2`
    entries of the increasing `p` (resp. `q`) in their order, so it cannot be decreasing. For
    `m = 2` the reading is forced by the data. If decreasing sequences also counted as monotonic,
    every sequence of length `2` would be monotonic and `a(2)` would be `0`. The entry lists
    `a(2) = 1`, with the example "The a(2) = 1 p/q subsequences of 1234 are 12/34".
  - A strictly decreasing `S` gives the same count. The condition is symmetric in `p` and `q`,
    so in either case the count is the number of unordered partitions `{p, q}` satisfying it.

  `A137398_data` checks the first `6` listed terms `a(1), …, a(6) = 0, 1, 2, 7, 22, 74` by
  direct enumeration in the kernel. (`a(7)` alone takes about 1.5 minutes this way.)
* *Indexing.* The conjecture predates the correction of A137398's offset. The entry's EXTENSIONS
  line reads "Offset, a(15), a(18) corrected by and more terms from _Georg Fischer_, Jun 07 2021".
  The listed row sums `1, 2, 7, 22, 74, …` of A188474 are the terms of A137398 from its second
  term on. So in the 2011 indexing, `A137398(n+1)` was the term matching row `n`. In the current
  indexing (offset `1`, the one that matches the name: `a(m)` is about `S` of length `2m`), these
  terms are `A137398(2), A137398(3), …`. So the conjecture says that row `n` sums to
  `A137398(n+2)`. The literal reading `A137398(n+1)` with the current offset already fails at
  `n = 0`: the row sum is `1`, but `A137398(1) = 0`. `rowSum_data` checks that the row sums for
  `n = 0, …, 10` are the listed terms `A137398(2), …, A137398(12)`. `statement_check` checks
  the statement itself for `n ≤ 4` (a sanity check of the transcription, not a proof).
* *The conjecture.* `statement`: for every `n ≥ 0`, `∑_{k=0}^{n} T(n,k) = A137398(n+2)`, as an
  equality in `ℚ`.
-/

namespace Math0.Statements.A188474

open Finset

/-! ### The triangle A188474 -/

/-- The generalized Deutsch triangle with `r = 2`:
`T(n,k) = ∑_{j=0}^{n-k+1} (j/(n+2-j)) C(n+2-j, n-k+1) C(n+2-j, k+1) 2^(j-1)`, `0 ≤ k ≤ n`,
computed exactly in `ℚ`. -/
def T (n k : ℕ) : ℚ :=
  ∑ j ∈ range (n - k + 2),
    (j : ℚ) / ((n : ℚ) + 2 - j) * ((n + 2 - j).choose (n - k + 1) : ℚ) *
      ((n + 2 - j).choose (k + 1) : ℚ) * (2 : ℚ) ^ ((j : ℤ) - 1)

/-- Row `n` of the triangle: `[T(n,0), …, T(n,n)]`. -/
def row (n : ℕ) : List ℚ := (List.range (n + 1)).map (T n)

/-- A188474: the triangle `T` read by rows (offset `0`). Rows `0, …, i` have more than `i`
entries, so the `i`-th entry of their concatenation exists. -/
def a (i : ℕ) : ℚ := ((List.range (i + 1)).flatMap row).getD i 0

set_option maxRecDepth 100000 in
/-- The definition reproduces the first terms listed in OEIS (kernel-checked): all `66` listed
terms `a(0), …, a(65)`, i.e. rows `0, …, 10`. -/
theorem a_data : (List.range 66).map (fun i => a (i + 0)) =
    [1,
     1, 1,
     1, 5, 1,
     1, 10, 10, 1,
     1, 16, 40, 16, 1,
     1, 23, 102, 102, 23, 1,
     1, 31, 209, 393, 209, 31, 1,
     1, 40, 376, 1122, 1122, 376, 40, 1,
     1, 50, 620, 2656, 4296, 2656, 620, 50, 1,
     1, 61, 960, 5536, 13100, 13100, 5536, 960, 61, 1,
     1, 73, 1417, 10522, 34036, 50180, 34036, 10522, 1417, 73, 1] := by
  decide +kernel

/-! ### A137398 -/

/-- A137398 (offset `1`), by its definition. With `S = [0, 1, …, 2m-1]`, count the
subsequences `p` of `S` of length `m` such that, with `q` the subsequence of the remaining
elements, the least element `0` belongs to `p`, and for every index `i < m` the exchange of
`p(i)` and `q(i)` makes at least one of `p`, `q` non-monotonic (not increasing). -/
def A137398 (m : ℕ) : ℕ :=
  ((List.range (2 * m)).sublistsLen m).countP fun p =>
    let q := (List.range (2 * m)).filter (· ∉ p)
    decide (0 ∈ p ∧ ∀ i < m,
      ¬ ((p.set i (q.getD i 0)).Pairwise (· < ·) ∧ (q.set i (p.getD i 0)).Pairwise (· < ·)))

set_option maxRecDepth 100000 in
/-- The definition of A137398 reproduces its first `6` listed terms (kernel-checked). -/
theorem A137398_data : (List.range 6).map (fun i => A137398 (i + 1)) = [0, 1, 2, 7, 22, 74] := by
  decide +kernel

/-! ### The conjecture -/

set_option maxRecDepth 100000 in
/-- The row sums for `n = 0, …, 10` are the listed terms `A137398(2), …, A137398(12)`
(kernel-checked; a check of the indexing, not a proof). -/
theorem rowSum_data : (List.range 11).map (fun n => ∑ k ∈ range (n + 1), T n k) =
    [1, 2, 7, 22, 74, 252, 875, 3078, 10950, 39316, 142278] := by
  decide +kernel

/-- Paul Barry's conjecture (in the current indexing of A137398): for every `n ≥ 0`, the sum
of row `n` of the triangle, `∑_{k=0}^{n} T(n,k)`, equals `A137398(n+2)`. -/
def statement : Prop :=
  ∀ n : ℕ, ∑ k ∈ range (n + 1), T n k = (A137398 (n + 2) : ℚ)

/-- The statement holds for `n ≤ 4` (a sanity check of the transcription, not a proof). -/
theorem statement_check (n : ℕ) (hn : n < 5) :
    ∑ k ∈ range (n + 1), T n k = (A137398 (n + 2) : ℚ) := by
  have h1 := congrArg (fun l => l.getD n 0) rowSum_data
  have h2 := congrArg (fun l => ((l.getD (n + 1) 0 : ℕ) : ℚ)) A137398_data
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range,
    show n < 11 by omega, show n + 1 < 6 by omega, Option.map_some,
    Option.getD_some] at h1 h2
  rw [h1, h2]
  interval_cases n <;> rfl

end Math0.Statements.A188474
