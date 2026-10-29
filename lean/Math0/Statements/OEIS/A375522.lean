/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A375522: denominators of the prime-scaled greedy Egyptian sums below 1

Source: https://oeis.org/A375522, Rémy Sigrist and N. J. A. Sloane, Aug 30 2024. Verbatim:
> Let S(n) = Sum_{k = 1..n} 1 / (k*A375781(k)) = S1(n)/S2(n) when reduced to lowest terms,
> where S1(n) = A375521(n), S2(n) = the present sequence.
> The differences S2(n) - S1(n) are surprisingly small: for n = 1,2,...,34 the values
> S2(n) - S1(n) are:
> 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
> 1, 1
> suggesting the conjecture that they are always 1 except for n = 4 and 6 (compare the Theorem
> in A374983).

## Encoding

* A375781 (Rémy Sigrist) is the "lexicographically earliest sequence of positive integers
  a(1), a(2), a(3), ... such that for any n > 0, Sum_{k = 1..n} 1 / (prime(k)*a(k)) < 1". The
  entries' Maple and Mathematica programs (and the PARI and Python programs) compute it greedily:
  with `s(0) = 0`,
  `b(n) = 1 + floor(1/((1 - s(n-1)) * prime(n)))` and `s(n) = s(n-1) + 1/(prime(n) * b(n))`.
  (When `s(n-1) < 1`, `b(n)` is the least positive integer with
  `s(n-1) + 1/(prime(n) b(n)) < 1`.) We encode
  exactly this recursion over `ℚ` with `Int.floor` (`s`, `b`).
* The entry's name and comment write `1 / (k*A375781(k))`, but its data, example
  (`0/1, 1/2, 5/6, 14/15, …`), Maple, Mathematica and Python programs all use
  `1 / (prime(k)*A375781(k))` (with `k` instead of `prime(k)` the first sum would already be
  `1/1`). So `k` there is a typo for `prime(k)`, and we use `prime(k)`. The data check below
  confirms this reading.
* `prime k` is the `k`-th prime (`k ≥ 1`), computed by a bounded search (`primeAt`, 0-indexed).
  `primeAt_eq_nth` proves `primeAt i = Nat.nth Nat.Prime i`, so `prime k` is Mathlib's
  `k`-th prime.
* `S1 n = (s n).num` (A375521) and `a n = S2 n = (s n).den` (A375522, offset 0, `a 0 = 1`);
  Mathlib's `Rat` is always in lowest terms with positive denominator.
* The conjecture is about `n = 1, 2, …` (the range of the comment). For `n = 0` the difference
  is also `1` (`s 0 = 0/1`), so this choice does not matter. The difference is taken in `ℤ`.
  We state the "always 1" part; the two exceptions (difference `2` at `n = 4, 6`) are checked
  by `diff_data`.
-/

namespace Math0.Statements.A375522

/-! ### The primes -/

/-- The first prime among `q, q + 1, …, q + fuel - 1`, or `0` if there is none. -/
def firstPrimeFrom : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, q => if q.Prime then q else firstPrimeFrom fuel (q + 1)

/-- The least prime `> m`, searched in `m + 1, …, 2 m + 2` (Bertrand's postulate guarantees one,
see `primeAt_eq_nth`). -/
def nextPrime (m : ℕ) : ℕ := firstPrimeFrom (m + 2) (m + 1)

/-- The `i`-th prime, 0-indexed: `primeAt 0 = 2`, `primeAt 1 = 3`, … -/
def primeAt : ℕ → ℕ
  | 0 => 2
  | i + 1 => nextPrime (primeAt i)

/-- The `k`-th prime, 1-indexed as in the OEIS: `prime 1 = 2`, `prime 2 = 3`, … -/
def prime (k : ℕ) : ℕ := primeAt (k - 1)

theorem firstPrimeFrom_spec (fuel q : ℕ) (h : ∃ r, r.Prime ∧ q ≤ r ∧ r < q + fuel) :
    (firstPrimeFrom fuel q).Prime ∧ q ≤ firstPrimeFrom fuel q ∧
      ∀ r, q ≤ r → r < firstPrimeFrom fuel q → ¬ r.Prime := by
  induction fuel generalizing q with
  | zero => obtain ⟨r, -, h1, h2⟩ := h; omega
  | succ fuel ih =>
    rw [firstPrimeFrom]
    split_ifs with hq
    · exact ⟨hq, le_rfl, fun r h1 h2 => by omega⟩
    · obtain ⟨r, hr, h1, h2⟩ := h
      have hqr : q ≠ r := fun e => hq (e ▸ hr)
      obtain ⟨h1', h2', h3'⟩ := ih (q + 1) ⟨r, hr, by omega, by omega⟩
      refine ⟨h1', by omega, fun r' hr1 hr2 => ?_⟩
      rcases Nat.eq_or_lt_of_le hr1 with e | e
      · exact e ▸ hq
      · exact h3' r' e hr2

/-- `primeAt` is Mathlib's `Nat.nth Nat.Prime`. -/
theorem primeAt_eq_nth (i : ℕ) : primeAt i = Nat.nth Nat.Prime i := by
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  induction i with
  | zero => simp [primeAt]
  | succ i ih =>
    rw [primeAt, ih]
    set m := Nat.nth Nat.Prime i with hm
    have hmp : m.Prime := Nat.nth_mem_of_infinite hinf i
    obtain ⟨r, hr, hr1, hr2⟩ := Nat.exists_prime_lt_and_le_two_mul m hmp.ne_zero
    obtain ⟨hx, hx1, hx2⟩ :=
      firstPrimeFrom_spec (m + 2) (m + 1) ⟨r, hr, by omega, by omega⟩
    have hn : (Nat.nth Nat.Prime (i + 1)).Prime := Nat.nth_mem_of_infinite hinf (i + 1)
    have hlt : m < Nat.nth Nat.Prime (i + 1) := Nat.nth_strictMono hinf (Nat.lt_succ_self i)
    rw [nextPrime]
    rcases lt_trichotomy (firstPrimeFrom (m + 2) (m + 1)) (Nat.nth Nat.Prime (i + 1))
      with h | h | h
    · have := Nat.le_nth_of_lt_nth_succ h hx
      omega
    · exact h
    · exact absurd hn (hx2 _ (by omega) h)

/-! ### The sums `s n` and the sequences -/

/-- `s n = ∑_{k = 1..n} 1 / (prime k * b k)` with the greedy
`b k = 1 + ⌊1 / ((1 - s (k - 1)) * prime k)⌋` (A375781), `s 0 = 0`. -/
def s : ℕ → ℚ
  | 0 => 0
  | n + 1 => s n + 1 / ((prime (n + 1) : ℚ) *
      ((1 + ⌊1 / ((1 - s n) * (prime (n + 1) : ℚ))⌋ : ℤ) : ℚ))

/-- A375781: `b n = 1 + floor(1/((1 - s(n-1)) * prime(n)))` for `n ≥ 1`. -/
def b (n : ℕ) : ℤ := 1 + ⌊1 / ((1 - s (n - 1)) * (prime n : ℚ))⌋

/-- The recursion of the OEIS programs: `s(n) = s(n-1) + 1/(prime(n) * b(n))`. -/
theorem s_succ (n : ℕ) : s (n + 1) = s n + 1 / ((prime (n + 1) : ℚ) * (b (n + 1) : ℚ)) := rfl

/-- A375521: `S1 n`, the numerator of `s n` in lowest terms. -/
def S1 (n : ℕ) : ℤ := (s n).num

/-- A375522: `a n = S2 n`, the denominator of `s n = ∑_{k = 1..n} 1 / (prime k * A375781 k)`
in lowest terms. -/
def a (n : ℕ) : ℕ := (s n).den

/-- The definition reproduces all 11 terms listed in OEIS (offset 0, kernel-checked). -/
theorem a_data : (List.range 11).map (fun i => a i) =
    [1, 2, 6, 15, 105, 1155, 1336335, 892896284280, 398631887241408183843480,
      19863422690705846097977473796903171171326157280,
      14091270035344566960604487534521565339065390839583445590118556137472614250693240040301050080]
    := by
  decide +kernel

/-- `S1` reproduces the 11 terms listed in A375521 (offset 0, kernel-checked). -/
theorem S1_data : (List.range 11).map (fun i => S1 i) =
    [0, 1, 5, 14, 103, 1154, 1336333, 892896284279, 398631887241408183843479,
      19863422690705846097977473796903171171326157279,
      14091270035344566960604487534521565339065390839583445590118556137472614250693240040301050079]
    := by
  decide +kernel

/-- `b` reproduces the 11 terms listed in A375781 (offset 1, kernel-checked). -/
theorem b_data : (List.range 11).map (fun i => b (i + 1)) =
    [1, 1, 2, 3, 5, 89, 39304, 46994541278, 17331821184409051471456,
      684945610024339520619912889548385212804350252,
      454557097914340869696918952726502107711786801276885341616727617337826266151394840009711293]
    := by
  decide +kernel

/-- The differences `S2(n) - S1(n)` for `n = 1, …, 24` (kernel-checked), matching the start of
the list in the comment: `2` at `n = 4` and `n = 6`, `1` otherwise. (`a 24` has about
1.5 million digits; the comment's list goes on to `n = 34`.) -/
theorem diff_data : (List.range 24).map (fun i => (a (i + 1) : ℤ) - S1 (i + 1)) =
    [1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  decide +kernel

/-- Conjecture (Sigrist and Sloane, 2024): for every `n ≥ 1` other than `n = 4` and `n = 6`,
`S2(n) - S1(n) = 1`, i.e. `s n = 1 - 1 / a n`. -/
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≠ 4 → n ≠ 6 → (a n : ℤ) - S1 n = 1

end Math0.Statements.A375522
