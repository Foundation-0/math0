/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A090905: the last term of row `n` is twice the largest prime of row `n - 1`

Source: https://oeis.org/A090905, Amarnath Murthy, Dec 13 2003 (COMMENTS section). Verbatim:
> Conjecture: For n > 4 the last term of the n-th group is 2p where p is the largest prime in the
> (n-1)th group. And these are the Bertrand primes.

The entry's name: "Left side of irregular triangle of natural numbers in which every row product
is a multiple of the previous." Offset `1`. The entry's example shows the triangle, which splits
`1, 2, 3, …` into consecutive blocks ("groups"):
`(1), (2), (3, 4), (5, 6, 7, 8), (9, …, 14), (15, …, 26), …`.
The same conjecture appears in A090904 (row products), A090906 (row lengths) and A090907.

## Encoding

* Row `n` (`n ≥ 1`) is the block of consecutive integers `a n, a n + 1, …, last n`, where
  `a n` is its first term (this sequence), `len n ≥ 1` its length and
  `last n = a n + len n - 1` its last term. The product of row `n` is
  `(a n).ascFactorial (len n) = a n * (a n + 1) * ⋯ * (a n + len n - 1)`
  (Mathematica's `Pochhammer[a n, len n]`).
* Row `1` is `(1)`. Row `n + 1` starts right after row `n`, at `a n + len n`, and its length is
  the least `k` with `k ≥ len n` such that the product of row `n` divides
  `(a (n + 1)).ascFactorial k`. This is the rule of the Mathematica program in the entry (Michael
  De Vlieger, Dec 15 2016), which starts its search at `k = len n` (the previous length). The
  entry's name does not mention the bound `k ≥ len n`. Searching from `k = 1` instead gives the
  same rows `1, …, 20` (checked outside Lean).
* To make `a` computable, the search for `k` is `search`, which runs for a limited number of
  steps (its "fuel"). `len_succ_isLeast` proves that the fuel always suffices, so `len (n + 1)`
  is exactly the least admissible `k`. Some `k` always works: for `k = a (n + 1) - 1`, the
  product of row `n` divides `k!`, and `k!` divides the product of any `k` consecutive integers.
  The theorems `a_one`, `len_one`, `a_succ` and `len_succ_isLeast` give the defining
  recursion, which determines the triangle. `row 0` is a junk value (equal to `row 1`).
* `a_data` checks the first 18 listed terms `a 1, …, a 18` (the product of row `18` has about
  610000 bits). `len_data` checks the first 17 row lengths against A090906.
* "The Bertrand primes" are A006992: `bertrand 1 = 2`, and `bertrand (k + 1)` is the largest
  prime `< 2 * bertrand k`. Here this is `Nat.findGreatest Nat.Prime (2 * b - 1)`.
  `bertrand_data` checks the first 13 listed terms `2, 3, 5, …, 2503`.
* Reading choices in the statement:
  - "the largest prime in the (n-1)th group" is the `p` that is the greatest element of the set
    of primes `q` with `a (n - 1) ≤ q ≤ last (n - 1)`. The statement asserts that this `p`
    exists, so in particular the group contains a prime.
  - "these are the Bertrand primes": the primes `p` (for `n > 4`, so from group `4` on) are the
    Bertrand primes. The largest prime of group `4 = (5, 6, 7, 8)` is `7 = A006992(4)`, and the
    groups are disjoint and increasing. So the claim is that the largest prime of group `n - 1` is
    `A006992(n - 1)`. (The Bertrand primes `2, 3, 5` before `7` do not occur as such `p`. Group
    `3 = (3, 4)` has largest prime `3`, and `5` is skipped. So the sentence cannot mean the whole
    sequence A006992.)
-/

namespace Math0.Statements.A090905

/-- `search P s fuel k Q` is called with `Q = s.ascFactorial k`. It returns the least `j` among
`k, k + 1, …, k + fuel - 1` with `P ∣ s.ascFactorial j`. If there is none, it returns
`k + fuel`. -/
def search (P s : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, k, _ => k
  | fuel + 1, k, Q => if P ∣ Q then k else search P s fuel (k + 1) ((s + k) * Q)

/-- From row `(s, L)` (first term `s`, length `L`) to the next row: it starts at `s + L`, and its
length is the least `k ≥ L` such that `s (s+1) ⋯ (s+L-1)` divides
`(s+L) (s+L+1) ⋯ (s+L+k-1)` (the search has fuel `s + L`, which always suffices). -/
def next (r : ℕ × ℕ) : ℕ × ℕ :=
  (r.1 + r.2,
    search (r.1.ascFactorial r.2) (r.1 + r.2) (r.1 + r.2) r.2 ((r.1 + r.2).ascFactorial r.2))

/-- Row `n` of the triangle (`n ≥ 1`), as the pair (first term, length). Row `1` is `(1)`.
(`row 0` is junk and equals `row 1`.) -/
def row (n : ℕ) : ℕ × ℕ := next^[n - 1] (1, 1)

/-- A090905: the first term (left side) of row `n` of the irregular triangle of natural numbers
in which every row product is a multiple of the previous. -/
def a (n : ℕ) : ℕ := (row n).1

/-- The length of row `n` (A090906). -/
def len (n : ℕ) : ℕ := (row n).2

/-- The last term of row `n`. -/
def last (n : ℕ) : ℕ := a n + len n - 1

/-! ### The definition satisfies the defining recursion -/

theorem a_one : a 1 = 1 := rfl

theorem len_one : len 1 = 1 := rfl

theorem row_succ (n : ℕ) (hn : 1 ≤ n) : row (n + 1) = next (row n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [row, Nat.add_sub_cancel]
  exact Function.iterate_succ_apply' next m (1, 1)

theorem one_le_a (n : ℕ) : 1 ≤ a n := by
  suffices h : ∀ m, 1 ≤ (next^[m] (1, 1)).1 from h (n - 1)
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    simp only [next]
    omega

/-- Row `n + 1` starts right after row `n`. -/
theorem a_succ (n : ℕ) (hn : 1 ≤ n) : a (n + 1) = a n + len n := by
  simp only [a, len, row_succ n hn, next]

theorem search_spec (P s : ℕ) : ∀ (fuel k j : ℕ), k ≤ j → j < k + fuel →
    P ∣ s.ascFactorial j →
    k ≤ search P s fuel k (s.ascFactorial k) ∧
      P ∣ s.ascFactorial (search P s fuel k (s.ascFactorial k)) ∧
      ∀ i, k ≤ i → i < search P s fuel k (s.ascFactorial k) → ¬ P ∣ s.ascFactorial i := by
  intro fuel
  induction fuel with
  | zero => intro k j h1 h2; omega
  | succ fuel ih =>
    intro k j hkj hj hP
    by_cases hk : P ∣ s.ascFactorial k
    · simp only [search, if_pos hk]
      exact ⟨le_rfl, hk, fun i h1 h2 => by omega⟩
    · have hQ : search P s (fuel + 1) k (s.ascFactorial k) =
          search P s fuel (k + 1) (s.ascFactorial (k + 1)) := by
        simp only [search, if_neg hk]
        rfl
      rw [hQ]
      have hkj' : k + 1 ≤ j := by
        rcases Nat.eq_or_lt_of_le hkj with h | h
        · subst h; exact absurd hP hk
        · omega
      obtain ⟨h1, h2, h3⟩ := ih (k + 1) j hkj' (by omega) hP
      refine ⟨by omega, h2, fun i hi1 hi2 => ?_⟩
      rcases Nat.eq_or_lt_of_le hi1 with h | h
      · subst h; exact hk
      · exact h3 i h hi2

/-- Some length always works: the product of row `(s, L)` divides `(s + L - 1)!`, which divides
the product of any `s + L - 1` consecutive integers. -/
theorem exists_len (s L : ℕ) (hs : 1 ≤ s) :
    L ≤ s + L - 1 ∧ s.ascFactorial L ∣ (s + L).ascFactorial (s + L - 1) := by
  refine ⟨by omega, ?_⟩
  have h1 : s.ascFactorial L ∣ Nat.factorial (s + L - 1) :=
    Dvd.intro_left _ (Nat.factorial_mul_ascFactorial' s L (by omega))
  exact h1.trans (Nat.factorial_dvd_ascFactorial _ _)

/-- The length of row `n + 1` is the least `k ≥ len n` such that the product of row `n` divides
the product of the `k` consecutive integers `a (n + 1), …, a (n + 1) + k - 1`. -/
theorem len_succ_isLeast (n : ℕ) (hn : 1 ≤ n) :
    IsLeast {k | len n ≤ k ∧ (a n).ascFactorial (len n) ∣ (a (n + 1)).ascFactorial k}
      (len (n + 1)) := by
  have hs := one_le_a n
  have ha : a (n + 1) = a n + len n := a_succ n hn
  have hl : len (n + 1) = search ((a n).ascFactorial (len n)) (a n + len n) (a n + len n)
      (len n) ((a n + len n).ascFactorial (len n)) := by
    simp only [len, a, row_succ n hn, next]
  obtain ⟨e1, e2⟩ := exists_len (a n) (len n) hs
  obtain ⟨h1, h2, h3⟩ := search_spec ((a n).ascFactorial (len n)) (a n + len n)
    (a n + len n) (len n) (a n + len n - 1) e1 (by omega) e2
  rw [hl, ha]
  exact ⟨⟨h1, h2⟩, fun k ⟨hk1, hk2⟩ => by
    by_contra hlt
    exact h3 k hk1 (by omega) hk2⟩

/-! ### Data checks -/

/-- The definition reproduces the first 18 terms listed in OEIS, `a 1, …, a 18`
(kernel-checked). -/
theorem a_data : (List.range 18).map (fun i => a (i + 1)) =
    [1, 2, 3, 5, 9, 15, 27, 47, 87, 167, 327, 635, 1263, 2519, 5007, 10007, 19947,
      39875] := by
  decide +kernel

/-- The row lengths reproduce the first 17 terms of A090906 (kernel-checked). -/
theorem len_data : (List.range 17).map (fun i => len (i + 1)) =
    [1, 1, 2, 4, 6, 12, 20, 40, 80, 160, 308, 628, 1256, 2488, 5000, 9940, 19928] := by
  decide +kernel

/-! ### Bertrand primes (A006992) -/

/-- A006992, the Bertrand primes: `bertrand 1 = 2`, and `bertrand (k + 1)` is the largest prime
`< 2 * bertrand k`, i.e. the largest prime `≤ 2 * bertrand k - 1`. (`bertrand 0` is junk.) -/
def bertrand (n : ℕ) : ℕ := (fun b => Nat.findGreatest Nat.Prime (2 * b - 1))^[n - 1] 2

/-- `bertrand` reproduces the first 13 terms listed in A006992 (kernel-checked). -/
theorem bertrand_data : (List.range 13).map (fun i => bertrand (i + 1)) =
    [2, 3, 5, 7, 13, 23, 43, 83, 163, 317, 631, 1259, 2503] := by
  decide +kernel

/-! ### The conjecture -/

/-- Conjecture (Amarnath Murthy, 2003): for every `n > 4`, the group `n - 1` has a largest prime
`p`, the last term of group `n` is `2 * p`, and `p` is the Bertrand prime `A006992(n - 1)`. -/
def statement : Prop :=
  ∀ n : ℕ, 4 < n → ∃ p : ℕ,
    IsGreatest {q : ℕ | q.Prime ∧ a (n - 1) ≤ q ∧ q ≤ last (n - 1)} p ∧
      last n = 2 * p ∧ p = bertrand (n - 1)

end Math0.Statements.A090905
