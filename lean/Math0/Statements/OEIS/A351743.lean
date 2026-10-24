/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A351743: greatest divisor of the partial sum prime to the previous term

Sources (all verbatim):

* https://oeis.org/A351743, _David James Sycamore_, Jun 07 2022 (COMMENTS section):
  > Conjecture: a(n)=1 occurs infinitely many times, and therefore so does a(n)=2.
* https://oeis.org/A351743, FORMULA section:
  > Conjectures from _Rémy Sigrist_, Jun 20 2022: (Start)
  > - a(2*(n+21)-1) = a(2*n-1) for n >= 70,
  > - a(2*(n+21)) = 3645*a(2*n) + b(n) for n >= 70 (where b is 21-periodic).
  > (End)
* https://oeis.org/A355149 ("Partial sums of A351743", offset `1`; _Michael De Vlieger_,
  _Rémy Sigrist_ and _David James Sycamore_, Jun 21 2022), FORMULA section:
  > Conjecture: a(n + 42) = 3645*a(n) + b(n) for n >= 138 (where b is 42-periodic).

The definition of A351743 (offset `1`): "a(1)=1. Thereafter, a(n+1) is the greatest divisor of
s(n) which is prime to a(n), where s(n) is the n-th partial sum."

## Encoding

* `a : ℕ → ℕ` with the OEIS offset `1`; `a 0 = 0` is a junk value that no statement uses (it is
  different from `1` and `2`, so it does not affect the sets in `sycamore` either).
  `s n = ∑ k ∈ [1, n], a k` is the `n`-th partial sum, literally; it is A355149 (offset `1`).
* Computation: the greatest divisor of `w > 0` prime to `v` is computed as in the entry's PARI
  program, by dividing `w` by `gcd(w, v)` while this gcd exceeds `1` (`strip`, `coprimePart`).
  The pairs `(a(n), s(n))` are produced by iterating `step` from `(a(1), s(1)) = (1, 1)`.
  The theorems `a_one` and `a_succ_isGreatest` prove that `a` satisfies exactly the OEIS
  definition: `a 1 = 1`, and for every `n ≥ 1`, `a (n + 1)` is the greatest element of
  `{d | d ∣ s n ∧ Nat.Coprime d (a n)}`. These conditions determine the sequence.
  `a_data` checks all 67 listed terms `a 1, …, a 67`, `s_data` the 50 listed terms of
  A355149, and `a_example` the values `a(150), …, a(153)` of the entry's last example.
* Sycamore's conjecture (`sycamore`): both sets `{n | a n = 1}` and `{n | a n = 2}` are
  infinite. The "and therefore" part is included as a second conjunct, since the conjecture
  asserts it too.
* Sigrist's first formula (`sigristOdd`): for every `n ≥ 70`, `a(2(n+21)-1) = a(2n-1)`
  (natural subtraction is harmless here, `2n - 1 ≥ 139`).
* Sigrist's second formula (`sigristEven`): "b is 21-periodic" is read as: there is an
  integer sequence `b : ℕ → ℤ` with `b (n + 21) = b n` for all `n`, such that
  `a(2(n+21)) = 3645 a(2n) + b(n)` for all `n ≥ 70`. The equation is stated in `ℤ`, as `b` may
  a priori take negative values. (Asking `b` to be periodic on all of `ℕ` rather than only on
  `n ≥ 70` changes nothing, since a sequence periodic from `70` on extends backwards
  periodically.)
* The A355149 conjecture (`partialSums`), with `s` in place of A355149's `a`: there is
  `c : ℕ → ℤ` with `c (n + 42) = c n` for all `n`, such that `s(n+42) = 3645 s(n) + c(n)` for
  all `n ≥ 138`.
* `statement` is the conjunction of these four conjectures.
-/

namespace Math0.Statements.A351743

/-- Divide `w` by `gcd(w, v)` as long as this gcd is not `1`, for at most `fuel` steps. -/
def strip : ℕ → ℕ → ℕ → ℕ
  | 0, w, _ => w
  | fuel + 1, w, v => if Nat.gcd w v = 1 then w else strip fuel (w / Nat.gcd w v) v

/-- The greatest divisor of `w` prime to `v`, for `w > 0` (see `coprimePart_isGreatest`). -/
def coprimePart (w v : ℕ) : ℕ := strip w w v

/-- From `(a(n), s(n))` to `(a(n+1), s(n+1))`. -/
def step (p : ℕ × ℕ) : ℕ × ℕ :=
  match p with
  | (x, y) =>
    match coprimePart y x with
    | z => (z, y + z)

/-- `state n = (a(n+1), s(n+1))`. -/
def state (n : ℕ) : ℕ × ℕ := step^[n] (1, 1)

/-- A351743 (offset `1`): `a(1) = 1`, and `a(n+1)` is the greatest divisor of the partial sum
`s(n) = a(1) + ⋯ + a(n)` which is prime to `a(n)`. (`a 0 = 0` is a junk value.) -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (state n).1

/-- The `n`-th partial sum `s(n) = a(1) + ⋯ + a(n)` of A351743, i.e. A355149 (offset `1`). -/
def s (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, a k

/-! ### `a` satisfies the OEIS definition -/

/-- `strip` computes the greatest divisor of `w` prime to `v`, once the fuel is at least `w`. -/
theorem strip_isGreatest (v : ℕ) :
    ∀ (fuel w : ℕ), 0 < w → w ≤ fuel →
      IsGreatest {d | d ∣ w ∧ Nat.Coprime d v} (strip fuel w v) := by
  intro fuel
  induction fuel with
  | zero => intro w hw hf; omega
  | succ fuel ih =>
    intro w hw hf
    simp only [strip]
    split_ifs with hg
    · refine ⟨⟨dvd_refl w, hg⟩, ?_⟩
      rintro d ⟨hd, -⟩
      exact Nat.le_of_dvd hw hd
    · set g := Nat.gcd w v with hgdef
      have hgw : g ∣ w := Nat.gcd_dvd_left w v
      have hgpos : 0 < g := Nat.gcd_pos_of_pos_left v hw
      have hg2 : 2 ≤ g := by omega
      have hwg : 0 < w / g := Nat.div_pos (Nat.le_of_dvd hw hgw) hgpos
      have hlt : w / g < w := Nat.div_lt_self hw (by omega)
      have key := ih (w / g) hwg (by omega)
      have hset : {d | d ∣ w / g ∧ Nat.Coprime d v} = {d | d ∣ w ∧ Nat.Coprime d v} := by
        ext d
        constructor
        · rintro ⟨hd, hc⟩
          exact ⟨dvd_trans hd (Nat.div_dvd_of_dvd hgw), hc⟩
        · rintro ⟨hd, hc⟩
          refine ⟨?_, hc⟩
          have hcg : Nat.Coprime d g := Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right w v) hc
          apply hcg.dvd_of_dvd_mul_right
          rw [Nat.div_mul_cancel hgw]
          exact hd
      rw [hset] at key
      exact key

/-- `coprimePart w v` is the greatest divisor of `w > 0` which is prime to `v`. -/
theorem coprimePart_isGreatest (w v : ℕ) (hw : 0 < w) :
    IsGreatest {d | d ∣ w ∧ Nat.Coprime d v} (coprimePart w v) :=
  strip_isGreatest v w w hw le_rfl

theorem state_succ (n : ℕ) :
    state (n + 1) = (coprimePart (state n).2 (state n).1,
      (state n).2 + coprimePart (state n).2 (state n).1) := by
  unfold state
  rw [Function.iterate_succ_apply']
  rfl

/-- `a(1) = 1`. -/
theorem a_one : a 1 = 1 := rfl

theorem a_succ_succ (n : ℕ) : a (n + 2) = coprimePart (state n).2 (state n).1 := by
  show (state (n + 1)).1 = _
  rw [state_succ]

theorem s_succ (n : ℕ) : s (n + 1) = s n + a (n + 1) := by
  unfold s
  rw [Finset.sum_Icc_succ_top (by omega)]

/-- The second component of `state n` is the partial sum `s(n+1)`. -/
theorem state_snd (n : ℕ) : (state n).2 = s (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [s_succ, ← ih, state_succ, a_succ_succ]

theorem s_pos (n : ℕ) : 0 < s (n + 1) := by
  rw [s_succ]
  cases n with
  | zero => simp [a_one]
  | succ n => have := s_pos n; omega

/-- The OEIS definition: for every `n ≥ 1`, `a(n+1)` is the greatest divisor of the partial sum
`s(n)` which is prime to `a(n)`. -/
theorem a_succ_isGreatest (n : ℕ) (hn : 1 ≤ n) :
    IsGreatest {d | d ∣ s n ∧ Nat.Coprime d (a n)} (a (n + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_succ_succ, state_snd]
  exact coprimePart_isGreatest _ _ (s_pos m)

/-! ### Data checks -/

/-- The definition reproduces all 67 terms listed in OEIS, `a 1, …, a 67` (kernel-checked). -/
theorem a_data : (List.range 67).map (fun i => a (i + 1)) =
    [1, 1, 2, 1, 5, 2, 3, 5, 4, 3, 1, 28, 1, 57, 2, 29, 5, 6, 13, 1, 170, 1, 341, 2, 171, 5, 172,
      3, 115, 2, 9, 43, 28, 11, 113, 12, 19, 73, 20, 37, 41, 38, 21, 11, 148, 3, 593, 4, 297, 1,
      2674, 1, 5349, 2, 2675, 1, 13376, 1, 26753, 2, 13377, 5, 13378, 3, 991, 82, 31] := by
  decide +kernel

/-- The partial sums reproduce all 50 terms listed in A355149, `s 1, …, s 50`
(kernel-checked). -/
theorem s_data : (List.range 50).map (fun i => s (i + 1)) =
    [1, 2, 4, 5, 10, 12, 15, 20, 24, 27, 28, 56, 57, 114, 116, 145, 150, 156, 169, 170, 340,
      341, 682, 684, 855, 860, 1032, 1035, 1150, 1152, 1161, 1204, 1232, 1243, 1356, 1368, 1387,
      1460, 1480, 1517, 1558, 1596, 1617, 1628, 1776, 1779, 2372, 2376, 2673, 2674] := by
  decide +kernel

/-- The entry's last example: `a(150) = 473394`, `a(151) = 1`, `a(152) = 2840365`,
`a(153) = 2` (kernel-checked). -/
theorem a_example : (List.range 4).map (fun i => a (i + 150)) = [473394, 1, 2840365, 2] := by
  decide +kernel

/-! ### The conjectures -/

/-- Sycamore's conjecture: `a(n) = 1` occurs infinitely many times, and so does `a(n) = 2`. -/
def sycamore : Prop :=
  {n : ℕ | a n = 1}.Infinite ∧ {n : ℕ | a n = 2}.Infinite

/-- Sigrist's first conjecture: `a(2(n+21)-1) = a(2n-1)` for all `n ≥ 70`. -/
def sigristOdd : Prop :=
  ∀ n : ℕ, 70 ≤ n → a (2 * (n + 21) - 1) = a (2 * n - 1)

/-- Sigrist's second conjecture: `a(2(n+21)) = 3645 a(2n) + b(n)` for all `n ≥ 70`, for some
21-periodic integer sequence `b`. -/
def sigristEven : Prop :=
  ∃ b : ℕ → ℤ, (∀ n, b (n + 21) = b n) ∧
    ∀ n : ℕ, 70 ≤ n → (a (2 * (n + 21)) : ℤ) = 3645 * (a (2 * n) : ℤ) + b n

/-- The A355149 conjecture: the partial sums satisfy `s(n+42) = 3645 s(n) + c(n)` for all
`n ≥ 138`, for some 42-periodic integer sequence `c`. -/
def partialSums : Prop :=
  ∃ c : ℕ → ℤ, (∀ n, c (n + 42) = c n) ∧
    ∀ n : ℕ, 138 ≤ n → (s (n + 42) : ℤ) = 3645 * (s n : ℤ) + c n

/-- The conjectures on A351743 and its partial sums A355149: `1` and `2` occur infinitely often
(Sycamore); the odd-indexed terms are eventually 42-periodic and the even-indexed terms satisfy
`a(2(n+21)) = 3645 a(2n) + b(n)` with `b` 21-periodic, both for `n ≥ 70` (Sigrist); and the
partial sums satisfy `s(n+42) = 3645 s(n) + c(n)` with `c` 42-periodic, for `n ≥ 138`
(A355149). -/
def statement : Prop :=
  sycamore ∧ sigristOdd ∧ sigristEven ∧ partialSums

end Math0.Statements.A351743
