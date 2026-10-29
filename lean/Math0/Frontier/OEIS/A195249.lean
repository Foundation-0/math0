/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A195249
import Math0.Audit

/-!
# 3 × 3 lower triangles with neighbours differing by at most two (A195249)

We prove Hardin's empirical formula `a(n) = 1047 n - 1459` for all `n > 2`.

Split the count by the entry `x₀` at the apex: `a n = ∑_{c ≤ n} T n c`, where `T n c` counts the
valid triangles with entries in `0..n` and apex `c` (this is the inner part of the pruned copy
`aL` of the statement file, in which every entry is searched within distance two of an already
chosen neighbour, and every window is centred at `x₀`, `x₁` or `x₂`, all within two of `c`).

* *Upper stability* (`T_up`): if `c + 4 ≤ n` then `T (n+1) c = T n c`, since all windows are
  centred at values `≤ c + 2 ≤ n - 2` and so are not clipped by the upper bound.
* *Translation* (`T_shift`): if `4 ≤ c` then `T (n+1) (c+1) = T n c`, since all windows are
  centred at values `≥ c - 2 ≥ 2` and so are not clipped at `0`; shifting every entry by one is
  then a bijection, and `near` is translation invariant.

Hence for `m ≥ 0`, splitting off the apices `c < 4` (unchanged by `T_up`) and shifting the
apices `c ≥ 5` down by one (`T_shift`), `a (m + 8) = a (m + 7) + T (m + 8) 4`, and
`T (m + 8) 4 = T 8 4 = 1047` by `T_up` and a kernel computation. With `a 7 = 5870` this gives
`a n = 1047 n - 1459` for `n ≥ 7`; the values `n = 3, …, 6` are kernel computations.
-/

namespace Math0.Frontier.A195249
open Math0.Statements.A195249 Finset

/-- `T n c`: the number of valid triangles with entries in `0..n` whose apex entry is `c`,
written as the inner part of the pruned sum `aL`. -/
private def T (n x0 : ℕ) : ℕ :=
  lsum (win n x0) fun x1 =>
  lsum (win n x0) fun x2 => if near x1 x2 then
  lsum (win n x1) fun x3 => if near x2 x3 then
  lsum (win n x1) fun x4 => if near x2 x4 ∧ near x3 x4 then
  lsum (win n x2) fun x5 => if near x4 x5 then 1 else 0
  else 0 else 0 else 0

/-- `a n` split according to the apex entry. -/
private theorem a_eq_sum (n : ℕ) : a n = ∑ c ∈ range (n + 1), T n c := by
  rw [a_eq_aL, sum_range_eq_lsum]
  rfl

/-- Congruence for `lsum` with membership hypotheses. -/
private theorem lsum_congr {l : List ℕ} {f g : ℕ → ℕ} (h : ∀ x ∈ l, f x = g x) :
    lsum l f = lsum l g := by
  rw [lsum_eq, lsum_eq, List.map_congr_left h]

/-- Summing over a list shifted by one. -/
private theorem lsum_map_succ (l : List ℕ) (f : ℕ → ℕ) :
    lsum (l.map (· + 1)) f = lsum l (fun x => f (x + 1)) := by
  rw [lsum_eq, lsum_eq, List.map_map]
  rfl

/-- Elements of a window lie within two of its centre and in `0..n`. -/
private theorem mem_win {n y x : ℕ} (h : x ∈ win n y) : y - 2 ≤ x ∧ x ≤ y + 2 ∧ x ≤ n := by
  unfold win at h
  rw [List.mem_range'_1] at h
  omega

/-- A window centred well below the upper bound does not see the upper bound. -/
private theorem win_succ_up {n y : ℕ} (h : y + 2 ≤ n) : win (n + 1) y = win n y := by
  unfold win
  congr 1
  omega

/-- A window centred at `≥ 2` is translated along with its centre and the upper bound. -/
private theorem win_succ_shift {n y : ℕ} (h : 2 ≤ y) :
    win (n + 1) (y + 1) = (win n y).map (· + 1) := by
  unfold win
  rw [show (fun x : ℕ => x + 1) = (1 + ·) from funext fun x => Nat.add_comm x 1,
    List.map_add_range']
  congr 1 <;> omega

/-- `near` is translation invariant. -/
private theorem near_succ (x y : ℕ) : near (x + 1) (y + 1) ↔ near x y := by
  unfold near
  omega

/-- Raising the upper bound does not change the count for apices far below it. -/
private theorem T_up {n c : ℕ} (h : c + 4 ≤ n) : T (n + 1) c = T n c := by
  unfold T
  rw [win_succ_up (by omega)]
  refine lsum_congr fun x1 h1 => ?_
  have h1' := mem_win h1
  refine lsum_congr fun x2 h2 => ?_
  have h2' := mem_win h2
  rw [win_succ_up (by omega : x1 + 2 ≤ n), win_succ_up (by omega : x2 + 2 ≤ n)]

/-- Translating the apex and the upper bound together does not change the count, as long as
the apex is far above `0`. -/
private theorem T_shift {n c : ℕ} (h : 4 ≤ c) : T (n + 1) (c + 1) = T n c := by
  unfold T
  rw [win_succ_shift (by omega : 2 ≤ c), lsum_map_succ]
  refine lsum_congr fun x1 h1 => ?_
  have h1' := mem_win h1
  rw [lsum_map_succ]
  refine lsum_congr fun x2 h2 => ?_
  have h2' := mem_win h2
  rw [win_succ_shift (by omega : 2 ≤ x1), win_succ_shift (by omega : 2 ≤ x2)]
  simp only [lsum_map_succ, near_succ]

/-- The number of valid triangles with apex `4` and entries in `0..8` (kernel computation). -/
private theorem T_eight : T 8 4 = 1047 := by
  decide +kernel

/-- The apex-`4` count is `1047` as soon as the upper bound is at least `8`. -/
private theorem T_four (m : ℕ) : T (m + 8) 4 = 1047 := by
  induction m with
  | zero => exact T_eight
  | succ m ih => rw [show m + 1 + 8 = m + 8 + 1 by omega, T_up (by omega), ih]

/-- Splitting off the first four terms of a sum over a range. -/
private theorem split4 (n : ℕ) (f : ℕ → ℕ) :
    ∑ c ∈ range (n + 4), f c = ∑ c ∈ range 4, f c + ∑ c ∈ range n, f (c + 4) := by
  rw [add_comm n 4, sum_range_add]
  exact congrArg _ (sum_congr rfl fun x _ => by rw [add_comm])

/-- The first differences are constant from `n = 7` on. -/
private theorem step (m : ℕ) : a (m + 8) = a (m + 7) + 1047 := by
  have e1 : a (m + 8) = ∑ c ∈ range ((m + 5) + 4), T (m + 8) c := a_eq_sum (m + 8)
  have e2 : a (m + 7) = ∑ c ∈ range ((m + 4) + 4), T (m + 7) c := a_eq_sum (m + 7)
  have h1 : ∑ x ∈ range 4, T (m + 8) x = ∑ x ∈ range 4, T (m + 7) x :=
    sum_congr rfl fun x hx => by
      rw [mem_range] at hx
      exact T_up (by omega)
  have h2 : ∑ x ∈ range (m + 4), T (m + 8) (x + 1 + 4) =
      ∑ x ∈ range (m + 4), T (m + 7) (x + 4) :=
    sum_congr rfl fun x _ => by
      rw [show x + 1 + 4 = x + 4 + 1 by omega]
      exact T_shift (by omega)
  rw [e1, e2, split4 (m + 5) (T (m + 8)), split4 (m + 4) (T (m + 7)),
    sum_range_succ' (fun c => T (m + 8) (c + 4)) (m + 4), h1, h2, zero_add, T_four]
  ring

/-- Small values, computed in the kernel. -/
private theorem a_vals : a 3 = 1682 ∧ a 4 = 2729 ∧ a 5 = 3776 ∧ a 6 = 4823 ∧ a 7 = 5870 := by
  simp only [a_eq_aL]
  decide +kernel

/-- The formula for `n ≥ 7`. -/
private theorem formula (m : ℕ) : (a (m + 7) : ℤ) = 1047 * ((m + 7 : ℕ) : ℤ) - 1459 := by
  induction m with
  | zero => rw [a_vals.2.2.2.2]; norm_num
  | succ m ih =>
    rw [show m + 1 + 7 = m + 8 by omega, step, Nat.cast_add, ih]
    push_cast
    ring

/-- Hardin's formula: `a(n) = 1047 n - 1459` for every `n > 2`. -/
theorem result : statement := by
  intro n hn
  obtain h | h := le_total n 7
  · obtain ⟨h3, h4, h5, h6, h7⟩ := a_vals
    interval_cases n
    · rw [h3]; norm_num
    · rw [h4]; norm_num
    · rw [h5]; norm_num
    · rw [h6]; norm_num
    · rw [h7]; norm_num
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
    exact formula m

end Math0.Frontier.A195249

#math0_settles Math0.Frontier.A195249.result Math0.Statements.A195249.statement
