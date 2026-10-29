/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A001040
import Math0.Audit

/-!
# Kurkov's rook-tour conjecture for A001040

We prove that the number of open rook tours (directed Hamiltonian paths of `K_n □ K_2`) of the
`n × 2` board whose first and last squares lie on different lines of length `n` is
`2 · n! · a(n)`, where `a(n+1) = n a(n) + a(n-1)`, `a(0) = 0`, `a(1) = 1` (A001040).

**First-step analysis.** Fix the current square `x` on line `c` and the set `U` of squares still to
be visited (`x ∉ U`). By symmetry the number of ways to finish, ending on a line `t`, depends only
on `F` (rows with both squares in `U`), `A` (rows with only their line-`c` square in `U`), `B`
(rows with only their other square in `U`), whether the partner of `x` is in `U`, and whether
`c = t`. The next square is the partner of `x`, a square of a full row on line `c`, or a single
square on line `c`; this gives a recursion (`card_paths`).

**Closed form.** A path with `i` switches between the lines is determined by the ordered switch
rows (`F^{(i)}` choices) and the arrangement of the remaining squares of each line into the
ordered slots of that line (rising factorials). We do not need this bijection: we only check that
the closed form `G` satisfies the recursion (`G_rec`, `g_rec`).

**Summation.** From a fixed corner of the full board the count is
`∑_k (n-1)^{(2k)} ((k+1)^{(n-1-2k)})^2`; its terms satisfy
`w(m+2,k+1) = (m+2)^2 w(m+1,k+1) + (m+2)(m+1) w(m,k)` (the identity
`n(n-2k) + k^2 = (n-k)^2`), so the sum is `(n-1)! a(n)`. Multiplying by the `2n` starting
squares gives `2 · n! · a(n)`.
-/

namespace Math0.Frontier.A001040
open Nat
open Math0.Statements.A001040

/-- `n.ascFactorial (k+1) = n * (n+1).ascFactorial k`. -/
private lemma asc_succ_left (n k : ℕ) : n.ascFactorial (k + 1) = n * (n + 1).ascFactorial k := by
  rw [Nat.ascFactorial_succ, Nat.succ_ascFactorial]

/-- Closed form for the number of paths with exactly `i` switches from a square on line `c`
having no partner, when `F` rows are full, `A` rows have only their line-`c` square and `B` rows
only their other square: `F^{(i)}` ways for the switch rows, then the free squares of each line
are distributed into the ordered slots of that line (rising factorials). -/
private def G (i F A B : ℕ) : ℕ :=
  F.descFactorial i * ((i + 2) / 2).ascFactorial (A + F - i) *
    ((i + 1) / 2).ascFactorial (B + F - i)

/-- `G` vanishes when there are more switches than full rows. -/
private lemma G_eq_zero {i F : ℕ} (A B : ℕ) (h : F < i) : G i F A B = 0 := by
  simp [G, Nat.descFactorial_eq_zero_iff_lt.mpr h]

/-- `G` with `F = i + m`, written without truncated subtraction. -/
private lemma G_add (i m A B : ℕ) : G i (i + m) A B =
    (i + m).descFactorial i * ((i + 2) / 2).ascFactorial (A + m) *
      ((i + 1) / 2).ascFactorial (B + m) := by
  unfold G
  rw [show A + (i + m) - i = A + m by omega, show B + (i + m) - i = B + m by omega]

/-- Key ascending factorial identity. -/
private lemma asc_key (i N : ℕ) : ((i + 2) / 2).ascFactorial (N + 1) =
    (N + 1) * ((i + 2) / 2).ascFactorial N +
      (if i = 0 then 0 else ((i + 2) / 2 - 1).ascFactorial (N + 1)) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · show (1 : ℕ).ascFactorial (N + 1) = (N + 1) * (1 : ℕ).ascFactorial N + 0
    rw [Nat.ascFactorial_succ]; ring
  · rw [if_neg (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, (i + 2) / 2 = k + 1 := ⟨(i + 2) / 2 - 1, by omega⟩
    rw [hk, show k + 1 - 1 = k by omega, asc_succ_left k, Nat.ascFactorial_succ]
    ring

/-- The first summand of the recursion for `G` in closed form. -/
private lemma T1 (i m A B : ℕ) : (i + m) * G i (i + m - 1) A (B + 1) =
    m * (i + m).descFactorial i * ((i + 2) / 2).ascFactorial (A + m - 1) *
      ((i + 1) / 2).ascFactorial (B + m) := by
  rcases m with _ | m
  · rcases i with _ | i
    · simp
    · rw [G_eq_zero _ _ (by omega)]; simp
  · rw [show i + (m + 1) - 1 = i + m by omega, G_add,
      show A + (m + 1) - 1 = A + m by omega, show B + 1 + m = B + (m + 1) by omega]
    have h1 := Nat.succ_descFactorial_succ (i + m) i
    have h2 := Nat.descFactorial_succ (i + m + 1) i
    rw [show i + m + 1 - i = m + 1 by omega] at h2
    rw [show i + (m + 1) = i + m + 1 by omega]
    have : (i + m + 1) * (i + m).descFactorial i = (m + 1) * (i + m + 1).descFactorial i := by
      rw [← h1, h2]
    calc (i + m + 1) * ((i + m).descFactorial i * ((i + 2) / 2).ascFactorial (A + m) *
          ((i + 1) / 2).ascFactorial (B + (m + 1)))
        = ((i + m + 1) * (i + m).descFactorial i) * ((i + 2) / 2).ascFactorial (A + m) *
          ((i + 1) / 2).ascFactorial (B + (m + 1)) := by ring
      _ = _ := by rw [this]

/-- The second summand of the recursion for `G` in closed form. -/
private lemma T2 (i m A B : ℕ) : (if i = 0 then 0 else (i + m) * G (i - 1) (i + m - 1) B A) =
    if i = 0 then 0 else (i + m).descFactorial i * ((i + 1) / 2).ascFactorial (B + m) *
      ((i + 2) / 2 - 1).ascFactorial (A + m) := by
  rcases i with _ | i
  · simp
  · rw [if_neg (by omega), if_neg (by omega), show i + 1 + m - 1 = i + m by omega,
      show i + 1 - 1 = i by omega, G_add, show (i + 1 + 1) / 2 = (i + 2) / 2 by omega,
      show (i + 1 + 2) / 2 - 1 = (i + 1) / 2 by omega, show i + 1 + m = i + m + 1 by omega,
      Nat.succ_descFactorial_succ]
    ring

/-- The third summand of the recursion for `G` in closed form. -/
private lemma T3 (i m A B : ℕ) : A * G i (i + m) (A - 1) B =
    A * (i + m).descFactorial i * ((i + 2) / 2).ascFactorial (A + m - 1) *
      ((i + 1) / 2).ascFactorial (B + m) := by
  rcases A with _ | A
  · simp
  · rw [G_add, show A + 1 - 1 + m = A + 1 + m - 1 by omega]; ring

/-- First-step recursion satisfied by the closed form `G`. -/
private lemma G_rec (i F A B : ℕ) : G i F A B =
    (if F = 0 ∧ A = 0 ∧ B = 0 ∧ i = 0 then 1 else 0) + F * G i (F - 1) A (B + 1) +
      (if i = 0 then 0 else F * G (i - 1) (F - 1) B A) + A * G i F (A - 1) B := by
  rcases lt_or_ge F i with h | h
  · rw [G_eq_zero A B h, G_eq_zero _ _ (show F < i from h)]
    rcases Nat.eq_zero_or_pos F with rfl | hF
    · simp
      omega
    · rw [G_eq_zero _ _ (show F - 1 < i by omega)]
      rw [if_neg (by omega), if_neg (by omega), G_eq_zero _ _ (show F - 1 < i - 1 by omega)]
      simp
  obtain ⟨m, rfl⟩ : ∃ m, F = i + m := ⟨F - i, by omega⟩
  rw [T1, T2, T3, G_add]
  rcases Nat.eq_zero_or_pos (A + m) with hAm | hAm
  · obtain ⟨rfl, rfl⟩ : A = 0 ∧ m = 0 := ⟨by omega, by omega⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rcases B with _ | B <;> simp [Nat.zero_ascFactorial]
    · rw [if_neg (by omega), if_neg (by omega)]
      simp
  · obtain ⟨N, hN⟩ : ∃ N, A + m = N + 1 := ⟨A + m - 1, by omega⟩
    rw [if_neg (by omega), hN, asc_key, show N + 1 - 1 = N by omega]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [if_true]
      have : (N + 1 : ℕ) = m + A := by omega
      rw [this]; ring
    · rw [if_neg (by omega), if_neg (by omega)]
      have : (N + 1 : ℕ) = m + A := by omega
      rw [this]; ring



/-- `g F A B s`: the closed form summed over the numbers of switches of the right parity
(`s` = the path ends on the line it starts on). -/
private def g (F A B : ℕ) (s : Bool) : ℕ :=
  ∑ k ∈ Finset.range (F + 1), G (2 * k + (if s then 0 else 1)) F A B

/-- First-step recursion for `g`: move to a full row of the current line (then either keep
its partner for later or not), or to a single square of the current line. -/
private lemma g_rec (F A B : ℕ) (s : Bool) : g F A B s =
    (if F = 0 ∧ A = 0 ∧ B = 0 ∧ s = true then 1 else 0) + F * g (F - 1) A (B + 1) s +
      F * g (F - 1) B A (!s) + A * g F (A - 1) B s := by
  unfold g
  rw [Finset.sum_congr rfl (fun k _ => G_rec (2 * k + (if s then 0 else 1)) F A B)]
  simp only [Finset.sum_add_distrib]
  congr 1
  congr 1
  congr 1
  · -- base
    rw [Finset.sum_range_succ']
    rw [Finset.sum_eq_zero (fun k _ => if_neg (by omega))]
    cases s <;> simp
  · rcases F with _ | F
    · simp
    · rw [Finset.sum_range_succ, G_eq_zero _ _ (show F + 1 - 1 < 2 * (F + 1) + _ by omega),
        Finset.mul_sum]
      simp
  · rcases F with _ | F
    · simp
    · rw [Finset.mul_sum]
      cases s
      · simp only [Bool.not_false, if_false, if_true, Bool.false_eq_true]
        rw [Finset.sum_range_succ, if_neg (by omega),
          show 2 * (F + 1) + 1 - 1 = 2 * (F + 1) by omega,
          G_eq_zero _ _ (show F + 1 - 1 < 2 * (F + 1) by omega)]
        simp only [mul_zero, add_zero, Nat.add_sub_cancel]
        apply Finset.sum_congr rfl
        intro k _
        rw [if_neg (by omega)]
      · simp only [Bool.not_true, if_false, if_true, Bool.false_eq_true]
        rw [Finset.sum_range_succ', if_pos (by omega), add_zero]
        simp only [Nat.add_sub_cancel]
        apply Finset.sum_congr rfl
        intro k _
        rw [if_neg (by omega), show 2 * (k + 1) + 0 - 1 = 2 * k + 1 by omega]
  · rw [Finset.mul_sum]

/-- The paired summand `m^{(2k)} ((k+1)^{(m-2k)})^2` (falling and rising factorials). -/
private def w (m k : ℕ) : ℕ := m.descFactorial (2 * k) * ((k + 1).ascFactorial (m - 2 * k)) ^ 2

/-- `w m k` vanishes when `m < 2k`. -/
private lemma w_eq_zero {m k : ℕ} (h : m < 2 * k) : w m k = 0 := by
  simp [w, Nat.descFactorial_eq_zero_iff_lt.mpr h]

/-- Pairing the two terms with `2k` and `2k+1` switches gives `w m k`. -/
private lemma G_pair (m k : ℕ) : G (2 * k + 1) m 0 1 + G (2 * k) m 0 0 = w m k := by
  unfold G w
  have e1 : (2 * k + 1 + 2) / 2 = k + 1 := by omega
  have e2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have e3 : (2 * k + 2) / 2 = k + 1 := by omega
  have e4 : (2 * k + 1) / 2 = k := by omega
  have e5 : 1 + m - (2 * k + 1) = m - 2 * k := by omega
  have e6 : 0 + m - (2 * k) = m - 2 * k := by omega
  have e7 : 0 + m - (2 * k + 1) = m - 2 * k - 1 := by omega
  simp only [e1, e2, e4, e5, e6, e7, Nat.descFactorial_succ]
  rcases lt_or_ge m (2 * k) with h | h
  · simp [Nat.descFactorial_eq_zero_iff_lt.mpr h]
  obtain ⟨N, rfl⟩ : ∃ N, m = 2 * k + N := ⟨m - 2 * k, by omega⟩
  rw [show 2 * k + N - 2 * k = N by omega]
  rcases N with _ | N
  · simp
  · rw [show N + 1 - 1 = N by omega, asc_succ_left k, Nat.ascFactorial_succ]
    ring

/-- The count of opposite-line paths from a fixed start, as a sum of `w`. -/
private lemma E_sum (m : ℕ) :
    g m 0 1 false + g m 0 0 true = ∑ k ∈ Finset.range (m + 1), w m k := by
  unfold g
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simpa using G_pair m k

/-- Recursion of `w` at `k = 0`. -/
private lemma w_rec0 (m : ℕ) : w (m + 2) 0 = (m + 2) ^ 2 * w (m + 1) 0 := by
  simp [w, Nat.factorial_succ]
  ring

/-- Termwise recursion of `w`, the identity `n(n-2k) + k^2 = (n-k)^2` in disguise. -/
private lemma w_rec (m j : ℕ) :
    w (m + 2) (j + 1) = (m + 2) ^ 2 * w (m + 1) (j + 1) + (m + 2) * (m + 1) * w m j := by
  rcases lt_or_ge m (2 * j) with h | h
  · rw [w_eq_zero (by omega), w_eq_zero (by omega), w_eq_zero h]; simp
  obtain ⟨N, rfl⟩ : ∃ N, m = 2 * j + N := ⟨m - 2 * j, by omega⟩
  unfold w
  rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, show 2 * j + N + 2 = 2 * j + N + 1 + 1 by ring,
    Nat.succ_descFactorial_succ, Nat.succ_descFactorial_succ, Nat.succ_descFactorial_succ,
    Nat.descFactorial_succ, show 2 * j + N - 2 * j = N by omega,
    show 2 * j + N + 1 + 1 - (2 * j + 1 + 1) = N by omega,
    show 2 * j + N + 1 - (2 * j + 1 + 1) = N - 1 by omega, show j + 1 + 1 = j + 2 by ring]
  rcases N with _ | N
  · simp; ring
  · rw [show N + 1 - 1 = N by omega, Nat.ascFactorial_succ, asc_succ_left (j + 1)]
    rw [show j + 1 + 1 = j + 2 by ring]
    ring

/-- The sum of `w` equals `m! * a (m+1)`. -/
private lemma S_eq (m : ℕ) : ∑ k ∈ Finset.range (m + 1), w m k = m ! * a (m + 1) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | m
    · simp [w, a]
    · simp [w, a, Finset.sum_range_succ]
    · rw [Finset.sum_range_succ', w_rec0]
      simp only [w_rec, Finset.sum_add_distrib, ← Finset.mul_sum]
      have h1 : ∑ k ∈ Finset.range (m + 2), w (m + 1) (k + 1) + w (m + 1) 0 =
          ∑ k ∈ Finset.range (m + 1 + 1), w (m + 1) k := by
        rw [← Finset.sum_range_succ', Finset.sum_range_succ, w_eq_zero (by omega), add_zero]
      have h2 : ∑ k ∈ Finset.range (m + 2), w m k = ∑ k ∈ Finset.range (m + 1), w m k := by
        rw [Finset.sum_range_succ, w_eq_zero (by omega), add_zero]
      have e : a (m + 1 + 1 + 1) = (m + 2) * a (m + 2) + a (m + 1) := by
        show a (m + 1 + 2) = _; rw [a]
      rw [h2, ih m (by omega)]
      have h3 := ih (m + 1) (by omega)
      rw [← h1] at h3
      calc (m + 2) ^ 2 * ∑ k ∈ Finset.range (m + 2), w (m + 1) (k + 1) +
            (m + 2) * (m + 1) * (m ! * a (m + 1)) + (m + 2) ^ 2 * w (m + 1) 0
          = (m + 2) ^ 2 * (∑ k ∈ Finset.range (m + 2), w (m + 1) (k + 1) + w (m + 1) 0) +
            (m + 2) * (m + 1) * (m ! * a (m + 1)) := by ring
        _ = _ := by
          rw [h3, e]; simp only [Nat.factorial_succ]
          ring

variable {n : ℕ}

/-- The other line. -/
private def oth (c : Fin 2) : Fin 2 := 1 - c

/-- The other line differs. -/
private lemma oth_ne (c : Fin 2) : oth c ≠ c := by fin_cases c <;> decide
/-- The other line differs (symmetric form). -/
private lemma ne_oth (c : Fin 2) : c ≠ oth c := fun h => oth_ne c h.symm
/-- `oth` is an involution. -/
private lemma oth_oth (c : Fin 2) : oth (oth c) = c := by fin_cases c <;> decide
/-- Every line is `c` or `oth c`. -/
private lemma eq_or_eq_oth (c d : Fin 2) : d = c ∨ d = oth c := by
  fin_cases c <;> fin_cases d <;> decide
/-- Ending on line `t` from the other line. -/
private lemma decide_oth (c t : Fin 2) : decide (oth c = t) = !decide (c = t) := by
  fin_cases c <;> fin_cases t <;> decide

/-- Rows with both squares in `U`. -/
private def full (U : Finset (Fin n × Fin 2)) (c : Fin 2) : ℕ :=
  (Finset.univ.filter fun r : Fin n => (r, c) ∈ U ∧ (r, oth c) ∈ U).card

/-- Rows whose only square in `U` is the one on line `c`. -/
private def only (U : Finset (Fin n × Fin 2)) (c : Fin 2) : ℕ :=
  (Finset.univ.filter fun r : Fin n => (r, c) ∈ U ∧ (r, oth c) ∉ U).card

/-- `full` does not depend on the line. -/
private lemma full_oth (U : Finset (Fin n × Fin 2)) (c : Fin 2) : full U (oth c) = full U c := by
  unfold full
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, oth_oth]
  tauto

/-- Removing a square of a full row. -/
private lemma full_erase_both {U : Finset (Fin n × Fin 2)} {r : Fin n} {c : Fin 2}
    (h1 : (r, c) ∈ U) (h2 : (r, oth c) ∈ U) : full (U.erase (r, c)) c = full U c - 1 := by
  unfold full
  rw [← Finset.card_erase_of_mem
    (s := Finset.univ.filter fun r' : Fin n => (r', c) ∈ U ∧ (r', oth c) ∈ U)
    (a := r) (by simp [h1, h2])]
  congr 1
  ext r'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq,
    Prod.mk.injEq, oth_ne, and_false, not_false_eq_true]
  tauto

/-- Removing a square of a full row does not change the singles of its line. -/
private lemma only_erase_both {U : Finset (Fin n × Fin 2)} {r : Fin n} {c : Fin 2}
    (h2 : (r, oth c) ∈ U) : only (U.erase (r, c)) c = only U c := by
  unfold only
  congr 1
  ext r'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq,
    Prod.mk.injEq, oth_ne, and_false, not_false_eq_true, and_true]
  constructor
  · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩
    refine ⟨⟨?_, h⟩, h'⟩
    rintro rfl; exact h' h2

/-- Removing a square of a full row creates a single on the other line. -/
private lemma only_erase_both_oth {U : Finset (Fin n × Fin 2)} {r : Fin n} {c : Fin 2}
    (h1 : (r, c) ∈ U) (h2 : (r, oth c) ∈ U) :
    only (U.erase (r, c)) (oth c) = only U (oth c) + 1 := by
  unfold only
  rw [oth_oth]
  rw [← Finset.card_insert_of_notMem
    (s := Finset.univ.filter fun r' : Fin n => (r', oth c) ∈ U ∧ (r', c) ∉ U)
    (a := r) (by simp [h1])]
  congr 1
  ext r'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq,
    Prod.mk.injEq, oth_ne, and_false, not_false_eq_true, Finset.mem_insert, and_true]
  by_cases hr : r' = r
  · subst hr; simp [h2]
  · simp [hr]

/-- Removing a single square does not change the full rows. -/
private lemma full_erase_single {U : Finset (Fin n × Fin 2)} {r : Fin n} {c : Fin 2}
    (h2 : (r, oth c) ∉ U) : full (U.erase (r, c)) c = full U c := by
  unfold full
  congr 1
  ext r'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq,
    Prod.mk.injEq, oth_ne, and_false, not_false_eq_true, and_true]
  by_cases hr : r' = r
  · subst hr; simp [h2]
  · simp [hr]

/-- Removing a single square. -/
private lemma only_erase_single {U : Finset (Fin n × Fin 2)} {r : Fin n} {c : Fin 2}
    (h1 : (r, c) ∈ U) (h2 : (r, oth c) ∉ U) : only (U.erase (r, c)) c = only U c - 1 := by
  unfold only
  rw [← Finset.card_erase_of_mem
    (s := Finset.univ.filter fun r' : Fin n => (r', c) ∈ U ∧ (r', oth c) ∉ U)
    (a := r) (by simp [h1, h2])]
  congr 1
  ext r'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq,
    Prod.mk.injEq, oth_ne, and_false, not_false_eq_true, and_true]
  tauto

/-- Removing a single square does not change the singles of the other line. -/
private lemma only_erase_single_oth {U : Finset (Fin n × Fin 2)} {r : Fin n} {c : Fin 2}
    (h2 : (r, oth c) ∉ U) : only (U.erase (r, c)) (oth c) = only U (oth c) := by
  unfold only
  rw [oth_oth]
  congr 1
  ext r'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq,
    Prod.mk.injEq, oth_ne, and_false, not_false_eq_true, and_true]
  by_cases hr : r' = r
  · subst hr; simp [h2]
  · simp [hr]



/-- Paths from `x` (excluded) through exactly the squares of `U`, ending on line `t`. -/
private noncomputable def paths (x : Fin n × Fin 2) (U : Finset (Fin n × Fin 2)) (t : Fin 2) :
    Finset (List (Fin n × Fin 2)) :=
  U.toList.permutations.toFinset.filter fun l => (x :: l).IsChain RookMove ∧ (l.getLastD x).2 = t

/-- Orderings of a finset are exactly the duplicate-free lists with its elements. -/
private lemma perm_toList_iff {U : Finset (Fin n × Fin 2)} {l : List (Fin n × Fin 2)} :
    l.Perm U.toList ↔ l.Nodup ∧ ∀ s, s ∈ l ↔ s ∈ U := by
  constructor
  · intro h
    exact ⟨h.nodup_iff.mpr U.nodup_toList, fun s => by rw [h.mem_iff, Finset.mem_toList]⟩
  · rintro ⟨hl, hs⟩
    exact (List.perm_ext_iff_of_nodup hl U.nodup_toList).mpr fun s => by
      rw [hs, Finset.mem_toList]

/-- Membership in `paths`. -/
private lemma mem_paths {x : Fin n × Fin 2} {U : Finset (Fin n × Fin 2)} {t : Fin 2}
    {l : List (Fin n × Fin 2)} : l ∈ paths x U t ↔
    (l.Nodup ∧ ∀ s, s ∈ l ↔ s ∈ U) ∧ (x :: l).IsChain RookMove ∧
      (l.getLastD x).2 = t := by
  rw [paths, Finset.mem_filter, List.mem_toFinset, List.mem_permutations, perm_toList_iff]

/-- No squares left: only the empty continuation, if we are on the target line. -/
private lemma card_paths_empty (x : Fin n × Fin 2) (t : Fin 2) :
    (paths x ∅ t).card = if x.2 = t then 1 else 0 := by
  have : paths x ∅ t = if x.2 = t then {[]} else ∅ := by
    ext l
    rw [mem_paths]
    rcases l with _ | ⟨y, l⟩
    · split_ifs with h <;> simp [h, List.getLastD]
    · have : ¬ ((y :: l).Nodup ∧
          ∀ s, s ∈ y :: l ↔ s ∈ (∅ : Finset (Fin n × Fin 2))) := by
        rintro ⟨_, h⟩
        simpa using (h y).mp (by simp)
      constructor
      · rintro ⟨h, _⟩; exact absurd h this
      · intro h; split_ifs at h <;> simp at h
  rw [this]
  split_ifs <;> simp

/-- Splitting off the first square of an ordering of `U`. -/
private lemma mem_cons_iff_erase {y : Fin n × Fin 2} {U : Finset (Fin n × Fin 2)}
    {l : List (Fin n × Fin 2)} :
    ((y :: l).Nodup ∧ ∀ s, s ∈ y :: l ↔ s ∈ U) ↔
      y ∈ U ∧ l.Nodup ∧ ∀ s, s ∈ l ↔ s ∈ U.erase y := by
  constructor
  · rintro ⟨hn, hs⟩
    rw [List.nodup_cons] at hn
    refine ⟨(hs y).mp (by simp), hn.2, fun s => ?_⟩
    rw [Finset.mem_erase, ← hs s, List.mem_cons]
    constructor
    · intro h; exact ⟨fun e => hn.1 (e ▸ h), Or.inr h⟩
    · rintro ⟨h1, h2 | h2⟩
      · exact absurd h2 h1
      · exact h2
  · rintro ⟨hy, hn, hs⟩
    refine ⟨List.nodup_cons.mpr ⟨fun h => ?_, hn⟩, fun s => ?_⟩
    · exact (Finset.mem_erase.mp ((hs y).mp h)).1 rfl
    · rw [List.mem_cons, hs s, Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨_, h⟩)
        · exact hy
        · exact h
      · intro h
        by_cases e : s = y
        · exact Or.inl e
        · exact Or.inr ⟨e, h⟩

/-- First-step decomposition of the paths. -/
private lemma paths_eq_biUnion {x : Fin n × Fin 2} {U : Finset (Fin n × Fin 2)} {t : Fin 2}
    (hU : U.Nonempty) :
    paths x U t = (U.filter (RookMove x)).biUnion fun y =>
      (paths y (U.erase y) t).map ⟨List.cons y, List.cons_injective⟩ := by
  ext l
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro hl
    rw [mem_paths] at hl
    rcases l with _ | ⟨y, l⟩
    · obtain ⟨s, hs⟩ := hU
      exact absurd ((hl.1.2 s).mpr hs) (by simp)
    · obtain ⟨h1, h2, h3⟩ := hl
      rw [mem_cons_iff_erase] at h1
      rw [List.isChain_cons_cons] at h2
      refine ⟨y, ⟨h1.1, h2.1⟩, l, ?_, rfl⟩
      rw [mem_paths]
      exact ⟨h1.2, h2.2, by rw [List.getLastD_cons] at h3; exact h3⟩
  · rintro ⟨y, ⟨hy, hxy⟩, l', hl', rfl⟩
    rw [mem_paths] at hl' ⊢
    refine ⟨mem_cons_iff_erase.mpr ⟨hy, hl'.1⟩,
      List.isChain_cons_cons.mpr ⟨hxy, hl'.2.1⟩, ?_⟩
    rw [List.getLastD_cons]; exact hl'.2.2

/-- First-step recursion for the number of paths. -/
private lemma card_paths_succ {x : Fin n × Fin 2} {U : Finset (Fin n × Fin 2)} {t : Fin 2}
    (hU : U.Nonempty) :
    (paths x U t).card = ∑ y ∈ U.filter (RookMove x), (paths y (U.erase y) t).card := by
  rw [paths_eq_biUnion hU, Finset.card_biUnion]
  · simp
  · intro y _ y' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro l h1 h2
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at h1 h2
    obtain ⟨l1, _, rfl⟩ := h1
    obtain ⟨l2, _, e⟩ := h2
    exact hne (List.cons.inj e).1.symm


/-- The predicted number of paths from `x` through `U` ending on line `t`: either the partner of
`x` is kept for later, or (if present) it is the next square. -/
private def Φ (x : Fin n × Fin 2) (U : Finset (Fin n × Fin 2)) (t : Fin 2) : ℕ :=
  g (full U x.2) (only U x.2) (only U (oth x.2)) (decide (x.2 = t)) +
    if (x.1, oth x.2) ∈ U then
      g (full U x.2) (only U (oth x.2) - 1) (only U x.2) (!decide (x.2 = t)) else 0

/-- The base values of `g`. -/
private lemma g_zero (s : Bool) : g 0 0 0 s = if s then 1 else 0 := by
  cases s <;> simp [g, G]

/-- `Φ` after stepping to a square of a full row of the current line. -/
private lemma Φ_both {U : Finset (Fin n × Fin 2)} {r : Fin n} {c t : Fin 2}
    (h1 : (r, c) ∈ U) (h2 : (r, oth c) ∈ U) :
    Φ (r, c) (U.erase (r, c)) t =
      g (full U c - 1) (only U c) (only U (oth c) + 1) (decide (c = t)) +
        g (full U c - 1) (only U (oth c)) (only U c) (!decide (c = t)) := by
  unfold Φ
  have hm : (r, oth c) ∈ U.erase (r, c) :=
    Finset.mem_erase.mpr ⟨by simp [oth_ne], h2⟩
  simp only
  rw [full_erase_both h1 h2, only_erase_both h2, only_erase_both_oth h1 h2, if_pos hm,
    Nat.add_sub_cancel]

/-- `Φ` after stepping to a single square of the current line. -/
private lemma Φ_single {U : Finset (Fin n × Fin 2)} {r : Fin n} {c t : Fin 2}
    (h1 : (r, c) ∈ U) (h2 : (r, oth c) ∉ U) :
    Φ (r, c) (U.erase (r, c)) t =
      g (full U c) (only U c - 1) (only U (oth c)) (decide (c = t)) := by
  unfold Φ
  have hm : (r, oth c) ∉ U.erase (r, c) := fun h => h2 (Finset.mem_of_mem_erase h)
  simp only
  rw [full_erase_single h2, only_erase_single h1 h2, only_erase_single_oth h2, if_neg hm,
    add_zero]

/-- `Φ` after stepping to the other square of the current row. -/
private lemma Φ_partner {U : Finset (Fin n × Fin 2)} {r : Fin n} {c t : Fin 2}
    (hx : (r, c) ∉ U) (h : (r, oth c) ∈ U) :
    Φ (r, oth c) (U.erase (r, oth c)) t =
      g (full U c) (only U (oth c) - 1) (only U c) (!decide (c = t)) := by
  unfold Φ
  have hx' : (r, oth (oth c)) ∉ U := by rw [oth_oth]; exact hx
  have hm : (r, oth (oth c)) ∉ U.erase (r, oth c) := fun h' => hx' (Finset.mem_of_mem_erase h')
  simp only
  rw [full_erase_single hx', only_erase_single h hx', only_erase_single_oth hx', if_neg hm,
    add_zero, full_oth, oth_oth, decide_oth]

/-- Squares of the current line whose partner is present correspond to full rows. -/
private lemma card_full_rows (U : Finset (Fin n × Fin 2)) (c : Fin 2) :
    ((U.filter fun y => y.2 = c).filter fun y => (y.1, oth c) ∈ U).card = full U c := by
  unfold full
  apply Finset.card_nbij' Prod.fst (fun r => (r, c))
  · intro y hy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ,
      true_and] at hy ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hy
    exact ⟨by rw [← h2]; exact h1, h3⟩
  · intro r hr
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ,
      true_and] at hr ⊢
    exact ⟨⟨hr.1, by simp⟩, hr.2⟩
  · intro y hy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_filter] at hy
    obtain ⟨r, d⟩ := y
    simp only at hy ⊢
    rw [hy.1.2]
  · intro r _
    rfl

/-- Squares of the current line whose partner is absent correspond to singles. -/
private lemma card_only_rows (U : Finset (Fin n × Fin 2)) (c : Fin 2) :
    ((U.filter fun y => y.2 = c).filter fun y => ¬ (y.1, oth c) ∈ U).card = only U c := by
  unfold only
  apply Finset.card_nbij' Prod.fst (fun r => (r, c))
  · intro y hy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ,
      true_and] at hy ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hy
    exact ⟨by rw [← h2]; exact h1, h3⟩
  · intro r hr
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ,
      true_and] at hr ⊢
    exact ⟨⟨hr.1, by simp⟩, hr.2⟩
  · intro y hy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_filter] at hy
    obtain ⟨r, d⟩ := y
    simp only at hy ⊢
    rw [hy.1.2]
  · intro r _
    rfl

/-- Main counting lemma: the number of paths from `x` through `U` ending on line `t` is
`Φ x U t`, by induction on `#U`. -/
private theorem card_paths (k : ℕ) :
    ∀ (U : Finset (Fin n × Fin 2)) (x : Fin n × Fin 2) (t : Fin 2),
    U.card = k → x ∉ U → (paths x U t).card = Φ x U t := by
  induction k with
  | zero =>
    intro U x t hU _
    rw [Finset.card_eq_zero] at hU
    subst hU
    rw [card_paths_empty]
    simp [Φ, full, only, g_zero]
  | succ k ih =>
    intro U x t hU hx
    have hne : U.Nonempty := by rw [← Finset.card_pos, hU]; omega
    rw [card_paths_succ hne]
    rw [Finset.sum_congr rfl (fun y hy => ih (U.erase y) y t
      (by rw [Finset.card_erase_of_mem (Finset.mem_filter.mp hy).1, hU]; rfl)
      (Finset.notMem_erase y U))]
    obtain ⟨r, c⟩ := x
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun y => y.2 = c)]
    have hsame : (U.filter (RookMove (r, c))).filter (fun y => y.2 = c) =
        U.filter (fun y => y.2 = c) := by
      ext ⟨r', d⟩
      simp only [Finset.mem_filter, RookMove]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        refine ⟨⟨h1, ?_, Or.inr h3.symm⟩, h3⟩
        rintro e; rw [e] at hx; exact hx h1
    have hpart : ∑ y ∈ (U.filter (RookMove (r, c))).filter (fun y => ¬ y.2 = c),
        Φ y (U.erase y) t =
        if (r, oth c) ∈ U then g (full U c) (only U (oth c) - 1) (only U c) (!decide (c = t))
        else 0 := by
      have hset : (U.filter (RookMove (r, c))).filter (fun y => ¬ y.2 = c) =
          U.filter (fun y => y = (r, oth c)) := by
        ext ⟨r', d⟩
        simp only [Finset.mem_filter, RookMove, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨h1, _, h2⟩, h3⟩
          refine ⟨h1, ?_, ?_⟩
          · rcases h2 with h2 | h2
            · exact h2.symm
            · exact absurd h2.symm h3
          · rcases eq_or_eq_oth c d with h | h
            · exact absurd h h3
            · exact h
        · rintro ⟨h1, rfl, rfl⟩
          exact ⟨⟨h1, by simp [ne_oth], Or.inl rfl⟩, oth_ne c⟩
      rw [hset, Finset.filter_eq' U (r, oth c)]
      split_ifs with h
      · rw [Finset.sum_singleton, Φ_partner hx h]
      · rw [Finset.sum_empty]
    have hsum : ∑ y ∈ U.filter (fun y => y.2 = c), Φ y (U.erase y) t =
        full U c * (g (full U c - 1) (only U c) (only U (oth c) + 1) (decide (c = t)) +
          g (full U c - 1) (only U (oth c)) (only U c) (!decide (c = t))) +
        only U c * g (full U c) (only U c - 1) (only U (oth c)) (decide (c = t)) := by
      rw [← Finset.sum_filter_add_sum_filter_not _ (fun y => (y.1, oth c) ∈ U)]
      have e1 : ∀ y ∈ (U.filter (fun y => y.2 = c)).filter (fun y => (y.1, oth c) ∈ U),
          Φ y (U.erase y) t =
            g (full U c - 1) (only U c) (only U (oth c) + 1) (decide (c = t)) +
              g (full U c - 1) (only U (oth c)) (only U c) (!decide (c = t)) := by
        rintro ⟨r', d⟩ hy
        simp only [Finset.mem_filter] at hy
        obtain ⟨⟨h1, h2⟩, h3⟩ := hy
        subst h2
        exact Φ_both h1 h3
      have e2 : ∀ y ∈ (U.filter (fun y => y.2 = c)).filter (fun y => ¬ (y.1, oth c) ∈ U),
          Φ y (U.erase y) t = g (full U c) (only U c - 1) (only U (oth c)) (decide (c = t)) := by
        rintro ⟨r', d⟩ hy
        simp only [Finset.mem_filter] at hy
        obtain ⟨⟨h1, h2⟩, h3⟩ := hy
        subst h2
        exact Φ_single h1 h3
      rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
      rw [Finset.sum_const, Finset.sum_const, card_full_rows, card_only_rows, smul_eq_mul,
        smul_eq_mul]
    rw [hsame, hsum, hpart]
    have hbase :
        ¬ (full U c = 0 ∧ only U c = 0 ∧ only U (oth c) = 0 ∧ decide (c = t) = true) := by
      rintro ⟨hF, hA, hB, _⟩
      obtain ⟨⟨r', d⟩, hy⟩ := hne
      unfold full at hF
      unfold only at hA hB
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hF hA hB
      rcases eq_or_eq_oth c d with rfl | rfl
      · by_cases h : (r', oth d) ∈ U
        · exact hF (Finset.mem_univ r') ⟨hy, h⟩
        · exact hA (Finset.mem_univ r') ⟨hy, h⟩
      · by_cases h : (r', c) ∈ U
        · exact hF (Finset.mem_univ r') ⟨h, hy⟩
        · exact hB (Finset.mem_univ r') ⟨hy, by rw [oth_oth]; exact h⟩
    unfold Φ
    simp only
    rw [g_rec (full U c) (only U c) (only U (oth c)) (decide (c = t)), if_neg hbase]
    ring

/-- The count from a fixed starting square of the full board. -/
private lemma Φ_init (m : ℕ) (x : Fin (m + 1) × Fin 2) :
    Φ x (Finset.univ.erase x) (oth x.2) = m ! * a (m + 1) := by
  obtain ⟨r, c⟩ := x
  unfold Φ
  simp only
  have hF : full (Finset.univ.erase (r, c)) c = m := by
    unfold full
    rw [show (Finset.univ.filter fun r' : Fin (m + 1) => (r', c) ∈ Finset.univ.erase (r, c) ∧
        (r', oth c) ∈ Finset.univ.erase (r, c)) = Finset.univ.erase r by
      ext r'
      simp [Finset.mem_erase, oth_ne]]
    rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, Fintype.card_fin]
    rfl
  have hA : only (Finset.univ.erase (r, c)) c = 0 := by
    unfold only
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro r' _ ⟨_, h⟩
    exact h (Finset.mem_erase.mpr ⟨by simp [oth_ne], Finset.mem_univ _⟩)
  have hB : only (Finset.univ.erase (r, c)) (oth c) = 1 := by
    unfold only
    rw [Finset.card_eq_one]
    refine ⟨r, ?_⟩
    ext r'
    simp [Finset.mem_erase, oth_oth, oth_ne]
  have hm : (r, oth c) ∈ Finset.univ.erase (r, c) :=
    Finset.mem_erase.mpr ⟨by simp [oth_ne], Finset.mem_univ _⟩
  rw [hF, hA, hB, if_pos hm]
  have : decide (c = oth c) = false := by simp [ne_oth]
  rw [this]
  simp only [Bool.not_false, Nat.sub_self]
  rw [E_sum, S_eq]

/-- Kurkov's conjecture holds: for `n ≥ 1` the number of open rook tours of the `n × 2` board
ending on the opposite line is `2 · n! · a(n)`. -/
theorem result : statement := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [ncard_eq_card_tours]
  have htours : tours (m + 1) = Finset.univ.biUnion fun x =>
      (paths x (Finset.univ.erase x) (oth x.2)).map ⟨List.cons x, List.cons_injective⟩ := by
    ext l
    rw [mem_tours]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨hnd, hall, hch⟩, hend⟩
      obtain ⟨s, hs, u, hu, hsu⟩ := hend
      rcases l with _ | ⟨x, l'⟩
      · simp at hs
      · refine ⟨x, l', ?_, rfl⟩
        rw [mem_paths]
        have h1 := mem_cons_iff_erase.mp
          ⟨hnd, fun s => ⟨fun _ => Finset.mem_univ s, fun _ => hall s⟩⟩
        refine ⟨h1.2, hch, ?_⟩
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hs
        rw [List.getLast?_cons, Option.mem_def, Option.some.injEq] at hu
        subst hs
        rw [List.getLastD_eq_getLast?, hu]
        rcases eq_or_eq_oth x.2 u.2 with h | h
        · exact absurd h.symm hsu
        · exact h
    · rintro ⟨x, l', hl', rfl⟩
      rw [mem_paths] at hl'
      obtain ⟨⟨hnd, hmem⟩, hch, hlast⟩ := hl'
      have h1 := mem_cons_iff_erase.mpr ⟨Finset.mem_univ x, hnd, hmem⟩
      refine ⟨⟨h1.1, fun s => (h1.2 s).mpr (Finset.mem_univ s), hch⟩, ?_⟩
      refine ⟨x, by simp, l'.getLastD x, ?_, ?_⟩
      · rw [List.getLast?_cons, List.getLastD_eq_getLast?]; rfl
      · rw [hlast]; exact ne_oth x.2
  rw [htours, Finset.card_biUnion]
  · simp only [Finset.card_map]
    rw [Finset.sum_congr rfl (fun x _ => card_paths _ _ x _ rfl (Finset.notMem_erase x _))]
    rw [Finset.sum_congr rfl (fun x _ => Φ_init m x)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, smul_eq_mul, Nat.factorial_succ]
    ring
  · intro y _ y' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro l h1 h2
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at h1 h2
    obtain ⟨l1, _, rfl⟩ := h1
    obtain ⟨l2, _, e⟩ := h2
    exact hne (List.cons.inj e).1.symm

end Math0.Frontier.A001040

#math0_settles Math0.Frontier.A001040.result Math0.Statements.A001040.statement
