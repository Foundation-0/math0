/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A373359
import Math0.Audit

/-!
# A373359: the Schreier-set rows have Zeckendorf-weight lengths

We prove that row `n` of A373359 (the binary support of the `n`-th term of A371176, the encodings
of Schreier sets) has exactly as many elements as the Zeckendorf representation of `n`.

Idea. Let `Q k` mean `popcount k ≤ (lowest set-bit index of k) + 1`, so `Q 0` holds and, for
`k ≥ 1`, `Q k ↔ IsTerm k`. For `2 j < 2 ^ a` the bits of `2 ^ a + 2 j` are those of `j` shifted
by one together with the top bit `a`, so `Q (2 ^ a + 2 j) ↔ Q j`, while `2 ^ a + 2 j + 1`
(for `a ≥ 1`) never satisfies `Q`. Hence, counting `Q`-numbers below a bound,
`count Q (2 ^ a + 2 k) = count Q (2 ^ a) + count Q k` whenever `2 k ≤ 2 ^ a`, and therefore
`count Q (2 ^ a) = fib (a + 2)`. Now by strong induction on `n` there is `k` with `Q k`,
`count Q k = n` and `popcount k = |zeckendorf n|`: for `n > 0`, with `g = greatestFib n = a + 2`
and `n' = n - fib g < fib (a + 1)`, take `k = 2 ^ a + 2 k'` where `k'` is given for `n'`; the
bound on `n'` forces `2 k' < 2 ^ a`. Finally `count IsTerm k = n - 1`, so `k = A371176 n`.
-/

namespace Math0.Frontier.A373359
open Math0.Statements.A373359

/-- The Schreier condition on the binary support, including `0`. -/
private abbrev Q (k : ℕ) : Prop := k.bitIndices.length ≤ k.bitIndices.headD 0 + 1

/-- The bits of `x + 2 ^ a` for `x < 2 ^ a`. -/
private lemma bitIndices_add_two_pow {x a : ℕ} (hx : x < 2 ^ a) :
    (x + 2 ^ a).bitIndices = x.bitIndices ++ [a] := by
  have hs : (x.bitIndices ++ [a]).SortedLT := by
    rw [List.sortedLT_iff_pairwise, List.pairwise_append]
    refine ⟨List.sortedLT_iff_pairwise.1 Nat.bitIndices_sorted, by simp, ?_⟩
    intro i hi j hj
    simp only [List.mem_singleton] at hj
    subst hj
    have := Nat.two_pow_le_of_mem_bitIndices hi
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 (lt_of_le_of_lt this hx)
  have := Nat.bitIndices_sum_map_two_pow hs
  simpa using this

/-- Bits of `2 ^ a + 2 j` for `2 j < 2 ^ a`. -/
private lemma bitIndices_block {a j : ℕ} (h : 2 * j < 2 ^ a) :
    (2 ^ a + 2 * j).bitIndices = (j.bitIndices.map (· + 1)) ++ [a] := by
  rw [add_comm, bitIndices_add_two_pow h, Nat.bitIndices_two_mul]

/-- The Schreier condition is preserved by the block map `j ↦ 2 ^ a + 2 j`. -/
private lemma Q_block {a j : ℕ} (h : 2 * j < 2 ^ a) : Q (2 ^ a + 2 * j) ↔ Q j := by
  simp only [Q]
  rw [bitIndices_block h]
  cases j.bitIndices with
  | nil => simp
  | cons i l => simp

/-- Odd numbers in the block `[2 ^ a, 2 ^ (a + 1))`, `a ≥ 1`, fail the Schreier condition. -/
private lemma not_Q_odd {a j : ℕ} (ha : 1 ≤ a) (h : 2 * j + 1 < 2 ^ a) :
    ¬ Q (2 ^ a + (2 * j + 1)) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hj : j < 2 ^ b := by rw [pow_succ] at h; omega
  have he : 2 ^ (b + 1) + (2 * j + 1) = 2 * (j + 2 ^ b) + 1 := by rw [pow_succ]; ring
  simp only [Q]
  rw [he, Nat.bitIndices_two_mul_add_one, bitIndices_add_two_pow hj]
  simp

/-- Counting `Q`-numbers across a block. -/
private lemma count_block (a k : ℕ) (h : 2 * k ≤ 2 ^ a) :
    Nat.count Q (2 ^ a + 2 * k) = Nat.count Q (2 ^ a) + Nat.count Q k := by
  rw [Nat.count_add]
  congr 1
  induction k with
  | zero => simp
  | succ k ih =>
    have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp at h; omega
      · exact ha
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.count_succ, Nat.count_succ,
      ih (by omega), Nat.count_succ]
    have h1 : Q (2 ^ a + 2 * k) ↔ Q k := Q_block (by omega)
    have h2 : ¬ Q (2 ^ a + (2 * k + 1)) := not_Q_odd ha (by omega)
    simp only [h1, h2, if_false, add_zero]

/-- `count Q (2 ^ a) = fib (a + 2)`. -/
private lemma count_two_pow (a : ℕ) : Nat.count Q (2 ^ a) = Nat.fib (a + 2) := by
  suffices H : ∀ a, Nat.count Q (2 ^ a) = Nat.fib (a + 2) ∧
      Nat.count Q (2 ^ (a + 1)) = Nat.fib (a + 3) from (H a).1
  intro a
  induction a with
  | zero =>
    refine ⟨?_, ?_⟩
    · show Nat.count Q (0 + 1) = 1
      rw [Nat.count_succ]
      simp
    · show Nat.count Q (0 + 1 + 1) = 2
      rw [Nat.count_succ, Nat.count_succ]
      simp
  | succ a ih =>
    refine ⟨ih.2, ?_⟩
    have e : 2 ^ (a + 1 + 1) = 2 ^ (a + 1) + 2 * 2 ^ a := by ring
    have h3 : Nat.fib (a + 1 + 3) = Nat.fib (a + 2) + Nat.fib (a + 3) := Nat.fib_add_two
    rw [e, count_block _ _ (by rw [pow_succ]; omega), ih.1, ih.2, h3]
    omega

/-- The main induction along the Zeckendorf decomposition. -/
private lemma main (n : ℕ) : ∃ k, Q k ∧ Nat.count Q k = n ∧
    k.bitIndices.length = (Nat.zeckendorf n).length := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, by simp [Q], by simp, by simp⟩
  have hg2 : 2 ≤ Nat.greatestFib n := by
    rw [Nat.le_greatestFib, Nat.fib_two]; omega
  obtain ⟨a, ha⟩ : ∃ a, Nat.greatestFib n = a + 2 := ⟨Nat.greatestFib n - 2, by omega⟩
  have hle := Nat.fib_greatestFib_le n
  have hlt := Nat.lt_fib_greatestFib_add_one n
  rw [ha] at hle hlt
  have hfib : Nat.fib (a + 2 + 1) = Nat.fib (a + 1) + Nat.fib (a + 2) := Nat.fib_add_two
  set n' := n - Nat.fib (a + 2) with hn'
  have hn'lt : n' < Nat.fib (a + 1) := by omega
  obtain ⟨k', hQ', hc', hl'⟩ := ih n' (by
    have : 0 < Nat.fib (a + 2) := Nat.fib_pos.2 (by omega)
    omega)
  have hk' : 2 * k' < 2 ^ a := by
    rcases a with _ | b
    · have h0 : n' = 0 := by simp at hn'lt; omega
      rcases Nat.eq_zero_or_pos k' with h | h
      · simp [h]
      · exfalso
        have := Nat.count_monotone Q (show 1 ≤ k' from h)
        simp [Nat.count_succ, Q] at this
        omega
    · by_contra hcon
      have hb : 2 ^ b ≤ k' := by rw [pow_succ] at hcon; omega
      have := Nat.count_monotone Q hb
      rw [count_two_pow] at this
      have e2 : Nat.fib (b + 1 + 1) = Nat.fib (b + 2) := rfl
      omega
  refine ⟨2 ^ a + 2 * k', (Q_block hk').2 hQ', ?_, ?_⟩
  · rw [count_block _ _ hk'.le, count_two_pow, hc']
    omega
  · rw [bitIndices_block hk', Nat.zeckendorf_of_pos hn, ha]
    simp [hl', hn']

/-- `Q` agrees with `IsTerm` on positive integers. -/
private lemma Q_iff_isTerm {k : ℕ} (hk : 0 < k) : Q k ↔ IsTerm k := by
  simp only [Q, IsTerm, padicValNat_two_mul k hk.ne', hk, true_and]

/-- `count Q` exceeds `count IsTerm` by one (for `0`) on positive bounds. -/
private lemma count_Q_eq (k : ℕ) : Nat.count Q (k + 1) = Nat.count IsTerm (k + 1) + 1 := by
  induction k with
  | zero =>
    have : ¬ IsTerm 0 := fun h => (lt_irrefl 0) h.1
    simp [Nat.count_succ, Q, this]
  | succ k ih =>
    rw [Nat.count_succ, Nat.count_succ (p := IsTerm), ih]
    have h := Q_iff_isTerm (show 0 < k + 1 by omega)
    by_cases hq : Q (k + 1)
    · rw [if_pos hq, if_pos (h.1 hq)]
    · rw [if_neg hq, if_neg (fun h' => hq (h.2 h'))]

/-- Every row of A373359 has as many elements as the Zeckendorf representation of its index. -/
theorem result : statement := by
  intro n hn
  obtain ⟨k, hQ, hc, hl⟩ := main n
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at hc; omega
    · exact h
  have hterm : IsTerm k := (Q_iff_isTerm hk).1 hQ
  have hcount : Nat.count IsTerm k = n - 1 := by
    obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
    have := count_Q_eq k0
    omega
  have hA : A371176 n = k := by
    rw [A371176, ← hcount, Nat.nth_count hterm]
  rw [T, List.length_map, hA, hl]

end Math0.Frontier.A373359

#math0_settles Math0.Frontier.A373359.result Math0.Statements.A373359.statement
