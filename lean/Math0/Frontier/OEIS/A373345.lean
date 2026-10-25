/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A373345
import Math0.Audit

/-!
# Row lengths of the Schreier-set triangle A373345 are A007895

We prove Paolo Xausa's conjecture: row `n` of A373345 (the Schreier set encoded by A371176(n))
has as many elements as the Zeckendorf representation of `n` has terms.

Write `w k` for the binary weight of `k` and `c k = #{j < k : IsTerm j}` (`Nat.count`). Since
A371176 enumerates the terms in increasing order, it suffices to show
`w k = (zeckendorf (c k + 1)).length` for every term `k`.

* **Structure.** For `0 < 2i < 2^p`, `IsTerm (2^p + 2i) ↔ IsTerm i`; `IsTerm (2^p)` always; and
  `2^p + (2i+1)` (with `2i + 1 < 2^p`) is never a term (weight `≥ 2`, lowest bit `0`).
* **Counting.** For `2i ≤ 2^p`, `c (2^p + 2i) = c (2^p) + c i + [i ≠ 0]`. Taking `i = 2^(p-1)`
  gives `c (2^(p+1)) = c (2^p) + c (2^(p-1)) + 1`, so `c (2^p) + 1 = F(p+2)`.
* **Zeckendorf.** For `m < F(p+1)`, the Zeckendorf representation of `F(p+2) + m` is that of `m`
  with `p + 2` prepended.
* **Induction.** A term `k` with top bit `p` is `2^p` or `2^p + 2i` with `i < 2^(p-1)` a term.
  Then `w k = 1 + w i` and `c k + 1 = F(p+2) + (c i + 1)` with `c i + 1 ≤ c (2^(p-1)) < F(p+1)`;
  strong induction on `k` finishes.
-/

namespace Math0.Frontier.A373345
open Math0.Statements.A373345

/-- Binary digits of `2^p + j` for `j < 2^p`: those of `j`, then `p`. -/
private theorem bitIndices_two_pow_add (p : ℕ) : ∀ j, j < 2 ^ p →
    (2 ^ p + j).bitIndices = j.bitIndices ++ [p] := by
  induction p with
  | zero =>
    intro j hj
    obtain rfl : j = 0 := by simpa using hj
    simp
  | succ p ih =>
    intro j hj
    obtain ⟨j', rfl | rfl⟩ := Nat.even_or_odd' j
    · have hj' : j' < 2 ^ p := by rw [pow_succ] at hj; omega
      rw [show 2 ^ (p + 1) + 2 * j' = 2 * (2 ^ p + j') by ring, Nat.bitIndices_two_mul,
        ih j' hj', Nat.bitIndices_two_mul]
      simp
    · have hj' : j' < 2 ^ p := by rw [pow_succ] at hj; omega
      rw [show 2 ^ (p + 1) + (2 * j' + 1) = 2 * (2 ^ p + j') + 1 by ring,
        Nat.bitIndices_two_mul_add_one, ih j' hj', Nat.bitIndices_two_mul_add_one]
      simp

/-- A positive number has a nonempty list of binary digits. -/
private theorem exists_bitIndices_cons (i : ℕ) (hi : i ≠ 0) :
    ∃ a l, i.bitIndices = a :: l := by
  cases h : i.bitIndices with
  | nil =>
    have := Nat.sum_map_two_pow_bitIndices i
    rw [h] at this
    simp at this
    omega
  | cons a l => exact ⟨a, l, rfl⟩

/-- Membership in A371176 for a positive number, via its list of binary digits. -/
private theorem isTerm_iff (k : ℕ) (hk : k ≠ 0) :
    IsTerm k ↔ k.bitIndices.length ≤ k.bitIndices.headD 0 + 1 := by
  rw [IsTerm, padicValNat_two_mul k hk]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨Nat.pos_of_ne_zero hk, h⟩

/-- `2^p + 2i` (with `2i < 2^p`) is a term iff `i = 0` or `i` is a term. -/
private theorem isTerm_two_pow_add_even (p i : ℕ) (hi : 2 * i < 2 ^ p) :
    IsTerm (2 ^ p + 2 * i) ↔ i = 0 ∨ IsTerm i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simpa using isTerm_two_pow p
  · obtain ⟨a, l, hal⟩ := exists_bitIndices_cons i hi0.ne'
    rw [isTerm_iff _ (by positivity), isTerm_iff _ hi0.ne', bitIndices_two_pow_add p _ hi,
      Nat.bitIndices_two_mul, hal]
    simp only [List.map_cons, List.cons_append, List.length_cons, List.length_append,
      List.length_map, List.length_nil, List.headD_cons]
    omega

/-- `2^p + (2i + 1)` (with `2i + 1 < 2^p`) is never a term. -/
private theorem not_isTerm_two_pow_add_odd (p i : ℕ) (hi : 2 * i + 1 < 2 ^ p) :
    ¬ IsTerm (2 ^ p + (2 * i + 1)) := by
  rw [isTerm_iff _ (by positivity), bitIndices_two_pow_add p _ hi,
    Nat.bitIndices_two_mul_add_one]
  simp

/-- Counting terms below `2^p + 2i`. -/
private theorem count_two_pow_add (p : ℕ) : ∀ i, 2 * i ≤ 2 ^ p →
    Nat.count IsTerm (2 ^ p + 2 * i) =
      Nat.count IsTerm (2 ^ p) + Nat.count IsTerm i + (if i = 0 then 0 else 1) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h1 : 2 * i < 2 ^ p := by omega
    have h2 : 2 * i + 1 < 2 ^ p := by omega
    rw [show 2 ^ p + 2 * (i + 1) = (2 ^ p + 2 * i) + 1 + 1 by ring, Nat.count_succ,
      Nat.count_succ, ih (by omega), Nat.count_succ,
      if_neg (show ¬ IsTerm (2 ^ p + 2 * i + 1) from by
        rw [add_assoc]; exact not_isTerm_two_pow_add_odd p i h2)]
    by_cases hi0 : i = 0
    · subst hi0
      have : ¬ IsTerm 0 := fun h => absurd h.1 (lt_irrefl 0)
      simp [isTerm_two_pow, this]
    · by_cases ht : IsTerm i
      · have : IsTerm (2 ^ p + 2 * i) := (isTerm_two_pow_add_even p i h1).2 (Or.inr ht)
        simp [hi0, ht, this]
        omega
      · have : ¬ IsTerm (2 ^ p + 2 * i) := fun h => by
          rcases (isTerm_two_pow_add_even p i h1).1 h with h | h
          · exact hi0 h
          · exact ht h
        simp [hi0, ht, this]

/-- There are `F(p+2) - 1` terms below `2^p`. -/
private theorem count_two_pow (p : ℕ) : Nat.count IsTerm (2 ^ p) + 1 = Nat.fib (p + 2) := by
  have key : ∀ p, Nat.count IsTerm (2 ^ p) + 1 = Nat.fib (p + 2) ∧
      Nat.count IsTerm (2 ^ (p + 1)) + 1 = Nat.fib (p + 3) := by
    have h0 : ¬ IsTerm 0 := fun h => absurd h.1 (lt_irrefl 0)
    intro p
    induction p with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [pow_zero, show (1 : ℕ) = 0 + 1 from rfl, Nat.count_succ, if_neg h0]
        simp
      · have h1 : IsTerm 1 := by simpa using isTerm_two_pow 0
        rw [show (2 : ℕ) ^ (0 + 1) = 0 + 1 + 1 from rfl, Nat.count_succ, Nat.count_succ,
          if_neg h0, if_pos h1]
        simp [Nat.fib_add_two]
    | succ p ih =>
      refine ⟨ih.2, ?_⟩
      have h := count_two_pow_add (p + 1) (2 ^ p) (by rw [pow_succ]; omega)
      rw [show 2 ^ (p + 1) + 2 * 2 ^ p = 2 ^ (p + 1 + 1) by ring,
        if_neg (by positivity)] at h
      rw [h, show p + 1 + 3 = (p + 3) + 1 by ring, Nat.fib_add_one (by omega),
        show p + 3 - 1 = p + 2 by omega, ← ih.1, ← ih.2]
      ring
  exact (key p).1

/-- The Zeckendorf representation of `F(p+2) + m` for `m < F(p+1)` is `p+2` followed by that of
`m`. -/
private theorem zeckendorf_fib_add (p m : ℕ) (hm : m < Nat.fib (p + 1)) :
    (Nat.zeckendorf (Nat.fib (p + 2) + m)).length = (Nat.zeckendorf m).length + 1 := by
  have hpos : 0 < Nat.fib (p + 2) + m := by
    have := Nat.fib_pos.2 (show 0 < p + 2 by omega)
    omega
  have hg : Nat.greatestFib (Nat.fib (p + 2) + m) = p + 2 := by
    apply le_antisymm
    · rw [← Nat.lt_succ_iff, Nat.greatestFib_lt, Nat.fib_add_two (n := p + 1)]
      rw [show p + 1 + 1 = p + 2 by ring]
      omega
    · rw [Nat.le_greatestFib]
      omega
  rw [Nat.zeckendorf_of_pos hpos, hg, Nat.add_sub_cancel_left]
  simp

/-- The main lemma: for every term `k`, its binary weight is the Zeckendorf length of its index
`count k + 1`. -/
private theorem main (k : ℕ) : IsTerm k →
    k.bitIndices.length = (Nat.zeckendorf (Nat.count IsTerm k + 1)).length := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hk0 : k ≠ 0 := hk.1.ne'
    obtain ⟨p, h1, h2⟩ : ∃ p, 2 ^ p ≤ k ∧ k < 2 ^ (p + 1) :=
      ⟨Nat.log 2 k, Nat.pow_log_le_self 2 hk0, Nat.lt_pow_succ_log_self (by norm_num) k⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 ^ p + j := ⟨k - 2 ^ p, by omega⟩
    have hj : j < 2 ^ p := by rw [pow_succ] at h2; omega
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
    · rcases (isTerm_two_pow_add_even p i hj).1 hk with rfl | hi
      · simp only [mul_zero, add_zero, Nat.bitIndices_two_pow, List.length_singleton]
        rw [count_two_pow, ← add_zero (Nat.fib (p + 2)),
          zeckendorf_fib_add p 0 (Nat.fib_pos.2 (by omega))]
        simp
      · have hi0 : i ≠ 0 := hi.1.ne'
        obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by
          rcases Nat.eq_zero_or_pos p with h | h
          · rw [h] at hj; omega
          · omega⟩
        have hiq : i < 2 ^ q := by rw [pow_succ] at hj; omega
        have hlt : i < 2 ^ (q + 1) + 2 * i := by
          have := Nat.one_le_two_pow (n := q + 1); omega
        have IH := ih i hlt hi
        have hc := count_two_pow_add (q + 1) i hj.le
        rw [if_neg hi0] at hc
        have hci : Nat.count IsTerm i + 1 ≤ Nat.count IsTerm (2 ^ q) := by
          have := Nat.count_strict_mono hi hiq
          omega
        have hcq := count_two_pow q
        have hcq1 := count_two_pow (q + 1)
        rw [bitIndices_two_pow_add (q + 1) _ hj, Nat.bitIndices_two_mul, hc,
          show Nat.count IsTerm (2 ^ (q + 1)) + Nat.count IsTerm i + 1 + 1 =
            Nat.fib (q + 1 + 2) + (Nat.count IsTerm i + 1) by omega,
          zeckendorf_fib_add (q + 1) _ (by rw [show q + 1 + 1 = q + 2 by ring]; omega), ← IH]
        simp
    · exact absurd hk (not_isTerm_two_pow_add_odd p i hj)

/-- Row `n` of A373345 has as many elements as the Zeckendorf representation of `n`. -/
theorem result : statement := by
  intro n hn
  have hinf : {k | IsTerm k}.Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨b, hb⟩
    have h := hb (isTerm_two_pow b)
    have := Nat.lt_two_pow_self (n := b)
    omega
  have hterm : IsTerm (Nat.nth IsTerm (n - 1)) := Nat.nth_mem_of_infinite hinf _
  have hcount : Nat.count IsTerm (Nat.nth IsTerm (n - 1)) = n - 1 :=
    Nat.count_nth_of_infinite hinf _
  rw [T, A371176, List.length_reverse, List.length_map, main _ hterm, hcount,
    show n - 1 + 1 = n by omega]

end Math0.Frontier.A373345

#math0_settles Math0.Frontier.A373345.result Math0.Statements.A373345.statement
