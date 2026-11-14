/-
  Frontier7000SpreadBounds.lean
  Core Lean 4 (zero external dependencies, zero `sorry`, zero `axiom`, zero `native_decide`)
  Exact Integer Witnesses & Algebraic Invariants for the Frontier #7000 Paid-Call Spread Scan:
    1. Exact 3-stratum decomposition of Frontier #7000's 117,612 paid calls and 23,392 targets,
       and exact rank surplus `S = 321,364 - 319,844 = 1,520`.
    2. Count and rank-mass invariance under arbitrary symmetric `(r, r) -> (r - d, r + d)` spreads
       and under the unique `[1, 8]` Bauer-Karamata extreme-point balayage `{1: 5645, 5: 1, 8: 664}`.
    3. All 12 exact integer concavity witnesses `r^(2*r) < (r - d)^(r - d) * (r + d)^(r + d)`
       governing every legal symmetric spread inside the 9-slot native rank cap `1 <= r - d < r + d <= 8`.
    4. Exact telescoping invariance of two-step `MOVE` compositions under commuting spectator contacts.

  License: Apache-2.0
-/

namespace Frontier7000SpreadBounds

/-! ## Section 1: Exact Frontier #7000 Accounting & Rank-Surplus Conservation -/

/-- Total productive targets `T` in `research/shared-wire-split-composition/FULL-RESULT.json` (`23,392`). -/
theorem frontier7000_productive_count :
    234 + 324 + 792 + 3870 + 1224 + 756 + 324 + 1206 + 11126 + 8 * 416 + 208 = 23392 := by
  omega

/-- Decomposition of productive targets into `18 * 1,080 = 19,440` helpers + `3,952` root fields. -/
theorem frontier7000_productive_stratum_split :
    18 * (13 + 18 + 44 + 215 + 68 + 42 + 18 + 67 + 595) = 19440 ∧
    (416 + 8 * 416 + 208 = 3952) ∧
    (19440 + 3952 = 23392) := by
  omega

/-- Total paid calls `P` (`117,612`) and exact 3-stratum split (`113,580` native + `416` QUERY + `3,616` whole-idle). -/
theorem frontier7000_paid_stratum_split :
    18 * (4075 + 828 + 811 + 241 + 320 + 17 + 12 + 6) = 113580 ∧
    (704 + 7 * 416 = 3616) ∧
    (113580 + 416 + 3616 = 117612) ∧
    (73766 + 14904 + 14598 + 4338 + 5760 + 306 + 216 + 812 + 7 * 416 = 117612) := by
  omega

/-- Exact Frontier #7000 global rank-mass conservation & surplus `S = 1,520`. -/
theorem frontier7000_rank_surplus_1520 :
    let mass_T := 1*234 + 2*324 + 3*792 + 4*3870 + 5*1224 + 6*756 + 7*324 + 8*1206 + 9*11126
                  + (17 + 25 + 33 + 41 + 49 + 57 + 65 + 73) * 416 + 145 * 208
    let mass_P := 1*73766 + 2*14904 + 3*14598 + 4*4338 + 5*5760 + 6*306 + 7*216 + 8*812
                  + (16 + 24 + 32 + 40 + 48 + 56 + 64) * 416
    mass_T = 321364 ∧ mass_P = 319844 ∧ mass_T - mass_P = 1520 := by
  omega

/-- Any `k`-pair symmetric spread `(r, r) -> (r - d, r + d)` preserves total call count and total rank mass. -/
theorem symmetric_spread_preserves_count_and_mass (r d k count0 mass0 : Int) :
    (count0 - 2 * k + k + k = count0) ∧
    (mass0 - 2 * k * r + k * (r - d) + k * (r + d) = mass0) := by
  have h1 : k * (r - d) = k * r - k * d := Int.mul_sub k r d
  have h2 : k * (r + d) = k * r + k * d := Int.mul_add k r d
  omega

/-- Exact `[1, 8]` Bauer-Karamata extreme-point balayage of `native.paid` (`N = 6,310`, `M = 10,962`). -/
theorem native_paid_balayage_conservation :
    let n_orig := 4075 + 828 + 811 + 241 + 320 + 17 + 12 + 6
    let m_orig := 1*4075 + 2*828 + 3*811 + 4*241 + 5*320 + 6*17 + 7*12 + 8*6
    n_orig = 6310 ∧ m_orig = 10962 ∧
    (5645 + 1 + 664 = 6310) ∧
    (1 * 5645 + 5 * 1 + 8 * 664 = 10962) := by
  omega

/-! ## Section 2: All 12 First-Order Integer Concavity Witnesses on `[1, 8]` -/

theorem spread_witness_2_to_1_3 : (2 : Nat) ^ 4 < 1 ^ 1 * 3 ^ 3 := by decide
theorem spread_witness_3_to_2_4 : (3 : Nat) ^ 6 < 2 ^ 2 * 4 ^ 4 := by decide
theorem spread_witness_3_to_1_5 : (3 : Nat) ^ 6 < 1 ^ 1 * 5 ^ 5 := by decide
theorem spread_witness_4_to_3_5 : (4 : Nat) ^ 8 < 3 ^ 3 * 5 ^ 5 := by decide
theorem spread_witness_4_to_2_6 : (4 : Nat) ^ 8 < 2 ^ 2 * 6 ^ 6 := by decide
theorem spread_witness_4_to_1_7 : (4 : Nat) ^ 8 < 1 ^ 1 * 7 ^ 7 := by decide
theorem spread_witness_5_to_4_6 : (5 : Nat) ^ 10 < 4 ^ 4 * 6 ^ 6 := by decide
theorem spread_witness_5_to_3_7 : (5 : Nat) ^ 10 < 3 ^ 3 * 7 ^ 7 := by decide
theorem spread_witness_5_to_2_8 : (5 : Nat) ^ 10 < 2 ^ 2 * 8 ^ 8 := by decide
theorem spread_witness_6_to_5_7 : (6 : Nat) ^ 12 < 5 ^ 5 * 7 ^ 7 := by decide
theorem spread_witness_6_to_4_8 : (6 : Nat) ^ 12 < 4 ^ 4 * 8 ^ 8 := by decide
theorem spread_witness_7_to_6_8 : (7 : Nat) ^ 14 < 6 ^ 6 * 8 ^ 8 := by decide

/-- Conjunction certifying all 12 legal pairwise symmetric spreads inside `[1, 8]`. -/
theorem all_12_native_spread_witnesses :
    ((2 : Nat) ^ 4 < 1 ^ 1 * 3 ^ 3) ∧
    ((3 : Nat) ^ 6 < 2 ^ 2 * 4 ^ 4) ∧
    ((3 : Nat) ^ 6 < 1 ^ 1 * 5 ^ 5) ∧
    ((4 : Nat) ^ 8 < 3 ^ 3 * 5 ^ 5) ∧
    ((4 : Nat) ^ 8 < 2 ^ 2 * 6 ^ 6) ∧
    ((4 : Nat) ^ 8 < 1 ^ 1 * 7 ^ 7) ∧
    ((5 : Nat) ^ 10 < 4 ^ 4 * 6 ^ 6) ∧
    ((5 : Nat) ^ 10 < 3 ^ 3 * 7 ^ 7) ∧
    ((5 : Nat) ^ 10 < 2 ^ 2 * 8 ^ 8) ∧
    ((6 : Nat) ^ 12 < 5 ^ 5 * 7 ^ 7) ∧
    ((6 : Nat) ^ 12 < 4 ^ 4 * 8 ^ 8) ∧
    ((7 : Nat) ^ 14 < 6 ^ 6 * 8 ^ 8) := by
  decide

/-! ## Section 3: Commuting-Spectator Flag Re-Pivoting Invariance -/

/-- Abstract monoid/operator composition lemma: if step-1 quotient `Q1 = S * Q1'` where the deferred
    subspace factor `S` commutes with the intervening contact operator `C` (`C * S = S * C`),
    then `(Q2 * C * Q1) = ((Q2 * S) * C * Q1')`, preserving exact end-to-end semantics while
    replacing transition `(Q1, Q2)` with `(Q1', Q2 * S)`. -/
theorem repivot_commuting_contact_invariance
    {M : Type} [Mul M]
    (h_assoc : ∀ a b c : M, (a * b) * c = a * (b * c))
    (Q2 C S Q1' : M)
    (h_comm : C * S = S * C) :
    (Q2 * C) * (S * Q1') = ((Q2 * S) * C) * Q1' := by
  rw [← h_assoc Q2 C (S * Q1')]
  rw [← h_assoc (Q2 * C) S Q1']
  rw [h_assoc Q2 C S]
  rw [h_comm]
  rw [← h_assoc Q2 S C]

/-- Rational cross-multiplication ordering of Frontier #7000 Complex vs BIT Premise vs BIT Ordinary savings. -/
theorem frontier7000_bit_headroom_hierarchy :
    let k_complex_num := 363005817
    let k_complex_den := 100000000000
    let k_premise_num := 376669
    let k_premise_den := 100000000
    let k_bit_num     := 12039
    let k_bit_den     := 3125000
    (k_complex_num * k_premise_den < k_premise_num * k_complex_den) ∧
    (k_premise_num * k_bit_den < k_bit_num * k_premise_den) := by
  omega

end Frontier7000SpreadBounds
