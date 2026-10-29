/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A368846
import Math0.Audit

/-!
# Diagonal sums of A368846 equal A229580 (Luschny's conjecture)

We prove `|∑_{j=0}^{k} T(k+j, k)| = A229580(k+1)` for all `k`; both sides equal
`(2k+1)·2^(2k-1)` for `k ≥ 1` (and `1` for `k = 0`).

**The sum.** For `k = m+1` and `N = 2m+1`, the terms with `n = k+j` outside `[0, N]` vanish
(`C(2n+1, 2k) = 0` for `n < k`, `C(N, 2k) = 0`), so the sum is
`2(-1)^k ∑_{n=0}^{N} (-1)^n C(N,n) C(2n+1,2k)`. The inner sum is the coefficient of `X^(2k)` in
`(1+X)(1-(1+X)²)^N = -(1+X) X^N (X+2)^N`, i.e. `-([X¹] + [X⁰])(X+2)^N = -(N 2^(N-1) + 2^N)`.

**The count.** Numbering the cells in row-major order turns the array graph into a path, a
coloring into a word of length `2n` over `{0,1,2}`, the mistakes into equal adjacent letters,
and "colors introduced in order" into: the word starts with `0` and every `2` is preceded by a
`1` (`Q2`). Peeling off the first letter gives recursions: proper words with a given first
letter number `2^M`, words with one mistake and given first letter `(M+1)2^M`, and the target
words of length `M+3` number `2^M + (M+1)2^M = (M+2)2^M`.
-/

namespace Math0.Frontier.A368846
open Math0.Statements.A368846 Polynomial Finset

/-- Generating function: `∑ₙ (-1)ⁿ C(N,n) C(2n+1,j)` is the coefficient of `X^j` in `(1+X)(1-(1+X)²)^N`. -/
private theorem polySum (N j : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (N.choose n : ℤ) * ((2 * n + 1).choose j : ℤ) =
      ((1 + X : ℤ[X]) * (-(1 + X) ^ 2 + 1) ^ N).coeff j := by
  rw [add_pow, Finset.mul_sum, finsetSum_coeff]
  refine Finset.sum_congr rfl fun n _ => ?_
  have : (1 + X : ℤ[X]) * ((-(1 + X) ^ 2) ^ n * 1 ^ (N - n) * (N.choose n : ℤ[X])) =
      C ((-1 : ℤ) ^ n * (N.choose n : ℤ)) * (1 + X) ^ (2 * n + 1) := by
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast, one_pow, mul_one]
    rw [neg_pow, ← pow_mul]
    ring
  rw [this, coeff_C_mul, coeff_one_add_X_pow]

/-- Since `1-(1+X)² = -X(X+2)`, the coefficient of `X^(2m+2)` in `(1+X)(1-(1+X)²)^(2m+1)` equals `-[X¹]((1+X)(X+2)^(2m+1)) = -(2m+3)·4^m`. -/
private theorem polyVal (m : ℕ) :
    ((1 + X : ℤ[X]) * (-(1 + X) ^ 2 + 1) ^ (2 * m + 1)).coeff (2 * m + 2) =
      -((2 * m + 3 : ℤ) * 2 ^ (2 * m)) := by
  have h : (1 + X : ℤ[X]) * (-(1 + X) ^ 2 + 1) ^ (2 * m + 1) =
      C (-1) * (X ^ (2 * m + 1) * ((X + C 2) ^ (2 * m + 1) + X * (X + C 2) ^ (2 * m + 1))) := by
    rw [show (-(1 + X) ^ 2 + 1 : ℤ[X]) = -X * (X + C 2) by simp only [map_ofNat]; ring]
    rw [mul_pow, neg_pow, pow_succ (-1 : ℤ[X]), pow_mul]
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [h, coeff_C_mul, coeff_X_pow_mul', if_pos (by omega), show 2 * m + 2 - (2 * m + 1) = 0 + 1 by omega,
    coeff_add, coeff_X_mul, coeff_X_add_C_pow, coeff_X_add_C_pow]
  simp only [zero_add, Nat.choose_one_right, Nat.choose_zero_right, Nat.sub_zero, Nat.add_sub_cancel]
  push_cast
  ring


/-- Closed form of the column sum: `∑_{j=0}^{m+1} T(m+1+j, m+1) = (-1)^m (2m+3) 2^(2m+1)`. -/
private theorem sumT (m : ℕ) : ∑ j ∈ Finset.range (m + 1 + 1), T (m + 1 + j) (m + 1) =
    (-1) ^ m * ((2 * m + 3 : ℤ) * 2 ^ (2 * m + 1)) := by
  have hT : ∀ n, T n (m + 1) = 2 * (-1) ^ (m + 1) *
      ((-1) ^ n * ((2 * m + 1).choose n : ℤ) * ((2 * n + 1).choose (2 * m + 2) : ℤ)) := by
    intro n
    simp only [T, Nat.add_one_ne_zero, if_false]
    rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, show 2 * (m + 1) = 2 * m + 2 by ring]
    ring
  have h1 : ∑ n ∈ Finset.range (2 * m + 3), T n (m + 1) =
      ∑ n ∈ Finset.range (m + 1), T n (m + 1) +
        ∑ j ∈ Finset.range (m + 1 + 1), T (m + 1 + j) (m + 1) := by
    rw [← Finset.sum_range_add]
    congr 2
    omega
  have h2 : ∑ n ∈ Finset.range (m + 1), T n (m + 1) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [Finset.mem_range] at hn
    rw [hT, Nat.choose_eq_zero_of_lt (by omega : 2 * n + 1 < 2 * m + 2)]
    simp
  have h3 : ∑ n ∈ Finset.range (2 * m + 3), T n (m + 1) =
      ∑ n ∈ Finset.range (2 * m + 1 + 1), T n (m + 1) := by
    rw [Finset.sum_range_succ _ (2 * m + 2), hT (2 * m + 2),
      Nat.choose_eq_zero_of_lt (by omega : 2 * m + 1 < 2 * m + 2)]
    simp
  rw [← zero_add (∑ j ∈ Finset.range (m + 1 + 1), T (m + 1 + j) (m + 1)), ← h2, ← h1, h3]
  simp_rw [hT]
  rw [← Finset.mul_sum, polySum, polyVal]
  ring

/-- Absolute value of the column sum for `k = m+1`. -/
private theorem absSumT (m : ℕ) : |∑ j ∈ Finset.range (m + 1 + 1), T (m + 1 + j) (m + 1)| =
    (2 * m + 3 : ℤ) * 2 ^ (2 * m + 1) := by
  rw [sumT, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (by positivity)]


/-- Number of mistakes of a word `w` of length `M+1`: adjacent positions with equal letters. -/
private def wmis {M : ℕ} (w : Fin (M + 1) → Fin 3) : ℕ :=
  ∑ i : Fin M, if w i.castSucc = w i.succ then 1 else 0

/-- Every letter `2` of the word is preceded (strictly earlier) by a letter `1`. -/
private def Q2 {L : ℕ} (w : Fin L → Fin 3) : Prop := ∀ i, w i = 2 → ∃ j, j < i ∧ w j = 1

/-- Decidability of `Q2`. -/
private instance {L : ℕ} : DecidablePred (Q2 (L := L)) := fun w => by unfold Q2; infer_instance

/-- Mistakes of `a :: u`. -/
private theorem wmis_cons {M : ℕ} (a : Fin 3) (u : Fin (M + 1) → Fin 3) :
    wmis (Fin.cons a u : Fin (M + 2) → Fin 3) = (if a = u 0 then 1 else 0) + wmis u := by
  unfold wmis
  rw [Fin.sum_univ_succ]
  congr 1

/-- `Q2 (a :: u)` holds iff `a = 1`, or `a = 0` and `Q2 u`. -/
private theorem Q2_cons {M : ℕ} (a : Fin 3) (u : Fin (M + 1) → Fin 3) :
    Q2 (Fin.cons a u : Fin (M + 2) → Fin 3) ↔ (a = 1 ∨ (a = 0 ∧ Q2 u)) := by
  constructor
  · intro h
    fin_cases a
    · refine Or.inr ⟨rfl, fun i hi => ?_⟩
      obtain ⟨j, hj, hj1⟩ := h i.succ (by simpa using hi)
      cases j using Fin.cases with
      | zero => simp at hj1
      | succ j => exact ⟨j, Fin.succ_lt_succ_iff.mp hj, by simpa using hj1⟩
    · exact Or.inl rfl
    · obtain ⟨j, hj, -⟩ := h 0 (by simp)
      exact absurd hj (Fin.not_lt_zero j)
  · rintro (rfl | ⟨rfl, h⟩) i hi
    · cases i using Fin.cases with
      | zero => simp at hi
      | succ i => exact ⟨0, Fin.succ_pos i, by simp⟩
    · cases i using Fin.cases with
      | zero => simp at hi
      | succ i =>
        obtain ⟨j, hj, hj1⟩ := h i (by simpa using hi)
        exact ⟨j.succ, Fin.succ_lt_succ_iff.mpr hj, by simpa using hj1⟩

/-- A word starting with `1` satisfies `Q2`. -/
private theorem Q2_of_one {M : ℕ} (u : Fin (M + 1) → Fin 3) (h : u 0 = 1) : Q2 u := by
  intro i hi
  refine ⟨0, ?_, h⟩
  rw [Fin.pos_iff_ne_zero]
  rintro rfl
  rw [h] at hi
  exact absurd hi (by decide)

/-- A word starting with `2` fails `Q2`. -/
private theorem not_Q2_of_two {M : ℕ} (u : Fin (M + 1) → Fin 3) (h : u 0 = 2) : ¬ Q2 u := by
  intro hq
  obtain ⟨j, hj, -⟩ := hq 0 h
  exact Fin.not_lt_zero j hj

/-- Counting words of length `M+2` by their first letter and their tail. -/
private theorem card_cons {M : ℕ} (P : (Fin (M + 2) → Fin 3) → Prop) [DecidablePred P] :
    (univ.filter P).card =
      ∑ a : Fin 3, (univ.filter fun u : Fin (M + 1) → Fin 3 => P (Fin.cons a u)).card := by
  simp only [card_filter]
  rw [← (Fin.consEquiv fun _ => Fin 3).sum_comp, Fintype.sum_prod_type]
  rfl

/-- Splitting a count of words according to the first letter. -/
private theorem card_split {M : ℕ} (Q : Fin 3 → (Fin (M + 1) → Fin 3) → Prop)
    [∀ c, DecidablePred (Q c)] :
    (univ.filter fun u => Q (u 0) u).card =
      ∑ c : Fin 3, (univ.filter fun u => u 0 = c ∧ Q c u).card := by
  simp only [card_filter]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [Finset.sum_eq_single (u 0)]
  · simp
  · intro c _ hc
    simp [Ne.symm hc]
  · simp


/-- Peel off a fixed first letter `b` and split on the next letter. -/
private theorem card_first {M : ℕ} (b : Fin 3) (R : Fin 3 → (Fin (M + 1) → Fin 3) → Prop)
    [∀ c, DecidablePred (R c)] (P : (Fin (M + 2) → Fin 3) → Prop) [DecidablePred P]
    (hP : ∀ a u, P (Fin.cons a u) ↔ a = b ∧ R (u 0) u) :
    (univ.filter P).card = ∑ c : Fin 3, (univ.filter fun u => u 0 = c ∧ R c u).card := by
  rw [card_cons, ← card_split R]
  rw [Finset.sum_eq_single b]
  · simp only [hP, true_and]
  · intro a _ hab
    simp [hP, hab]
  · simp

/-- Proper words (no mistakes) of length `M+1` with a given first letter: `2^M`. -/
private theorem N0 : ∀ M : ℕ, ∀ b : Fin 3,
    (univ.filter fun v : Fin (M + 1) → Fin 3 => v 0 = b ∧ wmis v = 0).card = 2 ^ M := by
  intro M
  induction M with
  | zero => decide
  | succ M ih =>
    intro b
    rw [card_first b (fun c u => (if b = c then 1 else 0) + wmis u = 0) _
      (fun a u => by simp only [Fin.cons_zero, wmis_cons]; constructor <;> rintro ⟨rfl, h⟩ <;> exact ⟨rfl, h⟩)]
    have key : ∀ c, (univ.filter fun u : Fin (M + 1) → Fin 3 =>
        u 0 = c ∧ (if b = c then 1 else 0) + wmis u = 0).card = if b = c then 0 else 2 ^ M := by
      intro c
      split_ifs with h
      · simp
      · simpa using ih c
    simp only [key]
    fin_cases b <;> simp [Fin.sum_univ_three] <;> ring


/-- Words of length `M+2` with exactly one mistake and a given first letter: `(M+1)·2^M`. -/
private theorem N1 : ∀ M : ℕ, ∀ b : Fin 3,
    (univ.filter fun v : Fin (M + 2) → Fin 3 => v 0 = b ∧ wmis v = 1).card = (M + 1) * 2 ^ M := by
  intro M
  induction M with
  | zero => decide
  | succ M ih =>
    intro b
    rw [card_first b (fun c u => (if b = c then 1 else 0) + wmis u = 1) _
      (fun a u => by simp only [Fin.cons_zero, wmis_cons]; constructor <;> rintro ⟨rfl, h⟩ <;> exact ⟨rfl, h⟩)]
    have key : ∀ c, (univ.filter fun u : Fin (M + 2) → Fin 3 =>
        u 0 = c ∧ (if b = c then 1 else 0) + wmis u = 1).card =
          if b = c then 2 ^ (M + 1) else (M + 1) * 2 ^ M := by
      intro c
      split_ifs with h
      · simpa using N0 (M + 1) c
      · simpa using ih c
    simp only [key]
    fin_cases b <;> simp [Fin.sum_univ_three] <;> ring

/-- Proper words of length `M+2` starting with `0` and satisfying `Q2`: `2^M`. -/
private theorem P0 (M : ℕ) :
    (univ.filter fun v : Fin (M + 2) → Fin 3 => v 0 = 0 ∧ wmis v = 0 ∧ Q2 v).card = 2 ^ M := by
  rw [card_first 0 (fun c u => (if (0 : Fin 3) = c then 1 else 0) + wmis u = 0 ∧ Q2 u) _
    (fun a u => by
      simp only [Fin.cons_zero, wmis_cons, Q2_cons]
      constructor
      · rintro ⟨rfl, h, h'⟩
        exact ⟨rfl, h, by simpa using h'⟩
      · rintro ⟨rfl, h, h'⟩
        exact ⟨rfl, h, Or.inr ⟨rfl, h'⟩⟩)]
  rw [Fin.sum_univ_three]
  have e0 : (univ.filter fun u : Fin (M + 1) → Fin 3 =>
      u 0 = 0 ∧ (if (0 : Fin 3) = 0 then 1 else 0) + wmis u = 0 ∧ Q2 u).card = 0 := by
    simp
  have e1 : (univ.filter fun u : Fin (M + 1) → Fin 3 =>
      u 0 = 1 ∧ (if (0 : Fin 3) = 1 then 1 else 0) + wmis u = 0 ∧ Q2 u).card = 2 ^ M := by
    rw [← N0 M 1]
    congr 1
    refine Finset.filter_congr fun u _ => ?_
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h1, by simpa using h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by simpa using h2, Q2_of_one u h1⟩
  have e2 : (univ.filter fun u : Fin (M + 1) → Fin 3 =>
      u 0 = 2 ∧ (if (0 : Fin 3) = 2 then 1 else 0) + wmis u = 0 ∧ Q2 u).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro u - ⟨h1, -, h3⟩
    exact not_Q2_of_two u h1 h3
  rw [e0, e1, e2]
  ring

/-- Words of length `M+3` with one mistake, starting with `0` and satisfying `Q2`: `(M+2)·2^M`. -/
private theorem Tgt (M : ℕ) :
    (univ.filter fun v : Fin (M + 3) → Fin 3 => wmis v = 1 ∧ v 0 = 0 ∧ Q2 v).card =
      (M + 2) * 2 ^ M := by
  rw [card_first 0 (fun c u => (if (0 : Fin 3) = c then 1 else 0) + wmis u = 1 ∧ Q2 u) _
    (fun a u => by
      simp only [Fin.cons_zero, wmis_cons, Q2_cons]
      constructor
      · rintro ⟨h, rfl, h'⟩
        exact ⟨rfl, h, by simpa using h'⟩
      · rintro ⟨rfl, h, h'⟩
        exact ⟨h, rfl, Or.inr ⟨rfl, h'⟩⟩)]
  rw [Fin.sum_univ_three]
  have e0 : (univ.filter fun u : Fin (M + 2) → Fin 3 =>
      u 0 = 0 ∧ (if (0 : Fin 3) = 0 then 1 else 0) + wmis u = 1 ∧ Q2 u).card = 2 ^ M := by
    rw [← P0 M]
    congr 1
    refine Finset.filter_congr fun u _ => ?_
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by simpa using h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by simpa using h2, h3⟩
  have e1 : (univ.filter fun u : Fin (M + 2) → Fin 3 =>
      u 0 = 1 ∧ (if (0 : Fin 3) = 1 then 1 else 0) + wmis u = 1 ∧ Q2 u).card = (M + 1) * 2 ^ M := by
    rw [← N1 M 1]
    congr 1
    refine Finset.filter_congr fun u _ => ?_
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h1, by simpa using h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by simpa using h2, Q2_of_one u h1⟩
  have e2 : (univ.filter fun u : Fin (M + 2) → Fin 3 =>
      u 0 = 2 ∧ (if (0 : Fin 3) = 2 then 1 else 0) + wmis u = 1 ∧ Q2 u).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro u - ⟨h1, -, h3⟩
    exact not_Q2_of_two u h1 h3
  rw [e0, e1, e2]
  ring


/-- The row-major numbering of the cells of the `n X 2` array (`2n = M+1` cells). -/
private def eqv (n M : ℕ) (h : n * 2 = M + 1) : Cell n ≃ Fin (M + 1) :=
  finProdFinEquiv.trans (finCongr h)

/-- The numbering is the rank. -/
private theorem eqv_val {n M : ℕ} (h : n * 2 = M + 1) (p : Cell n) : (eqv n M h p).val = p.rank := by
  simp [eqv, Cell.rank]
  ring

/-- The array graph is the path through the cells in row-major order. -/
private theorem isEdge_iff {n : ℕ} (p q : Cell n) : IsEdge p q ↔ q.rank = p.rank + 1 := by
  have h1 := p.2.isLt
  have h2 := q.2.isLt
  simp only [IsEdge, Cell.rank, Fin.ext_iff, Fin.val_zero, Fin.val_one]
  omega

/-- Mistakes of a coloring are the mistakes of its row-major word. -/
private theorem mistakes_eq {n M : ℕ} (h : n * 2 = M + 1) (c : Cell n → Fin 3) :
    mistakes c = wmis (c ∘ (eqv n M h).symm) := by
  symm
  rw [wmis, ← Finset.card_filter]
  refine Finset.card_bij (fun i _ => ((eqv n M h).symm i.castSucc, (eqv n M h).symm i.succ))
    ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at hi ⊢
    refine ⟨?_, hi⟩
    rw [isEdge_iff, ← eqv_val h, ← eqv_val h]
    simp
  · intro i _ j _ hij
    simp only [Prod.mk.injEq] at hij
    exact Fin.castSucc_injective _ ((eqv n M h).symm.injective hij.1)
  · rintro ⟨p, q⟩ hpq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpq
    obtain ⟨he, hc⟩ := hpq
    rw [isEdge_iff, ← eqv_val h, ← eqv_val h] at he
    have hlt : (eqv n M h p).val < M := by have := (eqv n M h q).isLt; omega
    have hp : (eqv n M h).symm (Fin.castSucc ⟨(eqv n M h p).val, hlt⟩) = p := by
      rw [Equiv.symm_apply_eq]; ext; simp
    have hq : (eqv n M h).symm (Fin.succ ⟨(eqv n M h p).val, hlt⟩) = q := by
      rw [Equiv.symm_apply_eq]; ext; simp [he]
    refine ⟨⟨(eqv n M h p).val, hlt⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply, hp, hq]
      exact hc
    · simp only [hp, hq]

/-- Colors in order means: the row-major word starts with `0` and satisfies `Q2`. -/
private theorem colorsInOrder_iff {n M : ℕ} (h : n * 2 = M + 1) (c : Cell n → Fin 3) :
    ColorsInOrder c ↔ (c ∘ (eqv n M h).symm) 0 = 0 ∧ Q2 (c ∘ (eqv n M h).symm) := by
  have hr : ∀ x : Fin (M + 1), ((eqv n M h).symm x).rank = x.val := fun x => by
    rw [← eqv_val h, Equiv.apply_symm_apply]
  have hR : ColorsInOrder c ↔ ∀ x : Fin (M + 1), (c ∘ (eqv n M h).symm) x ≠ 0 →
      ∃ y, y < x ∧ ((c ∘ (eqv n M h).symm) y).val + 1 = ((c ∘ (eqv n M h).symm) x).val := by
    constructor
    · intro H x hx
      obtain ⟨q, hq, hv⟩ := H ((eqv n M h).symm x) hx
      refine ⟨eqv n M h q, ?_, ?_⟩
      · rw [Fin.lt_def, eqv_val h, ← hr x]
        exact hq
      · simpa using hv
    · intro H p hp
      obtain ⟨y, hy, hv⟩ := H (eqv n M h p) (by simpa using hp)
      refine ⟨(eqv n M h).symm y, ?_, ?_⟩
      · rw [hr y, ← eqv_val h p]
        exact hy
      · simpa using hv
  rw [hR]
  generalize c ∘ (eqv n M h).symm = w
  constructor
  · intro H
    refine ⟨?_, fun i hi => ?_⟩
    · by_contra h0
      obtain ⟨y, hy, -⟩ := H 0 h0
      exact Fin.not_lt_zero y hy
    · obtain ⟨y, hy, hv⟩ := H i (by rw [hi]; decide)
      refine ⟨y, hy, ?_⟩
      rw [hi] at hv
      ext
      simp only [Fin.val_two] at hv
      simp only [Fin.val_one]
      omega
  · rintro ⟨h0, hq⟩ x hx
    have hx' : w x = 1 ∨ w x = 2 := by
      revert hx; generalize w x = t; fin_cases t <;> simp
    rcases hx' with h1 | h2
    · refine ⟨0, ?_, by rw [h0, h1]; rfl⟩
      rw [Fin.pos_iff_ne_zero]
      rintro rfl
      rw [h0] at h1
      exact absurd h1 (by decide)
    · obtain ⟨y, hy, hy1⟩ := hq x h2
      exact ⟨y, hy, by rw [hy1, h2]; rfl⟩

/-- A229580 as a count of words. -/
private theorem A229580_eq {n M : ℕ} (h : n * 2 = M + 1) :
    A229580 n = (univ.filter fun w : Fin (M + 1) → Fin 3 => wmis w = 1 ∧ w 0 = 0 ∧ Q2 w).card := by
  unfold A229580
  refine Finset.card_equiv (Equiv.arrowCongr (eqv n M h) (Equiv.refl _)) fun c => ?_
  have hc : (Equiv.arrowCongr (eqv n M h) (Equiv.refl (Fin 3))) c = c ∘ (eqv n M h).symm := rfl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hc]
  rw [mistakes_eq h, colorsInOrder_iff h]

/-- Closed form `A229580(m+2) = (2m+3)·2^(2m+1)`. -/
private theorem A229580_closed (m : ℕ) : A229580 (m + 1 + 1) = (2 * m + 3) * 2 ^ (2 * m + 1) := by
  rw [A229580_eq (M := 2 * m + 1 + 2) (by ring), Tgt]

/-- Luschny's conjecture holds: `|∑_{j=0}^{k} T(k+j, k)| = A229580(k+1)` for every `k`. -/
theorem result : statement := by
  intro k
  cases k with
  | zero => exact statement_check 0 (by norm_num)
  | succ m =>
    rw [absSumT, A229580_closed]
    push_cast
    ring

end Math0.Frontier.A368846

#math0_settles Math0.Frontier.A368846.result Math0.Statements.A368846.statement
