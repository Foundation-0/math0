/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A348484
import Math0.Audit

/-!
# A348484: no two squares two steps apart — the conjectured formula holds

We prove Yang Hong's conjecture: the maximum number of squares of an `n × n` board with no two
exactly two steps apart in a row or column is `n²/2`, `(n²+1)/2` or `n²/2 + 2` according as
`n ≡ 0`, `n` odd, or `n ≡ 2 (mod 4)`.

The idea. Let `f` be the involution `j ↦ j xor 2` of `ℕ` (`j + 2` if `j mod 4 < 2`, else
`j - 2`). Pair each square `(i, j)` with `(i, f j)` when `f j < n`, otherwise with `(f i, j)` when
`f i < n`, otherwise leave it unpaired. This is an involution `sig` of the board whose non-trivial
orbits are pairs of squares two steps apart, and whose fixed points are `A × A` with
`A = {j < n | f j ≥ n}`, a set of size `0, 1, 2, 1` for `n ≡ 0, 1, 2, 3 (mod 4)`.

* Upper bound: an admissible `T` meets each pair at most once, so `T ∩ sig T` consists of fixed
  points and `2|T| = |T ∪ sig T| + |T ∩ sig T| ≤ n² + |Fix|`.
* Lower bound: colour `(i, j)` by the parity of `i/2 + j/2`. Two squares two steps apart get
  different colours, so the colour-`0` class `S₀` is admissible; every fixed point has colour `0`,
  and `sig` maps the colour-`1` squares injectively into `S₀ \ Fix`. Hence
  `n² - |S₀| ≤ |S₀| - |Fix|`.

Together, `a n = |S₀|` and `2 a(n) = n² + |A|²`, which is the conjectured formula in each case.
-/

namespace Math0.Frontier.A348484
open Math0.Statements.A348484

/-- The involution `j ↦ j xor 2` of `ℕ`. -/
private def f (j : ℕ) : ℕ := if j % 4 < 2 then j + 2 else j - 2

/-- `f` is an involution. -/
private lemma f_f (j : ℕ) : f (f j) = j := by
  unfold f; split_ifs <;> omega

/-- `f` moves every number by exactly two. -/
private lemma f_cases (j : ℕ) : f j = j + 2 ∨ j = f j + 2 := by
  unfold f; split_ifs <;> omega

/-- The pairing involution of the board: move two steps within the row (by `f` on the column)
if that stays on the board, else two steps within the column, else stay put. -/
private def sig {n : ℕ} (c : Fin n × Fin n) : Fin n × Fin n :=
  if h : f c.2 < n then (c.1, ⟨f c.2, h⟩)
  else if h' : f c.1 < n then (⟨f c.1, h'⟩, c.2) else c

/-- `sig` is an involution. -/
private lemma sig_sig {n : ℕ} (c : Fin n × Fin n) : sig (sig c) = c := by
  obtain ⟨i, j⟩ := c
  unfold sig
  by_cases h1 : f j < n
  · simp [h1, f_f]
  · by_cases h3 : f i < n
    · simp [h1, h3, f_f]
    · simp [h1, h3]

/-- The fixed points of `sig` are the squares whose row and column both satisfy `f · ≥ n`. -/
private lemma sig_eq_iff {n : ℕ} (c : Fin n × Fin n) :
    sig c = c ↔ n ≤ f c.1 ∧ n ≤ f c.2 := by
  obtain ⟨i, j⟩ := c
  unfold sig
  by_cases h1 : f j < n
  · simp only [h1, dite_true, Prod.mk.injEq, true_and, Fin.ext_iff]
    have := f_cases j.val
    constructor
    · intro h; omega
    · intro h; omega
  · by_cases h3 : f i < n
    · simp only [h1, h3, dite_true, dite_false, Prod.mk.injEq, and_true, Fin.ext_iff]
      have := f_cases i.val
      constructor
      · intro h; omega
      · intro h; omega
    · simp only [h1, h3, dite_false]
      exact ⟨fun _ => by omega, fun _ => trivial⟩

/-- A square not fixed by `sig` is two steps apart from its image. -/
private lemma sig_adj {n : ℕ} (c : Fin n × Fin n) (h : sig c ≠ c) : TwoApart c (sig c) := by
  obtain ⟨i, j⟩ := c
  unfold sig at h ⊢
  by_cases h1 : f j < n
  · simp only [h1, dite_true]
    left
    exact ⟨rfl, by have := f_cases j.val; simp only; omega⟩
  · by_cases h3 : f i < n
    · simp only [h1, h3, dite_true, dite_false]
      right
      exact ⟨rfl, by have := f_cases i.val; simp only; omega⟩
    · simp [h1, h3] at h

/-- The colour of a square: the checkerboard colour of its position in its parity class. -/
private def P {n : ℕ} (c : Fin n × Fin n) : Prop := (c.1.val / 2 + c.2.val / 2) % 2 = 0

/-- Decidability of the colour predicate. -/
private instance {n : ℕ} : DecidablePred (P (n := n)) := fun c =>
  inferInstanceAs (Decidable ((c.1.val / 2 + c.2.val / 2) % 2 = 0))

/-- Squares two steps apart have different colours. -/
private lemma P_flip {n : ℕ} (c d : Fin n × Fin n) (h : TwoApart c d) : (P c ↔ ¬ P d) := by
  unfold P
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1]; omega
  · rw [h1]; omega

/-- Every fixed point of `sig` has colour `0` (its coordinates are `≡ 0, 1 (mod 4)`). -/
private lemma P_of_fix {n : ℕ} (c : Fin n × Fin n) (h : sig c = c) : P c := by
  rw [sig_eq_iff] at h
  have hi := c.1.isLt
  have hj := c.2.isLt
  unfold P
  unfold f at h
  split_ifs at h <;> omega

/-- The colour-`0` class is a maximum admissible set, and twice its size is `n²` plus the
number of fixed points of `sig`. -/
private lemma key {n : ℕ} :
    a n = (Finset.univ.filter (P (n := n))).card ∧
    2 * (Finset.univ.filter (P (n := n))).card =
      n * n + (Finset.univ.filter (fun c : Fin n × Fin n => sig c = c)).card := by
  classical
  set S0 := Finset.univ.filter (P (n := n)) with hS0
  set C := Finset.univ.filter (fun c : Fin n × Fin n => ¬ P c) with hC
  set Fx := Finset.univ.filter (fun c : Fin n × Fin n => sig c = c) with hFx
  have hinj : Function.Injective (sig (n := n)) :=
    Function.Involutive.injective sig_sig
  have huniv : (Finset.univ : Finset (Fin n × Fin n)).card = n * n := by
    simp
  -- upper bound for any admissible set
  have hub : ∀ T : Finset (Fin n × Fin n), Admissible T → 2 * T.card ≤ n * n + Fx.card := by
    intro T hT
    have h1 : (T.image sig).card = T.card := Finset.card_image_of_injective _ hinj
    have h2 : (T ∪ T.image sig).card ≤ n * n := huniv ▸ Finset.card_le_univ _
    have h3 : T ∩ T.image sig ⊆ Fx := by
      intro c hc
      rw [Finset.mem_inter, Finset.mem_image] at hc
      obtain ⟨hcT, d, hdT, rfl⟩ := hc
      rw [hFx, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [sig_sig]
      by_contra hne
      have := sig_adj d (Ne.symm hne)
      exact hT d hdT (sig d) hcT this
    have h4 := Finset.card_le_card h3
    have h5 := Finset.card_union_add_card_inter T (T.image sig)
    omega
  -- lower bound for S0
  have hlb : n * n + Fx.card ≤ 2 * S0.card := by
    have h1 : (C.image sig).card = C.card := Finset.card_image_of_injective _ hinj
    have h2 : S0.card + C.card = n * n := by
      rw [← huniv]; exact Finset.card_filter_add_card_filter_not _
    have hdisj : Disjoint (C.image sig) Fx := by
      rw [Finset.disjoint_left]
      intro x hx hxF
      rw [Finset.mem_image] at hx
      obtain ⟨c, hcC, rfl⟩ := hx
      rw [hFx, Finset.mem_filter, sig_sig] at hxF
      rw [hC, Finset.mem_filter] at hcC
      exact hcC.2 (P_of_fix c hxF.2.symm)
    have hsub : C.image sig ∪ Fx ⊆ S0 := by
      intro x hx
      rw [Finset.mem_union] at hx
      rw [hS0, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hx with hx | hx
      · rw [Finset.mem_image] at hx
        obtain ⟨c, hcC, rfl⟩ := hx
        rw [hC, Finset.mem_filter] at hcC
        have hne : sig c ≠ c := fun h => hcC.2 (P_of_fix c h)
        have := (P_flip c (sig c) (sig_adj c hne)).not
        tauto
      · rw [hFx, Finset.mem_filter] at hx
        exact P_of_fix _ hx.2
    have h3 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at h3
    omega
  have hS0adm : Admissible S0 := by
    intro c hc d hd hcd
    rw [hS0, Finset.mem_filter] at hc hd
    exact (P_flip c d hcd).1 hc.2 hd.2
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · apply Finset.sup_le
    intro T hT
    have := hub T (Finset.mem_filter.1 hT).2
    omega
  · exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hS0adm⟩)
  · have := hub S0 hS0adm
    omega

/-- The fixed points of `sig` are the squares both of whose coordinates lie in `A`. -/
private lemma card_fix {n : ℕ} :
    (Finset.univ.filter (fun c : Fin n × Fin n => sig c = c)).card =
      (Finset.univ.filter (fun j : Fin n => n ≤ f j)).card *
        (Finset.univ.filter (fun j : Fin n => n ≤ f j)).card := by
  rw [← Finset.card_product]
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, sig_eq_iff]

/-- The number of `j < n` with `f j ≥ n`, by the residue of `n` mod `4`. -/
private lemma card_A (n : ℕ) :
    (Finset.univ.filter (fun j : Fin n => n ≤ f j)).card =
      if n % 4 = 0 then 0 else if n % 4 = 2 then 2 else 1 := by
  split_ifs with h0 h2
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j _
    have := j.isLt
    unfold f; split_ifs <;> omega
  · rw [Finset.card_eq_two]
    refine ⟨⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩, by simp [Fin.ext_iff]; omega, ?_⟩
    ext j
    have := j.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
    unfold f; split_ifs <;> omega
  · rw [Finset.card_eq_one]
    refine ⟨⟨if n % 4 = 1 then n - 1 else n - 2, by split_ifs <;> omega⟩, ?_⟩
    ext j
    have := j.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
    unfold f; split_ifs <;> omega

/-- `2 a(n) = n² + s`, where `s = 0, 1, 4, 1` according as `n ≡ 0, 1, 2, 3 (mod 4)`. -/
private lemma two_a (n : ℕ) :
    2 * a n = n * n + (if n % 4 = 0 then 0 else if n % 4 = 2 then 4 else 1) := by
  obtain ⟨h1, h2⟩ := key (n := n)
  rw [h1, h2, card_fix, card_A]
  split_ifs <;> rfl

/-- Yang Hong's conjectured formula for A348484 holds for every `n ≥ 1`. -/
theorem result : statement := by
  intro n _
  have h := two_a n
  have hsq : n ^ 2 = n * n := sq n
  rw [← hsq] at h
  refine ⟨fun h0 => ?_, fun h13 => ?_, fun h2 => ?_⟩
  · rw [if_pos h0] at h; omega
  · rw [if_neg (by omega), if_neg (by omega)] at h; omega
  · rw [if_neg (by omega), if_pos h2] at h; omega

end Math0.Frontier.A348484

#math0_settles Math0.Frontier.A348484.result Math0.Statements.A348484.statement
