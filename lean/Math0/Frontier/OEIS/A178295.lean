/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A178295
import Math0.Audit

/-!
# A178295: collinear 4-subsets of `{0, …, 4}ⁿ` (Mathar's conjecture is true)

We prove all three of Mathar's formulas: `a(n) = 9^n/2 + 3*7^n/2 - 2*5^n`, the recurrence
`a(n) = 21 a(n-1) - 143 a(n-2) + 315 a(n-3)` and the rational generating function.

*Idea.* Count ordered 4-tuples `f : Fin 4 → Pt n` of distinct collinear points instead; each
4-set is the image of exactly `24` of them (`card_E`). Transposing, such a tuple is a family
`G : Fin n → Col` of *columns* `G i = (f 0 i, f 1 i, f 2 i, f 3 i) ∈ {0, …, 4}⁴`, and the
conditions become: any two columns are *compatible* (`RR`: the planar points `(G i a, G j a)`
are collinear) and the four rows are distinct (`card_E_V`). Under these conditions every column
is constant or injective (`const_of_RR`), compatibility is transitive through a non-constant
column (`RR_trans`), and the `120` injective columns fall into `48` compatibility classes:
`12` classes of size `4` (value set of span `3`) and `36` of size `2` (span `4`). These finite
facts about `{0, …, 4}⁴` are checked by the kernel (`rep_sep`, `cover_check`, `count_check`).
So the good families are the disjoint union, over the `48` classes, of the families of columns
each constant or in the class, not all constant (`V_eq`, `W_disj`), giving
`24 a(n) = 12 (9^n - 5^n) + 36 (7^n - 5^n)` (`card_V`). The recurrence and the generating
function follow from the closed form.
-/

namespace Math0.Frontier.A178295
open Math0.Statements.A178295

/-! ### Columns -/

/-- A column: the values of one coordinate at the four points of an ordered 4-tuple. -/
private abbrev Col := Fin 4 → Fin 5

/-- The entries of a column, as integers. -/
private def zc (u : Col) (a : Fin 4) : ℤ := ((u a : ℕ) : ℤ)

/-- Two columns are compatible: the four planar points `(u a, w a)` are collinear. -/
private def RR (u w : Col) : Prop :=
  ∀ a b c : Fin 4, (zc u b - zc u a) * (zc w c - zc w a) = (zc w b - zc w a) * (zc u c - zc u a)

/-- Boolean version of `RR`. -/
private def RRb (u w : Col) : Bool :=
  (List.finRange 4).all fun a => (List.finRange 4).all fun b => (List.finRange 4).all fun c =>
    minorB ((u a : ℕ), (u b : ℕ), (u c : ℕ)) ((w a : ℕ), (w b : ℕ), (w c : ℕ))

/-- `RRb` decides `RR`. -/
private theorem RRb_iff (u w : Col) : RRb u w = true ↔ RR u w := by
  unfold RRb RR
  simp only [List.all_eq_true, List.mem_finRange, forall_const, minorB_iff, zc]

/-- `RR` is decided by `RRb`. -/
private instance (u w : Col) : Decidable (RR u w) := decidable_of_iff _ (RRb_iff u w)

/-- Integer entries are equal iff the entries are. -/
private theorem zc_eq {u : Col} {a b : Fin 4} : zc u a = zc u b ↔ u a = u b := by
  unfold zc
  constructor
  · intro h; exact Fin.ext (by exact_mod_cast h)
  · intro h; rw [h]

/-- Compatibility is symmetric. -/
private theorem RR_symm {u w : Col} (h : RR u w) : RR w u := fun a b c => (h a b c).symm

/-- A constant column is compatible with every column. -/
private theorem RR_const_right (u : Col) {w : Col} (hw : ∀ a, w a = w 0) : RR u w := by
  intro a b c
  have h1 : zc w c = zc w a := zc_eq.2 ((hw c).trans (hw a).symm)
  have h2 : zc w b = zc w a := zc_eq.2 ((hw b).trans (hw a).symm)
  rw [h1, h2]; ring

/-- Compatibility is transitive through a non-constant column. -/
private theorem RR_trans {u v w : Col} {a₀ b₀ : Fin 4} (hv : v a₀ ≠ v b₀) (h1 : RR v u)
    (h2 : RR v w) : RR u w := by
  intro a b c
  set D := zc v b₀ - zc v a₀ with hD
  have hD0 : D ≠ 0 := sub_ne_zero.mpr (fun h => hv (zc_eq.1 h).symm)
  have hA : ∀ x y, D * (zc u y - zc u x) = (zc u b₀ - zc u a₀) * (zc v y - zc v x) := by
    intro x y
    linear_combination h1 a₀ b₀ y - h1 a₀ b₀ x
  have hB : ∀ x y, D * (zc w y - zc w x) = (zc w b₀ - zc w a₀) * (zc v y - zc v x) := by
    intro x y
    linear_combination h2 a₀ b₀ y - h2 a₀ b₀ x
  apply mul_left_cancel₀ (pow_ne_zero 2 hD0)
  calc D ^ 2 * ((zc u b - zc u a) * (zc w c - zc w a))
      = (D * (zc u b - zc u a)) * (D * (zc w c - zc w a)) := by ring
    _ = (D * (zc w b - zc w a)) * (D * (zc u c - zc u a)) := by
        rw [hA a b, hB a c, hB a b, hA a c]; ring
    _ = D ^ 2 * ((zc w b - zc w a) * (zc u c - zc u a)) := by ring

/-- If `w` is compatible with `t`, and `w` takes equal values at two indices where `t` does
not, then `w` is constant. -/
private theorem const_of_RR {w t : Col} {a b : Fin 4} (h : RR w t) (hw : w a = w b)
    (ht : t a ≠ t b) : ∀ c, w c = w a := by
  intro c
  have h' := h a b c
  rw [zc_eq.2 hw.symm, sub_self, zero_mul] at h'
  have hne : zc t b - zc t a ≠ 0 := sub_ne_zero.mpr (fun e => ht (zc_eq.1 e).symm)
  have := (mul_eq_zero.1 h'.symm).resolve_left hne
  exact zc_eq.1 (sub_eq_zero.1 this)

/-! ### Finite data: the 48 classes of injective columns -/

/-- Representatives of the 48 classes of injective columns (the first 12 have span 3). -/
private def repL : List (List ℕ) :=
  [[0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3], [0, 2, 3, 1], [0, 3, 1, 2], [0, 3, 2, 1],
   [1, 0, 2, 3], [1, 0, 3, 2], [1, 2, 0, 3], [1, 2, 3, 0], [1, 3, 0, 2], [1, 3, 2, 0],
   [0, 1, 2, 4], [0, 1, 3, 4], [0, 1, 4, 2], [0, 1, 4, 3], [0, 2, 1, 4], [0, 2, 3, 4],
   [0, 2, 4, 1], [0, 2, 4, 3], [0, 3, 1, 4], [0, 3, 2, 4], [0, 3, 4, 1], [0, 3, 4, 2],
   [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 2, 1], [0, 4, 2, 3], [0, 4, 3, 1], [0, 4, 3, 2],
   [1, 0, 2, 4], [1, 0, 3, 4], [1, 0, 4, 2], [1, 0, 4, 3], [1, 2, 0, 4], [1, 2, 4, 0],
   [1, 3, 0, 4], [1, 3, 4, 0], [1, 4, 0, 2], [1, 4, 0, 3], [1, 4, 2, 0], [1, 4, 3, 0],
   [2, 0, 1, 4], [2, 0, 3, 4], [2, 0, 4, 1], [2, 0, 4, 3], [2, 1, 0, 4], [2, 1, 4, 0]]

/-- The `k`-th representative column. -/
private def rep (k : Fin 48) : Col :=
  fun a => ⟨((repL.getD k.val []).getD a.val 0) % 5, Nat.mod_lt _ (by norm_num)⟩

/-- Boolean test for constant columns. -/
private def constB (u : Col) : Bool := (List.finRange 4).all fun a => decide (u a = u 0)

/-- `constB` decides constancy. -/
private theorem constB_iff (u : Col) : constB u = true ↔ ∀ a, u a = u 0 := by
  simp [constB, List.all_eq_true]

/-- Boolean test for injective columns. -/
private def injB (u : Col) : Bool :=
  (List.finRange 4).all fun a => (List.finRange 4).all fun b => decide (u a = u b → a = b)

/-- `injB` decides injectivity. -/
private theorem injB_iff (u : Col) : injB u = true ↔ Function.Injective u := by
  simp only [injB, List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq]
  rfl

/-- Every representative is injective. -/
private theorem rep_injB : ∀ k : Fin 48, injB (rep k) = true := by decide +kernel

/-- Distinct representatives are incompatible. -/
private theorem rep_sep : ∀ k k' : Fin 48, k ≠ k' → RRb (rep k) (rep k') = false := by
  decide +kernel

/-- Every injective column is compatible with some representative. -/
private theorem cover_check :
    (L 4).all (fun u => !injB u || (List.finRange 48).any (fun k => RRb (rep k) u)) = true := by
  decide +kernel

/-- The number of columns compatible with each representative. -/
private theorem count_check :
    ∀ k : Fin 48, (L 4).countP (RRb (rep k)) = if k.val < 12 then 9 else 7 := by
  decide +kernel

/-- There are 5 constant columns. -/
private theorem const_check : (L 4).countP constB = 5 := by decide +kernel

/-! ### Consequences of the finite checks -/

/-- Counting columns with a property via the list `L 4` of all columns. -/
private theorem card_filter_col (P : Col → Prop) [DecidablePred P] (B : Col → Bool)
    (hB : ∀ u, B u = true ↔ P u) : (Finset.univ.filter P).card = (L 4).countP B := by
  rw [Finset.card_def, Finset.filter_val, univ_val, Multiset.filter_coe, Multiset.coe_card,
    List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro u _
  rw [Bool.eq_iff_iff, decide_eq_true_iff, hB]

/-- Every injective column is compatible with some representative. -/
private theorem cover (u : Col) (hu : Function.Injective u) : ∃ k : Fin 48, RR (rep k) u := by
  have h := List.all_eq_true.1 cover_check u (mem_L 4 u)
  rw [← injB_iff] at hu
  simp only [hu, Bool.not_true, Bool.false_or, List.any_eq_true, List.mem_finRange,
    true_and] at h
  obtain ⟨k, hk⟩ := h
  exact ⟨k, (RRb_iff _ _).1 hk⟩

/-- The constant columns. -/
private def Cst : Finset Col := Finset.univ.filter fun u => ∀ a, u a = u 0

/-- The columns compatible with the `k`-th representative. -/
private def A (k : Fin 48) : Finset Col := Finset.univ.filter fun w => RR (rep k) w

/-- There are `5` constant columns. -/
private theorem card_Cst : Cst.card = 5 := by
  rw [Cst, card_filter_col _ constB constB_iff, const_check]

/-- `9` columns are compatible with each of the first `12` representatives, `7` with the
others. -/
private theorem card_A (k : Fin 48) : (A k).card = if k.val < 12 then 9 else 7 := by
  rw [A, card_filter_col _ (RRb (rep k)) (RRb_iff _), count_check]

/-- Constant columns are compatible with every representative. -/
private theorem Cst_sub_A (k : Fin 48) : Cst ⊆ A k := by
  intro u hu
  simp only [Cst, A, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  exact RR_const_right _ hu

/-- The good column families: pairwise compatible columns, and the four rows distinct. -/
private def V (n : ℕ) : Finset (Fin n → Col) :=
  Finset.univ.filter fun G =>
    (∀ i j, RR (G i) (G j)) ∧ ∀ a b : Fin 4, (∀ i, G i a = G i b) → a = b

/-- Column families whose columns are all compatible with the `k`-th representative, not all
constant. -/
private def W (n : ℕ) (k : Fin 48) : Finset (Fin n → Col) :=
  Fintype.piFinset (fun _ => A k) \ Fintype.piFinset (fun _ => Cst)

/-- Membership in `W n k`. -/
private theorem mem_W {n : ℕ} {k : Fin 48} {G : Fin n → Col} :
    G ∈ W n k ↔ (∀ i, RR (rep k) (G i)) ∧ ∃ i a, G i a ≠ G i 0 := by
  simp only [W, Finset.mem_sdiff, Fintype.mem_piFinset, A, Cst, Finset.mem_filter,
    Finset.mem_univ, true_and, not_forall]

/-- The good families are those whose columns are all compatible with one representative,
not all constant. -/
private theorem V_eq (n : ℕ) : V n = Finset.univ.biUnion (W n) := by
  ext G
  simp only [V, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, mem_W]
  constructor
  · rintro ⟨hR, hD⟩
    have hnc : ∃ i a, G i a ≠ G i 0 := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      have := hD 1 0 (fun i => hc i 1)
      exact absurd this (by decide)
    obtain ⟨i₀, a₀, ha₀⟩ := hnc
    have hinj : Function.Injective (G i₀) := by
      intro a b hab
      by_contra hne
      have : ¬ ∀ i, G i a = G i b := fun h => hne (hD a b h)
      simp only [not_forall] at this
      obtain ⟨j, hj⟩ := this
      have hc := const_of_RR (hR i₀ j) hab hj
      exact ha₀ ((hc a₀).trans (hc 0).symm)
    obtain ⟨k, hk⟩ := cover (G i₀) hinj
    exact ⟨k, fun j => RR_trans (a₀ := a₀) (b₀ := 0) ha₀ (RR_symm hk) (hR i₀ j), i₀, a₀, ha₀⟩
  · rintro ⟨k, hk, i₀, a₀, ha₀⟩
    have hrep : Function.Injective (rep k) := (injB_iff _).1 (rep_injB k)
    refine ⟨fun i j => RR_trans (a₀ := 0) (b₀ := 1)
      (fun h => absurd (hrep h) (by decide)) (hk i) (hk j), ?_⟩
    intro a b hab
    by_contra hne
    have hc := const_of_RR (RR_symm (hk i₀)) (hab i₀) (fun h => hne (hrep h))
    exact ha₀ ((hc a₀).trans (hc 0).symm)

/-- The pieces `W n k` are pairwise disjoint. -/
private theorem W_disj (n : ℕ) :
    ((Finset.univ : Finset (Fin 48)) : Set (Fin 48)).PairwiseDisjoint (W n) := by
  intro k _ k' _ hkk'
  rw [Function.onFun, Finset.disjoint_left]
  intro G hG hG'
  rw [mem_W] at hG hG'
  obtain ⟨hk, i₀, a₀, ha₀⟩ := hG
  have h := RR_trans (a₀ := a₀) (b₀ := 0) ha₀ (RR_symm (hk i₀)) (RR_symm (hG'.1 i₀))
  have := rep_sep k k' hkk'
  rw [(RRb_iff _ _).2 h] at this
  exact Bool.noConfusion this

/-- The size of the piece `W n k`. -/
private theorem card_W (n : ℕ) (k : Fin 48) :
    (W n k).card = (if k.val < 12 then 9 else 7) ^ n - 5 ^ n := by
  rw [W, Finset.card_sdiff_of_subset (Fintype.piFinset_subset _ _ fun _ => Cst_sub_A k),
    Fintype.card_piFinset_const, Fintype.card_piFinset_const, card_A, card_Cst]

/-- The number of good column families. -/
private theorem card_V (n : ℕ) : (V n).card = 12 * (9 ^ n - 5 ^ n) + 36 * (7 ^ n - 5 ^ n) := by
  rw [V_eq, Finset.card_biUnion (W_disj n)]
  have h : ∀ k : Fin 48, (W n k).card =
      if k.val < 12 then 9 ^ n - 5 ^ n else 7 ^ n - 5 ^ n := by
    intro k; rw [card_W]; split_ifs <;> rfl
  rw [Finset.sum_congr rfl (fun k _ => h k), Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul]
  have h12 : (Finset.univ.filter fun k : Fin 48 => k.val < 12).card = 12 := by decide
  have h36 : (Finset.univ.filter fun k : Fin 48 => ¬ k.val < 12).card = 36 := by decide
  rw [h12, h36]

/-! ### Ordered 4-tuples -/

/-- Ordered 4-tuples of distinct collinear grid points. -/
private def E (n : ℕ) : Finset (Fin 4 → Pt n) :=
  Finset.univ.filter fun f => Function.Injective f ∧ ∀ a b c, Coll3 (f a) (f b) (f c)

/-- Transposition: ordered collinear 4-tuples are the good column families. -/
private theorem card_E_V (n : ℕ) : (E n).card = (V n).card := by
  refine Finset.card_bij' (fun f _ => fun i a => f a i) (fun G _ => fun a i => G i a) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [E, V, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    exact ⟨fun i j a b c => hf.2 a b c i j, fun a b h => hf.1 (funext h)⟩
  · intro G hG
    simp only [E, V, Finset.mem_filter, Finset.mem_univ, true_and] at hG ⊢
    exact ⟨fun a b h => hG.2 a b (fun i => congrFun h i), fun a b c i j => hG.1 i j a b c⟩
  · intro f _; rfl
  · intro G _; rfl

/-- Each 4-element set is the image of exactly `24` injective maps from `Fin 4`. -/
private theorem fiber_card {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α)
    (hs : s.card = 4) :
    (Finset.univ.filter fun f : Fin 4 → α =>
      Function.Injective f ∧ Finset.univ.image f = s).card = 24 := by
  have key : (Finset.univ.filter fun f : Fin 4 → α =>
      Function.Injective f ∧ Finset.univ.image f = s).card =
      (Finset.univ : Finset (Fin 4 ↪ s)).card := by
    refine Finset.card_bij' (fun f hf => ⟨fun a => ⟨f a, ?_⟩, ?_⟩)
      (fun g _ => fun a => ((g a : s) : α)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · have h := (Finset.mem_filter.1 hf).2.2
      rw [← h]
      exact Finset.mem_image_of_mem f (Finset.mem_univ a)
    · intro a b h
      exact (Finset.mem_filter.1 hf).2.1 (congrArg Subtype.val h)
    · intro g _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hg : Function.Injective fun a => ((g a : s) : α) :=
        fun a b h => g.injective (Subtype.ext h)
      refine ⟨hg, ?_⟩
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hx
        exact (g a).2
      · rw [hs, Finset.card_image_of_injective _ hg]; simp
    · intro f _; rfl
    · intro g _; rfl
  rw [key, Finset.card_univ, Fintype.card_embedding_eq]
  simp [hs]

/-- Each collinear 4-set corresponds to `24` ordered 4-tuples. -/
private theorem card_E (n : ℕ) : (E n).card = 24 * a n := by
  have hmaps : ((E n : Finset (Fin 4 → Pt n)) : Set (Fin 4 → Pt n)).MapsTo
      (fun f => Finset.univ.image f)
      ((Finset.univ : Finset (Pt n)).powersetCard 4 |>.filter IsCollinear) := by
    intro f hf
    simp only [E, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hf
    simp only [Finset.coe_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Set.mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hf.1]; simp
    · intro p hp q hq r hr
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 hq
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.1 hr
      exact hf.2 x y z
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ s ∈ ((Finset.univ : Finset (Pt n)).powersetCard 4 |>.filter IsCollinear),
      ((E n).filter fun f => Finset.univ.image f = s).card = 24 := by
    intro s hs
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hs
    rw [← fiber_card s hs.1.2]
    congr 1
    ext f
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hinj, _⟩, himg⟩; exact ⟨hinj, himg⟩
    · rintro ⟨hinj, himg⟩
      refine ⟨⟨hinj, fun x y z => ?_⟩, himg⟩
      have mem : ∀ x, f x ∈ s := fun x => himg ▸ Finset.mem_image_of_mem f (Finset.mem_univ x)
      exact hs.2 _ (mem x) _ (mem y) _ (mem z)
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]
  rfl

/-! ### The closed form and the conjecture -/

/-- The count, multiplied by `24`. -/
private theorem a_mul (n : ℕ) : 24 * a n = 12 * (9 ^ n - 5 ^ n) + 36 * (7 ^ n - 5 ^ n) := by
  rw [← card_E, card_E_V, card_V]

/-- Mathar's closed form. -/
private theorem closed (n : ℕ) : (a n : ℚ) = 9 ^ n / 2 + 3 * 7 ^ n / 2 - 2 * 5 ^ n := by
  have h := a_mul n
  have h9 : 5 ^ n ≤ 9 ^ n := Nat.pow_le_pow_left (by norm_num) n
  have h7 : 5 ^ n ≤ 7 ^ n := Nat.pow_le_pow_left (by norm_num) n
  have hq : (24 : ℚ) * a n = 12 * ((9 : ℚ) ^ n - 5 ^ n) + 36 * ((7 : ℚ) ^ n - 5 ^ n) := by
    have := congrArg (fun x : ℕ => (x : ℚ)) h
    push_cast [Nat.cast_sub h9, Nat.cast_sub h7] at this
    linear_combination this
  linear_combination hq / 24

/-- Mathar's conjecture for A178295 holds. -/
theorem result : statement := by
  refine ⟨closed, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    have e1 : m + 3 - 1 = m + 2 := by omega
    have e2 : m + 3 - 2 = m + 1 := by omega
    have e3 : m + 3 - 3 = m := by omega
    rw [e1, e2, e3]
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [closed, closed, closed, closed]
    ring
  · rw [genFun_iff]
    ext n
    rw [show PowerSeries.mk (fun n => (a n : ℚ)) * den =
        PowerSeries.C (-1 : ℚ) * PowerSeries.mk (fun n => (a n : ℚ)) +
        PowerSeries.C (21 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1) +
        PowerSeries.C (-143 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 2) +
        PowerSeries.C (315 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 3) by
      unfold den; simp only [map_neg, map_one, map_ofNat]; ring]
    rw [show (PowerSeries.X * (-5 + 41 * PowerSeries.X) : PowerSeries ℚ) =
        PowerSeries.C (-5 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (41 : ℚ) * PowerSeries.X ^ 2 by
      simp only [map_neg, map_ofNat]; ring]
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_C]
    rcases n with _ | _ | _ | m
    · simp [closed]; norm_num
    · simp [closed]; norm_num
    · simp [closed]; norm_num
    · have e1 : m + 3 - 1 = m + 2 := by omega
      have e2 : m + 3 - 2 = m + 1 := by omega
      have e3 : m + 3 - 3 = m := by omega
      simp only [show 1 ≤ m + 3 by omega, show 2 ≤ m + 3 by omega, show 3 ≤ m + 3 by omega,
        if_true, e1, e2, e3, show m + 2 ≠ 0 by omega, show m + 1 ≠ 0 by omega, if_false, closed]
      ring

end Math0.Frontier.A178295

#math0_settles Math0.Frontier.A178295.result Math0.Statements.A178295.statement
