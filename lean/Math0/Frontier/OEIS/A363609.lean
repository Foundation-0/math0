/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A363609
import Math0.Audit

/-!
# A363609: the `k × k × k` cube of dice shows at least `6k(k + 2)` pips

We prove the conjecture `a(k³) = 6 (k + 2) k` for `k > 1`: no polycube of `k³` dice shows fewer
than `6k² + 12k` pips, and the `k × k × k` cube shows exactly that many.

**Per die.** Since the dice are oriented independently, the minimum for a fixed polycube `P` is
`LB P = ∑ c ∈ P, fmin (exposed P c)`. A check of the `64` cases of the table `tabF` shows
`fmin E ≥ |E| + (number of perpendicular pairs of faces in E)`.

**Faces.** For every axis direction `d`, the cells of `P` whose `d`-face is exposed project onto
the whole projection of `P` along that axis (the last cell of each line along `d` is exposed). So
the number of exposed faces is at least `2 (A + B + C)`, where `A, B, C` are the sizes of the three
coordinate projections of `P`.

**Edges.** For two perpendicular directions `d, e`, the lexicographically last cell (first along
`d`, then along `e`) of each slice of `P` orthogonal to the third axis has both its `d`- and its
`e`-face exposed. Summing over the `12` perpendicular pairs, the number of exposed perpendicular
face pairs is at least `4 (a + b + c)`, where `a, b, c` count the occupied slices in the three
axis directions.

**Inequalities.** `|P| ≤ a b c`, so AM-GM gives `a + b + c ≥ 3k`. Slicing along `z`, the slice
`P_z` has at most `C` cells and at most `α_z β_z` cells, where `α_z, β_z` are the sizes of its two
projections and `∑ α_z = B`, `∑ β_z = A`. Hence `4 k |P_z| ≤ (C + k²)(α_z + β_z)`, and summing gives
`4 k⁴ ≤ (C + k²)(A + B)`, so `(C + k²) + (A + B) ≥ 4k²`, i.e. `A + B + C ≥ 3k²` (a discrete
Loomis–Whitney inequality). Altogether `LB P ≥ 2 · 3k² + 4 · 3k = 6k(k + 2)`.

**The cube.** In `[0, k)³` a die with `m` exposed faces (`m ≤ 3`, no two opposite) contributes
`m (m + 1) / 2`. Writing `u(x) = [x = k - 1] + [x = 0]`, a die contributes
`(1 + u x)(1 + u y)(1 + u z) - 1 - u x u y u z`, and summing gives `(k + 2)³ - k³ - 8 = 6k² + 12k`.
-/

namespace Math0.Frontier.A363609
open Math0.Statements.A363609

/-- Per-die bound (all `64` cases): a die shows at least as many pips as it has exposed faces
plus exposed pairs of perpendicular faces. The arguments of `tabF` are the exposure flags of
`+x, -x, +y, -y, +z, -z`. -/
private theorem tabF_lower : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    ((if b0 then 1 else 0) + (if b1 then 1 else 0) + (if b2 then 1 else 0) +
      (if b3 then 1 else 0) + (if b4 then 1 else 0) + (if b5 then 1 else 0)) +
    ((if b0 && b2 then 1 else 0) + (if b0 && b3 then 1 else 0) + (if b1 && b2 then 1 else 0) +
      (if b1 && b3 then 1 else 0)) +
    ((if b0 && b4 then 1 else 0) + (if b0 && b5 then 1 else 0) + (if b1 && b4 then 1 else 0) +
      (if b1 && b5 then 1 else 0)) +
    ((if b2 && b4 then 1 else 0) + (if b2 && b5 then 1 else 0) + (if b3 && b4 then 1 else 0) +
      (if b3 && b5 then 1 else 0)) ≤ tabF b0 b1 b2 b3 b4 b5 := by
  decide

/-- Number of cells of `P` whose face with normal `d` is exposed. -/
private def E1 (P : Finset Cell) (d : Cell) : ℕ := (P.filter fun c => c + d ∉ P).card

/-- Number of cells of `P` whose faces with normals `d` and `e` are both exposed. -/
private def E2 (P : Finset Cell) (d e : Cell) : ℕ :=
  (P.filter fun c => c + d ∉ P ∧ c + e ∉ P).card

/-- Summing the per-die bound: exposed faces plus exposed perpendicular face pairs (counted per
direction and per pair of directions) are at most `LB P`. -/
private theorem LB_ge_E (P : Finset Cell) :
    (E1 P (1, 0, 0) + E1 P (-1, 0, 0) + E1 P (0, 1, 0) + E1 P (0, -1, 0) + E1 P (0, 0, 1) +
      E1 P (0, 0, -1)) +
    (E2 P (1, 0, 0) (0, 1, 0) + E2 P (1, 0, 0) (0, -1, 0) + E2 P (-1, 0, 0) (0, 1, 0) +
      E2 P (-1, 0, 0) (0, -1, 0)) +
    (E2 P (1, 0, 0) (0, 0, 1) + E2 P (1, 0, 0) (0, 0, -1) + E2 P (-1, 0, 0) (0, 0, 1) +
      E2 P (-1, 0, 0) (0, 0, -1)) +
    (E2 P (0, 1, 0) (0, 0, 1) + E2 P (0, 1, 0) (0, 0, -1) + E2 P (0, -1, 0) (0, 0, 1) +
      E2 P (0, -1, 0) (0, 0, -1)) ≤ LB P := by
  unfold LB E1 E2
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [fmin_exposed]
  have := tabF_lower (decide (c + (1, 0, 0) ∉ P)) (decide (c + (-1, 0, 0) ∉ P))
      (decide (c + (0, 1, 0) ∉ P)) (decide (c + (0, -1, 0) ∉ P)) (decide (c + (0, 0, 1) ∉ P))
      (decide (c + (0, 0, -1) ∉ P))
  simpa only [decide_eq_true_eq, Bool.and_eq_true] using this

/-- Projection bound for one exposed direction. -/
private theorem card_image_le_E1 {β : Type} [DecidableEq β] (P : Finset Cell) (d : Cell)
    (π : Cell → β) (h : Cell → ℤ) (hπ : ∀ c, π (c + d) = π c) (hh : ∀ c, h (c + d) = h c + 1) :
    (P.image π).card ≤ E1 P d := by
  unfold E1
  calc (P.image π).card ≤ ((P.filter fun c => c + d ∉ P).image π).card := by
        apply Finset.card_le_card
        intro p hp
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hp
        obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (P.filter fun c' => π c' = π c) h
          ⟨c, Finset.mem_filter.2 ⟨hc, rfl⟩⟩
        rw [Finset.mem_filter] at hm
        refine Finset.mem_image.2 ⟨m, Finset.mem_filter.2 ⟨hm.1, fun hd => ?_⟩, hm.2⟩
        have := hmax (m + d) (Finset.mem_filter.2 ⟨hd, by rw [hπ, hm.2]⟩)
        rw [hh] at this
        omega
    _ ≤ _ := Finset.card_image_le

/-- Projection bound for two perpendicular exposed directions. -/
private theorem card_image_le_E2 {β : Type} [DecidableEq β] (P : Finset Cell) (d e : Cell)
    (π : Cell → β) (h1 h2 : Cell → ℤ) (hπ1 : ∀ c, π (c + d) = π c) (hπ2 : ∀ c, π (c + e) = π c)
    (h11 : ∀ c, h1 (c + d) = h1 c + 1) (h12 : ∀ c, h1 (c + e) = h1 c)
    (h22 : ∀ c, h2 (c + e) = h2 c + 1) :
    (P.image π).card ≤ E2 P d e := by
  unfold E2
  calc (P.image π).card ≤ ((P.filter fun c => c + d ∉ P ∧ c + e ∉ P).image π).card := by
        apply Finset.card_le_card
        intro p hp
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hp
        obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (P.filter fun c' => π c' = π c)
          (fun c' => toLex (h1 c', h2 c')) ⟨c, Finset.mem_filter.2 ⟨hc, rfl⟩⟩
        rw [Finset.mem_filter] at hm
        refine Finset.mem_image.2 ⟨m, Finset.mem_filter.2 ⟨hm.1, fun hd => ?_, fun he => ?_⟩,
          hm.2⟩
        · have := hmax (m + d) (Finset.mem_filter.2 ⟨hd, by rw [hπ1, hm.2]⟩)
          rw [Prod.Lex.toLex_le_toLex, h11] at this
          dsimp only at this
          omega
        · have := hmax (m + e) (Finset.mem_filter.2 ⟨he, by rw [hπ2, hm.2]⟩)
          rw [Prod.Lex.toLex_le_toLex, h12, h22] at this
          dsimp only at this
          omega
    _ ≤ _ := Finset.card_image_le

/-- Surface and edge counts dominate the projection sizes. -/
private theorem LB_ge_proj (P : Finset Cell) :
    2 * ((P.image fun c => c.2).card + (P.image fun c => (c.1, c.2.2)).card +
        (P.image fun c => (c.1, c.2.1)).card) +
      4 * ((P.image fun c => c.1).card + (P.image fun c => c.2.1).card +
        (P.image fun c => c.2.2).card) ≤ LB P := by
  refine le_trans ?_ (LB_ge_E P)
  have hx : ∀ s : ℤ, s * s = 1 → (P.image fun c => c.2).card ≤ E1 P (s, 0, 0) := by
    intro s hs
    refine card_image_le_E1 P _ (fun c => c.2) (fun c => s * c.1) ?_ ?_
    · intro c; obtain ⟨x, y, z⟩ := c; simp only [Prod.mk_add_mk, add_zero]
    · intro c; obtain ⟨x, y, z⟩ := c; simp only [Prod.mk_add_mk]; linear_combination hs
  have hy : ∀ s : ℤ, s * s = 1 → (P.image fun c => (c.1, c.2.2)).card ≤ E1 P (0, s, 0) := by
    intro s hs
    refine card_image_le_E1 P _ (fun c => (c.1, c.2.2)) (fun c => s * c.2.1) ?_ ?_
    · intro c; obtain ⟨x, y, z⟩ := c; simp only [Prod.mk_add_mk, add_zero]
    · intro c; obtain ⟨x, y, z⟩ := c; simp only [Prod.mk_add_mk]; linear_combination hs
  have hz : ∀ s : ℤ, s * s = 1 → (P.image fun c => (c.1, c.2.1)).card ≤ E1 P (0, 0, s) := by
    intro s hs
    refine card_image_le_E1 P _ (fun c => (c.1, c.2.1)) (fun c => s * c.2.2) ?_ ?_
    · intro c; obtain ⟨x, y, z⟩ := c; simp only [Prod.mk_add_mk, add_zero]
    · intro c; obtain ⟨x, y, z⟩ := c; simp only [Prod.mk_add_mk]; linear_combination hs
  have hxy : ∀ s t : ℤ, s * s = 1 → t * t = 1 →
      (P.image fun c => c.2.2).card ≤ E2 P (s, 0, 0) (0, t, 0) := by
    intro s t hs ht
    refine card_image_le_E2 P _ _ (fun c => c.2.2) (fun c => s * c.1) (fun c => t * c.2.1)
      ?_ ?_ ?_ ?_ ?_ <;>
    · intro c; obtain ⟨x, y, z⟩ := c; simp only [Prod.mk_add_mk]
      first | linear_combination | linear_combination hs | linear_combination ht
  have hxz : ∀ s t : ℤ, s * s = 1 → t * t = 1 →
      (P.image fun c => c.2.1).card ≤ E2 P (s, 0, 0) (0, 0, t) := by
    intro s t hs ht
    refine card_image_le_E2 P _ _ (fun c => c.2.1) (fun c => s * c.1) (fun c => t * c.2.2)
      ?_ ?_ ?_ ?_ ?_ <;>
    · intro c; obtain ⟨x, y, z⟩ := c; simp only [Prod.mk_add_mk]
      first | linear_combination | linear_combination hs | linear_combination ht
  have hyz : ∀ s t : ℤ, s * s = 1 → t * t = 1 →
      (P.image fun c => c.1).card ≤ E2 P (0, s, 0) (0, 0, t) := by
    intro s t hs ht
    refine card_image_le_E2 P _ _ (fun c => c.1) (fun c => s * c.2.1) (fun c => t * c.2.2)
      ?_ ?_ ?_ ?_ ?_ <;>
    · intro c; obtain ⟨x, y, z⟩ := c; simp only [Prod.mk_add_mk]
      first | linear_combination | linear_combination hs | linear_combination ht
  have p1 : (1 : ℤ) * 1 = 1 := by norm_num
  have m1 : (-1 : ℤ) * -1 = 1 := by norm_num
  have := hx 1 p1
  have := hx (-1) m1
  have := hy 1 p1
  have := hy (-1) m1
  have := hz 1 p1
  have := hz (-1) m1
  have := hxy 1 1 p1 p1
  have := hxy 1 (-1) p1 m1
  have := hxy (-1) 1 m1 p1
  have := hxy (-1) (-1) m1 m1
  have := hxz 1 1 p1 p1
  have := hxz 1 (-1) p1 m1
  have := hxz (-1) 1 m1 p1
  have := hxz (-1) (-1) m1 m1
  have := hyz 1 1 p1 p1
  have := hyz 1 (-1) p1 m1
  have := hyz (-1) 1 m1 p1
  have := hyz (-1) (-1) m1 m1
  omega

/-- The per-slice inequality: from `m ≤ C` and `m ≤ α β`, `4 k m ≤ (C + k²)(α + β)` (two AM-GM
steps, `4 C k² ≤ (C + k²)²` and `4 α β ≤ (α + β)²`). -/
private theorem slice_arith (k m C α β : ℕ) (hC : m ≤ C) (hαβ : m ≤ α * β) :
    4 * k * m ≤ (C + k ^ 2) * (α + β) := by
  have h1 : m * m ≤ C * (α * β) := Nat.mul_le_mul hC hαβ
  have h2 : 4 * (C * k ^ 2) ≤ (C + k ^ 2) ^ 2 := by
    have : (0 : ℤ) ≤ ((C : ℤ) - k ^ 2) ^ 2 := sq_nonneg _
    have : (4 * (C * k ^ 2) : ℤ) ≤ ((C : ℤ) + k ^ 2) ^ 2 := by nlinarith
    exact_mod_cast this
  have h3 : 4 * (α * β) ≤ (α + β) ^ 2 := by
    have : (0 : ℤ) ≤ ((α : ℤ) - β) ^ 2 := sq_nonneg _
    have : (4 * (α * β) : ℤ) ≤ ((α : ℤ) + β) ^ 2 := by nlinarith
    exact_mod_cast this
  have h4 : (4 * k * m) ^ 2 ≤ ((C + k ^ 2) * (α + β)) ^ 2 := by
    calc (4 * k * m) ^ 2 = 4 * k ^ 2 * (4 * (m * m)) := by ring
      _ ≤ 4 * k ^ 2 * (4 * (C * (α * β))) := by gcongr
      _ = (4 * (C * k ^ 2)) * (4 * (α * β)) := by ring
      _ ≤ (C + k ^ 2) ^ 2 * (α + β) ^ 2 := Nat.mul_le_mul h2 h3
      _ = ((C + k ^ 2) * (α + β)) ^ 2 := by ring
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h4

/-- A discrete Loomis–Whitney type estimate, slicing along the third coordinate. -/
private theorem loomis (P : Finset Cell) (k : ℕ) :
    4 * k * P.card ≤ ((P.image fun c => (c.1, c.2.1)).card + k ^ 2) *
      ((P.image fun c => c.2).card + (P.image fun c => (c.1, c.2.2)).card) := by
  set C := (P.image fun c => (c.1, c.2.1)).card
  set Z := P.image fun c => c.2.2
  have hP : P.card = ∑ z ∈ Z, (P.filter fun c => c.2.2 = z).card :=
    Finset.card_eq_sum_card_image _ _
  have hfib : ∀ (f : Cell → ℤ × ℤ), (∀ c, (f c).2 = c.2.2) →
      (P.image f).card = ∑ z ∈ Z, ((P.filter fun c => c.2.2 = z).image f).card := by
    intro f hf
    rw [Finset.card_eq_sum_card_image Prod.snd (P.image f), Finset.image_image]
    have e : Prod.snd ∘ f = fun c => c.2.2 := funext hf
    rw [e]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.filter_image]
    simp only [hf]
  rw [hfib (fun c => c.2) (fun _ => rfl), hfib (fun c => (c.1, c.2.2)) (fun _ => rfl), hP,
    Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun z _ => ?_
  set F := P.filter fun c => c.2.2 = z
  apply slice_arith
  · calc F.card = (F.image fun c => (c.1, c.2.1)).card := by
          refine (Finset.card_image_of_injOn ?_).symm
          intro u hu v hv huv
          simp only [F, Finset.mem_coe, Finset.mem_filter] at hu hv
          simp only [Prod.mk.injEq] at huv
          exact Prod.ext huv.1 (Prod.ext huv.2 (hu.2.trans hv.2.symm))
      _ ≤ C := Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))
  · rw [mul_comm, ← Finset.card_product]
    refine Finset.card_le_card_of_injOn (fun c => ((c.1, c.2.2), c.2)) ?_ ?_
    · intro c hc
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe]
      exact ⟨Finset.mem_image_of_mem _ hc, Finset.mem_image_of_mem _ hc⟩
    · intro u _ v _ huv
      simp only [Prod.mk.injEq] at huv
      exact Prod.ext huv.1.1 huv.2

/-- AM-GM for three natural numbers, in cubed form. -/
private theorem amgm3 (a b c : ℕ) : 27 * (a * b * c) ≤ (a + b + c) ^ 3 := by
  have ha : (0 : ℤ) ≤ a := by positivity
  have hb : (0 : ℤ) ≤ b := by positivity
  have hc : (0 : ℤ) ≤ c := by positivity
  have : (27 * (a * b * c) : ℤ) ≤ ((a : ℤ) + b + c) ^ 3 := by
    nlinarith [mul_nonneg (add_nonneg (add_nonneg ha hb) hc) (sq_nonneg ((a : ℤ) - b)),
      mul_nonneg (add_nonneg (add_nonneg ha hb) hc) (sq_nonneg ((b : ℤ) - c)),
      mul_nonneg (add_nonneg (add_nonneg ha hb) hc) (sq_nonneg ((a : ℤ) - c)),
      mul_nonneg ha (sq_nonneg ((b : ℤ) - c)), mul_nonneg hb (sq_nonneg ((a : ℤ) - c)),
      mul_nonneg hc (sq_nonneg ((a : ℤ) - b))]
  exact_mod_cast this

/-- If `k³ ≤ a b c` then `3 k ≤ a + b + c`. -/
private theorem sum3_ge (k a b c : ℕ) (h : k ^ 3 ≤ a * (b * c)) : 3 * k ≤ a + b + c := by
  have h1 : (3 * k) ^ 3 ≤ (a + b + c) ^ 3 := by
    calc (3 * k) ^ 3 = 27 * k ^ 3 := by ring
      _ ≤ 27 * (a * b * c) := by rw [mul_assoc a]; omega
      _ ≤ _ := amgm3 a b c
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h1

/-- If `4 k⁴ ≤ u v` then `4 k² ≤ u + v`. -/
private theorem sum2_ge (k u v : ℕ) (h : 4 * k ^ 4 ≤ u * v) : 4 * k ^ 2 ≤ u + v := by
  have h1 : (4 * k ^ 2) ^ 2 ≤ (u + v) ^ 2 := by
    have : (0 : ℤ) ≤ ((u : ℤ) - v) ^ 2 := sq_nonneg _
    have : (4 * (u * v) : ℤ) ≤ ((u : ℤ) + v) ^ 2 := by nlinarith
    have h' : 4 * (u * v) ≤ (u + v) ^ 2 := by exact_mod_cast this
    calc (4 * k ^ 2) ^ 2 = 4 * (4 * k ^ 4) := by ring
      _ ≤ 4 * (u * v) := by omega
      _ ≤ _ := h'
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h1

/-- The `k × k × k` cube `[0, k)³`. -/
private noncomputable def cube (k : ℕ) : Finset Cell :=
  Finset.Ico (0 : ℤ) k ×ˢ Finset.Ico (0 : ℤ) k ×ˢ Finset.Ico (0 : ℤ) k

/-- The cube has `k³` cells. -/
private theorem card_cube (k : ℕ) : (cube k).card = k ^ 3 := by
  simp only [cube, Finset.card_product, Int.card_Ico, sub_zero, Int.toNat_natCast]
  ring

/-- Membership in the cube, coordinatewise. -/
private theorem mem_cube {k : ℕ} {x y z : ℤ} :
    (x, y, z) ∈ cube k ↔ (0 ≤ x ∧ x < k) ∧ (0 ≤ y ∧ y < k) ∧ (0 ≤ z ∧ z < k) := by
  simp only [cube, Finset.mem_product, Finset.mem_Ico]

/-- Cells along a line inside `P` are connected to its starting cell, in both directions. -/
private theorem line {P : Finset Cell} (f : ℤ → Cell) (k : ℕ)
    (hf : ∀ i : ℤ, 0 ≤ i → i < k → f i ∈ P) (hd : ∀ i, f i - f (i + 1) ∈ dirs)
    (hd' : ∀ i, f (i + 1) - f i ∈ dirs) :
    ∀ n : ℕ, (n : ℤ) < k → Relation.ReflTransGen (Adj P) (f n) (f 0) ∧
      Relation.ReflTransGen (Adj P) (f 0) (f n) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨by simpa using Relation.ReflTransGen.refl,
      by simpa using Relation.ReflTransGen.refl⟩
  | succ n ih =>
    intro hn
    push_cast at hn ⊢
    obtain ⟨h1, h2⟩ := ih (by omega)
    have m1 : f (n + 1) ∈ P := hf _ (by omega) hn
    have m0 : f n ∈ P := hf _ (by omega) (by omega)
    exact ⟨Relation.ReflTransGen.head ⟨m1, m0, hd n⟩ h1, h2.tail ⟨m0, m1, hd' n⟩⟩

/-- The cube is face-connected: every cell is joined to the origin along the three axes. -/
private theorem cube_conn (k : ℕ) : FaceConnected (cube k) := by
  have key : ∀ c ∈ cube k, Relation.ReflTransGen (Adj (cube k)) c (0, 0, 0) ∧
      Relation.ReflTransGen (Adj (cube k)) (0, 0, 0) c := by
    rintro ⟨x, y, z⟩ hc
    rw [mem_cube] at hc
    obtain ⟨⟨hx0, hxk⟩, ⟨hy0, hyk⟩, ⟨hz0, hzk⟩⟩ := hc
    obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hx0
    obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hy0
    obtain ⟨c, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
    have l1 := line (P := cube k) (fun i => (i, (b : ℤ), (c : ℤ))) k
      (fun i h0 h1 => mem_cube.2 ⟨⟨h0, h1⟩, ⟨hy0, hyk⟩, ⟨hz0, hzk⟩⟩)
      (fun i => by simp [dirs, Prod.ext_iff]) (fun i => by simp [dirs, Prod.ext_iff]) a hxk
    have l2 := line (P := cube k) (fun i => ((0 : ℤ), i, (c : ℤ))) k
      (fun i h0 h1 => mem_cube.2 ⟨⟨le_rfl, by omega⟩, ⟨h0, h1⟩, ⟨hz0, hzk⟩⟩)
      (fun i => by simp [dirs, Prod.ext_iff]) (fun i => by simp [dirs, Prod.ext_iff]) b hyk
    have l3 := line (P := cube k) (fun i => ((0 : ℤ), (0 : ℤ), i)) k
      (fun i h0 h1 => mem_cube.2 ⟨⟨le_rfl, by omega⟩, ⟨le_rfl, by omega⟩, ⟨h0, h1⟩⟩)
      (fun i => by simp [dirs, Prod.ext_iff]) (fun i => by simp [dirs, Prod.ext_iff]) c hzk
    exact ⟨(l1.1.trans l2.1).trans l3.1, (l3.2.trans l2.2).trans l1.2⟩
  intro u hu v hv
  exact (key u hu).1.trans (key v hv).2

/-- When no two opposite faces are exposed, a die with exposure counts `X, Y, Z ∈ {0, 1}` per axis
has `fmin = X + Y + Z + XY + XZ + YZ`, written as `fmin + 1 + XYZ = (1 + X)(1 + Y)(1 + Z)`. -/
private theorem tabF_upper : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    (b0 && b1) = false → (b2 && b3) = false → (b4 && b5) = false →
    tabF b0 b1 b2 b3 b4 b5 + 1 +
        ((if b0 then 1 else 0) + (if b1 then 1 else 0)) *
        ((if b2 then 1 else 0) + (if b3 then 1 else 0)) *
        ((if b4 then 1 else 0) + (if b5 then 1 else 0)) =
      (1 + ((if b0 then 1 else 0) + (if b1 then 1 else 0))) *
        (1 + ((if b2 then 1 else 0) + (if b3 then 1 else 0))) *
        (1 + ((if b4 then 1 else 0) + (if b5 then 1 else 0))) := by
  decide

/-- A product of one-variable functions sums over the cube to the product of the sums. -/
private theorem sum_cube_mul (k : ℕ) (f g h : ℤ → ℕ) :
    ∑ c ∈ cube k, f c.1 * g c.2.1 * h c.2.2 =
      (∑ x ∈ Finset.Ico (0 : ℤ) k, f x) * (∑ x ∈ Finset.Ico (0 : ℤ) k, g x) *
        (∑ x ∈ Finset.Ico (0 : ℤ) k, h x) := by
  rw [mul_assoc, Finset.sum_mul_sum, Finset.sum_mul]
  simp only [cube, Finset.sum_product, Finset.mul_sum, mul_assoc]

/-- The cube attains the bound: `LB (cube k) = 6 (k + 2) k` for `k ≥ 2`. -/
private theorem LB_cube (k : ℕ) (hk : 2 ≤ k) : LB (cube k) = 6 * (k + 2) * k := by
  set u : ℤ → ℕ := fun x => (if x = k - 1 then 1 else 0) + (if x = 0 then 1 else 0) with hu
  have hcell : ∀ c ∈ cube k, fmin (exposed (cube k) c) + 1 + u c.1 * u c.2.1 * u c.2.2 =
      (1 + u c.1) * (1 + u c.2.1) * (1 + u c.2.2) := by
    rintro ⟨x, y, z⟩ hc
    rw [mem_cube] at hc
    rw [fmin_exposed]
    have e0 : decide ((x, y, z) + (1, 0, 0) ∉ cube k) = decide (x = k - 1) := by
      simp only [Prod.mk_add_mk, mem_cube, decide_eq_decide]; omega
    have e1 : decide ((x, y, z) + (-1, 0, 0) ∉ cube k) = decide (x = 0) := by
      simp only [Prod.mk_add_mk, mem_cube, decide_eq_decide]; omega
    have e2 : decide ((x, y, z) + (0, 1, 0) ∉ cube k) = decide (y = k - 1) := by
      simp only [Prod.mk_add_mk, mem_cube, decide_eq_decide]; omega
    have e3 : decide ((x, y, z) + (0, -1, 0) ∉ cube k) = decide (y = 0) := by
      simp only [Prod.mk_add_mk, mem_cube, decide_eq_decide]; omega
    have e4 : decide ((x, y, z) + (0, 0, 1) ∉ cube k) = decide (z = k - 1) := by
      simp only [Prod.mk_add_mk, mem_cube, decide_eq_decide]; omega
    have e5 : decide ((x, y, z) + (0, 0, -1) ∉ cube k) = decide (z = 0) := by
      simp only [Prod.mk_add_mk, mem_cube, decide_eq_decide]; omega
    rw [e0, e1, e2, e3, e4, e5]
    have hx : (decide (x = k - 1) && decide (x = 0)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    have hy : (decide (y = k - 1) && decide (y = 0)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    have hz : (decide (z = k - 1) && decide (z = 0)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    have := tabF_upper _ _ _ _ _ _ hx hy hz
    simpa only [decide_eq_true_eq, hu] using this
  have hsum : ∑ x ∈ Finset.Ico (0 : ℤ) k, u x = 2 := by
    simp only [hu, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_Ico]
    split_ifs <;> omega
  clear_value u
  have hsum1 : ∑ x ∈ Finset.Ico (0 : ℤ) k, (1 + u x) = k + 2 := by
    rw [Finset.sum_add_distrib, hsum]
    simp
  have key := Finset.sum_congr rfl hcell
  have key2 := sum_cube_mul k (fun x => 1 + u x) (fun x => 1 + u x) (fun x => 1 + u x)
  rw [key2, Finset.sum_add_distrib, Finset.sum_add_distrib, sum_cube_mul k u u u, hsum,
    hsum1] at key
  simp only [Finset.sum_const, card_cube, smul_eq_mul, mul_one] at key
  unfold LB
  nlinarith [key]

/-- The lower bound: every polycube of `k³` dice has `LB ≥ 6 (k + 2) k` (connectivity is not
needed). -/
private theorem LB_lower (k : ℕ) (P : Finset Cell) (hc : P.card = k ^ 3) :
    6 * (k + 2) * k ≤ LB P := by
  have h1 := LB_ge_proj P
  have h2 := loomis P k
  rw [hc] at h2
  have h3 := sum2_ge k _ _ (by
    calc 4 * k ^ 4 = 4 * k * k ^ 3 := by ring
      _ ≤ _ := h2)
  have h4 : P.card ≤ (P.image fun c => c.1).card *
      ((P.image fun c => c.2.1).card * (P.image fun c => c.2.2).card) := by
    rw [← Finset.card_product, ← Finset.card_product]
    apply Finset.card_le_card
    intro c hc
    simp only [Finset.mem_product]
    exact ⟨Finset.mem_image_of_mem _ hc, Finset.mem_image_of_mem _ hc,
      Finset.mem_image_of_mem _ hc⟩
  rw [hc] at h4
  have h5 := sum3_ge k _ _ _ h4
  nlinarith

/-- The conjecture of A363609: `a (k ^ 3) = 6 (k + 2) k` for every `k > 1`. -/
theorem result : statement := by
  intro k hk
  have hLB : LB (cube k) = 6 * (k + 2) * k := LB_cube k hk
  rw [← hLB]
  exact a_eq_of (LB_mem_totals (card_cube k) (cube_conn k)) fun P hc _ => by
    rw [hLB]
    exact LB_lower k P hc

end Math0.Frontier.A363609

#math0_settles Math0.Frontier.A363609.result Math0.Statements.A363609.statement
