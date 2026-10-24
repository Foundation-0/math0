/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A369366: least number of inequivalent cells of an `n`-iamond, `a(6k+5) = 3(k+1)`

Source: https://oeis.org/A369366, _Peter Exley_, Apr 07 2026 (COMMENTS section). Verbatim:
> Conjecture: a(6k+5) = 3(k+1) for all k >= 0. Observed for k = 0, 1, 2 (n = 5, 11, 17). The
> next test case is a(23), predicted to be 12.

The entry (offset `1`) is "Least number of inequivalent cells in a polyiamond with n cells.",
with the comment "Equivalently, a(n) is the least number of free rooted (or pointed) polyiamonds
(A369365) corresponding to a given polyiamond with n cells."

## Encoding

* *Cells.* The triangular grid is cut by three families of parallel lines. A cell (triangle) is
  labelled by the indices `(a, b, c) ∈ ℤ³` of the strips of the three families that contain it
  (`⌊p·u₁⌋, ⌊p·u₂⌋, ⌊p·u₃⌋` for an interior point `p`, where `u₁ + u₂ + u₃ = 0`, shifted by a
  constant), normalised so that `a + b + c ∈ {0, 1}` (`0` for one orientation of triangles, `1`
  for the other). Every such triple is exactly one cell (`IsCell`). Two cells share an edge iff
  their labels differ by `±1` in exactly one coordinate, i.e. `|a - a'| + |b - b'| + |c - c'| = 1`
  (`Adj`).
* *Polyiamonds.* A polyiamond with `n` cells is a finite set `P` of `n` cells that is
  edge-connected (`IsConnected`: any two cells of `P` are joined by a chain of cells of `P`,
  consecutive ones sharing an edge). `IsPolyiamond n P`.
* *Symmetries.* The symmetries of the triangular grid (the wallpaper group `p6m`) are, in these
  coordinates, the maps `x ↦ σ(x) + t` with `t₁ + t₂ + t₃ = 0` and `x ↦ -σ(x) + t` with
  `t₁ + t₂ + t₃ = 1`, where `σ` is one of the six permutations of the coordinates (`perm`):
  the coordinate permutations are the reflections and `120°`-rotations exchanging the three line
  families, `x ↦ -x + (const)` is a half-turn, and the translations of the grid are the integer
  vectors with coordinate sum `0` (`Isom`, `Isom.app`). (An isometry of the plane mapping a
  polyiamond onto itself maps its boundary corners, which are grid vertices, to grid vertices and
  its boundary edge directions to grid directions, so it is a symmetry of the grid: reading
  "inequivalent" with all isometries of the plane gives the same classes.)
* *Inequivalent cells.* Two cells `c, d` of `P` are equivalent (`Equivalent P c d`) when some
  symmetry of the grid maps `P` onto itself and `c` to `d`; equivalently, the rooted polyiamonds
  `(P, c)` and `(P, d)` are the same free rooted polyiamond. This is an equivalence relation
  (`equivalent_refl`, `equivalent_symm`, `equivalent_trans`); `numClasses P` is the number of its
  classes, i.e. the number of distinct sets `{d ∈ P | Equivalent P c d}` for `c ∈ P`.
* `a n` is the least value of `numClasses P` over all polyiamonds `P` with `n` cells (`sInf`;
  this set is nonempty for every `n ≥ 1`). This definition is not computable as it stands.
  `a_eq_aComp` proves `a n = aComp n` for every `n ≥ 1`, where `aComp` enumerates the
  polyiamonds with `n` cells up to symmetry (`polys`: grown one cell at a time from a single
  cell, each new set replaced by its image under some symmetry of the grid (`canon`), exact
  duplicates removed) and computes the number of classes from the explicit list of symmetries of
  each listed set (`numClassesC`; the translation part of a symmetry is forced by the centroid,
  `t_eq_of_sym`). The proof uses only soundness and completeness of the enumeration up to
  symmetry (`isPolyiamond_of_mem_polys`, `exists_sub_mem_polys`) and the invariance of
  `numClasses` under symmetries of the grid (`numClasses_image`); which symmetric image `canon`
  picks (`bestLin`, `keyOf`, `codeZ`) only affects efficiency, not correctness.
* `a_data` checks the first 8 listed terms `a(1), …, a(8)` in the kernel (about a minute). Each
  further term multiplies the kernel time by about three (the enumeration has 66, 160, 448 free
  polyiamonds with 8, 9, 10 cells), so `a(9)`, `a(10)`, … are not checked.
* The conjecture is stated for every `k ≥ 0`: `a (6k + 5) = 3(k + 1)`.
-/

namespace Math0.Statements.A369366

/-! ### Cells, adjacency and the symmetries of the triangular grid -/

/-- Labels `(a, b, c) ∈ ℤ³`; the cells of the triangular grid are the labels with coordinate sum
`0` or `1`. -/
abbrev Pt := ℤ × ℤ × ℤ

/-- The coordinate sum `a + b + c`. -/
def sumC (x : Pt) : ℤ := x.1 + x.2.1 + x.2.2

/-- `x` is (the label of) a cell of the triangular grid. -/
def IsCell (x : Pt) : Prop := sumC x = 0 ∨ sumC x = 1

/-- The cells `x` and `y` share an edge: their labels differ by `±1` in exactly one coordinate. -/
def Adj (x y : Pt) : Prop := |y.1 - x.1| + |y.2.1 - x.2.1| + |y.2.2 - x.2.2| = 1

/-- The six permutations `σ` of the three coordinates. -/
def perm {α : Type} (s : Fin 6) (x : α × α × α) : α × α × α :=
  match s.val with
  | 0 => (x.1, x.2.1, x.2.2)
  | 1 => (x.1, x.2.2, x.2.1)
  | 2 => (x.2.1, x.1, x.2.2)
  | 3 => (x.2.1, x.2.2, x.1)
  | 4 => (x.2.2, x.1, x.2.1)
  | _ => (x.2.2, x.2.1, x.1)

/-- The linear part `x ↦ σ(x)` (`neg = false`) or `x ↦ -σ(x)` (`neg = true`) of a symmetry. -/
def lin (s : Fin 6) (neg : Bool) (x : Pt) : Pt := if neg then -perm s x else perm s x

/-- The coordinate sum required of the translation part: `0` for `x ↦ σ(x) + t`, `1` for
`x ↦ -σ(x) + t`. -/
def tReq (neg : Bool) : ℤ := if neg then 1 else 0

/-- A symmetry of the triangular grid: `x ↦ σ(x) + t` with `t₁ + t₂ + t₃ = 0`, or
`x ↦ -σ(x) + t` with `t₁ + t₂ + t₃ = 1`. -/
structure Isom where
  /-- the coordinate permutation `σ` -/
  s : Fin 6
  /-- whether the map is `x ↦ -σ(x) + t` -/
  neg : Bool
  /-- the translation part -/
  t : Pt
  ht : sumC t = tReq neg

/-- The action of a symmetry on labels. -/
def Isom.app (g : Isom) (x : Pt) : Pt := lin g.s g.neg x + g.t

/-! ### Polyiamonds and inequivalent cells -/

/-- One step of a chain inside `P`: two cells of `P` sharing an edge. -/
def Step (P : Finset Pt) (u v : Pt) : Prop := u ∈ P ∧ v ∈ P ∧ Adj u v

/-- `P` is edge-connected: any two cells of `P` are joined by a chain of cells of `P` in which
consecutive cells share an edge. -/
def IsConnected (P : Finset Pt) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, Relation.ReflTransGen (Step P) x y

/-- `P` is a polyiamond with `n` cells. -/
def IsPolyiamond (n : ℕ) (P : Finset Pt) : Prop :=
  P.card = n ∧ (∀ x ∈ P, IsCell x) ∧ IsConnected P

/-- The cells `c` and `d` of `P` are equivalent: some symmetry of the grid maps `P` onto itself
and `c` to `d`. -/
def Equivalent (P : Finset Pt) (c d : Pt) : Prop :=
  ∃ g : Isom, P.image g.app = P ∧ g.app c = d

open Classical in
/-- The equivalence class `{d ∈ P | Equivalent P c d}` of `c` in `P`. -/
noncomputable def cls (P : Finset Pt) (c : Pt) : Finset Pt := P.filter (Equivalent P c)

/-- The number of inequivalent cells of `P` (the number of equivalence classes). -/
noncomputable def numClasses (P : Finset Pt) : ℕ := (P.image (cls P)).card

/-- A369366: the least number of inequivalent cells in a polyiamond with `n` cells. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m | ∃ P : Finset Pt, IsPolyiamond n P ∧ numClasses P = m}

/-! ### Algebra of the symmetries -/

/-- Multiplication table of the coordinate permutations: `perm (mulTab i j) = perm i ∘ perm j`. -/
def mulTab (i j : Fin 6) : Fin 6 :=
  ![![0, 1, 2, 3, 4, 5], ![1, 0, 3, 2, 5, 4], ![2, 4, 0, 5, 1, 3], ![3, 5, 1, 4, 0, 2],
    ![4, 2, 5, 0, 3, 1], ![5, 3, 4, 1, 2, 0]] i j

/-- Inverses of the coordinate permutations. -/
def invTab (i : Fin 6) : Fin 6 := ![0, 1, 2, 4, 3, 5] i

theorem perm_mul (i j : Fin 6) (x : Pt) : perm (mulTab i j) x = perm i (perm j x) := by
  fin_cases i <;> fin_cases j <;> rfl

theorem perm_zero (x : Pt) : perm 0 x = x := rfl

theorem mulTab_invTab (i : Fin 6) : mulTab i (invTab i) = 0 := by
  fin_cases i <;> rfl

theorem invTab_mulTab (i : Fin 6) : mulTab (invTab i) i = 0 := by
  fin_cases i <;> rfl

theorem perm_add (s : Fin 6) (x y : Pt) : perm s (x + y) = perm s x + perm s y := by
  fin_cases s <;> rfl

theorem perm_neg (s : Fin 6) (x : Pt) : perm s (-x) = -perm s x := by
  fin_cases s <;> rfl

theorem sumC_perm (s : Fin 6) (x : Pt) : sumC (perm s x) = sumC x := by
  fin_cases s <;> simp only [perm, sumC] <;> ring

theorem sumC_add (x y : Pt) : sumC (x + y) = sumC x + sumC y := by
  simp only [sumC, Prod.fst_add, Prod.snd_add]
  ring

theorem sumC_neg (x : Pt) : sumC (-x) = -sumC x := by
  simp only [sumC, Prod.fst_neg, Prod.snd_neg]
  ring

theorem lin_add (s : Fin 6) (n : Bool) (x y : Pt) : lin s n (x + y) = lin s n x + lin s n y := by
  cases n
  · simp [lin, perm_add]
  · simp only [lin, if_true, perm_add, neg_add]

theorem lin_neg (s : Fin 6) (n : Bool) (x : Pt) : lin s n (-x) = -lin s n x := by
  cases n <;> simp [lin, perm_neg]

theorem lin_sub (s : Fin 6) (n : Bool) (x y : Pt) : lin s n (x - y) = lin s n x - lin s n y := by
  rw [sub_eq_add_neg, lin_add, lin_neg, ← sub_eq_add_neg]

theorem lin_lin (s₁ s₂ : Fin 6) (n₁ n₂ : Bool) (x : Pt) :
    lin s₁ n₁ (lin s₂ n₂ x) = lin (mulTab s₁ s₂) (Bool.xor n₁ n₂) x := by
  cases n₁ <;> cases n₂ <;> simp [lin, perm_neg, perm_mul]

theorem lin_zero (x : Pt) : lin 0 false x = x := rfl

theorem sumC_lin (s : Fin 6) (n : Bool) (x : Pt) :
    sumC (lin s n x) = if n then -sumC x else sumC x := by
  cases n <;> simp [lin, sumC_neg, sumC_perm]

/-- The identity symmetry. -/
def Isom.id : Isom := ⟨0, false, 0, by simp [sumC, tReq]⟩

theorem Isom.id_app (x : Pt) : Isom.id.app x = x := by
  simp [Isom.id, Isom.app, lin_zero]

theorem Isom.id_app' : Isom.id.app = _root_.id := funext Isom.id_app

/-- Composition of symmetries. -/
def Isom.comp (g h : Isom) : Isom where
  s := mulTab g.s h.s
  neg := Bool.xor g.neg h.neg
  t := lin g.s g.neg h.t + g.t
  ht := by
    rw [sumC_add, sumC_lin, g.ht, h.ht]
    cases g.neg <;> cases h.neg <;> simp [tReq]

theorem Isom.comp_app (g h : Isom) (x : Pt) : (g.comp h).app x = g.app (h.app x) := by
  simp only [Isom.app, Isom.comp, lin_add, lin_lin]
  abel

/-- The inverse of a symmetry. -/
def Isom.inv (g : Isom) : Isom where
  s := invTab g.s
  neg := g.neg
  t := -lin (invTab g.s) g.neg g.t
  ht := by
    rw [sumC_neg, sumC_lin, g.ht]
    cases g.neg <;> simp [tReq]

theorem Isom.inv_app_app (g : Isom) (x : Pt) : g.inv.app (g.app x) = x := by
  simp only [Isom.app, Isom.inv, lin_add, lin_lin, invTab_mulTab, Bool.xor_self, lin_zero]
  abel

theorem Isom.app_inv_app (g : Isom) (x : Pt) : g.app (g.inv.app x) = x := by
  simp only [Isom.app, Isom.inv, lin_add, lin_neg, lin_lin, mulTab_invTab, Bool.xor_self,
    lin_zero]
  abel

theorem Isom.app_injective (g : Isom) : Function.Injective g.app := fun x y h => by
  rw [← g.inv_app_app x, h, g.inv_app_app]

theorem Isom.isCell_app (g : Isom) {x : Pt} (hx : IsCell x) : IsCell (g.app x) := by
  obtain ⟨s, n, t, ht⟩ := g
  unfold IsCell at *
  simp only [Isom.app, sumC_add, sumC_lin, ht, tReq]
  cases n <;> simp <;> omega

/-- The `ℓ¹` norm `|a| + |b| + |c|`. -/
def l1 (v : Pt) : ℤ := |v.1| + |v.2.1| + |v.2.2|

theorem adj_iff (x y : Pt) : Adj x y ↔ l1 (y - x) = 1 := Iff.rfl

theorem l1_perm (s : Fin 6) (v : Pt) : l1 (perm s v) = l1 v := by
  fin_cases s <;> simp only [perm, l1] <;> ring

theorem l1_neg (v : Pt) : l1 (-v) = l1 v := by
  simp only [l1, Prod.fst_neg, Prod.snd_neg, abs_neg]

theorem l1_lin (s : Fin 6) (n : Bool) (v : Pt) : l1 (lin s n v) = l1 v := by
  cases n
  · simp [lin, l1_perm]
  · simp only [lin, if_true, l1_neg, l1_perm]

theorem Isom.adj_app (g : Isom) (x y : Pt) : Adj (g.app x) (g.app y) ↔ Adj x y := by
  rw [adj_iff, adj_iff, Isom.app, Isom.app, add_sub_add_right_eq_sub, ← lin_sub, l1_lin]

theorem adj_symm {x y : Pt} (h : Adj x y) : Adj y x := by
  rw [adj_iff] at *
  rw [← neg_sub, l1_neg]
  exact h

/-! ### Equivalence of cells -/

theorem image_image_app (P : Finset Pt) (g h : Isom) :
    (P.image h.app).image g.app = P.image (g.comp h).app := by
  rw [Finset.image_image]
  congr 1
  funext x
  exact (Isom.comp_app g h x).symm

theorem image_inv_image (P : Finset Pt) (h : Isom) : (P.image h.app).image h.inv.app = P := by
  rw [Finset.image_image]
  conv_rhs => rw [← Finset.image_id (s := P)]
  congr 1
  funext x
  exact h.inv_app_app x

theorem equivalent_refl (P : Finset Pt) (c : Pt) : Equivalent P c c :=
  ⟨Isom.id, by rw [Isom.id_app', Finset.image_id], Isom.id_app c⟩

theorem equivalent_symm {P : Finset Pt} {c d : Pt} (h : Equivalent P c d) : Equivalent P d c := by
  obtain ⟨g, hg, rfl⟩ := h
  refine ⟨g.inv, ?_, g.inv_app_app c⟩
  conv_lhs => rw [← hg]
  exact image_inv_image P g

theorem equivalent_trans {P : Finset Pt} {c d e : Pt} (h₁ : Equivalent P c d)
    (h₂ : Equivalent P d e) : Equivalent P c e := by
  obtain ⟨g, hg, rfl⟩ := h₁
  obtain ⟨h, hh, rfl⟩ := h₂
  refine ⟨h.comp g, ?_, h.comp_app g c⟩
  rw [← image_image_app, hg, hh]

/-- Conjugating by a symmetry `h` of the grid. -/
theorem equivalent_image (P : Finset Pt) (h : Isom) (c d : Pt) :
    Equivalent (P.image h.app) (h.app c) (h.app d) ↔ Equivalent P c d := by
  constructor
  · rintro ⟨g, hg, hgc⟩
    refine ⟨h.inv.comp (g.comp h), ?_, ?_⟩
    · rw [← image_image_app, ← image_image_app, hg, image_inv_image]
    · rw [Isom.comp_app, Isom.comp_app, hgc, Isom.inv_app_app]
  · rintro ⟨g, hg, rfl⟩
    refine ⟨h.comp (g.comp h.inv), ?_, ?_⟩
    · rw [← image_image_app, ← image_image_app, image_inv_image, hg]
    · rw [Isom.comp_app, Isom.comp_app, Isom.inv_app_app]

theorem cls_image (P : Finset Pt) (h : Isom) (c : Pt) :
    cls (P.image h.app) (h.app c) = (cls P c).image h.app := by
  ext y
  simp only [cls, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hxy⟩
    exact ⟨x, ⟨hx, (equivalent_image P h c x).1 hxy⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hcx⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (equivalent_image P h c x).2 hcx⟩

/-- The number of inequivalent cells is invariant under the symmetries of the grid. -/
theorem numClasses_image (P : Finset Pt) (h : Isom) :
    numClasses (P.image h.app) = numClasses P := by
  unfold numClasses
  rw [Finset.image_image]
  have : (cls (P.image h.app) ∘ h.app) = (Finset.image h.app) ∘ cls P := by
    funext c
    exact cls_image P h c
  rw [this, ← Finset.image_image]
  exact Finset.card_image_of_injective _ (Finset.image_injective h.app_injective)

/-- A symmetry maps `P` onto itself iff it maps `P` into itself. -/
theorem image_eq_iff (P : Finset Pt) (g : Isom) : P.image g.app = P ↔ ∀ x ∈ P, g.app x ∈ P := by
  constructor
  · intro h x hx
    rw [← h]
    exact Finset.mem_image_of_mem _ hx
  · intro h
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.image_subset_iff.2 h
    · exact (Finset.card_image_of_injective _ g.app_injective).ge

/-! ### Computing the number of inequivalent cells -/

/-- The twelve linear parts `(σ, ±)`. -/
def allLin : List (Fin 6 × Bool) := (List.finRange 6).flatMap fun s => [(s, false), (s, true)]

theorem mem_allLin : ∀ sn : Fin 6 × Bool, sn ∈ allLin := by
  decide

/-- Componentwise integer division. -/
def divPt (v : Pt) (k : ℤ) : Pt := (v.1 / k, v.2.1 / k, v.2.2 / k)

theorem divPt_smul (t : Pt) {k : ℤ} (hk : k ≠ 0) : divPt (k • t) k = t := by
  obtain ⟨a, b, c⟩ := t
  simp [divPt, Int.mul_ediv_cancel_left _ hk]

theorem perm_zero' (s : Fin 6) : perm s (0 : Pt) = 0 := by
  fin_cases s <;> rfl

/-- The linear part of a symmetry, as an additive map. -/
def linHom (s : Fin 6) (n : Bool) : Pt →+ Pt where
  toFun := lin s n
  map_zero' := by cases n <;> simp [lin, perm_zero']
  map_add' := lin_add s n

/-- A symmetry `g` of a nonempty finite set `P` fixes its centroid, so its translation part is
`(Σ P - (±σ)(Σ P)) / |P|`. -/
theorem t_eq_of_sym {P : Finset Pt} (hP : P.Nonempty) {g : Isom} (hg : P.image g.app = P) :
    g.t = divPt (P.sum id - lin g.s g.neg (P.sum id)) P.card := by
  have h1 : P.sum id = P.sum g.app := by
    conv_lhs => rw [← hg]
    rw [Finset.sum_image fun x _ y _ h => g.app_injective h]
    rfl
  have h2 : P.sum g.app = lin g.s g.neg (P.sum id) + (P.card : ℤ) • g.t := by
    rw [show P.sum g.app = ∑ x ∈ P, (lin g.s g.neg x + g.t) from rfl,
      Finset.sum_add_distrib, Finset.sum_const, ← natCast_zsmul]
    congr 1
    exact (map_sum (linHom g.s g.neg) id P).symm
  rw [sub_eq_iff_eq_add'.2 (h1.trans h2), divPt_smul _ (by exact_mod_cast hP.card_pos.ne')]

/-- The translation part forced by the centroid of `Q` for the linear part `sn`. -/
def tOf (Q : List Pt) (sn : Fin 6 × Bool) : Pt :=
  divPt (Q.toFinset.sum id - lin sn.1 sn.2 (Q.toFinset.sum id)) Q.toFinset.card

/-- The symmetries `(σ, ±, t)` of the grid mapping the cells of `Q` into themselves (the
translation part is forced by the centroid, `t_eq_of_sym`). -/
def symsC (Q : List Pt) : List (Fin 6 × Bool × Pt) :=
  allLin.filterMap fun sn =>
    if sumC (tOf Q sn) = tReq sn.2 ∧ ∀ x ∈ Q, lin sn.1 sn.2 x + tOf Q sn ∈ Q then
      some (sn.1, sn.2, tOf Q sn)
    else none

theorem of_mem_symsC {Q : List Pt} {s : Fin 6} {n : Bool} {t : Pt} (h : (s, n, t) ∈ symsC Q) :
    sumC t = tReq n ∧ ∀ x ∈ Q, lin s n x + t ∈ Q := by
  obtain ⟨sn, -, hsn⟩ := List.mem_filterMap.1 h
  split_ifs at hsn with hc
  cases hsn
  exact hc

theorem mem_symsC_of_sym {Q : List Pt} (hQ : Q ≠ []) {g : Isom}
    (hg : Q.toFinset.image g.app = Q.toFinset) : (g.s, g.neg, g.t) ∈ symsC Q := by
  have hne : Q.toFinset.Nonempty := by
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hQ
    exact ⟨x, by simp⟩
  have ht : tOf Q (g.s, g.neg) = g.t := (t_eq_of_sym hne hg).symm
  have hc : sumC g.t = tReq g.neg ∧ ∀ x ∈ Q, lin g.s g.neg x + g.t ∈ Q :=
    ⟨g.ht, fun x hx => List.mem_toFinset.1 ((image_eq_iff _ g).1 hg x (List.mem_toFinset.2 hx))⟩
  refine List.mem_filterMap.2 ⟨(g.s, g.neg), mem_allLin _, ?_⟩
  dsimp only
  rw [ht, if_pos hc]

/-- The orbit of `c` under the symmetries of `Q`. -/
def orbitC (Q : List Pt) (c : Pt) : List Pt := (symsC Q).map fun g => lin g.1 g.2.1 c + g.2.2

theorem equivalent_iff_mem_orbitC {Q : List Pt} (hQ : Q ≠ []) (c d : Pt) :
    Equivalent Q.toFinset c d ↔ d ∈ orbitC Q c := by
  simp only [orbitC, List.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨(g.s, g.neg, g.t), mem_symsC_of_sym hQ hg, rfl⟩
  · rintro ⟨⟨s, n, t⟩, hm, rfl⟩
    obtain ⟨h1, h2⟩ := of_mem_symsC hm
    refine ⟨⟨s, n, t, h1⟩, (image_eq_iff _ _).2 fun x hx => ?_, rfl⟩
    exact List.mem_toFinset.2 (h2 x (List.mem_toFinset.1 hx))

/-- The number of inequivalent cells of the polyiamond listed by `Q`, computed from the list of
its symmetries. -/
def numClassesC (Q : List Pt) : ℕ :=
  (Q.toFinset.image fun c => Q.toFinset.filter (· ∈ orbitC Q c)).card

theorem numClassesC_eq {Q : List Pt} (hQ : Q ≠ []) : numClassesC Q = numClasses Q.toFinset := by
  unfold numClassesC numClasses
  congr 1
  apply Finset.image_congr
  intro c _
  ext d
  simp only [cls, Finset.mem_filter]
  exact and_congr_right fun _ => (equivalent_iff_mem_orbitC hQ c d).symm

/-! ### Enumerating polyiamonds up to symmetry -/

/-- The three cells sharing an edge with the cell `x`. -/
def nbrs (x : Pt) : List Pt :=
  if sumC x = 0 then [x + (1, 0, 0), x + (0, 1, 0), x + (0, 0, 1)]
  else [x - (1, 0, 0), x - (0, 1, 0), x - (0, 0, 1)]

theorem of_mem_nbrs {x y : Pt} (hx : IsCell x) (h : y ∈ nbrs x) : Adj x y ∧ IsCell y := by
  unfold nbrs at h
  unfold IsCell sumC at *
  unfold Adj
  split_ifs at h <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.ext_iff, Prod.fst_add,
      Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at h
    rcases abs_cases (y.1 - x.1) with h1 | h1 <;> rcases abs_cases (y.2.1 - x.2.1) with h2 | h2 <;>
      rcases abs_cases (y.2.2 - x.2.2) with h3 | h3 <;> omega

theorem mem_nbrs {x y : Pt} (hx : IsCell x) (hy : IsCell y) (h : Adj x y) : y ∈ nbrs x := by
  unfold nbrs
  unfold IsCell sumC at *
  unfold Adj at h
  split_ifs <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.ext_iff, Prod.fst_add,
      Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    rcases abs_cases (y.1 - x.1) with h1 | h1 <;> rcases abs_cases (y.2.1 - x.2.1) with h2 | h2 <;>
      rcases abs_cases (y.2.2 - x.2.2) with h3 | h3 <;> omega

/-- The least element of a list of naturals (`0` for the empty list). -/
def listMin : List ℕ → ℕ
  | [] => 0
  | x :: xs => xs.foldl min x

/-- The largest element of a list of naturals (`0` for the empty list). -/
def listMax : List ℕ → ℕ
  | [] => 0
  | x :: xs => xs.foldl max x

/-- A translation (coordinate sum `0`) moving the least first and second coordinates of the
cells of `l` to `0`. -/
def shiftOf : List Pt → Pt
  | [] => 0
  | x :: xs =>
    (-(xs.foldl (fun m y => min m y.1) x.1), -(xs.foldl (fun m y => min m y.2.1) x.2.1),
      xs.foldl (fun m y => min m y.1) x.1 + xs.foldl (fun m y => min m y.2.1) x.2.1)

theorem sumC_shiftOf (l : List Pt) : sumC (shiftOf l) = 0 := by
  cases l with
  | nil => rfl
  | cons x xs => simp only [shiftOf, sumC]; ring

/-- `(1, 0, 0)` for `x ↦ -σ(x)` (to bring the coordinate sums back to `{0, 1}`), else `0`. -/
def eVec (neg : Bool) : Pt := if neg then (1, 0, 0) else 0

theorem sumC_eVec (neg : Bool) : sumC (eVec neg) = tReq neg := by
  cases neg <;> rfl

/-- The image of `l` under the linear part `sn`, translated so that the least first and second
coordinates of its cells are `0`. -/
def image12 (l : List Pt) (sn : Fin 6 × Bool) : List Pt :=
  (l.map fun x => lin sn.1 sn.2 x + eVec sn.2).map
    (· + shiftOf (l.map fun x => lin sn.1 sn.2 x + eVec sn.2))

/-- A numerical code of a cell (used only to order cells). -/
def codeZ (x : Pt) : ℕ := (x.1.toNat * 128 + x.2.1.toNat) * 2 + (sumC x).toNat

/-- Offset natural coordinates of a label (used only to choose a representative). -/
def natC (x : Pt) : ℕ × ℕ × ℕ := ((x.1 + 64).toNat, (x.2.1 + 64).toNat, (x.2.2 + 64).toNat)

/-- For a cell with offset coordinates `p`, given the coordinatewise minima `mn` and maxima `mx`:
`(p - mn, mx - p, orientation)` (used only to choose a representative). -/
def prep (mn mx : ℕ × ℕ × ℕ) (p : ℕ × ℕ × ℕ) : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × ℕ :=
  ((p.1 - mn.1, p.2.1 - mn.2.1, p.2.2 - mn.2.2), (mx.1 - p.1, mx.2.1 - p.2.1, mx.2.2 - p.2.2),
    p.1 + p.2.1 + p.2.2 - 192)

/-- For small polyiamonds, the sum of `2 ^ codeZ y` over the cells `y` of `image12 l sn`,
computed with natural numbers from the data `prep` of the cells of `l` (used only to choose a
representative). -/
def keyOf (D : List ((ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × ℕ)) (sn : Fin 6 × Bool) : ℕ :=
  D.foldl (fun acc d => acc + 2 ^ (if sn.2 then
      ((perm sn.1 d.2.1).1 * 128 + (perm sn.1 d.2.1).2.1) * 2 + (1 - d.2.2)
    else ((perm sn.1 d.1).1 * 128 + (perm sn.1 d.1).2.1) * 2 + d.2.2)) 0

/-- A linear part whose normalised image of `l` has the least key, with that key (used only to
choose a representative). -/
def bestLin (l : List Pt) : ℕ × (Fin 6 × Bool) :=
  let N := l.map natC
  let mn := (listMin (N.map (·.1)), listMin (N.map (·.2.1)), listMin (N.map (·.2.2)))
  let mx := (listMax (N.map (·.1)), listMax (N.map (·.2.1)), listMax (N.map (·.2.2)))
  let D := N.map (prep mn mx)
  allLin.foldl (fun best sn => if keyOf D sn < best.1 then (keyOf D sn, sn) else best)
    (keyOf D (0, false), (0, false))

/-- A representative of the cell set `l` up to symmetry, with a key: a normalised image of `l`
under one of the twelve linear parts, its cells sorted. -/
def canon (l : List Pt) : ℕ × List Pt :=
  ((bestLin l).1, (image12 l (bestLin l).2).insertionSort fun x y => codeZ x ≤ codeZ y)

theorem toFinset_map (l : List Pt) (f : Pt → Pt) : (l.map f).toFinset = l.toFinset.image f := by
  ext x
  simp

theorem image12_spec (l : List Pt) (sn : Fin 6 × Bool) :
    ∃ g : Isom, (image12 l sn).toFinset = l.toFinset.image g.app := by
  refine ⟨⟨sn.1, sn.2, eVec sn.2 + shiftOf (l.map fun x => lin sn.1 sn.2 x + eVec sn.2), ?_⟩, ?_⟩
  · rw [sumC_add, sumC_eVec, sumC_shiftOf, add_zero]
  · rw [image12, List.map_map, toFinset_map]
    congr 1
    funext x
    simp only [Function.comp, Isom.app, add_assoc]

theorem canon_spec (l : List Pt) :
    ∃ g : Isom, (canon l).2.toFinset = l.toFinset.image g.app := by
  obtain ⟨g, hg⟩ := image12_spec l (bestLin l).2
  refine ⟨g, ?_⟩
  simp only [canon]
  rw [List.toFinset_eq_of_perm _ _ (List.perm_insertionSort _ _), hg]

/-- The cell sets obtained from `Q` by adding one cell sharing an edge with a cell of `Q`, each
replaced by its representative up to symmetry. -/
def children (Q : List Pt) : List (ℕ × List Pt) :=
  (Q.flatMap nbrs).filterMap fun y => if y ∈ Q then none else some (canon (y :: Q))

/-- Insert `k` into `acc` unless it is already there. -/
def addNew (acc : List (ℕ × List Pt)) (k : ℕ × List Pt) : List (ℕ × List Pt) :=
  if k ∈ acc then acc else k :: acc

theorem mem_foldl_addNew (k : ℕ × List Pt) :
    ∀ (l acc : List (ℕ × List Pt)), k ∈ l.foldl addNew acc ↔ k ∈ acc ∨ k ∈ l
  | [], acc => by simp
  | x :: xs, acc => by
    rw [List.foldl_cons, mem_foldl_addNew k xs, addNew]
    split_ifs with h
    · constructor
      · rintro (h' | h')
        · exact Or.inl h'
        · exact Or.inr (List.mem_cons_of_mem _ h')
      · rintro (h' | h')
        · exact Or.inl h'
        · rcases List.mem_cons.1 h' with rfl | h'
          · exact Or.inl h
          · exact Or.inr h'
    · simp only [List.mem_cons]
      tauto

/-- One growth step, with duplicates removed. -/
def grow (L : List (ℕ × List Pt)) : List (ℕ × List Pt) :=
  (L.flatMap fun e => children e.2).foldl addNew []

theorem mem_grow {L : List (ℕ × List Pt)} {k : ℕ × List Pt} :
    k ∈ grow L ↔ ∃ e ∈ L, ∃ b ∈ e.2, ∃ y ∈ nbrs b, y ∉ e.2 ∧ k = canon (y :: e.2) := by
  rw [grow, mem_foldl_addNew]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap, children, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, y, ⟨b, hb, hy⟩, h⟩
    split_ifs at h with hyQ
    exact ⟨e, he, b, hb, y, hy, hyQ, (Option.some.inj h).symm⟩
  · rintro ⟨e, he, b, hb, y, hy, hyQ, rfl⟩
    exact ⟨e, he, y, ⟨b, hb, hy⟩, by rw [if_neg hyQ]⟩

/-- Representatives (with keys), up to symmetry, of all polyiamonds with `n` cells (possibly with
repetitions up to symmetry). -/
def polys : ℕ → List (ℕ × List Pt)
  | 0 => [(0, [])]
  | 1 => [(0, [0])]
  | n + 2 => grow (polys (n + 1))

theorem foldl_min_le : ∀ (xs : List ℕ) (x : ℕ), xs.foldl min x ≤ x ∧ ∀ y ∈ xs, xs.foldl min x ≤ y
  | [], x => by simp
  | z :: zs, x => by
    obtain ⟨h1, h2⟩ := foldl_min_le zs (min x z)
    refine ⟨h1.trans (min_le_left _ _), fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h1.trans (min_le_right _ _)
    · exact h2 y hy

theorem foldl_min_mem : ∀ (xs : List ℕ) (x : ℕ), xs.foldl min x ∈ x :: xs
  | [], x => by simp
  | z :: zs, x => by
    rcases List.mem_cons.1 (foldl_min_mem zs (min x z)) with h | h
    · rw [List.foldl_cons, h]
      rcases min_choice x z with h' | h' <;> rw [h'] <;> simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem listMin_le {l : List ℕ} {y : ℕ} (hy : y ∈ l) : listMin l ≤ y := by
  cases l with
  | nil => simp at hy
  | cons x xs =>
    rcases List.mem_cons.1 hy with rfl | hy
    · exact (foldl_min_le xs _).1
    · exact (foldl_min_le xs x).2 y hy

theorem listMin_mem {l : List ℕ} (hl : l ≠ []) : listMin l ∈ l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons x xs => exact foldl_min_mem xs x

/-- A computable version of A369366 (equal to `a n` for `n ≥ 1`, `a_eq_aComp`). -/
def aComp (n : ℕ) : ℕ := listMin ((polys n).map fun e => numClassesC e.2)

/-! ### Correctness of the enumeration -/

/-- Mapping a chain along `f`. -/
theorem rtg_map {r p : Pt → Pt → Prop} (f : Pt → Pt) (h : ∀ u v, r u v → p (f u) (f v))
    {x y : Pt} (hxy : Relation.ReflTransGen r x y) : Relation.ReflTransGen p (f x) (f y) := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

theorem isPolyiamond_image {n : ℕ} {P : Finset Pt} (hP : IsPolyiamond n P) (g : Isom) :
    IsPolyiamond n (P.image g.app) := by
  obtain ⟨hcard, hcell, hconn⟩ := hP
  refine ⟨by rw [Finset.card_image_of_injective _ g.app_injective, hcard], ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact g.isCell_app (hcell y hy)
  · intro x' hx' y' hy'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hy'
    exact rtg_map g.app
      (fun u v (huv : Step P u v) => ⟨Finset.mem_image_of_mem _ huv.1,
        Finset.mem_image_of_mem _ huv.2.1, (g.adj_app u v).2 huv.2.2⟩)
      (hconn x hx y hy)

theorem isConnected_insert {P : Finset Pt} (hP : IsConnected P) {b y : Pt} (hb : b ∈ P)
    (hby : Adj b y) : IsConnected (insert y P) := by
  have mono : ∀ u v, Relation.ReflTransGen (Step P) u v →
      Relation.ReflTransGen (Step (insert y P)) u v := fun u v h =>
    rtg_map _root_.id (fun p q (hpq : Step P p q) =>
      ⟨Finset.mem_insert_of_mem hpq.1, Finset.mem_insert_of_mem hpq.2.1, hpq.2.2⟩) h
  have hbI : b ∈ insert y P := Finset.mem_insert_of_mem hb
  have hyI : y ∈ insert y P := Finset.mem_insert_self y P
  have to_y : ∀ u ∈ P, Relation.ReflTransGen (Step (insert y P)) u y := fun u hu =>
    (mono u b (hP u hu b hb)).tail ⟨hbI, hyI, hby⟩
  have from_y : ∀ u ∈ P, Relation.ReflTransGen (Step (insert y P)) y u := fun u hu =>
    Relation.ReflTransGen.head ⟨hyI, hbI, adj_symm hby⟩ (mono b u (hP b hb u hu))
  intro u hu v hv
  rcases Finset.mem_insert.1 hu with hu | hu <;> rcases Finset.mem_insert.1 hv with hv | hv
  · rw [hu, hv]
  · rw [hu]
    exact from_y v hv
  · rw [hv]
    exact to_y u hu
  · exact mono u v (hP u hu v hv)

/-- Every listed cell set is a polyiamond with `n` cells. -/
theorem isPolyiamond_of_mem_polys : ∀ (n : ℕ), 1 ≤ n → ∀ e ∈ polys n,
    IsPolyiamond n e.2.toFinset
  | 0, h, _, _ => absurd h (by norm_num)
  | 1, _, e, he => by
    rw [polys, List.mem_singleton] at he
    subst he
    refine ⟨by simp, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_toFinset, List.mem_singleton] at hx
      subst hx
      left
      simp [sumC]
    · intro x hx y hy
      simp only [List.mem_toFinset, List.mem_singleton] at hx hy
      subst hx hy
      exact Relation.ReflTransGen.refl
  | n + 2, _, e', he' => by
    rw [polys, mem_grow] at he'
    obtain ⟨e, he, b, hb, y, hy, hyQ, rfl⟩ := he'
    obtain ⟨hcard, hcell, hconn⟩ := isPolyiamond_of_mem_polys (n + 1) (by omega) e he
    set Q := e.2
    have hbQ : b ∈ Q.toFinset := List.mem_toFinset.2 hb
    obtain ⟨hadj, hycell⟩ := of_mem_nbrs (hcell b hbQ) hy
    have hP : IsPolyiamond (n + 2) (y :: Q).toFinset := by
      rw [List.toFinset_cons]
      refine ⟨?_, ?_, isConnected_insert hconn hbQ hadj⟩
      · rw [Finset.card_insert_of_notMem (by simpa using hyQ), hcard]
      · intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hycell
        · exact hcell x hx
    obtain ⟨g, hg⟩ := canon_spec (y :: Q)
    rw [hg]
    exact isPolyiamond_image hP g

theorem frontier {P A : Finset Pt} {x q : Pt} (hx : x ∈ A) (hq : q ∉ A)
    (h : Relation.ReflTransGen (Step P) x q) : ∃ b ∈ A, ∃ c ∈ P, c ∉ A ∧ Adj b c := by
  induction h with
  | refl => exact absurd hx hq
  | @tail b c _ hbc ih =>
    by_cases hb : b ∈ A
    · exact ⟨b, hb, c, hbc.2.1, hq, hbc.2.2⟩
    · exact ih hb

/-- A symmetry moving the cell `p` to `0`. -/
theorem exists_isom_zero {p : Pt} (hp : IsCell p) : ∃ g : Isom, g.app p = 0 := by
  rcases hp with hp | hp
  · refine ⟨⟨0, false, -p, by rw [sumC_neg, hp]; rfl⟩, ?_⟩
    simp [Isom.app, lin_zero]
  · refine ⟨⟨0, true, p, by rw [hp]; rfl⟩, ?_⟩
    simp [Isom.app, lin, perm_zero]

/-- Every polyiamond with at least `k ≥ 1` cells contains `k` cells whose set is mapped by a
symmetry onto a listed cell set. -/
theorem exists_sub_mem_polys {P : Finset Pt} (hcell : ∀ x ∈ P, IsCell x) (hconn : IsConnected P) :
    ∀ k, 1 ≤ k → k ≤ P.card → ∃ A ⊆ P, A.card = k ∧ ∃ Q ∈ polys k, ∃ g : Isom,
      A.image g.app = Q.2.toFinset
  | 0, h, _ => absurd h (by norm_num)
  | 1, _, hk => by
    obtain ⟨p, hp⟩ := Finset.card_pos.1 (show 0 < P.card by omega)
    obtain ⟨g, hg⟩ := exists_isom_zero (hcell p hp)
    refine ⟨{p}, Finset.singleton_subset_iff.2 hp, rfl, (0, [0]), List.mem_singleton_self _, g,
      ?_⟩
    rw [Finset.image_singleton, hg]
    simp
  | k + 2, _, hk => by
    obtain ⟨A, hAP, hAc, e, he, g, hg⟩ := exists_sub_mem_polys hcell hconn (k + 1) (by omega)
      (by omega)
    set Q := e.2 with hQe
    obtain ⟨q, hqP, hqA⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := A) (t := P)
      (by omega)
    obtain ⟨x, hx⟩ : A.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨b, hbA, c, hcP, hcA, hbc⟩ := frontier hx hqA (hconn x (hAP hx) q hqP)
    have hgb : g.app b ∈ Q := by
      rw [← List.mem_toFinset, ← hg]
      exact Finset.mem_image_of_mem _ hbA
    have hgc : g.app c ∉ Q := by
      intro h
      rw [← List.mem_toFinset, ← hg] at h
      obtain ⟨c', hc', hcc⟩ := Finset.mem_image.1 h
      exact hcA (g.app_injective hcc ▸ hc')
    have hnb : g.app c ∈ nbrs (g.app b) :=
      mem_nbrs (g.isCell_app (hcell b (hAP hbA))) (g.isCell_app (hcell c hcP))
        ((g.adj_app b c).2 hbc)
    obtain ⟨g', hg'⟩ := canon_spec (g.app c :: Q)
    refine ⟨insert c A, Finset.insert_subset hcP hAP, by
      rw [Finset.card_insert_of_notMem hcA, hAc], canon (g.app c :: Q), ?_, g'.comp g, ?_⟩
    · rw [polys, mem_grow]
      exact ⟨e, he, g.app b, hgb, g.app c, hnb, hgc, rfl⟩
    · rw [hg', ← image_image_app, Finset.image_insert, hg, List.toFinset_cons]

theorem a_eq_aComp {n : ℕ} (hn : 1 ≤ n) : a n = aComp n := by
  have hval : ∀ Q ∈ polys n, numClassesC Q.2 = numClasses Q.2.toFinset := by
    intro Q hQ
    apply numClassesC_eq
    intro h
    have := (isPolyiamond_of_mem_polys n hn _ hQ).1
    rw [h] at this
    simp at this
    omega
  have cover : ∀ P, IsPolyiamond n P → ∃ Q ∈ polys n, numClasses P = numClassesC Q.2 := by
    rintro P ⟨hcard, hcell, hconn⟩
    obtain ⟨A, hAP, hAc, Q, hQ, g, hg⟩ :=
      exists_sub_mem_polys hcell hconn n hn hcard.ge
    have hA : A = P := Finset.eq_of_subset_of_card_le hAP (by omega)
    subst hA
    refine ⟨Q, hQ, ?_⟩
    rw [hval Q hQ, ← hg, numClasses_image]
  unfold a aComp
  by_cases hL : polys n = []
  · rw [hL, List.map_nil, listMin]
    convert Nat.sInf_empty
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨P, hP, -⟩
    obtain ⟨Q, hQ, -⟩ := cover P hP
    rw [hL] at hQ
    simp at hQ
  · have hne : (polys n).map (fun e => numClassesC e.2) ≠ [] := by simpa using hL
    obtain ⟨Q, hQ, hQm⟩ := List.mem_map.1 (listMin_mem hne)
    have hmem : listMin ((polys n).map fun e => numClassesC e.2) ∈
        {m | ∃ P : Finset Pt, IsPolyiamond n P ∧ numClasses P = m} :=
      ⟨Q.2.toFinset, isPolyiamond_of_mem_polys n hn Q hQ, by rw [← hQm, hval Q hQ]⟩
    apply le_antisymm (Nat.sInf_le hmem)
    apply le_csInf ⟨_, hmem⟩
    rintro m ⟨P, hP, rfl⟩
    obtain ⟨Q', hQ', hQ'm⟩ := cover P hP
    rw [hQ'm]
    have hm : numClassesC Q'.2 ∈ (polys n).map fun e => numClassesC e.2 :=
      List.mem_map_of_mem hQ'
    exact listMin_le hm

/-! ### Data and the conjecture -/

/-- The definition reproduces the first 8 listed terms `a(1), …, a(8)` (kernel-checked). -/
theorem a_data : (List.range 8).map (fun i => a (i + 1)) = [1, 1, 2, 2, 3, 1, 3, 3] := by
  rw [show (fun i => a (i + 1)) = fun i => aComp (i + 1) from
    funext fun i => a_eq_aComp (by omega)]
  decide +kernel

/-- Conjecture (Exley, A369366): for every `k ≥ 0`, the least number of inequivalent cells in a
polyiamond with `6k + 5` cells is `3(k + 1)`. -/
def statement : Prop := ∀ k : ℕ, a (6 * k + 5) = 3 * (k + 1)

end Math0.Statements.A369366
