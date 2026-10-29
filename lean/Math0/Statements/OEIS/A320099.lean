/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A320099: Kagey's order-10 recurrence for no-leaf subgraphs of the `5 × n` grid

Source: https://oeis.org/A320099, Peter Kagey (author of the entry), Oct 05 2018 (FORMULA
section). Verbatim:
> Conjecture: a(n) = 103*a(n-1) + 1063*a(n-2) - 1873*a(n-3) - 20274*a(n-4) + 44071*a(n-5) -
> 10365*a(n-6) - 20208*a(n-7) + 5959*a(n-8) + 2300*a(n-9) - 500*a(n-10) for n > 10.

The sequence (offset `1`) is "Number of no-leaf subgraphs of the 5 X n grid." with the comment
"Also, the number of ways to lay unit-length matchsticks on a 5 X n grid of points in such a way
that no end is "orphaned"."

## Encoding

* The `5 × n` grid is Mathlib's `pathGraph 5 □ pathGraph n` on `Fin 5 × Fin n` (row, column):
  `(r, c)` and `(r', c')` are adjacent iff they agree in one coordinate and differ by `1` in the
  other. It has `4n` vertical and `5(n - 1)` horizontal edges.
* A subgraph is identified with its edge set `S ⊆ E(grid n)`, all vertices being kept (a spanning
  subgraph); a leaf is a vertex of degree exactly `1`, and the degree `deg S v` of `v` is the
  number of edges of `S` containing `v` (the grid has no loops). So
  `a n = #{S ⊆ E(grid n) | ∀ v, deg S v ≠ 1}`. This is the matchstick reading of the comment
  (a matchstick is a grid edge, an orphaned end is a point touched by exactly one matchstick),
  and it is the reading fixed by the data: `a(1) = 1`, since every nonempty edge set of the path
  `5 × 1` has an end of degree `1` (if subgraphs could also omit vertices, the empty edge set
  alone would give `2^5` subgraphs of the `5 × 1` grid).
* The OEIS offset is `1`; `a 0 = 1` (the empty grid) is not a term of the sequence.
* `a` is computable but far too slow for the kernel, so `a_eq_T` proves, for every `n`, that
  `a n = (T ^ n) noH noH` for the `32 × 32` column transfer matrix `T` (states are the sets of
  horizontal edges between consecutive columns, `T L R` counts the vertical-edge sets of a
  column that leave no vertex of that column with degree `1`). The proof is a bijection between
  edge sets and column data (`dec`, `enc`) that reads off every degree (`deg_dec`). Then
  `a_eq_fastA` turns this into a list computation and `a_data` checks all `15` listed terms
  `a(1), …, a(15)` with `decide +kernel`.
* `statement` asserts the recurrence for every `n > 10`, as stated, as an identity in `ℤ`
  (because of the subtractions). The indices `n - k` (`1 ≤ k ≤ 10`) are natural-number
  subtractions; for `n > 10` they are exact and `≥ 1`, so only terms of the sequence occur.
  `statement_check_listed` checks (in the kernel) that the identity holds at `n = 11, …, 15`,
  as a guard against transcription errors; this is not a proof of `statement`.
-/

namespace Math0.Statements.A320099

open Finset SimpleGraph

/-- The `5 × n` grid graph: Mathlib's box product of the path graphs on `5` and on `n` vertices,
with vertex set `Fin 5 × Fin n` (row, column). Two vertices are adjacent iff they agree in one
coordinate and differ by `1` in the other. -/
abbrev grid (n : ℕ) : SimpleGraph (Fin 5 × Fin n) := pathGraph 5 □ pathGraph n

/-- Adjacency in the grid is decidable (unfolded through `boxProd_adj` and `pathGraph_adj`). -/
instance (n : ℕ) : DecidableRel (grid n).Adj := fun x y =>
  decidable_of_iff
    ((x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val) ∧ x.2 = y.2 ∨
      (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val) ∧ x.1 = y.1)
    (by simp only [boxProd_adj, pathGraph_adj])

/-- The degree of the vertex `v` in the (spanning) subgraph with edge set `S`: the number of edges
of `S` that contain `v`. -/
def deg {n : ℕ} (S : Finset (Sym2 (Fin 5 × Fin n))) (v : Fin 5 × Fin n) : ℕ := #{e ∈ S | v ∈ e}

/-- A320099: the number of no-leaf subgraphs of the `5 × n` grid, i.e. the number of edge sets
`S ⊆ E(grid n)` such that no vertex has degree exactly `1` in `S`. -/
def a (n : ℕ) : ℕ := #{S ∈ (grid n).edgeFinset.powerset | ∀ v, deg S v ≠ 1}

/-! ### The column transfer matrix

The data check cannot enumerate the `2 ^ (9n - 5)` edge sets of the grid, so `a` is computed by
the standard column transfer matrix, and `a_eq_T` proves that this is correct for every `n`. -/

/-- A set of horizontal edges between two consecutive columns: `L r` says whether the edge in
row `r` is present. -/
abbrev St := Fin 5 → Bool

/-- A set of vertical edges inside one column: `V i` says whether the edge between rows `i` and
`i + 1` is present. -/
abbrev Col := Fin 4 → Bool

/-- The degree of the vertex in row `r` of a column, given the horizontal edges `L` to its left,
the vertical edges `V` of the column and the horizontal edges `R` to its right. -/
def colDeg (L : St) (V : Col) (R : St) (r : Fin 5) : ℕ :=
  (if L r then 1 else 0) + (if R r then 1 else 0) +
    #{i : Fin 4 | V i = true ∧ (i.castSucc = r ∨ i.succ = r)}

/-- No vertex of the column is a leaf. -/
def ok (L : St) (V : Col) (R : St) : Prop := ∀ r : Fin 5, colDeg L V R r ≠ 1

instance (L : St) (V : Col) (R : St) : Decidable (ok L V R) := by unfold ok; infer_instance

/-- The `32 × 32` transfer matrix: `T L R` counts the vertical-edge sets of a column that make
no vertex of the column a leaf, given `L` and `R`. -/
def T : Matrix St St ℕ := fun L R => #{V : Col | ok L V R}

/-- Column data of a `5 × n` grid: for each column `c`, its vertical edges and the horizontal
edges from column `c` to column `c + 1`. -/
abbrev ColSeq (n : ℕ) := Fin n → Col × St

/-- No horizontal edges. -/
def noH : St := fun _ => false

/-- The horizontal edges to the left of column `c` (`s` for the first column). -/
def prevH {n : ℕ} (s : St) (x : ColSeq n) (c : Fin n) : St :=
  if c.val = 0 then s else (x ⟨c.val - 1, by omega⟩).2

/-- The horizontal edges to the right of the last column (`s` if there are no columns). -/
def lastH {n : ℕ} (s : St) (x : ColSeq n) : St :=
  if h : n = 0 then s else (x ⟨n - 1, by omega⟩).2

/-- Column data, starting with horizontal edges `s` and ending with `e`, with no leaf. -/
def Good {n : ℕ} (s e : St) (x : ColSeq n) : Prop :=
  (∀ c, ok (prevH s x c) (x c).1 (x c).2) ∧ lastH s x = e

instance {n : ℕ} (s e : St) : DecidablePred (@Good n s e) := fun x => by
  unfold Good; infer_instance

theorem cons_mk {n : ℕ} (y : Col × St) (x : ColSeq n) (k : ℕ) (hk : k + 1 < n + 1) :
    (Fin.cons y x : ColSeq (n + 1)) ⟨k + 1, hk⟩ = x ⟨k, by omega⟩ :=
  Fin.cons_succ (α := fun _ => Col × St) y x ⟨k, by omega⟩

theorem prevH_cons_zero {n : ℕ} (s : St) (y : Col × St) (x : ColSeq n) :
    prevH s (Fin.cons y x : ColSeq (n + 1)) 0 = s := by
  simp [prevH]

theorem prevH_cons_succ {n : ℕ} (s : St) (y : Col × St) (x : ColSeq n) (c : Fin n) :
    prevH s (Fin.cons y x : ColSeq (n + 1)) c.succ = prevH y.2 x c := by
  unfold prevH
  rw [if_neg (by simp)]
  rcases c with ⟨k, hk⟩
  rcases k with _ | k
  · simp
  · simp only [Fin.succ_mk, Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false]
    exact congrArg Prod.snd (cons_mk y x k _)

theorem lastH_cons {n : ℕ} (s : St) (y : Col × St) (x : ColSeq n) :
    lastH s (Fin.cons y x : ColSeq (n + 1)) = lastH y.2 x := by
  unfold lastH
  rw [dif_neg (by omega)]
  rcases n with _ | n
  · simp
  · rw [dif_neg (by omega)]
    exact congrArg Prod.snd (cons_mk y x n _)

theorem good_cons {n : ℕ} (s e : St) (y : Col × St) (x : ColSeq n) :
    Good s e (Fin.cons y x : ColSeq (n + 1)) ↔ ok s y.1 y.2 ∧ Good y.2 e x := by
  unfold Good
  rw [Fin.forall_fin_succ]
  simp only [prevH_cons_zero, prevH_cons_succ, Fin.cons_zero, Fin.cons_succ, lastH_cons]
  tauto

theorem sum_cons (n : ℕ) (F : ColSeq (n + 1) → ℕ) :
    ∑ f, F f = ∑ y : Col × St, ∑ g : ColSeq n, F (Fin.cons y g) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv fun _ => Col × St).symm _ _ (fun f => by simp)

theorem T_apply (L R : St) : T L R = #{V : Col | ok L V R} := rfl

/-- Counting column data by the transfer matrix. -/
theorem card_good : ∀ (n : ℕ) (s e : St), #{x : ColSeq n | Good s e x} = (T ^ n) s e
  | 0, s, e => by
    rw [pow_zero, Matrix.one_apply]
    have h : ∀ x : ColSeq 0, Good s e x ↔ s = e := fun x => by simp [Good, lastH]
    simp only [h]
    by_cases hse : s = e <;> simp [hse]
  | n + 1, s, e => by
    rw [pow_succ', Matrix.mul_apply, Finset.card_filter, sum_cons]
    simp only [good_cons, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun R _ => ?_
    have h1 : ∀ V : Col, (∑ x : ColSeq n, if ok s V R ∧ Good R e x then 1 else 0) =
        if ok s V R then (T ^ n) R e else 0 := by
      intro V
      by_cases hV : ok s V R
      · simp only [hV, true_and, if_true]
        rw [← card_good n R e, Finset.card_filter]
      · simp [hV]
    simp only [h1]
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, T_apply]


/-! ### Graph side -/

section Graph

variable {n : ℕ}

/-- The vertical edge between rows `i` and `i + 1` of column `c`. -/
def vE (i : Fin 4) (c : Fin n) : Sym2 (Fin 5 × Fin n) := s((i.castSucc, c), (i.succ, c))

/-- The horizontal edge between columns `c` and `c + 1` in row `r`. -/
def hE (r : Fin 5) (c : Fin n) (h : c.val + 1 < n) : Sym2 (Fin 5 × Fin n) :=
  s((r, c), (r, ⟨c.val + 1, h⟩))

theorem mem_edges (u w : Fin 5 × Fin n) : s(u, w) ∈ (grid n).edgeFinset ↔
    ((u.1.val + 1 = w.1.val ∨ w.1.val + 1 = u.1.val) ∧ u.2.val = w.2.val) ∨
    ((u.2.val + 1 = w.2.val ∨ w.2.val + 1 = u.2.val) ∧ u.1.val = w.1.val) := by
  rw [mem_edgeFinset, mem_edgeSet, boxProd_adj, pathGraph_adj, pathGraph_adj, Fin.ext_iff,
    Fin.ext_iff]

theorem vE_mem (i : Fin 4) (c : Fin n) : vE i c ∈ (grid n).edgeFinset := by
  rw [vE, mem_edges]; simp

theorem hE_mem (r : Fin 5) (c : Fin n) (h : c.val + 1 < n) : hE r c h ∈ (grid n).edgeFinset := by
  rw [hE, mem_edges]; simp

theorem vE_inj {i i' : Fin 4} {c c' : Fin n} : vE i c = vE i' c' ↔ i = i' ∧ c = c' := by
  simp only [vE, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  omega

theorem hE_inj {r r' : Fin 5} {c c' : Fin n} {h : c.val + 1 < n} {h' : c'.val + 1 < n} :
    hE r c h = hE r' c' h' ↔ r = r' ∧ c = c' := by
  simp only [hE, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff]
  omega

theorem vE_ne_hE (i : Fin 4) (c : Fin n) (r : Fin 5) (c' : Fin n) (h : c'.val + 1 < n) :
    vE i c ≠ hE r c' h := by
  simp only [vE, hE, ne_eq, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff, Fin.val_castSucc,
    Fin.val_succ]
  omega

theorem edge_cases {e : Sym2 (Fin 5 × Fin n)} (he : e ∈ (grid n).edgeFinset) :
    (∃ i c, e = vE i c) ∨ ∃ r c h, e = hE r c h := by
  induction e using Sym2.ind with
  | _ u w =>
    rw [mem_edges] at he
    rcases u with ⟨⟨r, hr⟩, ⟨c, hc⟩⟩
    rcases w with ⟨⟨r', hr'⟩, ⟨c', hc'⟩⟩
    simp only at he
    rcases he with ⟨h1 | h1, h2⟩ | ⟨h1 | h1, h2⟩
    · left
      refine ⟨⟨r, by omega⟩, ⟨c, hc⟩, ?_⟩
      simp only [vE, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ,
        true_and, and_true]
      omega
    · left
      refine ⟨⟨r', by omega⟩, ⟨c, hc⟩, ?_⟩
      simp only [vE, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ,
        true_and, and_true]
      omega
    · right
      refine ⟨⟨r, hr⟩, ⟨c, hc⟩, by simp only; omega, ?_⟩
      simp only [hE, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff, true_and]
      omega
    · right
      refine ⟨⟨r, hr⟩, ⟨c', hc'⟩, by simp only; omega, ?_⟩
      simp only [hE, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff, true_and, and_true]
      omega

theorem deg_eq_nbrs (S : Finset (Sym2 (Fin 5 × Fin n))) (v : Fin 5 × Fin n) :
    deg S v = #{w | s(v, w) ∈ S} := by
  unfold deg
  symm
  apply Finset.card_nbij (fun w => s(v, w))
  · intro w hw
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw
    simp only [coe_filter, Set.mem_ofPred_eq]
    exact ⟨hw, Sym2.mem_mk_left _ _⟩
  · intro w _ w' _ h
    exact Sym2.congr_right.mp h
  · intro e he
    simp only [coe_filter, Set.mem_ofPred_eq] at he
    obtain ⟨hS, hv⟩ := he
    refine ⟨Sym2.Mem.other hv, ?_, Sym2.other_spec hv⟩
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    rw [Sym2.other_spec hv]
    exact hS

theorem card_filter_single {α : Type*} [Fintype α] [DecidableEq α] (Q : α → Prop)
    [DecidablePred Q] (w0 : α) (R : Prop) [Decidable R] (h : ∀ w, Q w ↔ w = w0 ∧ R) :
    #{w | Q w} = if R then 1 else 0 := by
  by_cases hR : R
  · rw [if_pos hR, Finset.card_eq_one]
    refine ⟨w0, ?_⟩
    ext w
    simp [h, hR]
  · rw [if_neg hR, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w _ hw
    exact hR ((h w).1 hw).2

/-- Purely finite fact about one column. -/
theorem col_count : ∀ (Q : Fin 4 → Bool) (r : Fin 5),
    #{r' : Fin 5 | ∃ i : Fin 4, Q i = true ∧
      ((i.castSucc = r ∧ i.succ = r') ∨ (i.succ = r ∧ i.castSucc = r'))} =
    #{i : Fin 4 | Q i = true ∧ (i.castSucc = r ∨ i.succ = r)} := by
  decide

open Classical in
/-- The column data of an edge set. -/
noncomputable def dec (S : Finset (Sym2 (Fin 5 × Fin n))) : ColSeq n := fun c =>
  (fun i => decide (vE i c ∈ S), fun r => decide (∃ h, hE r c h ∈ S))

/-- The degree of a vertex, read off from the column data. -/
theorem deg_dec {S : Finset (Sym2 (Fin 5 × Fin n))} (hS : S ⊆ (grid n).edgeFinset)
    (r : Fin 5) (c : Fin n) :
    deg S (r, c) = colDeg (prevH noH (dec S) c) (dec S c).1 (dec S c).2 r := by
  classical
  have adj : ∀ w : Fin 5 × Fin n, s((r, c), w) ∈ S →
      ((r.val + 1 = w.1.val ∨ w.1.val + 1 = r.val) ∧ c.val = w.2.val) ∨
      ((c.val + 1 = w.2.val ∨ w.2.val + 1 = c.val) ∧ r.val = w.1.val) :=
    fun w hw => (mem_edges _ _).1 (hS hw)
  rw [deg_eq_nbrs]
  -- split the neighbours by column
  have hsplit : #{w | s((r, c), w) ∈ S} =
      #{w | s((r, c), w) ∈ S ∧ w.2.val = c.val} +
      #{w | s((r, c), w) ∈ S ∧ w.2.val + 1 = c.val} +
      #{w | s((r, c), w) ∈ S ∧ c.val + 1 = w.2.val} := by
    simp only [Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : s((r, c), w) ∈ S
    · have := adj w hw
      simp only [hw, true_and, if_true]
      split_ifs <;> omega
    · simp [hw]
  -- same column
  have h1 : #{w | s((r, c), w) ∈ S ∧ w.2.val = c.val} =
      #{i : Fin 4 | (dec S c).1 i = true ∧ (i.castSucc = r ∨ i.succ = r)} := by
    rw [← col_count]
    apply Finset.card_nbij' Prod.fst (fun r' => (r', c))
    · intro w hw
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢
      obtain ⟨hw, hc⟩ := hw
      have hwc : w = (w.1, c) := Prod.ext rfl (Fin.ext hc)
      rw [hwc] at hw
      have := adj _ hw
      simp only at this
      rcases this with ⟨h | h, -⟩ | ⟨h, -⟩
      · refine ⟨⟨r.val, by omega⟩, ?_, Or.inl ⟨Fin.ext rfl, Fin.ext (by simp; omega)⟩⟩
        simp only [dec, decide_eq_true_eq]
        convert hw using 1
        simp only [vE, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ,
          true_and, and_true]
        omega
      · refine ⟨⟨w.1.val, by omega⟩, ?_, Or.inr ⟨Fin.ext (by simp; omega), Fin.ext rfl⟩⟩
        simp only [dec, decide_eq_true_eq]
        convert hw using 1
        simp only [vE, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ,
          true_and, and_true]
        omega
      · omega
    · intro r' hr'
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, and_true] at hr' ⊢
      obtain ⟨i, hi, hor⟩ := hr'
      simp only [dec, decide_eq_true_eq] at hi
      convert hi using 1
      simp only [vE, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ,
        and_true] at hor ⊢
      omega
    · intro w hw
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw
      exact Prod.ext rfl (Fin.ext hw.2.symm)
    · intro r' _
      rfl
  -- left neighbour
  have h2 : #{w | s((r, c), w) ∈ S ∧ w.2.val + 1 = c.val} =
      if prevH noH (dec S) c r then 1 else 0 := by
    by_cases hc0 : c.val = 0
    · have : prevH noH (dec S) c = noH := by simp [prevH, hc0]
      rw [this, noH, if_neg (by simp), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w _ hw
      omega
    · obtain ⟨k, hk⟩ : ∃ k, c.val = k + 1 := ⟨c.val - 1, by omega⟩
      have hkn : k < n := by omega
      have hp : prevH noH (dec S) c r = decide (∃ h, hE r ⟨k, hkn⟩ h ∈ S) := by
        simp only [prevH, dec, hk, Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false]
      rw [hp]
      simp only [decide_eq_true_eq]
      apply card_filter_single _ (r, ⟨k, hkn⟩)
      intro w
      have key : ∀ h, hE r ⟨k, hkn⟩ h = s((r, c), (r, ⟨k, hkn⟩)) := by
        intro h
        simp only [hE, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff, true_and]
        omega
      constructor
      · rintro ⟨hw, hwc⟩
        have := adj w hw
        have hw0 : w = (r, ⟨k, hkn⟩) := by
          ext <;> simp <;> omega
        subst hw0
        exact ⟨rfl, by have := c.isLt; omega, by rw [key]; exact hw⟩
      · rintro ⟨rfl, h, hm⟩
        rw [key] at hm
        exact ⟨hm, by show k + 1 = c.val; omega⟩
  -- right neighbour
  have h3 : #{w | s((r, c), w) ∈ S ∧ c.val + 1 = w.2.val} =
      if (dec S c).2 r then 1 else 0 := by
    simp only [dec, decide_eq_true_eq]
    by_cases hcn : c.val + 1 < n
    · have hiff : (∃ h, hE r c h ∈ S) ↔ s((r, c), (r, ⟨c.val + 1, hcn⟩)) ∈ S :=
        ⟨fun ⟨_, h⟩ => h, fun h => ⟨hcn, h⟩⟩
      rw [if_congr hiff rfl rfl]
      apply card_filter_single _ (r, ⟨c.val + 1, hcn⟩)
      intro w
      constructor
      · rintro ⟨hw, hwc⟩
        have := adj w hw
        have hw0 : w = (r, ⟨c.val + 1, hcn⟩) := by
          ext <;> simp <;> omega
        subst hw0
        exact ⟨rfl, hw⟩
      · rintro ⟨rfl, hm⟩
        exact ⟨hm, rfl⟩
    · rw [if_neg (fun ⟨h, _⟩ => hcn h), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w _ hw
      have := w.2.isLt
      omega
  rw [hsplit, h1, h2, h3, colDeg]
  omega


open Classical in
/-- The edge set with the given column data. -/
noncomputable def enc (x : ColSeq n) : Finset (Sym2 (Fin 5 × Fin n)) :=
  (grid n).edgeFinset.filter fun e =>
    (∃ i c, e = vE i c ∧ (x c).1 i = true) ∨ ∃ r c h, e = hE r c h ∧ (x c).2 r = true

theorem enc_subset (x : ColSeq n) : enc x ⊆ (grid n).edgeFinset := by
  classical
  unfold enc
  exact Finset.filter_subset _ _

theorem enc_dec {S : Finset (Sym2 (Fin 5 × Fin n))} (hS : S ⊆ (grid n).edgeFinset) :
    enc (dec S) = S := by
  classical
  ext e
  unfold enc
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, ⟨i, c, rfl, hi⟩ | ⟨r, c, h, rfl, hr⟩⟩
    · simpa [dec] using hi
    · simp only [dec, decide_eq_true_eq] at hr
      obtain ⟨_, hm⟩ := hr
      exact hm
  · intro he
    refine ⟨hS he, ?_⟩
    rcases edge_cases (hS he) with ⟨i, c, rfl⟩ | ⟨r, c, h, rfl⟩
    · exact Or.inl ⟨i, c, rfl, by simpa [dec] using he⟩
    · exact Or.inr ⟨r, c, h, rfl, by simp only [dec, decide_eq_true_eq]; exact ⟨h, he⟩⟩

theorem dec_enc {x : ColSeq n} (hx : lastH noH x = noH) : dec (enc x) = x := by
  classical
  funext c
  refine Prod.ext (funext fun i => ?_) (funext fun r => ?_)
  · have : vE i c ∈ enc x ↔ (x c).1 i = true := by
      unfold enc
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨-, ⟨i', c', h, hi⟩ | ⟨r', c', h', h, -⟩⟩
        · obtain ⟨rfl, rfl⟩ := vE_inj.1 h
          exact hi
        · exact absurd h (vE_ne_hE _ _ _ _ _)
      · intro hi
        exact ⟨vE_mem i c, Or.inl ⟨i, c, rfl, hi⟩⟩
    simp only [dec]
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact this
  · have : (∃ h, hE r c h ∈ enc x) ↔ (x c).2 r = true := by
      by_cases hcn : c.val + 1 < n
      · unfold enc
        constructor
        · rintro ⟨h, hm⟩
          rw [Finset.mem_filter] at hm
          rcases hm with ⟨-, ⟨i', c', h', -⟩ | ⟨r', c', h'', h', hr⟩⟩
          · exact absurd h'.symm (vE_ne_hE _ _ _ _ _)
          · obtain ⟨rfl, rfl⟩ := hE_inj.1 h'
            exact hr
        · intro hr
          exact ⟨hcn, Finset.mem_filter.2 ⟨hE_mem r c hcn, Or.inr ⟨r, c, hcn, rfl, hr⟩⟩⟩
      · have hlast : (x c).2 = noH := by
          rw [← hx]
          unfold lastH
          rw [dif_neg (by have := c.isLt; omega)]
          congr 2
          ext
          simp only
          have := c.isLt
          omega
        rw [hlast]
        simp only [noH, Bool.false_eq_true, iff_false]
        rintro ⟨h, -⟩
        exact hcn h
    simp only [dec]
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact this

theorem lastH_dec (S : Finset (Sym2 (Fin 5 × Fin n))) : lastH noH (dec S) = noH := by
  classical
  unfold lastH
  split_ifs with hn
  · rfl
  · funext r
    simp only [dec, noH, decide_eq_false_iff_not]
    rintro ⟨h, -⟩
    omega

/-- `a n` counts the sequences of column data that are `Good` from `noH` to `noH`. -/
theorem a_eq_card_good (n : ℕ) : a n = #{x : ColSeq n | Good noH noH x} := by
  classical
  unfold a
  apply Finset.card_nbij' dec enc
  · intro S hS
    simp only [coe_filter, mem_powerset, Set.mem_ofPred_eq, mem_univ, true_and] at hS ⊢
    refine ⟨fun c r => ?_, lastH_dec S⟩
    rw [← deg_dec hS.1]
    exact hS.2 (r, c)
  · intro x hx
    simp only [coe_filter, mem_powerset, Set.mem_ofPred_eq, mem_univ, true_and] at hx ⊢
    refine ⟨enc_subset x, fun v => ?_⟩
    rw [deg_dec (enc_subset x), dec_enc hx.2]
    exact hx.1 v.2 v.1
  · intro S hS
    simp only [coe_filter, mem_powerset, Set.mem_ofPred_eq] at hS
    exact enc_dec hS.1
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hx
    exact dec_enc hx.2

/-- The transfer-matrix formula for `a`, valid for every `n`. -/
theorem a_eq_T (n : ℕ) : a n = (T ^ n) noH noH := by
  rw [a_eq_card_good, card_good]
end Graph

/-! ### Fast evaluation -/

/-- All `32` sets of horizontal edges between two columns, starting with `noH`. -/
def states : List St := (List.finRange 32).map (fun k r => k.val.testBit r.val)

theorem states_nodup : states.Nodup := by decide +kernel

theorem mem_states : ∀ L : St, L ∈ states := by decide +kernel

theorem states_eq_cons : states = noH :: states.tail := by decide +kernel

theorem sum_states (f : St → ℕ) : ∑ L, f L = (states.map f).sum := by
  rw [← List.sum_toFinset f states_nodup]
  congr 1
  ext L
  simp [mem_states]

/-- The columns of `T` (indexed as in `states`), as a literal table. -/
def Mcols : List (List ℕ) :=
  [[1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 2,
      0, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3],
    [0, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3,
      1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 5],
    [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2,
      1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 3, 3],
    [1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3, 2, 4,
      1, 2, 1, 2, 2, 3, 2, 4, 2, 3, 2, 4, 3, 5, 3, 6],
    [0, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2,
      1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 4],
    [1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 2, 3,
      1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 5, 2, 4, 4, 6],
    [1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2,
      1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 3, 3, 2, 4, 4, 4],
    [1, 2, 1, 2, 2, 3, 2, 4, 2, 3, 2, 4, 2, 3, 2, 4,
      2, 3, 2, 4, 2, 3, 2, 4, 3, 5, 3, 6, 4, 6, 4, 8],
    [0, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3,
      1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 2, 3],
    [1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 5,
      1, 2, 2, 3, 2, 3, 3, 5, 1, 2, 2, 3, 2, 3, 3, 5],
    [1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 3, 3,
      1, 2, 2, 2, 2, 3, 3, 3, 1, 2, 2, 2, 2, 3, 3, 3],
    [1, 2, 1, 2, 2, 3, 2, 4, 2, 3, 2, 4, 3, 5, 3, 6,
      2, 3, 2, 4, 3, 5, 3, 6, 2, 3, 2, 4, 3, 5, 3, 6],
    [1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 4,
      1, 2, 2, 3, 2, 2, 2, 4, 1, 2, 2, 3, 2, 2, 2, 4],
    [1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 5, 2, 4, 4, 6,
      2, 3, 3, 5, 2, 4, 4, 6, 2, 3, 3, 5, 2, 4, 4, 6],
    [1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 3, 3, 2, 4, 4, 4,
      2, 3, 3, 3, 2, 4, 4, 4, 2, 3, 3, 3, 2, 4, 4, 4],
    [2, 3, 2, 4, 2, 3, 2, 4, 3, 5, 3, 6, 4, 6, 4, 8,
      3, 5, 3, 6, 4, 6, 4, 8, 3, 5, 3, 6, 4, 6, 4, 8],
    [0, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3,
      1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 5],
    [1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 5,
      1, 2, 2, 3, 2, 3, 3, 5, 2, 3, 3, 5, 3, 5, 5, 8],
    [1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 3, 3,
      1, 2, 2, 2, 2, 3, 3, 3, 2, 3, 3, 3, 3, 5, 5, 5],
    [1, 2, 1, 2, 2, 3, 2, 4, 2, 3, 2, 4, 3, 5, 3, 6,
      2, 3, 2, 4, 3, 5, 3, 6, 3, 5, 3, 6, 5, 8, 5, 10],
    [1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 4,
      1, 2, 2, 3, 2, 2, 2, 4, 2, 3, 3, 5, 3, 3, 3, 6],
    [1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 5, 2, 4, 4, 6,
      2, 3, 3, 5, 2, 4, 4, 6, 3, 5, 5, 8, 3, 6, 6, 9],
    [1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 3, 3, 2, 4, 4, 4,
      2, 3, 3, 3, 2, 4, 4, 4, 3, 5, 5, 5, 3, 6, 6, 6],
    [2, 3, 2, 4, 2, 3, 2, 4, 3, 5, 3, 6, 4, 6, 4, 8,
      3, 5, 3, 6, 4, 6, 4, 8, 5, 8, 5, 10, 6, 9, 6, 12],
    [1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 2, 3,
      1, 2, 2, 3, 2, 3, 3, 5, 2, 2, 2, 4, 2, 4, 4, 6],
    [1, 2, 2, 3, 2, 3, 3, 5, 1, 2, 2, 3, 2, 3, 3, 5,
      2, 3, 3, 5, 3, 5, 5, 8, 2, 4, 4, 6, 4, 6, 6, 10],
    [1, 2, 2, 2, 2, 3, 3, 3, 1, 2, 2, 2, 2, 3, 3, 3,
      2, 3, 3, 3, 3, 5, 5, 5, 2, 4, 4, 4, 4, 6, 6, 6],
    [2, 3, 2, 4, 3, 5, 3, 6, 2, 3, 2, 4, 3, 5, 3, 6,
      3, 5, 3, 6, 5, 8, 5, 10, 4, 6, 4, 8, 6, 10, 6, 12],
    [1, 2, 2, 3, 2, 2, 2, 4, 1, 2, 2, 3, 2, 2, 2, 4,
      2, 3, 3, 5, 3, 3, 3, 6, 2, 4, 4, 6, 4, 4, 4, 8],
    [2, 3, 3, 5, 2, 4, 4, 6, 2, 3, 3, 5, 2, 4, 4, 6,
      3, 5, 5, 8, 3, 6, 6, 9, 4, 6, 6, 10, 4, 8, 8, 12],
    [2, 3, 3, 3, 2, 4, 4, 4, 2, 3, 3, 3, 2, 4, 4, 4,
      3, 5, 5, 5, 3, 6, 6, 6, 4, 6, 6, 6, 4, 8, 8, 8],
    [3, 5, 3, 6, 4, 6, 4, 8, 3, 5, 3, 6, 4, 6, 4, 8,
      5, 8, 5, 10, 6, 9, 6, 12, 6, 10, 6, 12, 8, 12, 8, 16]]

theorem Mcols_eq : Mcols = states.map (fun R => states.map (fun L => T L R)) := by
  decide +kernel

/-- Dot product of two lists. -/
def dot (u w : List ℕ) : ℕ := (List.zipWith (· * ·) u w).sum

/-- One transfer-matrix step on a row vector. -/
def step (v : List ℕ) : List ℕ := Mcols.map (dot v)

/-- The row of the identity matrix at `noH`. -/
def row0 : List ℕ := 1 :: List.replicate 31 0

theorem row0_eq : row0 = states.map (fun R => if noH = R then 1 else 0) := by decide +kernel

/-- `fastRow n` is the row of `T ^ n` at `noH`. -/
def fastRow : ℕ → List ℕ
  | 0 => row0
  | n + 1 => step (fastRow n)

/-- Fast evaluator of `a`. -/
def fastA (n : ℕ) : ℕ := (fastRow n).headD 0

theorem fastRow_eq (n : ℕ) : fastRow n = states.map (fun R => (T ^ n) noH R) := by
  induction n with
  | zero =>
    rw [fastRow, row0_eq]
    simp [Matrix.one_apply]
  | succ n ih =>
    rw [fastRow, ih, step, Mcols_eq, List.map_map]
    refine List.map_congr_left fun R _ => ?_
    simp only [Function.comp, dot, List.zipWith_map, List.zipWith_self]
    rw [pow_succ, Matrix.mul_apply, sum_states]

/-- The fast evaluator computes `a`, for every `n`. -/
theorem a_eq_fastA (n : ℕ) : a n = fastA n := by
  rw [a_eq_T, fastA, fastRow_eq, states_eq_cons, List.map_cons, List.headD_cons]

/-- The definition reproduces the first terms listed in OEIS (kernel-checked): all `15` listed
terms `a(1), …, a(15)`. -/
theorem a_data : (List.range 15).map (fun i => a (i + 1)) =
    [1, 50, 5193, 583199, 65485654, 7354266811, 825905301851, 92751581627976,
      10416273692997679, 1169777980482365913, 131369486228240893660,
      14753177269494392259423, 1656824927874469183283433, 186066281959642930757881316,
      20895787297635543757965741097] := by
  simp only [a_eq_fastA]
  decide +kernel


/-- Kagey's conjecture: for every `n > 10`,
`a(n) = 103*a(n-1) + 1063*a(n-2) - 1873*a(n-3) - 20274*a(n-4) + 44071*a(n-5) - 10365*a(n-6)
- 20208*a(n-7) + 5959*a(n-8) + 2300*a(n-9) - 500*a(n-10)` (an identity of integers). -/
def statement : Prop :=
  ∀ n : ℕ, 10 < n →
    (a n : ℤ) = 103 * (a (n - 1) : ℤ) + 1063 * (a (n - 2) : ℤ) - 1873 * (a (n - 3) : ℤ)
      - 20274 * (a (n - 4) : ℤ) + 44071 * (a (n - 5) : ℤ) - 10365 * (a (n - 6) : ℤ)
      - 20208 * (a (n - 7) : ℤ) + 5959 * (a (n - 8) : ℤ) + 2300 * (a (n - 9) : ℤ)
      - 500 * (a (n - 10) : ℤ)

/-- Sanity check of the transcription (not a proof of `statement`): the identity holds for
`n = 11, …, 15`, the values of `n > 10` within the listed data. -/
theorem statement_check_listed : ∀ n : ℕ, 10 < n → n ≤ 15 →
    (a n : ℤ) = 103 * (a (n - 1) : ℤ) + 1063 * (a (n - 2) : ℤ) - 1873 * (a (n - 3) : ℤ)
      - 20274 * (a (n - 4) : ℤ) + 44071 * (a (n - 5) : ℤ) - 10365 * (a (n - 6) : ℤ)
      - 20208 * (a (n - 7) : ℤ) + 5959 * (a (n - 8) : ℤ) + 2300 * (a (n - 9) : ℤ)
      - 500 * (a (n - 10) : ℤ) := by
  intro n h1 h2
  simp only [a_eq_fastA]
  interval_cases n <;> decide +kernel

end Math0.Statements.A320099
