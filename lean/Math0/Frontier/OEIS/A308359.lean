/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A308359
import Math0.Audit

/-!
# Fixed polyominoes with `n` cells and width `n - 2` (A308359)

We prove R. J. Mathar's conjecture `T(n, n - 2) = 8n² - 51n + 86` for all `n ≥ 5`.

Write `w = n - 2 ≥ 3`. A fixed polyomino `S` with `w + 2` cells and width `w` has every column
`0, …, w - 1` nonempty, so the column sizes exceed `1` by `2` in total, and it has at most `3`
rows (`cols_add_rows_le`), i.e. it lies in `[0, w) × [0, 3)`.

* *Structure.* Consecutive columns share a row (otherwise no edge crosses between them), and no
  column is `{0, 2}`: a chain joining its two cells passes a vertical edge between rows `0, 1` and
  one between rows `1, 2`, in columns other than the gapped one, which forces at least `w + 3`
  cells. So every column is a vertical interval. Conversely such "good" configurations (column
  intervals, consecutive overlap) are connected. Hence the polyominoes are exactly the good
  configurations with `w + 2` cells meeting row `0`.
* *Transfer matrix.* Classify good configurations of width `w` by the state `(e, a, b, z)`:
  excess `e = |S| - w ≤ 2`, last column `a, …, b`, and whether row `0` is used. Removing the last
  column is a bijection onto the configurations of width `w - 1` in compatible states, so the
  counts satisfy a linear recursion `D` over 36 states.
* *Closed form.* For `w ≥ 3` each `D w s` is a quadratic `A w² + B w + C`; this is checked at
  `w = 3` and propagated by three coefficient identities of the transfer matrix (all verified by
  `decide`). Summing over the final states (`e = 2`, row `0` used) gives `8w² - 19w + 16`, which is
  `8n² - 51n + 86`.
-/

namespace Math0.Frontier.A308359
open Math0.Statements.A308359

/-- Column `x` of `S` consists exactly of the rows `a, …, b`. -/
private def ColIs (S : Finset (ℕ × ℕ)) (x a b : ℕ) : Prop := ∀ y, (x, y) ∈ S ↔ a ≤ y ∧ y ≤ b

/-- `S` is a good configuration of width `w`: its cells lie in the columns `0, …, w - 1`, each of
these columns is a nonempty vertical interval of rows inside `0, 1, 2`, and any two consecutive
columns share a row. -/
private def Good (w : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  (∀ p ∈ S, p.1 < w) ∧ (∀ x < w, ∃ a b, a ≤ b ∧ b ≤ 2 ∧ ColIs S x a b) ∧
    (∀ x, x + 1 < w → ∃ y, (x, y) ∈ S ∧ (x + 1, y) ∈ S)

/-- Reachability inside `S` along edge-adjacent cells. -/
private abbrev Reach (S : Finset (ℕ × ℕ)) := Relation.ReflTransGen (Step S)

/-- A nonempty column interval determines its endpoints. -/
private lemma colIs_unique {S : Finset (ℕ × ℕ)} {x a b a' b' : ℕ} (h : ColIs S x a b)
    (h' : ColIs S x a' b') (hab : a ≤ b) (hab' : a' ≤ b') : a = a' ∧ b = b' := by
  have h1 := (h' a).1 ((h a).2 ⟨le_rfl, hab⟩)
  have h2 := (h a').1 ((h' a').2 ⟨le_rfl, hab'⟩)
  have h3 := (h' b).1 ((h b).2 ⟨hab, le_rfl⟩)
  have h4 := (h b').1 ((h' b').2 ⟨hab', le_rfl⟩)
  omega

/-- The cells of a good configuration lie in the box `[0, w) × [0, 3)`. -/
private lemma good_row {w : ℕ} {S : Finset (ℕ × ℕ)} (hS : Good w S) {p : ℕ × ℕ} (hp : p ∈ S) :
    p.1 < w ∧ p.2 ≤ 2 := by
  have h1 := hS.1 p hp
  obtain ⟨a, b, -, hb, hc⟩ := hS.2.1 p.1 h1
  have := (hc p.2).1 hp
  exact ⟨h1, by omega⟩

/-- A good configuration of width `w` has at least `w` cells (every column is nonempty). -/
private lemma good_le_card {w : ℕ} {S : Finset (ℕ × ℕ)} (hS : Good w S) : w ≤ S.card := by
  have hsub : Finset.range w ⊆ S.image Prod.fst := by
    intro x hx
    rw [Finset.mem_range] at hx
    obtain ⟨a, b, hab, -, hc⟩ := hS.2.1 x hx
    exact Finset.mem_image.2 ⟨(x, a), (hc a).2 ⟨le_rfl, hab⟩, rfl⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  exact this.trans Finset.card_image_le

/-- Inside a column interval `a, …, b`, the cell in row `a + k` is reachable from row `a`. -/
private lemma vert {S : Finset (ℕ × ℕ)} {x a b : ℕ} (h : ColIs S x a b) :
    ∀ k, a + k ≤ b → Reach S (x, a) (x, a + k)
  | 0, _ => Relation.ReflTransGen.refl
  | k + 1, hk => by
    refine (vert h k (by omega)).tail ⟨(h _).2 ⟨by omega, by omega⟩, (h _).2 ⟨by omega, hk⟩, ?_⟩
    unfold Adj
    omega

/-- Any two cells of a column that is an interval are joined inside that column. -/
private lemma vert' {S : Finset (ℕ × ℕ)} {x a b y y' : ℕ} (h : ColIs S x a b) (hy : (x, y) ∈ S)
    (hy' : (x, y') ∈ S) : Reach S (x, y) (x, y') := by
  have h1 := (h y).1 hy
  have h2 := (h y').1 hy'
  have e1 := vert h (y - a) (by omega)
  have e2 := vert h (y' - a) (by omega)
  rw [show a + (y - a) = y by omega] at e1
  rw [show a + (y' - a) = y' by omega] at e2
  exact (reach_symm e1).trans e2

/-- A good configuration is edge-connected: walk up and down inside the column intervals and
step right through a shared row. -/
private lemma good_conn {w : ℕ} {S : Finset (ℕ × ℕ)} (hS : Good w S) : IsConnected S := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · intro p hp
    exact absurd (hS.1 p hp) (Nat.not_lt_zero _)
  obtain ⟨a0, b0, hab0, -, hc0⟩ := hS.2.1 0 hw
  have h0 : (0, a0) ∈ S := (hc0 a0).2 ⟨le_rfl, hab0⟩
  have key : ∀ x, x < w → ∀ y, (x, y) ∈ S → Reach S (0, a0) (x, y) := by
    intro x
    induction x with
    | zero => intro _ y hy; exact vert' hc0 h0 hy
    | succ x ih =>
      intro hx y hy
      obtain ⟨r, hr, hr'⟩ := hS.2.2 x hx
      obtain ⟨a1, b1, -, -, hc1⟩ := hS.2.1 (x + 1) hx
      refine ((ih (by omega) r hr).tail ⟨hr, hr', ?_⟩).trans (vert' hc1 hr' hy)
      unfold Adj
      omega
  intro p hp q hq
  exact (reach_symm (key p.1 (hS.1 p hp) p.2 hp)).trans (key q.1 (hS.1 q hq) q.2 hq)

/-- A chain from row `≤ k` to row `> k` uses a vertical edge between rows `k` and `k + 1`. -/
private lemma cross {S : Finset (ℕ × ℕ)} {p q : ℕ × ℕ} (h : Reach S p q) :
    ∀ k, p.2 ≤ k → k < q.2 → ∃ c, (c, k) ∈ S ∧ (c, k + 1) ∈ S := by
  induction h with
  | refl => intro k h1 h2; omega
  | @tail b c _ hbc ih =>
    intro k h1 h2
    by_cases hk : k < b.2
    · exact ih k h1 hk
    · obtain ⟨hb, hc, hadj⟩ := hbc
      unfold Adj at hadj
      have e1 : b.1 = c.1 := by omega
      have e2 : b.2 = k := by omega
      have e3 : c.2 = k + 1 := by omega
      refine ⟨b.1, ?_, ?_⟩
      · rw [← e2]; exact hb
      · rw [← e3, e1]; exact hc

/-- In a connected set with `w + 2` cells, `w` nonempty columns, no column is `{0, 2}`: joining its
two cells needs a column containing rows `0, 1` and one containing rows `1, 2`, both different from
it, and then the columns carry at least `w + 3` cells. -/
private lemma no_gap {w : ℕ} {S : Finset (ℕ × ℕ)} (hcard : S.card = w + 2)
    (hS : ∀ p ∈ S, p.1 < w) (hcol : ∀ x < w, ∃ y, (x, y) ∈ S) (hconn : IsConnected S)
    {x : ℕ} (h0 : (x, 0) ∈ S) (h1 : (x, 1) ∉ S) (h2 : (x, 2) ∈ S) : False := by
  obtain ⟨c1, hc10, hc11⟩ := cross (hconn _ h0 _ h2) 0 (by simp) (by simp)
  obtain ⟨c2, hc21, hc22⟩ := cross (hconn _ h0 _ h2) 1 (by simp) (by simp)
  have hc1x : c1 ≠ x := by rintro rfl; exact h1 hc11
  have hc2x : c2 ≠ x := by rintro rfl; exact h1 hc21
  set g : ℕ → ℕ := fun x' => (S.filter (fun p => p.1 = x')).card with hg
  have hsum : S.card = ∑ x' ∈ Finset.range w, g x' :=
    Finset.card_eq_sum_card_fiberwise (fun p hp => Finset.mem_range.2 (hS p hp))
  have hlow : ∀ x' (T : Finset (ℕ × ℕ)), T ⊆ S → (∀ p ∈ T, p.1 = x') → T.card ≤ g x' := by
    intro x' T hT hT'
    exact Finset.card_le_card fun p hp => Finset.mem_filter.2 ⟨hT hp, hT' p hp⟩
  have hg1 : ∀ x' ∈ Finset.range w, 1 ≤ g x' := by
    intro x' hx'
    obtain ⟨y, hy⟩ := hcol x' (Finset.mem_range.1 hx')
    simpa using hlow x' {(x', y)} (by simpa using hy) (by simp)
  have hgx : 2 ≤ g x := by
    have := hlow x {(x, 0), (x, 2)} (by simp [Finset.insert_subset_iff, h0, h2]) (by simp)
    simpa using this
  have hxw : x < w := hS _ h0
  have hc1w : c1 < w := hS _ hc10
  have hc2w : c2 < w := hS _ hc21
  have hsplit : ∑ x' ∈ Finset.range w, g x' =
      ∑ x' ∈ Finset.range w, 1 + ∑ x' ∈ Finset.range w, (g x' - 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x' hx' => by have := hg1 x' hx'; omega
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hsplit
  by_cases hc12 : c1 = c2
  · subst hc12
    have hgc : 3 ≤ g c1 := by
      have := hlow c1 {(c1, 0), (c1, 1), (c1, 2)}
        (by simp [Finset.insert_subset_iff, hc10, hc11, hc22]) (by simp)
      simpa using this
    have hT : ({x, c1} : Finset ℕ) ⊆ Finset.range w := by
      simp [Finset.insert_subset_iff, hxw, hc1w]
    have := Finset.sum_le_sum_of_subset (f := fun x' => g x' - 1) hT
    rw [Finset.sum_pair (Ne.symm hc1x)] at this
    omega
  · have hgc1 : 2 ≤ g c1 := by
      have := hlow c1 {(c1, 0), (c1, 1)} (by simp [Finset.insert_subset_iff, hc10, hc11])
        (by simp)
      simpa using this
    have hgc2 : 2 ≤ g c2 := by
      have := hlow c2 {(c2, 1), (c2, 2)} (by simp [Finset.insert_subset_iff, hc21, hc22])
        (by simp)
      simpa using this
    have hT : ({x, c1, c2} : Finset ℕ) ⊆ Finset.range w := by
      simp [Finset.insert_subset_iff, hxw, hc1w, hc2w]
    have := Finset.sum_le_sum_of_subset (f := fun x' => g x' - 1) hT
    rw [Finset.sum_insert (by simp [Ne.symm hc1x, Ne.symm hc2x]), Finset.sum_pair hc12] at this
    omega

/-- Checking a column interval inside the rows `0, 1, 2`. -/
private lemma colIs_of {S : Finset (ℕ × ℕ)} {x a b : ℕ} (hb : b ≤ 2)
    (hS : ∀ y, (x, y) ∈ S → y < 3) (h : ∀ y < 3, ((x, y) ∈ S ↔ a ≤ y ∧ y ≤ b)) :
    ColIs S x a b := by
  intro y
  by_cases hy : y < 3
  · exact h y hy
  · constructor
    · intro hm; exact absurd (hS y hm) hy
    · intro hm; omega

/-- Every fixed polyomino with `w + 2` cells and width `w` is a good configuration. -/
private lemma struct {w : ℕ} {S : Finset (ℕ × ℕ)} (h : IsPoly (w + 2) w S) : Good w S := by
  have hbox := subset_box h
  obtain ⟨hcard, ⟨p0, hp0S, hp0⟩, -, hsup, hconn⟩ := h
  have hb : ∀ p ∈ S, p.1 < w ∧ p.2 < 3 := by
    intro p hp
    have := hbox hp
    simp only [box, Finset.mem_product, Finset.mem_range] at this
    omega
  have hne : S.Nonempty := ⟨p0, hp0S⟩
  obtain ⟨m, hmS, hm⟩ := Finset.exists_mem_eq_sup S hne Prod.fst
  have hfst : ∀ p q : ℕ × ℕ, Adj p q → q.1 ≤ p.1 + 1 := by
    intro p q h
    unfold Adj at h
    omega
  have hcol : ∀ x < w, ∃ y, (x, y) ∈ S := by
    intro x hx
    obtain ⟨c, hc, hcx⟩ :=
      exists_coord Prod.fst hfst hp0S (hconn p0 hp0S m hmS) x (by omega) (by omega)
    exact ⟨c.2, by rw [← hcx]; exact hc⟩
  refine ⟨fun p hp => (hb p hp).1, ?_, ?_⟩
  · intro x hx
    have hS3 : ∀ y, (x, y) ∈ S → y < 3 := fun y hy => (hb _ hy).2
    by_cases h0 : (x, 0) ∈ S <;> by_cases h1 : (x, 1) ∈ S <;> by_cases h2 : (x, 2) ∈ S
    · exact ⟨0, 2, by omega, le_rfl, colIs_of le_rfl hS3 fun y hy => by
        interval_cases y <;> simp [h0, h1, h2]⟩
    · exact ⟨0, 1, by omega, by omega, colIs_of (by omega) hS3 fun y hy => by
        interval_cases y <;> simp [h0, h1, h2]⟩
    · exact (no_gap hcard (fun p hp => (hb p hp).1) hcol hconn h0 h1 h2).elim
    · exact ⟨0, 0, le_rfl, by omega, colIs_of (by omega) hS3 fun y hy => by
        interval_cases y <;> simp [h0, h1, h2]⟩
    · exact ⟨1, 2, by omega, le_rfl, colIs_of le_rfl hS3 fun y hy => by
        interval_cases y <;> simp [h0, h1, h2]⟩
    · exact ⟨1, 1, le_rfl, by omega, colIs_of (by omega) hS3 fun y hy => by
        interval_cases y <;> simp [h0, h1, h2]⟩
    · exact ⟨2, 2, le_rfl, le_rfl, colIs_of le_rfl hS3 fun y hy => by
        interval_cases y <;> simp [h0, h1, h2]⟩
    · exfalso
      obtain ⟨y, hy⟩ := hcol x hx
      have := hS3 y hy
      interval_cases y <;> contradiction
  · intro x hx
    by_contra hno
    obtain ⟨y0, hy0⟩ := hcol x (by omega)
    obtain ⟨y1, hy1⟩ := hcol (x + 1) hx
    obtain ⟨b, hbA, c, hcS, hcA, hbc⟩ :=
      Math0.Statements.A308359.frontier (A := S.filter (fun p => p.1 ≤ x))
        (Finset.mem_filter.2 ⟨hy0, le_rfl⟩) (by simp) (hconn _ hy0 _ hy1)
    rw [Finset.mem_filter] at hbA hcA
    have hcx : x < c.1 := by
      by_contra hh
      exact hcA ⟨hcS, by omega⟩
    unfold Adj at hbc
    have e1 : b.1 = x := by omega
    have e2 : c.1 = x + 1 := by omega
    have e3 : b.2 = c.2 := by omega
    refine hno ⟨b.2, ?_, ?_⟩
    · rw [← e1]; exact hbA.1
    · rw [e3, ← e2]; exact hcS

/-- The fixed polyominoes with `w + 2` cells and width `w` are exactly the good configurations
with `w + 2` cells meeting row `0`. -/
private lemma poly_iff {w : ℕ} (hw : 1 ≤ w) (S : Finset (ℕ × ℕ)) :
    IsPoly (w + 2) w S ↔ Good w S ∧ S.card = w + 2 ∧ ∃ p ∈ S, p.2 = 0 := by
  constructor
  · intro h
    exact ⟨struct h, h.1, h.2.2.1⟩
  · rintro ⟨hS, hcard, hrow⟩
    obtain ⟨a0, b0, hab0, -, hc0⟩ := hS.2.1 0 (by omega)
    obtain ⟨a1, b1, hab1, -, hc1⟩ := hS.2.1 (w - 1) (by omega)
    have hm := (hc1 a1).2 ⟨le_rfl, hab1⟩
    refine ⟨hcard, ⟨(0, a0), (hc0 a0).2 ⟨le_rfl, hab0⟩, rfl⟩, hrow, ?_, good_conn hS⟩
    have h1 : S.sup Prod.fst ≤ w - 1 := Finset.sup_le fun p hp => by have := hS.1 p hp; omega
    have h2 := Finset.le_sup (f := Prod.fst) hm
    simp only at h2
    omega

/-- A state `(e, a, b, z)`: the excess `e` (cells minus columns), the last column `a, …, b`, and
whether row `0` is used. -/
private abbrev State := ℕ × ℕ × ℕ × Bool

/-- The 36 states with `e ≤ 2` and `a ≤ b ≤ 2`. -/
private def states : Finset State :=
  (Finset.range 3 ×ˢ Finset.range 3 ×ˢ Finset.range 3 ×ˢ (Finset.univ : Finset Bool)).filter
    (fun s => s.2.1 ≤ s.2.2.1)

/-- A configuration in state `t` extended by the column `a, …, b` (of state `s = (e, a, b, z)`)
is in state `s`: excesses add up, the two columns overlap, and the row-`0` flag is updated. -/
private def Compat (s t : State) : Prop :=
  s.1 = t.1 + (s.2.2.1 - s.2.1) ∧ s.2.1 ≤ t.2.2.1 ∧ t.2.1 ≤ s.2.2.1 ∧
    s.2.2.2 = (t.2.2.2 || decide (s.2.1 = 0))

/-- `Compat` is decidable. -/
private instance (s t : State) : Decidable (Compat s t) :=
  inferInstanceAs (Decidable (s.1 = t.1 + (s.2.2.1 - s.2.1) ∧ s.2.1 ≤ t.2.2.1 ∧
    t.2.1 ≤ s.2.2.1 ∧ s.2.2.2 = (t.2.2.2 || decide (s.2.1 = 0))))

/-- The transfer-matrix count: `D w s` configurations of width `w` in state `s`. -/
private def D : ℕ → State → ℕ
  | 0, _ => 0
  | 1, s => if s.1 = s.2.2.1 - s.2.1 ∧ s.2.2.2 = decide (s.2.1 = 0) then 1 else 0
  | w + 2, s => ∑ t ∈ states.filter (Compat s), D (w + 1) t

/-- The coefficients `(A, B, C)` of the closed form `D w s = A w² + B w + C` (`w ≥ 3`). -/
private def coef : State → ℤ × ℤ × ℤ
  | (0, 0, 0, true) => (0, 0, 1)
  | (0, 1, 1, false) => (0, 0, 1)
  | (0, 2, 2, false) => (0, 0, 1)
  | (1, 0, 0, true) => (0, 2, -3)
  | (1, 0, 1, true) => (0, 0, 2)
  | (1, 1, 1, false) => (0, 2, -3)
  | (1, 1, 1, true) => (0, 2, -3)
  | (1, 1, 2, false) => (0, 0, 2)
  | (1, 2, 2, false) => (0, 2, -3)
  | (2, 0, 0, true) => (3, -11, 12)
  | (2, 0, 1, true) => (0, 6, -11)
  | (2, 0, 2, true) => (0, 0, 3)
  | (2, 1, 1, false) => (2, -10, 13)
  | (2, 1, 1, true) => (4, -15, 16)
  | (2, 1, 2, false) => (0, 4, -8)
  | (2, 1, 2, true) => (0, 2, -3)
  | (2, 2, 2, false) => (2, -10, 13)
  | (2, 2, 2, true) => (1, -1, -1)
  | _ => (0, 0, 0)

/-- The final states: excess `2`, row `0` used. -/
private def final : Finset State := states.filter (fun s => s.1 = 2 ∧ s.2.2.2 = true)

set_option maxHeartbeats 4000000 in
/-- The quadratic coefficients are invariant under the transfer step. -/
private lemma coefA : ∀ s ∈ states, ∑ t ∈ states.filter (Compat s), (coef t).1 = (coef s).1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- The transfer step on the linear coefficients. -/
private lemma coefB : ∀ s ∈ states,
    ∑ t ∈ states.filter (Compat s), (coef t).2.1 = 2 * (coef s).1 + (coef s).2.1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- The transfer step on the constant coefficients. -/
private lemma coefC : ∀ s ∈ states,
    ∑ t ∈ states.filter (Compat s), (coef t).2.2 = (coef s).1 + (coef s).2.1 + (coef s).2.2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- The closed form at `w = 3`. -/
private lemma D_three : ∀ s ∈ states,
    (D 3 s : ℤ) = (coef s).1 * 3 ^ 2 + (coef s).2.1 * 3 + (coef s).2.2 := by
  decide +kernel

/-- Summing the closed forms over the final states gives `8w² - 19w + 16`. -/
private lemma final_sum : (∑ s ∈ final, (coef s).1 = 8) ∧ (∑ s ∈ final, (coef s).2.1 = -19) ∧
    (∑ s ∈ final, (coef s).2.2 = 16) := by
  decide +kernel

/-- Membership in `states`. -/
private lemma mem_states {s : State} :
    s ∈ states ↔ s.1 < 3 ∧ s.2.1 < 3 ∧ s.2.2.1 < 3 ∧ s.2.1 ≤ s.2.2.1 := by
  obtain ⟨e, a, b, z⟩ := s
  simp [states, and_assoc]

/-- The column `{x} × [a, b]`. -/
private def colSet (x a b : ℕ) : Finset (ℕ × ℕ) := {x} ×ˢ Finset.Icc a b

/-- Membership in a column. -/
private lemma mem_colSet {x a b x' y : ℕ} : (x', y) ∈ colSet x a b ↔ x' = x ∧ a ≤ y ∧ y ≤ b := by
  simp only [colSet, Finset.mem_product, Finset.mem_singleton, Finset.mem_Icc]

/-- The size of a column. -/
private lemma card_colSet (x a b : ℕ) : (colSet x a b).card = b + 1 - a := by
  simp [colSet]

/-- Adding the column `{x} × [a, b]` uses row `0` iff it was used or `a = 0`. -/
private lemma row0_union {S' : Finset (ℕ × ℕ)} {x a b : ℕ} :
    (∃ p ∈ S' ∪ colSet x a b, p.2 = 0) ↔ (∃ p ∈ S', p.2 = 0) ∨ a = 0 := by
  constructor
  · rintro ⟨⟨x', y⟩, hp, hp0⟩
    rcases Finset.mem_union.1 hp with hp | hp
    · exact Or.inl ⟨_, hp, hp0⟩
    · right
      rw [mem_colSet] at hp
      simp only at hp0
      omega
  · rintro (⟨p, hp, hp0⟩ | ha)
    · exact ⟨p, Finset.mem_union_left _ hp, hp0⟩
    · exact ⟨(x, 0), Finset.mem_union_right _ (mem_colSet.2 ⟨rfl, by omega, by omega⟩), rfl⟩

/-- `S` is a good configuration of width `w` in state `s`. -/
private def InP (w : ℕ) (s : State) (S : Finset (ℕ × ℕ)) : Prop :=
  Good w S ∧ S.card = w + s.1 ∧ ColIs S (w - 1) s.2.1 s.2.2.1 ∧
    ((∃ p ∈ S, p.2 = 0) ↔ s.2.2.2 = true)

open scoped Classical in
/-- The finite set of good configurations of width `w` in state `s`. -/
private noncomputable def Pset (w : ℕ) (s : State) : Finset (Finset (ℕ × ℕ)) :=
  (Finset.range w ×ˢ Finset.range 3).powerset.filter (InP w s)

/-- Membership in `Pset`. -/
private lemma mem_Pset {w : ℕ} {s : State} {S : Finset (ℕ × ℕ)} :
    S ∈ Pset w s ↔ InP w s S := by
  classical
  unfold Pset
  rw [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun p hp => ?_, h⟩
    have := good_row h.1 hp
    simp only [Finset.mem_product, Finset.mem_range]
    omega

/-- A configuration has only one state. -/
private lemma Pset_unique {w : ℕ} {s t : State} (hs : s ∈ states) (ht : t ∈ states)
    {S : Finset (ℕ × ℕ)} (h1 : S ∈ Pset w s) (h2 : S ∈ Pset w t) : s = t := by
  obtain ⟨e, a, b, z⟩ := s
  obtain ⟨e', a', b', z'⟩ := t
  rw [mem_Pset] at h1 h2
  rw [mem_states] at hs ht
  obtain ⟨-, hc1, hcol1, hz1⟩ := h1
  obtain ⟨-, hc2, hcol2, hz2⟩ := h2
  simp only at hs ht hc1 hcol1 hz1 hc2 hcol2 hz2
  obtain ⟨rfl, rfl⟩ := colIs_unique hcol1 hcol2 hs.2.2.2 ht.2.2.2
  have : z = z' := Bool.eq_iff_iff.2 (hz1.symm.trans hz2)
  subst this
  have : e = e' := by omega
  subst this
  rfl

/-- Width one: the only configuration is the column itself. -/
private lemma Pset_one {s : State} (hs : s ∈ states) : (Pset 1 s).card = D 1 s := by
  obtain ⟨e, a, b, z⟩ := s
  rw [mem_states] at hs
  simp only at hs
  have hsub : ∀ S ∈ Pset 1 (e, a, b, z), S = colSet 0 a b := by
    intro S hS
    rw [mem_Pset] at hS
    obtain ⟨hG, -, hcol, -⟩ := hS
    simp only [Nat.sub_self] at hcol
    ext ⟨x, y⟩
    rw [mem_colSet]
    constructor
    · intro hp
      have h1 : x = 0 := by have := hG.1 _ hp; simp only at this; omega
      subst h1
      exact ⟨rfl, (hcol y).1 hp⟩
    · rintro ⟨rfl, h⟩
      exact (hcol y).2 h
  have hrow : (∃ p ∈ colSet 0 a b, p.2 = 0) ↔ a = 0 := by
    have := row0_union (S' := ∅) (x := 0) (a := a) (b := b)
    simpa using this
  rw [show D 1 (e, a, b, z) = if e = b - a ∧ z = decide (a = 0) then 1 else 0 from rfl]
  split_ifs with hcond
  · obtain ⟨rfl, rfl⟩ := hcond
    rw [Finset.card_eq_one]
    refine ⟨colSet 0 a b, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, hsub⟩⟩
    rw [mem_Pset]
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rintro ⟨x, y⟩ hp
      rw [mem_colSet] at hp
      simp only
      omega
    · intro x hx
      refine ⟨a, b, hs.2.2.2, by omega, ?_⟩
      intro y
      rw [mem_colSet]
      omega
    · intro x hx
      omega
    · simp only
      rw [card_colSet]
      omega
    · intro y
      rw [mem_colSet]
      simp
    · simp only [decide_eq_true_eq]
      exact hrow
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro S hS
    have hSC := hsub S hS
    rw [mem_Pset] at hS
    obtain ⟨-, hcard, -, hz⟩ := hS
    subst hSC
    apply hcond
    rw [card_colSet] at hcard
    simp only at hcard hz
    have he : e = b - a := by clear hrow hz hsub hcond; omega
    refine ⟨he, Bool.eq_iff_iff.2 ?_⟩
    rw [← hz, hrow, decide_eq_true_eq]

/-- The transfer step: removing the last column is a bijection from the configurations of width
`w + 1` in state `s` onto the configurations of width `w` in states compatible with `s`. -/
private lemma Pset_succ {w : ℕ} (hw : 1 ≤ w) {s : State} (hs : s ∈ states) :
    (Pset (w + 1) s).card = ∑ t ∈ states.filter (Compat s), (Pset w t).card := by
  classical
  rw [← Finset.card_biUnion (s := states.filter (Compat s)) (t := Pset w) ?_]
  swap
  · intro t ht t' ht' htt'
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ht ht'
    rw [Function.onFun, Finset.disjoint_left]
    intro S h1 h2
    exact htt' (Pset_unique ht.1 ht'.1 h1 h2)
  obtain ⟨e, a, b, z⟩ := s
  rw [mem_states] at hs
  simp only at hs
  refine Finset.card_nbij' (fun S => S.filter (fun p => p.1 < w)) (fun S' => S' ∪ colSet w a b)
    ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_coe] at hS ⊢
    rw [mem_Pset] at hS
    obtain ⟨hG, hcard, hcol, hz⟩ := hS
    simp only [Nat.add_sub_cancel] at hcard hcol hz
    obtain ⟨a', b', hab', hb', hcol'⟩ := hG.2.1 (w - 1) (by omega)
    have hmem : ∀ x y, x < w → ((x, y) ∈ S.filter (fun p => p.1 < w) ↔ (x, y) ∈ S) := by
      intro x y hx
      simp [Finset.mem_filter, hx]
    have hSu : S = S.filter (fun p => p.1 < w) ∪ colSet w a b := by
      ext ⟨x, y⟩
      rw [Finset.mem_union, mem_colSet, Finset.mem_filter]
      constructor
      · intro hp
        by_cases hx : x < w
        · exact Or.inl ⟨hp, hx⟩
        · have := hG.1 _ hp
          simp only at this
          have hxw : x = w := by omega
          subst hxw
          exact Or.inr ⟨rfl, (hcol y).1 hp⟩
      · rintro (⟨hp, -⟩ | ⟨rfl, h⟩)
        · exact hp
        · exact (hcol y).2 h
    have hdisj : Disjoint (S.filter (fun p => p.1 < w)) (colSet w a b) := by
      rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ hp hpC
      rw [mem_colSet] at hpC
      have := (Finset.mem_filter.1 hp).2
      simp only at this
      omega
    have hG' : Good w (S.filter (fun p => p.1 < w)) := by
      refine ⟨fun p hp => (Finset.mem_filter.1 hp).2, ?_, ?_⟩
      · intro x hx
        obtain ⟨a1, b1, h1, h2, h3⟩ := hG.2.1 x (by omega)
        exact ⟨a1, b1, h1, h2, fun y => (hmem x y hx).trans (h3 y)⟩
      · intro x hx
        obtain ⟨y, hy1, hy2⟩ := hG.2.2 x (by omega)
        exact ⟨y, (hmem x y (by omega)).2 hy1, (hmem (x + 1) y hx).2 hy2⟩
    have hle := good_le_card hG'
    have hcardS : S.card = (S.filter (fun p => p.1 < w)).card + (b + 1 - a) := by
      conv_lhs => rw [hSu]
      rw [Finset.card_union_of_disjoint hdisj, card_colSet]
    obtain ⟨y, hy1, hy2⟩ := hG.2.2 (w - 1) (by omega)
    rw [Nat.sub_add_cancel hw] at hy2
    have hy1' := (hcol' y).1 hy1
    have hy2' := (hcol y).1 hy2
    have hrowS : (∃ p ∈ S, p.2 = 0) ↔
        (∃ p ∈ S.filter (fun p => p.1 < w), p.2 = 0) ∨ a = 0 := by
      conv_lhs => rw [hSu]
      exact row0_union
    have hnum : (S.filter (fun p => p.1 < w)).card - w < 3 ∧
        e = (S.filter (fun p => p.1 < w)).card - w + (b - a) ∧ a ≤ b' ∧ a' ≤ b ∧
        (S.filter (fun p => p.1 < w)).card = w + ((S.filter (fun p => p.1 < w)).card - w) := by
      clear hz hrowS hSu hmem hcol hcol' hG hG' hdisj
      omega
    rw [Finset.mem_biUnion]
    refine ⟨((S.filter (fun p => p.1 < w)).card - w, a', b',
      decide (∃ p ∈ S.filter (fun p => p.1 < w), p.2 = 0)), ?_, ?_⟩
    · rw [Finset.mem_filter, mem_states, Compat]
      simp only
      refine ⟨⟨hnum.1, by omega, by omega, hab'⟩, hnum.2.1, hnum.2.2.1, hnum.2.2.2.1, ?_⟩
      apply Bool.eq_iff_iff.2
      rw [← hz, hrowS]
      simp
    · rw [mem_Pset]
      refine ⟨hG', hnum.2.2.2.2, ?_, ?_⟩
      · intro y'
        exact (hmem _ y' (by omega)).trans (hcol' y')
      · simp
  · intro S' hS'
    simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_filter] at hS' ⊢
    obtain ⟨⟨e', a', b', z'⟩, ⟨ht, hcomp⟩, hS'⟩ := hS'
    rw [mem_states] at ht
    rw [mem_Pset] at hS' ⊢
    obtain ⟨hG, hcard, hcol, hz⟩ := hS'
    rw [Compat] at hcomp
    obtain ⟨he, h1, h2, hzz⟩ := hcomp
    simp only at ht hcard hcol hz he h1 h2 hzz ⊢
    have hdisj : Disjoint S' (colSet w a b) := by
      rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ hp hpC
      rw [mem_colSet] at hpC
      have := hG.1 _ hp
      simp only at this
      omega
    have hmemU : ∀ x y, x < w → ((x, y) ∈ S' ∪ colSet w a b ↔ (x, y) ∈ S') := by
      intro x y hx
      rw [Finset.mem_union, mem_colSet]
      constructor
      · rintro (h | ⟨rfl, -⟩)
        · exact h
        · omega
      · exact Or.inl
    have hcolw : ColIs (S' ∪ colSet w a b) w a b := by
      intro y
      rw [Finset.mem_union, mem_colSet]
      constructor
      · rintro (h | ⟨-, h⟩)
        · have := hG.1 _ h
          simp at this
        · exact h
      · intro h
        exact Or.inr ⟨rfl, h⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rintro ⟨x, y⟩ hp
      rcases Finset.mem_union.1 hp with hp | hp
      · have := hG.1 _ hp
        simp only at this ⊢
        omega
      · rw [mem_colSet] at hp
        simp only
        omega
    · intro x hx
      by_cases hx' : x < w
      · obtain ⟨a1, b1, h1, h2, h3⟩ := hG.2.1 x hx'
        exact ⟨a1, b1, h1, h2, fun y => (hmemU x y hx').trans (h3 y)⟩
      · have hxw : x = w := by omega
        subst hxw
        exact ⟨a, b, hs.2.2.2, by omega, hcolw⟩
    · intro x hx
      by_cases hx' : x + 1 < w
      · obtain ⟨y, hy1, hy2⟩ := hG.2.2 x hx'
        exact ⟨y, (hmemU x y (by omega)).2 hy1, (hmemU (x + 1) y hx').2 hy2⟩
      · have hxw : x = w - 1 := by omega
        subst hxw
        refine ⟨max a a', (hmemU _ _ (by omega)).2 ((hcol _).2 ⟨le_max_right _ _, by omega⟩), ?_⟩
        rw [Nat.sub_add_cancel hw]
        exact (hcolw _).2 ⟨le_max_left _ _, by omega⟩
    · rw [Finset.card_union_of_disjoint hdisj, hcard, card_colSet]
      omega
    · rw [Nat.add_sub_cancel]
      exact hcolw
    · rw [row0_union, hz, hzz]
      simp
  · intro S hS
    simp only [Finset.mem_coe] at hS
    rw [mem_Pset] at hS
    obtain ⟨hG, -, hcol, -⟩ := hS
    simp only [Nat.add_sub_cancel] at hcol
    ext ⟨x, y⟩
    rw [Finset.mem_union, mem_colSet, Finset.mem_filter]
    constructor
    · rintro (⟨h, -⟩ | ⟨rfl, h⟩)
      · exact h
      · exact (hcol y).2 h
    · intro h
      by_cases hx : x < w
      · exact Or.inl ⟨h, hx⟩
      · have := hG.1 _ h
        simp only at this
        have hxw : x = w := by omega
        subst hxw
        exact Or.inr ⟨rfl, (hcol y).1 h⟩
  · intro S' hS'
    simp only [Finset.mem_coe, Finset.mem_biUnion] at hS'
    obtain ⟨t, -, hS'⟩ := hS'
    rw [mem_Pset] at hS'
    ext ⟨x, y⟩
    rw [Finset.mem_filter, Finset.mem_union, mem_colSet]
    constructor
    · rintro ⟨h | ⟨rfl, -⟩, hx⟩
      · exact h
      · simp at hx
    · intro h
      exact ⟨Or.inl h, hS'.1.1 _ h⟩

/-- The configurations are counted by `D`. -/
private lemma card_Pset : ∀ w, 1 ≤ w → ∀ s ∈ states, (Pset w s).card = D w s := by
  intro w hw
  induction w, hw using Nat.le_induction with
  | base => exact fun s hs => Pset_one hs
  | succ w hw ih =>
    intro s hs
    rw [Pset_succ hw hs]
    obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
    show _ = ∑ t ∈ states.filter (Compat s), D (k + 1) t
    exact Finset.sum_congr rfl fun t ht => ih t (Finset.mem_filter.1 ht).1

/-- The closed form of `D w s` for `w ≥ 3`, by induction using the coefficient identities. -/
private lemma D_poly : ∀ w, 3 ≤ w → ∀ s ∈ states,
    (D w s : ℤ) = (coef s).1 * (w : ℤ) ^ 2 + (coef s).2.1 * w + (coef s).2.2 := by
  intro w hw
  induction w, hw using Nat.le_induction with
  | base =>
    intro s hs
    have := D_three s hs
    push_cast
    exact this
  | succ w hw ih =>
    intro s hs
    obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
    have hD : D (k + 1 + 1) s = ∑ t ∈ states.filter (Compat s), D (k + 1) t := rfl
    rw [hD, Nat.cast_sum, Finset.sum_congr rfl fun t ht => ih t (Finset.mem_filter.1 ht).1,
      Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      coefA s hs, coefB s hs, coefC s hs]
    push_cast
    ring

/-- Final states are states. -/
private lemma mem_final {s : State} (h : s ∈ final) : s ∈ states := (Finset.mem_filter.1 h).1

/-- `T(w + 2, w)` is the number of good configurations in the final states. -/
private lemma T_eq {w : ℕ} (hw : 1 ≤ w) : T (w + 2) w = ∑ s ∈ final, (Pset w s).card := by
  classical
  rw [T, ← Finset.card_biUnion (s := final) (t := Pset w) ?_]
  · rw [← Set.ncard_coe_finset]
    congr 1
    ext S
    simp only [Set.mem_ofPred_eq, Finset.coe_biUnion, Finset.mem_coe, Set.mem_iUnion, exists_prop]
    rw [poly_iff hw]
    constructor
    · rintro ⟨hG, hcard, hrow⟩
      obtain ⟨a, b, hab, hb, hcol⟩ := hG.2.1 (w - 1) (by omega)
      refine ⟨(2, a, b, true), ?_, ?_⟩
      · rw [final, Finset.mem_filter, mem_states]
        exact ⟨⟨by norm_num, show a < 3 by omega, show b < 3 by omega, hab⟩, rfl, rfl⟩
      · rw [mem_Pset]
        exact ⟨hG, hcard, hcol, by simp [hrow]⟩
    · rintro ⟨s, hs, hS⟩
      rw [final, Finset.mem_filter] at hs
      rw [mem_Pset] at hS
      obtain ⟨hG, hcard, -, hz⟩ := hS
      rw [hs.2.1] at hcard
      exact ⟨hG, hcard, hz.2 hs.2.2⟩
  · intro t ht t' ht' htt'
    simp only [final, Finset.coe_filter, Set.mem_ofPred_eq] at ht ht'
    rw [Function.onFun, Finset.disjoint_left]
    intro S h1 h2
    exact htt' (Pset_unique ht.1 ht'.1 h1 h2)

/-- **Mathar's conjecture for A308359.** For every `n ≥ 5` the number of fixed polyominoes with
`n` cells and width `n - 2` is `8n² - 51n + 86`. -/
theorem result : statement := by
  intro n hn
  obtain ⟨w, rfl⟩ : ∃ w, n = w + 2 := ⟨n - 2, by omega⟩
  rw [Nat.add_sub_cancel, T_eq (by omega),
    Finset.sum_congr rfl fun s hs => card_Pset w (by omega) s (mem_final hs),
    Nat.cast_sum,
    Finset.sum_congr rfl fun s hs => D_poly w (by omega) s (mem_final hs),
    Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    final_sum.1, final_sum.2.1, final_sum.2.2]
  push_cast
  ring

end Math0.Frontier.A308359

#math0_settles Math0.Frontier.A308359.result Math0.Statements.A308359.statement
