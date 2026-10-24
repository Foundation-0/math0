/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A178295: collinear 4-subsets of the grid `{0, …, 4}ⁿ`

Source: https://oeis.org/A178295, _R. J. Mathar_, May 24 2010 (FORMULA section). Verbatim:
> Conjecture: a(n) = 9^n/2+3*7^n/2-2*5^n. a(n)= +21*a(n-1) -143*a(n-2) +315*a(n-3).
> G.f.: x*(-5+41*x)/((9*x-1)*(7*x-1)*(5*x-1)). [_R. J. Mathar_, May 24 2010]

The entry (_R. H. Hardin_, May 24 2010, offset `0`) is "Number of collinear point 4-tuples in a
5 X 5 X 5 X... n-dimensional cubic grid."

## Encoding

* *The grid.* The `5 × 5 × ⋯ × 5` grid in dimension `n` is `Pt n = Fin n → Fin 5`, i.e. the
  points of `{0, …, 4}ⁿ ⊆ ℤⁿ` (`coord p i ∈ ℤ` is the `i`-th coordinate). For `n = 0` it is a
  single point.
* *"Point 4-tuples".* These are 4-element sets of grid points (unordered, distinct points): the
  data `a(1) = 5 = C(5, 4)` and `a(2) = 64` (25 rows, 25 columns, 2 · 5 on the two main
  diagonals and 4 on the four diagonals with 4 points) fix this reading.
* *Collinearity.* Three points are collinear (`Coll3 p q r`) iff the vectors `q - p` and `r - p`
  are parallel, i.e. all `2 × 2` minors `(q - p)ᵢ (r - p)ⱼ - (q - p)ⱼ (r - p)ᵢ` vanish. A finite
  set is collinear (`IsCollinear`) iff every three of its points (repetitions allowed) are.
  `isCollinear_iff_collinear` proves that this is exactly Mathlib's `Collinear ℝ` for the
  corresponding set of points of `ℝⁿ` (all points lie on one affine line).
* *The sequence.* `a n` is the number of 4-element subsets of `Pt n` that are collinear
  (`Finset.powersetCard 4` of `Finset.univ`, filtered by `IsCollinear`); it is computable.
* *Data.* `a` is too slow for the kernel as written, so `fastA` counts the same sets: the points
  are listed once each (`L n`), and for every pair `p, q` (in this order) the 4-sets with first
  two elements `p, q` are counted as `C(m, 2)`, where `m` is the number of later points `r` with
  `p, q, r` collinear (a 4-set `{p, q, r, s}` with `p ≠ q` is collinear iff `r` and `s` both lie
  on the line `pq`, `coll4_iff`). `a_eq_fastA` proves `a n = fastA n` for every `n`.
  `a_data` checks the listed terms `a(0), a(1), a(2)` in the kernel. `a(3) = 629` is out of
  reach for this `O(5^{3n})` evaluator (a kernel evaluation of `a(3)` with an evaluator of this
  kind ran out of memory above 10 GB), and a faster evaluator would need the structure of the
  long grid lines, which is the content of the conjecture itself. (A Python brute force over
  all lines gives `a(1), …, a(5) = 5, 64, 629, 5632, 48485`, as listed.) As a separate sanity
  check of the transcription of the three formulas (not about `a`), `closedForm_data` and
  `recurrence_data` check that the closed form gives, and the recurrence is satisfied by, all
  10 listed terms `0, 5, 64, …, 250334405`.
* *The conjecture* (`statement`) is the conjunction of the three stated formulas:
  1. `a(n) = 9^n/2 + 3*7^n/2 - 2*5^n` for every `n ≥ 0` (the offset; no range is given), in `ℚ`
     so that the divisions are exact;
  2. `a(n) = 21 a(n-1) - 143 a(n-2) + 315 a(n-3)` for every `n ≥ 3` (the range where all
     indices are in the domain `n ≥ 0`), in `ℤ`;
  3. the generating function: `∑ a(n) xⁿ = x(-5+41x) / ((9x-1)(7x-1)(5x-1))` as formal power
     series over `ℚ`, with Mathlib's inverse of a power series; the denominator has constant
     coefficient `-1 ≠ 0`, so this is the honest quotient (`genFun_iff` restates it as
     `A(x) · D(x) = x(-5+41x)`).
-/

namespace Math0.Statements.A178295

/-! ### The grid and collinearity -/

/-- The points of the `n`-dimensional `5 × 5 × ⋯ × 5` grid `{0, …, 4}ⁿ`. -/
abbrev Pt (n : ℕ) := Fin n → Fin 5

/-- The `i`-th coordinate of a grid point, as an integer. -/
def coord {n : ℕ} (p : Pt n) (i : Fin n) : ℤ := ((p i : ℕ) : ℤ)

/-- `p`, `q`, `r` are collinear: `q - p` and `r - p` are parallel, i.e. every `2 × 2` minor
`(q - p)ᵢ (r - p)ⱼ - (q - p)ⱼ (r - p)ᵢ` vanishes. -/
def Coll3 {n : ℕ} (p q r : Pt n) : Prop :=
  ∀ i j : Fin n, (coord q i - coord p i) * (coord r j - coord p j) =
    (coord q j - coord p j) * (coord r i - coord p i)

instance {n : ℕ} (p q r : Pt n) : Decidable (Coll3 p q r) := by
  unfold Coll3; infer_instance

/-- A finite set of grid points is collinear iff any three of its points are collinear. -/
def IsCollinear {n : ℕ} (s : Finset (Pt n)) : Prop :=
  ∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s, Coll3 p q r

instance {n : ℕ} : DecidablePred (IsCollinear (n := n)) := fun s => by
  unfold IsCollinear; infer_instance

/-- A178295: the number of collinear 4-point subsets of the grid `{0, …, 4}ⁿ`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Pt n)).powersetCard 4 |>.filter IsCollinear).card

/-! ### `IsCollinear` is collinearity in `ℝⁿ` -/

/-- A grid point as a point of `ℝⁿ`. -/
def toReal {n : ℕ} (p : Pt n) : Fin n → ℝ := fun i => ((p i : ℕ) : ℝ)

theorem coll3_iff_real {n : ℕ} (p q r : Pt n) : Coll3 p q r ↔
    ∀ i j : Fin n, (toReal q i - toReal p i) * (toReal r j - toReal p j) =
      (toReal q j - toReal p j) * (toReal r i - toReal p i) := by
  unfold Coll3 coord toReal
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [← Int.cast_inj (α := ℝ)]
  push_cast
  rfl

/-- `IsCollinear s` says exactly that the points of `s` lie on one line of `ℝⁿ`. -/
theorem isCollinear_iff_collinear {n : ℕ} (s : Finset (Pt n)) :
    IsCollinear s ↔ Collinear ℝ (toReal '' (s : Set (Pt n))) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  constructor
  · intro h
    by_cases hs : ∃ p ∈ s, ∃ q ∈ s, toReal p ≠ toReal q
    · obtain ⟨p, hp, q, hq, hpq⟩ := hs
      obtain ⟨k, hk⟩ : ∃ k, toReal p k ≠ toReal q k := by
        by_contra hc
        push Not at hc
        exact hpq (funext hc)
      have hd : toReal q k - toReal p k ≠ 0 := sub_ne_zero.mpr (Ne.symm hk)
      refine ⟨toReal p, toReal q - toReal p, ?_⟩
      rintro _ ⟨r, hr, rfl⟩
      refine ⟨(toReal r k - toReal p k) / (toReal q k - toReal p k), ?_⟩
      have hc := (coll3_iff_real p q r).1 (h p hp q hq r hr)
      funext j
      have hkj := hc k j
      simp only [vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      field_simp
      linear_combination hkj
    · push Not at hs
      by_cases hne : s.Nonempty
      · obtain ⟨p, hp⟩ := hne
        refine ⟨toReal p, 0, ?_⟩
        rintro _ ⟨r, hr, rfl⟩
        exact ⟨0, by simp [hs r hr p hp]⟩
      · refine ⟨0, 0, ?_⟩
        rintro _ ⟨r, hr, rfl⟩
        exact absurd ⟨r, hr⟩ hne
  · rintro ⟨p₀, v, h⟩ p hp q hq r hr
    obtain ⟨x, hx⟩ := h (toReal p) ⟨p, hp, rfl⟩
    obtain ⟨y, hy⟩ := h (toReal q) ⟨q, hq, rfl⟩
    obtain ⟨z, hz⟩ := h (toReal r) ⟨r, hr, rfl⟩
    rw [coll3_iff_real]
    intro i j
    rw [hx, hy, hz]
    simp only [vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-! ### Collinear 4-sets -/

/-- Collinearity of a multiset of grid points (used for the 4-sets as lists). -/
def Q {n : ℕ} (m : Multiset (Pt n)) : Prop := ∀ p ∈ m, ∀ q ∈ m, ∀ r ∈ m, Coll3 p q r

instance {n : ℕ} : DecidablePred (Q (n := n)) := fun m => by unfold Q; infer_instance

/-- If `q ≠ p` (witnessed by the coordinate `k`), all points on the line `pq` are collinear. -/
theorem coll3_of_line {n : ℕ} (p q x y z : Pt n) (k : Fin n) (hk : coord q k ≠ coord p k)
    (hx : Coll3 p q x) (hy : Coll3 p q y) (hz : Coll3 p q z) : Coll3 x y z := by
  intro i j
  set D := coord q k - coord p k with hD
  have hD0 : D ≠ 0 := sub_ne_zero.mpr hk
  have hA : ∀ i, D * (coord y i - coord x i) =
      (coord q i - coord p i) * (coord y k - coord x k) := by
    intro i
    linear_combination hy k i - hx k i
  have hB : ∀ i, D * (coord z i - coord x i) =
      (coord q i - coord p i) * (coord z k - coord x k) := by
    intro i
    linear_combination hz k i - hx k i
  apply mul_left_cancel₀ (pow_ne_zero 2 hD0)
  calc D ^ 2 * ((coord y i - coord x i) * (coord z j - coord x j))
      = (D * (coord y i - coord x i)) * (D * (coord z j - coord x j)) := by ring
    _ = (D * (coord y j - coord x j)) * (D * (coord z i - coord x i)) := by
        rw [hA i, hB j, hA j, hB i]; ring
    _ = D ^ 2 * ((coord y j - coord x j) * (coord z i - coord x i)) := by ring

theorem coord_ne_of_ne {n : ℕ} {p q : Pt n} (h : p ≠ q) : ∃ k, coord q k ≠ coord p k := by
  by_contra hc
  push Not at hc
  apply h
  funext k
  have := hc k
  unfold coord at this
  exact Fin.ext (by exact_mod_cast this.symm)

theorem coll3_self_left {n : ℕ} (p q : Pt n) : Coll3 p q p := by
  intro i j; ring

theorem coll3_self_right {n : ℕ} (p q : Pt n) : Coll3 p q q := by
  intro i j; ring

/-- A 4-set `{p, q, r, s}` with `p ≠ q` is collinear iff `r` and `s` lie on the line `pq`. -/
theorem coll4_iff {n : ℕ} {p q : Pt n} (r s : Pt n) (h : p ≠ q) :
    Q (([p, q, r, s] : List (Pt n)) : Multiset (Pt n)) ↔ Coll3 p q r ∧ Coll3 p q s := by
  unfold Q
  simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · intro H
    exact ⟨H p (Or.inl rfl) q (Or.inr (Or.inl rfl)) r (Or.inr (Or.inr (Or.inl rfl))),
      H p (Or.inl rfl) q (Or.inr (Or.inl rfl)) s (Or.inr (Or.inr (Or.inr rfl)))⟩
  · rintro ⟨hr, hs⟩
    obtain ⟨k, hk⟩ := coord_ne_of_ne h
    have hall : ∀ x, x = p ∨ x = q ∨ x = r ∨ x = s → Coll3 p q x := by
      rintro x (rfl | rfl | rfl | rfl)
      · exact coll3_self_left _ _
      · exact coll3_self_right _ _
      · exact hr
      · exact hs
    intro x hx y hy z hz
    exact coll3_of_line p q x y z k hk (hall x hx) (hall y hy) (hall z hz)

/-! ### A fast evaluator -/

/-- All points of `Pt n`, each listed once. -/
def L : (n : ℕ) → List (Pt n)
  | 0 => [fun i => i.elim0]
  | n + 1 => (List.finRange 5).flatMap fun c => (L n).map fun p => (Fin.cons c p : Pt (n + 1))

theorem mem_L : ∀ (n : ℕ) (p : Pt n), p ∈ L n
  | 0, p => by
    simp only [L, List.mem_singleton]
    funext i; exact i.elim0
  | n + 1, p => by
    simp only [L, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and]
    exact ⟨p 0, Fin.tail p, mem_L n _, Fin.cons_self_tail p⟩

theorem nodup_L : ∀ n : ℕ, (L n).Nodup
  | 0 => List.nodup_singleton _
  | n + 1 => by
    simp only [L]
    rw [List.nodup_flatMap]
    refine ⟨fun c _ => (nodup_L n).map (Fin.cons_right_injective (α := fun _ => Fin 5) c), ?_⟩
    refine (List.nodup_finRange 5).pairwise_of_forall_ne ?_
    intro c _ d _ hcd
    simp only [Function.onFun, List.disjoint_left, List.mem_map]
    rintro _ ⟨x, _, rfl⟩ ⟨y, _, hy⟩
    exact hcd (congrFun hy 0).symm

theorem univ_val (n : ℕ) :
    (Finset.univ : Finset (Pt n)).val = ((L n : List (Pt n)) : Multiset (Pt n)) := by
  have : (⟨(L n : Multiset (Pt n)), nodup_L n⟩ : Finset (Pt n)) = Finset.univ :=
    Finset.eq_univ_of_forall fun p => mem_L n p
  rw [← this]

/-- The coordinates of a grid point, as a list of natural numbers. -/
def coords {n : ℕ} (p : Pt n) : List ℕ := List.ofFn fun i => (p i : ℕ)

/-- Zip three lists. -/
def zip3 : List ℕ → List ℕ → List ℕ → List (ℕ × ℕ × ℕ)
  | x :: u, y :: v, z :: w => (x, y, z) :: zip3 u v w
  | _, _, _ => []

/-- For `x = (pᵢ, qᵢ, rᵢ)`, `y = (pⱼ, qⱼ, rⱼ)`: the minor condition
`(qᵢ - pᵢ)(rⱼ - pⱼ) = (qⱼ - pⱼ)(rᵢ - pᵢ)`, rearranged into an equation of natural numbers. -/
def minorB (x y : ℕ × ℕ × ℕ) : Bool :=
  Nat.beq (x.2.1 * y.2.2 + y.2.1 * x.1 + y.1 * x.2.2) (y.2.1 * x.2.2 + x.2.1 * y.1 + x.1 * y.2.2)

/-- `minorB` holds for all pairs `i < j`. -/
def pairsB : List (ℕ × ℕ × ℕ) → Bool
  | [] => true
  | x :: T => T.all (minorB x) && pairsB T

/-- Boolean version of `Coll3`. -/
def coll3B {n : ℕ} (p q r : Pt n) : Bool := pairsB (zip3 (coords p) (coords q) (coords r))

theorem zip3_ofFn : ∀ {n : ℕ} (f g h : Fin n → ℕ),
    zip3 (List.ofFn f) (List.ofFn g) (List.ofFn h) = List.ofFn fun i => (f i, g i, h i)
  | 0, _, _, _ => by simp [zip3]
  | n + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, zip3,
      zip3_ofFn (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ)]

theorem minorB_iff (x y : ℕ × ℕ × ℕ) : minorB x y = true ↔
    ((x.2.1 : ℤ) - x.1) * ((y.2.2 : ℤ) - y.1) = ((y.2.1 : ℤ) - y.1) * ((x.2.2 : ℤ) - x.1) := by
  unfold minorB
  rw [Nat.beq_eq]
  constructor
  · intro h
    have h' := congrArg (fun t : ℕ => (t : ℤ)) h
    push_cast at h'
    linear_combination h'
  · intro h
    have h' : ((x.2.1 * y.2.2 + y.2.1 * x.1 + y.1 * x.2.2 : ℕ) : ℤ) =
        ((y.2.1 * x.2.2 + x.2.1 * y.1 + x.1 * y.2.2 : ℕ) : ℤ) := by
      push_cast
      linear_combination h
    exact_mod_cast h'

theorem pairsB_iff (T : List (ℕ × ℕ × ℕ)) :
    pairsB T = true ↔ T.Pairwise fun x y => minorB x y = true := by
  induction T with
  | nil => simp [pairsB]
  | cons x T ih => simp [pairsB, ih, List.pairwise_cons, List.all_eq_true]

theorem pairsB_iff_forall (T : List (ℕ × ℕ × ℕ)) :
    pairsB T = true ↔ ∀ x ∈ T, ∀ y ∈ T, minorB x y = true := by
  have hsymm : ∀ x y, minorB x y = true → minorB y x = true := by
    intro x y h
    rw [minorB_iff] at h ⊢
    exact h.symm
  rw [pairsB_iff]
  constructor
  · intro h
    refine List.Pairwise.forall_of_forall_of_flip (fun x _ => ?_) h
      (h.imp fun {x y} hxy => hsymm x y hxy)
    rw [minorB_iff]
  · exact List.pairwise_of_forall_mem_list

theorem coll3B_iff {n : ℕ} (p q r : Pt n) : coll3B p q r = true ↔ Coll3 p q r := by
  unfold coll3B coords
  rw [zip3_ofFn, pairsB_iff_forall, List.forall_mem_ofFn_iff]
  refine forall_congr' fun i => ?_
  rw [List.forall_mem_ofFn_iff]
  refine forall_congr' fun j => ?_
  rw [minorB_iff]
  rfl

section Count

variable {α : Type*} (c : α → α → α → Bool)

/-- For a point `p` and a list `l`: the sum, over the entries `q` of `l`, of `C(m, 2)`, where
`m` is the number of entries `r` after `q` with `c p q r`. -/
def cnt2 (p : α) : List α → ℕ
  | [] => 0
  | q :: l => cnt2 p l + (l.countP (c p q)).choose 2

/-- The sum of `cnt2 c p l'` over the entries `p` of `l` (`l'` the list after `p`). -/
def cnt : List α → ℕ
  | [] => 0
  | p :: l => cnt l + cnt2 c p l

theorem countP_sublistsLen_one_all (P : α → Bool) (l : List α) :
    (l.sublistsLen 1).countP (fun t => t.all P) = l.countP P := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.sublistsLen_succ_cons, List.countP_append, ih, List.countP_cons]
    simp [List.sublistsLen_zero, List.countP_singleton]

theorem countP_sublistsLen_two_all (P : α → Bool) (l : List α) :
    (l.sublistsLen 2).countP (fun t => t.all P) = (l.countP P).choose 2 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.sublistsLen_succ_cons, List.countP_append, ih, List.countP_map, List.countP_cons]
    by_cases hx : P x = true
    · have : ((fun t => t.all P) ∘ List.cons x) = fun t => t.all P := by
        funext t; simp [hx]
      rw [this, countP_sublistsLen_one_all, if_pos hx, Nat.choose_succ_succ', Nat.choose_one_right]
      ring
    · have : ((fun t => t.all P) ∘ List.cons x) = fun _ => false := by
        funext t; simp [hx]
      rw [this, if_neg hx, List.countP_false]
      simp

variable (P : List α → Bool)
  (hP : ∀ p q r s, p ≠ q → P [p, q, r, s] = (c p q r && c p q s))
include hP

theorem countP_sublistsLen_three (p : α) (l : List α) (hp : p ∉ l) :
    (l.sublistsLen 3).countP (fun t => P (p :: t)) = cnt2 c p l := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    have hpq : p ≠ q := fun h => hp (h ▸ List.mem_cons_self)
    rw [List.sublistsLen_succ_cons, List.countP_append, ih (fun h => hp (List.mem_cons_of_mem _ h)),
      List.countP_map, cnt2, ← countP_sublistsLen_two_all]
    congr 1
    apply List.countP_congr
    intro t ht
    obtain ⟨-, hlen⟩ := List.mem_sublistsLen.1 ht
    match t, hlen with
    | [r, s], _ => simp [hP p q r s hpq]

theorem countP_sublistsLen_four (l : List α) (hl : l.Nodup) :
    (l.sublistsLen 4).countP P = cnt c l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.nodup_cons] at hl
    rw [List.sublistsLen_succ_cons, List.countP_append, ih hl.2, List.countP_map, cnt]
    congr 1
    exact countP_sublistsLen_three c P hP p l hl.1

end Count

/-- Fast evaluator of `a`. -/
def fastA (n : ℕ) : ℕ := cnt coll3B (L n)

/-- The fast evaluator computes `a`. -/
theorem a_eq_fastA (n : ℕ) : a n = fastA n := by
  unfold a fastA
  rw [Finset.card_def, Finset.filter_val, ← Multiset.countP_eq_card_filter]
  have h1 : Multiset.countP IsCollinear ((Finset.univ : Finset (Pt n)).powersetCard 4).val =
      Multiset.countP Q (((Finset.univ : Finset (Pt n)).powersetCard 4).val.map Finset.val) := by
    rw [Multiset.countP_map, Multiset.countP_eq_card_filter]
    rfl
  rw [h1, Finset.map_val_val_powersetCard, univ_val, Multiset.powersetCard_coe,
    Multiset.coe_countP, List.countP_map]
  refine countP_sublistsLen_four coll3B _ ?_ (L n) (nodup_L n)
  intro p q r s hpq
  rw [Bool.eq_iff_iff, Function.comp_apply, decide_eq_true_iff, coll4_iff r s hpq,
    Bool.and_eq_true, coll3B_iff, coll3B_iff]

/-- The definition reproduces the first terms listed in OEIS (kernel-checked): `a(0), a(1),
a(2)`. -/
theorem a_data : (List.range 3).map (fun i => a (i + 0)) = [0, 5, 64] := by
  simp only [Nat.add_zero, a_eq_fastA]
  decide +kernel

/-! ### The conjecture -/

/-- The 10 terms listed in the entry, `a(0), …, a(9)`. -/
def listed : List ℤ := [0, 5, 64, 629, 5632, 48485, 410944, 3470549, 29389312, 250334405]

/-- Transcription check (not about `a`): the conjectured closed form gives the listed terms. -/
theorem closedForm_data :
    (List.range 10).map (fun n : ℕ => (9 ^ n / 2 + 3 * 7 ^ n / 2 - 2 * 5 ^ n : ℚ)) =
      listed.map (fun x : ℤ => (x : ℚ)) := by
  norm_num [listed, List.range_succ]

/-- Transcription check (not about `a`): the listed terms satisfy the conjectured recurrence
for `3 ≤ n ≤ 9`. -/
theorem recurrence_data : ∀ n ∈ [3, 4, 5, 6, 7, 8, 9],
    listed.getD n 0 = 21 * listed.getD (n - 1) 0 - 143 * listed.getD (n - 2) 0 +
      315 * listed.getD (n - 3) 0 := by
  decide

/-- The conjectured denominator `(9x-1)(7x-1)(5x-1)`. -/
noncomputable def den : PowerSeries ℚ :=
  (9 * PowerSeries.X - 1) * (7 * PowerSeries.X - 1) * (5 * PowerSeries.X - 1)

/-- Mathar's conjecture (all three formulas):
`a(n) = 9^n/2 + 3*7^n/2 - 2*5^n` for all `n ≥ 0`;
`a(n) = 21 a(n-1) - 143 a(n-2) + 315 a(n-3)` for all `n ≥ 3`;
`∑ a(n) xⁿ = x(-5+41x)/((9x-1)(7x-1)(5x-1))`. -/
def statement : Prop :=
  (∀ n : ℕ, (a n : ℚ) = 9 ^ n / 2 + 3 * 7 ^ n / 2 - 2 * 5 ^ n) ∧
  (∀ n : ℕ, 3 ≤ n →
    (a n : ℤ) = 21 * (a (n - 1) : ℤ) - 143 * (a (n - 2) : ℤ) + 315 * (a (n - 3) : ℤ)) ∧
  PowerSeries.mk (fun n => (a n : ℚ)) =
    PowerSeries.X * (-5 + 41 * PowerSeries.X) *
      ((9 * PowerSeries.X - 1) * (7 * PowerSeries.X - 1) * (5 * PowerSeries.X - 1))⁻¹

theorem constantCoeff_den : PowerSeries.constantCoeff den ≠ 0 := by
  simp [den]

/-- The generating-function clause, with the denominator multiplied out. -/
theorem genFun_iff :
    PowerSeries.mk (fun n => (a n : ℚ)) =
        PowerSeries.X * (-5 + 41 * PowerSeries.X) *
          ((9 * PowerSeries.X - 1) * (7 * PowerSeries.X - 1) * (5 * PowerSeries.X - 1))⁻¹ ↔
      PowerSeries.mk (fun n => (a n : ℚ)) * den = PowerSeries.X * (-5 + 41 * PowerSeries.X) :=
  PowerSeries.eq_mul_inv_iff_mul_eq constantCoeff_den

end Math0.Statements.A178295
